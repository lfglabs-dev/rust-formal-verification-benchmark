"""Independent verifier: pristine repo copy + one submitted editable file.

Steps (all must pass):
  1. static policy (imports, forbidden tokens, textual theorem statement);
  2. copy the pristine benchmark (lakefile, extracted implementation, specs)
     into a fresh directory and overlay only the submitted editable file;
  3. `lake build <task module>` (full elaboration + kernel checking);
  4. a check module, elaborated in a context that never saw the submission's
     source, states `theorem rfvb_check : <canonical statement> := @<theorem>`,
     so the submitted theorem must have (definitionally) the canonical type;
  5. `#print axioms rfvb_check` must be a subset of the trusted Lean axioms.
"""
from __future__ import annotations

import hashlib
import re
import shutil
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from . import ROOT
from .limits import lake_command, run_limited
from .policy import policy_failure, split_statement
from .tasks import Task, opens_block

TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COPY_ROOTS = ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "extracted", "Benchmark"]
CHECK_NS = "Benchmark.VerifierCheck"


@dataclass
class VerifyResult:
    task_id: str
    theorem_name: str
    status: str
    detail: str = ""
    axioms: list[str] | None = None
    submitted_sha256: str | None = None
    duration_seconds: float = 0.0

    @property
    def passed(self) -> bool:
        return self.status == "passed"

    def to_json(self) -> dict:
        return {"task_id": self.task_id, "pass": self.passed, "status": self.status, "detail": self.detail,
                "axioms": self.axioms, "theorem_name": self.theorem_name,
                "submitted_sha256": self.submitted_sha256, "duration_seconds": self.duration_seconds}


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    gated = False
    if cmd and cmd[0] == "lake":
        cmd, gated = lake_command(cmd[1:])
    code, out = run_limited(cmd, cwd, timeout, gated=gated)
    return code, (out + "\ntimeout" if code == 124 else out)


def compact(output: str, limit: int = 6000) -> str:
    lines = [l for l in output.splitlines() if not l.startswith("trace:") and "LEAN_PATH=" not in l
             and not l.startswith("✔") and not l.startswith("⣿")]
    errs: list[str] = []
    for i, line in enumerate(lines):
        if "error" in line.lower():
            errs.extend(lines[i : i + 12])
    text = "\n".join(errs or lines)
    return text[-limit:]


def link_lake_packages(dst: Path, source_root: Path = ROOT) -> None:
    (dst / ".lake").mkdir(parents=True, exist_ok=True)
    pk = dst / ".lake" / "packages"
    if not pk.exists():
        pk.symlink_to((source_root / ".lake" / "packages").resolve(), target_is_directory=True)


def copy_build_artifacts(task: Task, dst: Path, source_root: Path = ROOT) -> None:
    """Seed a fresh copy with prebuilt oleans of the case's extraction and Specs.

    Files are copied (never hardlinked). Lake re-validates them against the
    pristine sources through its trace hashes and rebuilds anything stale.
    """
    src_build = source_root / ".lake" / "build"
    spec_rel = Path(*task.specs_module.split("."))
    for sub in ("lib/lean", "ir"):
        base = src_build / sub
        pkg_dir = base / task.lean_package
        if pkg_dir.is_dir():
            shutil.copytree(pkg_dir, dst / ".lake" / "build" / sub / task.lean_package, dirs_exist_ok=True)
        spec_parent = (base / spec_rel).parent
        if spec_parent.is_dir():
            for f in spec_parent.glob(spec_rel.name + ".*"):
                out = dst / ".lake" / "build" / sub / f.relative_to(base)
                out.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(f, out)


def copy_pristine(dst: Path, source_root: Path = ROOT) -> None:
    # Reference proofs are not needed (and not importable by policy); leave them out.
    ignore = shutil.ignore_patterns(".lake", "__pycache__", "Proofs")
    for name in COPY_ROOTS:
        src = source_root / name
        if src.is_dir():
            shutil.copytree(src, dst / name, ignore=ignore)
        else:
            shutil.copy2(src, dst / name)
    link_lake_packages(dst, source_root)


def statement_module(task: Task) -> str:
    binders, concl = split_statement(task.theorem_statement)
    prop = f"∀ {binders}, {concl}" if binders else concl
    return (
        f"import {task.specs_module}\n\n{opens_block(task)}\n\n"
        f"namespace {task.namespace}\n\n"
        f"/-- Canonical statement of task `{task.id}`. -/\n"
        f"def rfvb_canonical_statement : Prop :=\n  {prop}\n\n"
        f"end {task.namespace}\n"
    )


def check_module(task: Task, submitted_module: str) -> str:
    return (
        f"import {CHECK_NS}.Statement\nimport {submitted_module}\n\n"
        f"theorem {CHECK_NS}.rfvb_check : {task.namespace}.rfvb_canonical_statement :=\n"
        f"  @{task.theorem_name}\n\n"
        f"#print axioms {CHECK_NS}.rfvb_check\n"
    )


AXIOMS_RE = re.compile(r"depends on axioms: \[(?P<ax>[^\]]*)\]", re.DOTALL)


def parse_axioms(output: str) -> list[str] | None:
    if "does not depend on any axioms" in output:
        return []
    m = AXIOMS_RE.search(output)
    if not m:
        return None
    return [a.strip() for a in m.group("ax").replace("\n", " ").split(",") if a.strip()]


def verify_task(task: Task, submitted_file: Path, *, timeout_seconds: int = 900,
                source_root: Path = ROOT, keep: bool = False) -> VerifyResult:
    started = time.time()
    res = VerifyResult(task.id, task.theorem_name, "harness_error")
    try:
        if not submitted_file.is_file():
            res.status, res.detail = "theorem_missing", f"{submitted_file} not found"
            return res
        text = submitted_file.read_text(encoding="utf-8")
        res.submitted_sha256 = sha256_text(text)
        fail = policy_failure(task, text, allowed_local_imports=(task.specs_module,))
        if fail:
            res.status, res.detail = fail
            return res
        tmp = Path(tempfile.mkdtemp(prefix="rfvb-verify-"))
        repo = tmp / "repo"
        repo.mkdir()
        try:
            copy_pristine(repo, source_root)
            copy_build_artifacts(task, repo, source_root)
            rel = task.editable_file
            (repo / rel).parent.mkdir(parents=True, exist_ok=True)
            (repo / rel).write_text(text, encoding="utf-8")
            module = task.target_module
            check_dir = repo / "Benchmark" / "VerifierCheck"
            check_dir.mkdir(parents=True, exist_ok=True)
            (check_dir / "Statement.lean").write_text(statement_module(task), encoding="utf-8")
            (check_dir / "Check.lean").write_text(check_module(task, module), encoding="utf-8")
            code, out = run(["lake", "build", f"{CHECK_NS}.Statement"], repo, timeout_seconds)
            if code != 0:
                res.status, res.detail = "verifier_infra_error", "canonical statement failed to elaborate:\n" + compact(out)
                return res
            code, out = run(["lake", "build", module], repo, timeout_seconds)
            if code != 0:
                res.status = "timeout" if code == 124 else "lean_check_failed"
                res.detail = compact(out)
                return res
            code, out = run(["lake", "env", "lean", "Benchmark/VerifierCheck/Check.lean"], repo, timeout_seconds)
            if code == 75:
                res.status, res.detail = "verifier_infra_error", "no Lean slot available for the statement check:\n" + out[-2000:]
                return res
            if code == 124:
                res.status, res.detail = "timeout", compact(out)
                return res
            if code != 0:
                res.status = "theorem_statement_mismatch" if ("mismatch" in out or "type" in out) else "theorem_missing"
                res.detail = compact(out)
                return res
            axioms = parse_axioms(out)
            res.axioms = axioms
            if axioms is None:
                res.status, res.detail = "verifier_infra_error", "could not parse #print axioms output:\n" + out[-2000:]
                return res
            bad = sorted(set(axioms) - TRUSTED_AXIOMS)
            if bad:
                res.status, res.detail = "untrusted_axioms", f"proof depends on untrusted axioms: {bad}"
                return res
            res.status = "passed"
            return res
        finally:
            if not keep:
                shutil.rmtree(tmp, ignore_errors=True)
    except Exception as exc:  # report, never crash the caller
        res.status, res.detail = "harness_error", repr(exc)
        return res
    finally:
        res.duration_seconds = round(time.time() - started, 3)
