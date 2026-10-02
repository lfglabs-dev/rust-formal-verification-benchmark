"""Isolated per-task agent workspaces.

A workspace contains only what the agent may see: the pinned Lake project
files, the case's verbatim extraction, the case Specs, the single editable task
file, the original Rust sources and a task briefing (`TASK.md`). Reference
proofs (`Benchmark/Cases/*/*/Proofs/`) and other cases are never copied.
"""
from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

from . import ROOT
from .tasks import Task
from .verifier import copy_build_artifacts, link_lake_packages

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:partial\s+)?(?:def|impl_def|abbrev|inductive|structure|theorem)\s+([^\s:(]+)", re.M)


def _decl_blocks(text: str) -> list[tuple[str, str]]:
    """Split an Aeneas output file into (declared name, source block) pairs."""
    ns_match = re.search(r"^namespace\s+(\S+)", text, re.M)
    ns = ns_match.group(1) + "." if ns_match else ""
    starts = [m.start() for m in re.finditer(r"^/-- ", text, re.M)]
    blocks = []
    for i, st in enumerate(starts):
        end = starts[i + 1] if i + 1 < len(starts) else len(text)
        block = text[st:end].rstrip()
        block = re.sub(r"\n\s*end\s+\S+\s*$", "", block)
        m = DECL_RE.search(block)
        if m:
            blocks.append((ns + m.group(1), block))
    return blocks


def relevant_extraction(task: Task, source_root: Path = ROOT, limit: int = 24000) -> str:
    """Extracted definitions in the dependency cone of the task's specs."""
    consts = task.raw.get("extracted_constants")
    wanted = set(consts) if consts is not None else None
    parts = []
    for rel in task.implementation_files:
        if not rel.endswith(("Extraction/Types.lean", "Extraction/Funs.lean")):
            continue
        text = (source_root / rel).read_text(encoding="utf-8")
        chosen = [b for name, b in _decl_blocks(text) if wanted is None or name in wanted]
        if chosen:
            parts.append(f"-- from {rel}\n" + "\n\n".join(chosen))
    out = "\n\n".join(parts)
    if len(out) > limit:
        out = out[:limit] + "\n-- [truncated; use read_file for the rest]"
    return out


def task_summary(task: Task, source_root: Path = ROOT) -> str:
    raw = task.raw
    pbt = raw.get("pbt", {})
    strategies = "\n".join(f"  - `{k}`: `{v}`" for k, v in (pbt.get("strategies") or {}).items()) or "  - (none)"
    assumptions = "\n".join(f"  - `{a}`" for a in (pbt.get("assumptions") or [])) or "  - (none)"
    impl = "\n".join(f"- `{p}`" for p in task.implementation_files)
    return f"""# Task `{task.id}`

Prove the theorem `{task.theorem_name}` by editing **only**
`{task.editable_file}`.

## Contract
- Implementation (fixed, verbatim `cargo hax extract` output of the Rust crate):
{impl}
- Specification (fixed): `{task.specs_file}`
- Editable proof file: `{task.editable_file}` — exactly one target theorem.
- Original Rust sources and the property test: `{task.rust_dir}/`

## Origin
{raw.get('docstring', '').strip()}

- Property-based test: `{pbt.get('test')}` in `{pbt.get('source_file')}` ({pbt.get('framework')})
- Strategies:
{strategies}
- Assumptions:
{assumptions}
- Assertion: `{pbt.get('assertion')}`
- Functions under test: {', '.join('`' + f + '`' for f in raw.get('functions_under_test', []))}

## Semantics
`e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e` returns
`ok r` (no panic, no divergence) and `P r` holds. Arithmetic follows Rust
debug-build semantics: plain `+ - * << >>` panic on overflow.

## Specification (`{task.specs_file}`)
```lean
{(source_root / task.specs_file).read_text(encoding="utf-8").strip()}
```

## Extracted definitions used by the specification
```lean
{relevant_extraction(task, source_root)}
```

## Target statement
```lean
theorem {task.decl_name} {task.theorem_statement}
```

## Rules
- Do not change the theorem statement, name or namespace; keep the imports
  limited to the case Specs and Mathlib/Aeneas/CoreModels/Hax modules.
- Forbidden: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `unsafe`, syntax extensions (`macro`, `notation`, `syntax`, `elab`, ...),
  `#eval`, `set_option debug.*`. The final proof may only depend on the axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- Helper lemmas are allowed inside the editable file.
- The independent verifier rebuilds your file in a pristine copy of the
  benchmark and checks the statement and the axioms.
"""


def build_workspace(task: Task, dst: Path, *, source_root: Path = ROOT, warm: bool = True) -> Path:
    if dst.exists():
        shutil.rmtree(dst)
    dst.mkdir(parents=True)
    for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        shutil.copy2(source_root / name, dst / name)
    shutil.copytree(source_root / "extracted" / task.lean_package, dst / "extracted" / task.lean_package)
    for rel in (task.specs_file, task.editable_file):
        (dst / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / rel, dst / rel)
    shutil.copytree(source_root / task.rust_dir, dst / task.rust_dir)
    (dst / "TASK.md").write_text(task_summary(task, source_root), encoding="utf-8")
    link_lake_packages(dst, source_root)
    if warm:
        copy_build_artifacts(task, dst, source_root)
        subprocess.run(["lake", "build", task.specs_module], cwd=dst, capture_output=True, text=True, timeout=1800)
    return dst
