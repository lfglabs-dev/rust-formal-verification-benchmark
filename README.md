# Rust Formal Verification Benchmark (RFVB)

100 Lean 4 theorem-proving tasks about real Rust code. Each task is the formal
version of a property-based test (proptest / quickcheck / ...) taken from an
open-source Rust crate. The crate code was translated mechanically to Lean by
`cargo hax into lean` (Charon + Aeneas); the specification restates the
property test over the extracted functions; the model must prove it.

| | easy | medium | hard | total |
|---|---|---|---|---|
| train | 15 | 34 | 27 | 76 |
| eval  | 6  | 13 | 5  | 24 |

38 extracted cases from 33 upstream projects. Splits assign whole families of
related projects (e.g. all bigint crates) to one side.

## What a task is

A task (one line of `tasks.jsonl`) fixes:

- **implementation**: verbatim extracted Lean under `extracted/<Package>/` (not editable);
- **specification**: `Benchmark/Cases/<Project>/<Case>/Specs.lean`, a `<name>_spec`
  predicate stating the property test, typically `f x ⦃ r => P r ⦄`
  ("`f x` returns `ok r` without panicking and `P r` holds");
- **editable file**: `Benchmark/Generated/<Project>/<Case>/Tasks/<Name>.lean`, containing
  exactly one theorem whose proof is the placeholder `exact ?_`;
- **target theorem**: `theorem_name` / `theorem_statement`.

The solver submits a complete replacement for the editable file. Helper lemmas are
allowed; the statement, name and namespace must stay unchanged.

Key fields of `tasks.jsonl`: `id` (`<project>/<case>/<task>`), `split`
(`train`/`eval`), `difficulty`, `property_class`, `category`, `theorem_name`,
`theorem_statement`, `namespace`, `opens`, `specs_module`, `specs_file`,
`editable_file`, `target_module`, `reference_file`, `reference_module`,
`implementation_files`, `rust_dir`, `pbt` (framework, test, source file/lines,
permalink, strategies, assertion) and `upstream` (repo, commit, license, crate).

## Grading

`rfvb.verify` accepts a submission only if all of the following hold:

1. **Static policy**: imports limited to the case `Specs` module and
   `Mathlib`/`Aeneas`/`CoreModels`/`Hax`/`Std`/`Batteries`/`Aesop`/`Qq`/`Plausible`/`Init`;
   no `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`,
   `extern`, `unsafe`, `run_cmd`/`run_elab`/`run_meta`, `initialize`, `#eval`, `#exit`,
   syntax extensions (`macro`, `syntax`, `notation`, `elab`, `infix`, ...),
   `set_option debug.*`/`backward.*`, instance-attribute removal; the theorem is declared
   exactly once with the exact statement text (whitespace-normalised) inside the task namespace.
2. **Build**: in a fresh copy of the pristine benchmark with only the editable file
   overlaid, `lake build <target_module>` succeeds.
3. **Statement check**: a separate module, which never sees the submission's source,
   states the canonical statement and proves it with `@<theorem_name>`; so the
   submitted theorem must have exactly the canonical type.
4. **Axioms**: `#print axioms` of that check is a subset of
   `{propext, Classical.choice, Quot.sound}`.

Score = number of tasks passed (pass@1 unless stated otherwise). Report train and eval separately.

## Layout

```
lakefile.lean, lake-manifest.json, lean-toolchain   Lean 4 v4.31.0; aeneas build-183e4f0, hax-lean v0.3.27 (+ Mathlib)
toolchain.json                                     extraction toolchain pins (cargo-hax 0.4.1, Charon, Aeneas)
tasks.jsonl                                        the 100 tasks
extracted/<Package>/                               verbatim cargo-hax output, one Lean package per case
Benchmark/Cases/<Project>/<Case>/Specs.lean        specifications
Benchmark/Cases/<Project>/<Case>/Proofs/*.lean     reference proofs (one per task)
Benchmark/Generated/<Project>/<Case>/Tasks/*.lean  blank editable task files
rust/<project>/<case>/                             original Rust sources at the pinned commit (+ licenses)
rfvb/                                              Python: task loader, verifier, reference agent
```

## Build

Requires [elan](https://github.com/leanprover/elan), git, Python >= 3.10 (standard library only).

```sh
lake exe cache get   # prebuilt Mathlib oleans (otherwise Mathlib builds from source)
lake build           # extraction + specs + all 100 reference proofs
```

The default target does not include the blank task files (they contain `?_`).
Elaborating some files needs several GB of RAM; use `RFVB_LEAN_MEMORY_BYTES`
(default 16 GiB, 0 = off) to cap a verifier/agent Lean process group.

## Verify a proof

```sh
python -m rfvb.verify arxid/permute/output_never_leaves_the_domain my_proof.lean
# {"task_id": "...", "pass": true, "status": "passed", "detail": "", "axioms": ["propext", ...], ...}
```

Exit code 0 iff passed. Other statuses: `forbidden_placeholder`, `hidden_import`,
`theorem_missing`, `theorem_statement_mismatch`, `lean_check_failed`, `timeout`,
`untrusted_axioms`, `verifier_infra_error`, `harness_error`.
The verifier needs a built checkout (`lake build`): it copies the case's prebuilt
oleans into a temporary directory.

Check all reference proofs / blank skeletons:

```sh
python -m rfvb.check_references --jobs 4              # expect 100/100 passing
python -m rfvb.check_references --jobs 4 --skeletons  # expect 100/100 rejected
```

## Run a model

The reference agent is an OpenAI-compatible tool-calling loop with tools
`show_task`, `read_file`, `search` (workspace, Aeneas, CoreModels, Mathlib, Lean core),
`run_lean` (exploration, `sorry` allowed) and `check_proof` (metered submission).
Each task runs in an isolated workspace holding only that case's extraction, specs,
editable file, Rust sources and a briefing (`TASK.md`); reference proofs are not
visible. The final editable file is then graded by the independent verifier.

```sh
export OPENAI_API_KEY=...
python -m rfvb.run_agent --model MODEL --base-url https://host/v1 --tasks eval --jobs 2
python -m rfvb.run_agent --mock --tasks easy        # no model: submits reference proofs (smoke test)
```

`--tasks`: comma-separated ids, `all`, `train`, `eval`, `easy`/`medium`/`hard`, or a file
of ids. `--budget quick|normal|deep|extended` (default `normal`: 10 submissions, 80 tool
calls, 50 turns, 400k completion tokens). `--api-key-env` selects the key variable.
Reasoning content returned by the endpoint is kept in the conversation history.
Results: `results/<run>.jsonl` (one line per task) and per-task logs in `results/<run>/`.

## Licenses

Benchmark code, specifications, task files and reference proofs: Apache-2.0 (`LICENSE`).
Rust sources under `rust/` and the Lean code extracted from them under `extracted/`
keep their upstream licenses (per-task `upstream.license` in `tasks.jsonl`; license files
are included in each `rust/<project>/<case>/`). `rev_bits` declares Apache-2.0 in its
`Cargo.toml` but ships no license file; a copy of the license text was added as
`rust/rev_bits/u32/LICENSE-APACHE`.
