# Rust Formal Verification Benchmark (RFVB)

**v1.0, 2026-10-02.** 100 Lean 4 theorem-proving tasks about real Rust code.

## Construction

1. **Sources.** We mined 186 open-source Rust repositories that use property-based
   testing (8,087 tests), then analysed 96 of them in depth (7,245 tests).
2. **Specifications.** Each task is one of the crate authors' own property-based
   tests (proptest: 69 tasks, quickcheck: 31). It is restated in Lean with fixed
   rules: generator bounds become hypotheses, `prop_assume!` becomes a
   precondition, and the assertion becomes the conclusion. Rust semantics are
   kept: overflow and panics fail, and `Option`/`Result` are preserved.
3. **Implementation model.** The code under test is translated to Lean
   mechanically by `cargo hax into lean` (Charon + Aeneas). The output is used
   verbatim and never edited by hand.
4. **Filtering.** A test becomes a task only if extraction succeeds, the
   statement is non-trivial and non-vacuous, and a reference proof exists. Every
   task's statement was reviewed against the original test.

The result is 100 tasks from 33 crates (38 extracted modules); 1.4% of the
analysed tests became tasks. Most losses happen at extraction: unsupported Rust
features, `unsafe`, floats and large dependency cones.

| | |
|---|---|
| Difficulty | easy 21, medium 47, hard 32 |
| Property class | reference equivalence 33, round trip 25, algebraic law 18, parse/serialize 7, container invariant 5, model equivalence 4, Option/Result behaviour 4, bounds 4 |
| Domains | integer and big-number arithmetic, encodings, bit manipulation, checksums, finite fields, parsers, containers, search |
| Licenses | MIT, Apache-2.0, Unlicense or CC0 (per task in `tasks.jsonl`) |

All 100 tasks form a single test set. Every task has a reference proof in the
repository, so results on models trained after 2026-10-02 may be contaminated.

## Task

The implementation (`extracted/`) and the specification
(`Benchmark/Cases/<P>/<C>/Specs.lean`) are fixed. The model submits a
replacement for one editable file containing the target theorem. Helper
lemmas are allowed. Specifications are typically `f x ⦃ r => P r ⦄`: `f x`
returns without panicking and its result satisfies `P`.

`tasks.jsonl` has one task per line: `id`, `difficulty`, `property_class`,
`theorem_name`, `theorem_statement`, file paths, the original test (`pbt`:
framework, source lines, permalink, generators, assertion) and `upstream`
(repo, commit, license).

## Grading

`python -m rfvb.verify <task_id> <file.lean>` passes a submission iff:

1. **Policy.** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
   `extern`, `unsafe`, `#eval`, syntax extensions or debug options; imports
   limited to the case specification and standard libraries; theorem statement
   unchanged.
2. **Build.** It compiles and is kernel-checked against a pristine copy of the
   implementation and specification.
3. **Statement.** A separate module restates the canonical theorem and accepts
   the submitted proof.
4. **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound` are used.

The score is the number of tasks passed out of 100 (pass@k), reported by
difficulty. All 100 reference proofs pass; all 100 blank task files fail.
Verification takes 19 s at the median and 148 s at most, using 0.6 GiB at the
median and 2 GiB at most.

## Usage

Requires elan, git and Python ≥ 3.10 (standard library only).

```sh
lake exe cache get && lake build                     # implementation, specs, reference proofs
python -m rfvb.verify <task_id> proof.lean           # JSON verdict; exit code 0 iff passed
python -m rfvb.check_references --jobs 4             # all reference proofs (expect 100/100)
python -m rfvb.run_agent --model M --base-url URL --api-key-env VAR --tasks all
```

`run_agent` is a reference tool-calling agent (OpenAI-compatible API). Its
tools are file reading, search, Lean elaboration and proof checking. Each task
runs in an isolated workspace without reference proofs. Results are written to
`results/<run>.jsonl`.

## Layout

```
tasks.jsonl                                        100 tasks
extracted/<Package>/                               cargo-hax output (verbatim)
Benchmark/Cases/<Project>/<Case>/Specs.lean        specifications
Benchmark/Cases/<Project>/<Case>/Proofs/           reference proofs
Benchmark/Generated/<Project>/<Case>/Tasks/        blank task files
rust/<project>/<case>/                             Rust sources at the pinned commit, with licenses
rfvb/                                              verifier, task loader, reference agent
```

Pins: Lean v4.31.0, Mathlib, Aeneas `build-183e4f0`, hax-lean v0.3.27, cargo-hax 0.4.1
(`lean-toolchain`, `lake-manifest.json`, `toolchain.json`).

## License

Benchmark code, specifications, task files and proofs: Apache-2.0. Files under
`rust/` and `extracted/` keep their upstream licenses. `rev_bits` declares
Apache-2.0 but ships no license file, so we added `rust/rev_bits/u32/LICENSE-APACHE`.
