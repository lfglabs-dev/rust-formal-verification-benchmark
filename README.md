# Rust Formal Verification Benchmark (RFVB)

**v1.0** — 100 Lean 4 theorem-proving tasks extracted from real-world Rust property-based tests.

## Overview

Each task translates an existing `proptest` (69) or `quickcheck` (31) property test from 33 open-source Rust crates into a Lean 4 theorem over the verbatim `cargo hax into lean` (Charon + Aeneas) extraction:

- **Implementation (`extracted/`):** Mechanical Lean translation of the crate under test (never hand-edited).
- **Specification (`Benchmark/Cases/<P>/<C>/Specs.lean`):** Generator bounds and `prop_assume!` become preconditions; assertions and panic/overflow-freedom (`f x ⦃ r => P r ⦄`) form the postcondition.
- **Task (`Benchmark/Generated/<P>/<C>/Tasks/`):** One editable Lean file per task containing the target theorem.
- **Splits:** 21 easy, 47 medium, 32 hard across arithmetic, encodings, bit manipulation, checksums, finite fields, parsers, containers, and search.

## Results

Evaluated with the reference tool-calling agent (`rfvb.run_agent`), one pass per task under the `normal` budget (50 turns, 80 tool calls, 10 `check_proof` submissions, streamed responses, provider-default temperature).

| Model | Provider ID | Solved | Easy (21) | Medium (47) | Hard (32) | Valid | Prompt Tokens | Completion Tokens | Median Time |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Gemini 4 Argon | `google/gemini-4-argon-eap` | **87**/100 | 21 | 45 | 21 | 100 | 88M | 2.3M | 6 min |
| Claude Opus 5.5 | `anthropic/claude-opus-5-5` | **84**/100 | 21 | 45 | 18 | 100 | 103M | 3.9M | 18 min |
| GPT-6.1 Sol | `openai/gpt-6.1-sol` | **75**/100 | 21 | 42 | 12 | 100 | 79M | 1.1M | 20 min |
| Z.ai GLM 5.3 | `zai/glm-5.3` | **46**/100 | 19 | 27 | 0 | 100 | 164M | 12.1M | 32 min |
| Z.ai GLM 5.3 Flash | `zai/glm-5.3-flash` | **32**/100 | 16 | 16 | 0 | 100 | 158M | 16.4M | 56 min |
| Grok 4.7 | `xai/grok-4.7` | **22**/100 | 13 | 9 | 0 | 100 | 176M | 2.3M | 32 min |
| Muse Spark 1.3 | `muse/muse-spark-1.3` | **13**/100 | 10 | 3 | 0 | 94 | 176M | 5.2M | 31 min |
| GPT-6 Luna | `openai/gpt-6-luna` | **5**/100 | 4 | 1 | 0 | 100 | 107M | 0.4M | 26 min |

*Notes:*
- **Kimi K3 256K (`kimi/k3-256k`):** Not scored; its native provider remained in rate-limit cooldown / HTTP 502 (the 3 completed attempts in `results/20261002-kimi_k3-normal.jsonl` are kept for reference).
- **Muse Spark 1.3 (`muse/muse-spark-1.3`):** 94/100 tasks completed before upstream HTTP 502 errors interrupted the remaining 6 tasks.
- Per-task verdicts and token usage are stored in `results/<run>.jsonl`, with full conversations, tool logs, and submitted proofs archived in `results/<run>.tar.zst`.

```sh
python -m rfvb.summarize results/*.jsonl
```

## Grading

`python -m rfvb.verify <task_id> <file.lean>` passes a submission iff:

1. **Policy:** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `#eval`, syntax extensions, or debug options; imports restricted to the case spec and standard libraries; theorem statement unchanged.
2. **Build & Check:** Compiles in a clean copy of the benchmark and matches the canonical theorem type in a separate check module.
3. **Axioms:** Depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Usage

Requires `elan`, `git`, and Python ≥ 3.10.

```sh
lake exe cache get && lake build                     # build extractions, specs, and reference proofs
python -m rfvb.verify <task_id> proof.lean           # verify a single proof submission
python -m rfvb.check_references --jobs 4             # verify all 100 reference proofs
python -m rfvb.run_agent --model M --base-url URL --api-key-env VAR --tasks all
```

## Layout

```text
tasks.jsonl                                        100 task definitions and metadata
extracted/<Package>/                               verbatim cargo-hax Lean extractions
Benchmark/Cases/<Project>/<Case>/Specs.lean        task specifications
Benchmark/Cases/<Project>/<Case>/Proofs/           reference proofs
Benchmark/Generated/<Project>/<Case>/Tasks/        editable task templates
rust/<project>/<case>/                             pinned upstream Rust sources
rfvb/                                              verifier, task loader, and reference agent
```

Pinned toolchain: Lean `v4.31.0`, Mathlib, Aeneas `build-183e4f0`, `hax-lean v0.3.27`, `cargo-hax 0.4.1`.

## License

Benchmark code, specifications, task files, and reference proofs are licensed under Apache-2.0. Files under `rust/` and `extracted/` retain their upstream licenses (MIT, Apache-2.0, Unlicense, or CC0).
