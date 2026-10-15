# Rust Formal Verification Benchmark (RFVB)

**v1.0, 2026-10-02.** 100 Lean 4 theorem-proving tasks extracted from real-world Rust property-based tests.

## Overview

Each task translates an existing `proptest` (69) or `quickcheck` (31) property test from 33 open-source Rust crates into a Lean 4 theorem over the verbatim `cargo hax into lean` (Charon + Aeneas) extraction:

- **Implementation (`extracted/`):** Mechanical Lean translation of the crate under test (never hand-edited).
- **Specification (`Benchmark/Cases/<P>/<C>/Specs.lean`):** Generator bounds and `prop_assume!` become preconditions; assertions and panic/overflow-freedom (`f x ⦃ r => P r ⦄`) form the postcondition.
- **Task (`Benchmark/Generated/<P>/<C>/Tasks/`):** One editable Lean file per task containing the target theorem.
- **Splits:** 21 easy, 47 medium, 32 hard across arithmetic, encodings, bit manipulation, checksums, finite fields, parsers, containers, and search.

## Results

**Task-set version:** all results below were scored on the v1.0 statements. In v1.1, `rust_crdt/dot/prop_ordered_dot_is_ordered_by_actor_first` was corrected to call `Ord::cmp`, as the Rust test does, instead of `partial_cmp`. Every listed system had solved the v1.0 version of that task, and none of those proofs verify against the corrected statement. Re-scoring without a re-run would therefore subtract one solve from every row and leave the ordering unchanged.

Evaluated with the reference tool-calling agent (`rfvb.run_agent`), one pass per task under the `normal` budget (50 turns, 80 tool calls, 10 `check_proof` submissions, streamed responses, `tool_choice="auto"`, provider-default temperature).

| Model | Provider ID | Solved | Easy (21) | Medium (47) | Hard (32) | Valid | Prompt Tokens | Completion Tokens | Median Time |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Gemini 4 Argon | `google/gemini-4-argon-eap` | **87**/100 | 21 | 45 | 21 | 100 | 88M | 2.3M | 6 min |
| Claude Opus 5.5 | `anthropic/claude-opus-5-5` | **84**/100 | 21 | 45 | 18 | 100 | 103M | 3.9M | 18 min |
| GPT-6 Astra | `openai/gpt-6-astra` | **75**/100 | 21 | 42 | 12 | 100 | 67M | 0.9M | 10 min |
| GPT-6.1 Sol | `openai/gpt-6.1-sol` | **75**/100 | 21 | 42 | 12 | 100 | 79M | 1.1M | 20 min |
| Z.ai GLM 5.3 | `zai/glm-5.3` | **46**/100 | 19 | 27 | 0 | 100 | 164M | 12.1M | 32 min |
| Z.ai GLM 5.3 Flash | `zai/glm-5.3-flash` | **32**/100 | 16 | 16 | 0 | 100 | 158M | 16.4M | 56 min |
| Muse Wonder 1.0 (partial) | `muse-code/muse-wonder-1.0` | **26**/100 | 14 | 12 | 0 | 53 | 67M | 1.1M | 5 min |
| Grok 4.7 | `xai/grok-4.7` | **22**/100 | 13 | 9 | 0 | 100 | 176M | 2.3M | 32 min |
| Muse Spark 1.3 | `muse/muse-spark-1.3` + `muse-code/muse-spark-1.3` | **16**/100 | 13 | 3 | 0 | 97 | 180M | 5.4M | 30 min |
| GPT-6 Luna | `openai/gpt-6-luna` | **5**/100 | 4 | 1 | 0 | 100 | 107M | 0.4M | 26 min |

*Notes:*
- **Muse Spark 1.3 (`muse/muse-spark-1.3` + `muse-code/muse-spark-1.3`):** Merged across the initial `muse/muse-spark-1.3` run (94 valid tasks, 13 solved) and the `muse-code/muse-spark-1.3` subscription continuation (+3 solved, **16/100** across 97 valid tasks before `HTTP 429` rate-limit cooldown on the remaining 3 tasks) in `results/20261009-muse_muse-spark-1.3-normal.jsonl`.
- **Muse Wonder 1.0 (`muse-code/muse-wonder-1.0`):** Partial run. 53 of 100 tasks finished (26 solved: 14/21 easy, 12/28 medium attempted, 0/4 hard attempted) before the Muse Code subscription quota ran out (`HTTP 429`, window resets 2026-10-19). The other 47 tasks are unscored, so this row is not comparable to the complete rows. Results are in `results/20261013-muse-code_muse-wonder-1.0-normal.jsonl`.
- **Kimi K3 256K (`kimi/k3-256k`):** Not scored; its native provider remained in rate-limit cooldown / HTTP 502 (the 3 completed attempts in `results/20261002-kimi_k3-normal.jsonl` are kept for reference).
- Per-task verdicts and token usage are stored in `results/<run>.jsonl`, with full conversations, tool logs, and submitted proofs archived in `results/<run>.tar.zst`.

```sh
python -m rfvb.summarize results/*.jsonl
```

## Grading

`python -m rfvb.verify <task_id> <file.lean>` passes a submission iff:

1. **Policy:** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `#eval`, syntax extensions, or debug options; imports restricted to the case spec and standard libraries; theorem statement unchanged.
2. **Build & Check:** Compiles in a clean copy of the benchmark and matches the canonical theorem type in a separate check module.
3. **Axioms:** Depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Submissions are built in a Landlock sandbox: writes are confined to the verification directory, and there is no network access.

**Known issue (open):** an independent audit (2026-10-14) found that the axiom check alone does not guarantee kernel checking, because code that runs at elaboration time can add declarations that the kernel never checks. Until the verifier replays the submitted module through the kernel (`leanchecker`, shipped with the toolchain), treat passes as provisional. The audit replayed all 367 archived v1.0 passes through `leanchecker` and found every one kernel-clean. It found no evidence that any v1.0 result exploited the issue. The later GPT-6 Astra and Muse Wonder 1.0 runs were replayed the same way: 26/26 Muse Wonder passes and 74/75 GPT-6 Astra passes are kernel-clean. The remaining Astra pass targets the original `rust_crdt` statement (see below) and does not verify against the corrected one.

**Statistics:** each model is evaluated in a single run. Per the audit, the top two v1.0 rows (87 and 84) are not statistically distinguishable (exact McNemar test, p = 0.45). Results in rows produced before v1.1 do not record the run configuration (temperature, endpoint, `max_tokens`).

**Harness note:** before v1.1, `run_lean` checked for the text `declaration uses 'sorry'`, but Lean 4.31 prints `` declaration uses `sorry` ``. As a result, it reported some sorry-containing files as clean. All results committed before v1.1 were produced with that harness.

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
