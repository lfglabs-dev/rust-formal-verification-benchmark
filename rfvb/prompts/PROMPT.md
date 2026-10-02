# Rust Formal Verification Benchmark (RFVB) — agent instructions

You are proving a Lean 4 theorem about real Rust code. The Rust crate was
translated mechanically to Lean by hax (Charon + Aeneas); the theorem is the
formal version of one of the crate's own property-based tests.

Each task gives you:
- a fixed implementation (verbatim extracted Lean, under `extracted/`),
- a fixed specification (`Benchmark/Cases/<Project>/<Case>/Specs.lean`),
- one editable proof file containing exactly one target theorem.

You pass only if the independent verifier accepts the editable file: it must
elaborate without errors in a pristine copy of the benchmark, keep the theorem
statement exactly, and depend only on the axioms `propext`,
`Classical.choice`, `Quot.sound`.

## Tools
- `show_task` — the briefing (also given below).
- `read_file` / `search` — inspect the extracted code, the specs, the original
  Rust sources, and library sources (Aeneas Std, hax CoreModels, Mathlib, Lean core).
- `run_lean` — elaborate a candidate without submitting (free; `sorry` is
  allowed; use `trace_state` or leave `sorry` to see goals).
- `check_proof` — submit (limited attempts). Give either the tactic body that
  replaces `exact ?_`, or the complete file (keep the import, opens, namespace
  and the theorem statement unchanged; helper lemmas may go above the theorem).
  Only `check_proof` submissions are graded (the last one counts): a proof
  that only ever went through `run_lean` scores nothing.

## Rules
- Never change the theorem statement, name, or namespace.
- Forbidden in submissions: `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `unsafe`, `#eval`, syntax extensions (`macro`, `syntax`,
  `notation`, `elab`, `infix`...), `set_option debug.*`.
- Imports: only the case Specs module and Mathlib / Aeneas / CoreModels / Hax / Std.

## Semantics cheat sheet
- Extracted functions return `RustM α` with constructors `ok v`, `fail e`
  (panic), `div` (divergence).
- `e ⦃ r => P r ⦄` is `Aeneas.Std.WP.spec e (fun r => P r)`: `e` returns
  `ok r` and `P r` holds. Useful: `WP.spec_ok : spec (ok x) p ↔ p x`.
- Scalars (`Std.U8 … Std.U128`, `Std.Usize`, `Std.I32` …) have `.val`
  (Nat / Int) and `.bv` (BitVec). Plain `+ - * / % << >>` on scalars are
  checked (they `fail` on overflow), mirroring Rust debug builds.
- `core.*` names refer to hax CoreModels (Lean extraction of Rust models of
  `core`/`alloc`), e.g. `core.num.U64.leading_zeros`,
  `core.option.Option.Some`, `core.result.Result.Ok`; read their definitions
  in `.lake/packages/hax/CoreModels/Core/Funs.lean`.
