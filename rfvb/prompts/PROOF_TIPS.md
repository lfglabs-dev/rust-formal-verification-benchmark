# Proof tips for extracted Rust (Aeneas + hax CoreModels)

Reference material shipped with the dependencies:
- `.lake/packages/aeneas/documentation/` — `tactics-reference.md`,
  `proof-strategies.md`, `tips-and-tricks.md`,
  `skills/aeneas-tactics-quickref.instructions.md`,
  `skills/proof-patterns.instructions.md`.
- `.lake/packages/hax/CoreModels/Core/Funs.lean` — Lean extraction of hax's
  Rust models of `core` (what `core.num.U64.leading_zeros`,
  `core.option.Option.or_else`, `core.slice.…` actually compute).
- `.lake/packages/aeneas/backends/lean/Aeneas/Std/` — primitive scalars,
  slices, vectors, `loop`, and their `@[step]` specs.

Basics:
- `e ⦃ r => P r ⦄` is `Aeneas.Std.WP.spec e (fun r => P r)`; `WP.spec_ok`
  rewrites `spec (ok x) p ↔ p x`; failure/divergence make it `False`.
- `open CoreModels` + `open Aeneas.Std hiding namespace core alloc`: `core.*`
  names are CoreModels' models, not Aeneas' own.
- `step` / `step*` apply `@[step]` specs of callees; after `step*`, close each
  goal with a separate `·` block (`agrind`, `scalar_tac`, `simp_scalar`, …).
- Scalar bounds: `U64.max` etc. are irreducible; use `U64.max_def`,
  `UScalar.max`, `U64.rMax` or `scalar_tac`.
- Loops extracted with the `loop` combinator: use `loop.spec_decr_nat`
  (invariant + Nat measure) or the `mvcgen` spec `loop_spec`.

## Lessons from the fastdivide reference proofs

- **Concrete evaluation:** `rfl` evaluates concrete calls through 128-bit
  arithmetic in the kernel, e.g.
  `DividerU64.divide_by 11#u64 = ok (DividerU64.Fast 13415813871788764812#u64 3#u8)`
  (no `decide`/`native_decide` needed).
- **Unfold CoreModels wrappers before `step`:** `step` does not see through
  them. Unfold e.g. `CoreModels.core.num.U64.wrapping_add` together with
  `CoreModels.rust_primitives.arithmetic.wrapping_add_u64` (same for
  `leading_zeros`/`leading_zeros_u64`); they become `ok (Aeneas.Std.…)`.
- **Useful lemmas:** `Nat.and_sub_one_eq_zero_iff_isPowerOfTwo` (Lean core)
  for `is_power_of_two`; the Aeneas `leading_zeros` model equals
  `w - Nat.log 2 x - 1` (read it off with
  `change (BitVec.ofNat 32 _).toNat = _; rw [BitVec.toNat_ofNat]`);
  `UScalar.cast_val_eq`, `U64.cast_U128_val_eq`, `UScalar.val_and`,
  `U64.wrapping_add_val_eq`, `UScalar.eq_equiv`, `U128.max_eq`,
  `Nat.shiftRight_eq_div_pow`, `Nat.shiftLeft_eq`; `U128.size = 2^128` via
  `simp [U128.size, U128.numBits]`.
- **Structure:** write small `@[local step]` spec lemmas for callees; for long
  functions step manually (`step as ⟨x, hx⟩`) and state clean value facts
  (`have hu : u.val = 2^(k+64)`) and side conditions (`have` the overflow /
  `massert` fact) *before* the step, so `step` discharges them. Glue per-function
  specs with `spec_bind` / `spec_mono`. A per-object correctness predicate
  (e.g. `DividerCorrect dv d := ∀ n, divide dv n ⦃ r => r.val = n.val / d ⦄`)
  keeps the top-level proof short.
- **omega:** great on literal constants (`M*n/2^64/8 = n/11`), but it fails on
  `x % 2^64` or cast atoms — first prove the no-wrap bound and
  `rw [Nat.mod_eq_of_lt]`. Don't `simp` right before `omega` (it normalises
  `2^64` inconsistently). For variable powers `generalize hk : Nat.log 2 d = k`
  and feed facts like `2^(k+64) = 2^64 * 2^k`.
- **Pitfalls:** after stepping `is_power_of_two`, branches appear as
  `if false = true` → `simp only [hbf, Bool.false_eq_true, ↓reduceIte]`;
  `rcases … ⟨rfl, _⟩` on Option matches can hit "invalid motive" — keep the
  equation and `simp only [ho, …]`; hypothesis names produced by `step*`
  (`r_post1`) are stable only for this pinned Aeneas version.
- **Speed:** scratch files should import the case `Specs` module, not all of
  Mathlib (much faster to load).
