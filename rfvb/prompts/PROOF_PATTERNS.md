# Proof patterns for Aeneas-extracted code

- Start by unfolding the spec and the functions: `unfold foo_spec`, then
  `unfold crate.foo` (or `simp only [crate.foo]`).
- `step` / `step*` apply registered `@[step]` specifications of callees and
  split on branches; close each remaining goal separately, e.g.
  ```lean
  step*
  · scalar_tac
  · agrind
  ```
- Arithmetic side conditions: `scalar_tac` (linear integer arithmetic over
  scalar `.val`s), `agrind` / `grind`, `simp_scalar`, `omega` after moving to
  `Nat`. Bit-level goals: `bv_decide` is NOT allowed (it relies on
  `Lean.ofReduceBool`); use `bvify`/`bv_tac` only if `#print axioms` stays clean,
  otherwise reason with `Nat.shiftRight_eq_div_pow`, `Nat.shiftLeft_eq`, `Nat.testBit`.
- Monadic plumbing: `simp only [bind_tc_ok, WP.spec_ok]`, or case on the result:
  `cases h : f x` / `obtain ⟨r, hr, hp⟩ := …`.
- Loops extracted with `loop`: use `loop.spec_decr_nat` with an invariant and
  a decreasing Nat measure; recursive `_loop` functions: well-founded
  induction on the measure.
- Scalar limits such as `U64.max` are irreducible; rewrite with `U64.max_def`
  or use numerals (`2^64 - 1`).
- Concrete computations: `decide`, `rfl`, `simp` (kernel reduction); never
  `native_decide`.
