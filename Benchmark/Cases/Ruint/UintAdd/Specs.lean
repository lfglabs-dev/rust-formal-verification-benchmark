import RuintUintAdd.Extraction

/-!
# ruint — `Uint<BITS, LIMBS>` addition, subtraction and negation — specifications

Implementation: `extracted/RuintUintAdd` (verbatim `cargo hax extract
ruint-uint-add` output for alloy-rs/ruint@2071680b).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`debug_assert!`s panic), which is the configuration `cargo test` runs the
original property tests under.

Common translation of the test scaffolding (see `review/translation-notes.md`):
* `const_for!(BITS in SIZES { const LIMBS: usize = nlimbs(BITS); type U =
  Uint<BITS, LIMBS>; ... })` runs the property for every `BITS` of
  `SIZES = [0, 1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096]`: the
  theorems quantify over the const generics `BITS LIMBS : Usize` with
  `BITS.val ∈ SIZES` and `nlimbs BITS = ok LIMBS` (the extracted `ruint::nlimbs`).
* A value `a: U` drawn by proptest comes from `Uint`'s `Arbitrary` impl
  (src/support/proptest.rs): `any::<[u64; LIMBS]>().prop_map(Uint::from_limbs_unmasked)`.
  The specs therefore take an arbitrary limb array `la : Array U64 LIMBS` and run
  the extracted `Uint.from_limbs_unmasked BITS la` first.
* `a + b`, `a - b`, `-a` are the `Add`/`Sub`/`Neg` operator impls for
  `Uint<BITS, LIMBS>` (by value); `U::ZERO` is the associated constant
  `Uint.ZERO BITS LIMBS`; `assert_eq!` compares with the derived `PartialEq`
  (structural equality of the limb arrays), i.e. Lean `=` on `Uint BITS LIMBS`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Ruint.UintAdd

open ruint

/-- PBT `add::tests::test_commutative` (src/add.rs:252-262):
```
proptest!(|(a: U, b: U)| {
    assert_eq!(a + b, b + a);
    assert_eq!(a - b, -(b - a));
});
``` -/
def commutative_spec (BITS LIMBS : Std.Usize) (la lb : Array Std.U64 LIMBS) : Prop :=
  (do
    let a ← Uint.from_limbs_unmasked BITS la -- a: U
    let b ← Uint.from_limbs_unmasked BITS lb -- b: U
    let apb ← Uint.Insts.CoreOpsArithAddUintUint.add a b -- a + b
    let bpa ← Uint.Insts.CoreOpsArithAddUintUint.add b a -- b + a
    let amb ← Uint.Insts.CoreOpsArithSubUintUint.sub a b -- a - b
    let bma ← Uint.Insts.CoreOpsArithSubUintUint.sub b a -- b - a
    let nbma ← Uint.Insts.CoreOpsArithNegUint.neg bma -- -(b - a)
    ok (apb, bpa, amb, nbma))
  ⦃ r => r.1 = r.2.1 ∧ r.2.2.1 = r.2.2.2 ⦄

/-- PBT `add::tests::test_associative` (src/add.rs:264-273):
```
proptest!(|(a: U, b: U, c: U)| {
    assert_eq!(a + (b + c), (a + b) + c);
});
``` -/
def associative_spec (BITS LIMBS : Std.Usize) (la lb lc : Array Std.U64 LIMBS) : Prop :=
  (do
    let a ← Uint.from_limbs_unmasked BITS la -- a: U
    let b ← Uint.from_limbs_unmasked BITS lb -- b: U
    let c ← Uint.from_limbs_unmasked BITS lc -- c: U
    let bpc ← Uint.Insts.CoreOpsArithAddUintUint.add b c -- b + c
    let lhs ← Uint.Insts.CoreOpsArithAddUintUint.add a bpc -- a + (b + c)
    let apb ← Uint.Insts.CoreOpsArithAddUintUint.add a b -- a + b
    let rhs ← Uint.Insts.CoreOpsArithAddUintUint.add apb c -- (a + b) + c
    ok (lhs, rhs))
  ⦃ r => r.1 = r.2 ⦄

/-- PBT `add::tests::test_identity` (src/add.rs:275-285):
```
proptest!(|(value: U)| {
    assert_eq!(value + U::ZERO, value);
    assert_eq!(value - U::ZERO, value);
});
``` -/
def identity_spec (BITS LIMBS : Std.Usize) (lv : Array Std.U64 LIMBS) : Prop :=
  (do
    let value ← Uint.from_limbs_unmasked BITS lv -- value: U
    let z ← Uint.ZERO BITS LIMBS -- U::ZERO
    let s ← Uint.Insts.CoreOpsArithAddUintUint.add value z -- value + U::ZERO
    let z' ← Uint.ZERO BITS LIMBS -- U::ZERO
    let d ← Uint.Insts.CoreOpsArithSubUintUint.sub value z' -- value - U::ZERO
    ok (value, s, d))
  ⦃ r => r.2.1 = r.1 ∧ r.2.2 = r.1 ⦄

/-- PBT `add::tests::test_inverse` (src/add.rs:287-298):
```
proptest!(|(a: U)| {
    assert_eq!(a + (-a), U::ZERO);
    assert_eq!(a - a, U::ZERO);
    assert_eq!(-(-a), a);
});
``` -/
def inverse_spec (BITS LIMBS : Std.Usize) (la : Array Std.U64 LIMBS) : Prop :=
  (do
    let a ← Uint.from_limbs_unmasked BITS la -- a: U
    let na ← Uint.Insts.CoreOpsArithNegUint.neg a -- -a
    let s ← Uint.Insts.CoreOpsArithAddUintUint.add a na -- a + (-a)
    let z ← Uint.ZERO BITS LIMBS -- U::ZERO
    let d ← Uint.Insts.CoreOpsArithSubUintUint.sub a a -- a - a
    let z' ← Uint.ZERO BITS LIMBS -- U::ZERO
    let na' ← Uint.Insts.CoreOpsArithNegUint.neg a -- -a
    let nna ← Uint.Insts.CoreOpsArithNegUint.neg na' -- -(-a)
    ok (a, s, z, d, z', nna))
  ⦃ r => r.2.1 = r.2.2.1 ∧ r.2.2.2.1 = r.2.2.2.2.1 ∧ r.2.2.2.2.2 = r.1 ⦄

end Benchmark.Cases.Ruint.UintAdd
