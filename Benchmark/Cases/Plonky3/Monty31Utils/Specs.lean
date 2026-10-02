import Plonky3Monty31Utils.Extraction

/-!
# Plonky3 `p3-monty-31` Montgomery helpers — specifications

Implementation: `extracted/Plonky3Monty31Utils` (verbatim `cargo hax extract
plonky3-monty31-utils` output for Plonky3/Plonky3@6468485f, crate `monty-31`,
functions of `monty-31/src/utils.rs`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`debug_assert!`s panic), which is the configuration `cargo test` runs the
original property tests under.

## Montgomery parameters

The functions under test are generic over `MP: MontyParameters`; the property
tests (module `utils::tests`, monty-31/src/utils.rs:224-567) instantiate them
with two test-local unit structs:

```rust
struct KB;
impl MontyParameters for KB {
    const PRIME: u32 = 0x7f000001; // 2^31 - 2^24 + 1
    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x81000001;
}
struct BB;
impl MontyParameters for BB {
    const PRIME: u32 = 0x78000001; // 2^31 - 2^27 + 1
    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x88000001;
}
```

Neither impl overrides the provided constant
`MONTY_MASK = ((1u64 << Self::MONTY_BITS) - 1) as u32`. In the extraction a
`MontyParameters` instance is a record of these four constants (as `RustM Std.U32`
values) plus the supertrait instances (`Copy`, `Default`, `Debug`, `Eq`,
`PartialEq`, `Hash`), which none of the functions under test uses. The test
structs themselves live in `#[cfg(test)]` code and are not extracted; the
predicates `KBParams` / `BBParams` below state exactly what their impls define,
and every theorem quantifies over *any* instance satisfying them (in particular
the test's own `KB` / `BB`).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Plonky3.Monty31Utils

open p3_monty_31

/-- `impl MontyParameters for KB` (monty-31/src/utils.rs:230-236): `PRIME = 0x7f000001`,
`MONTY_BITS = 32`, `MONTY_MU = 0x81000001`, and `MONTY_MASK` is the trait's provided
default (monty-31/src/data_traits.rs:23). -/
def KBParams {MP : Type} (inst : data_traits.MontyParameters MP) : Prop :=
  inst.PRIME = ok 2130706433#u32 ∧            -- 0x7f000001
  inst.MONTY_BITS = ok 32#u32 ∧
  inst.MONTY_MU = ok 2164260865#u32 ∧         -- 0x81000001
  inst.MONTY_MASK = data_traits.MontyParameters.MONTY_MASK.default inst

/-- `impl MontyParameters for BB` (monty-31/src/utils.rs:238-244): `PRIME = 0x78000001`,
`MONTY_BITS = 32`, `MONTY_MU = 0x88000001`, and `MONTY_MASK` is the trait's provided
default (monty-31/src/data_traits.rs:23). -/
def BBParams {MP : Type} (inst : data_traits.MontyParameters MP) : Prop :=
  inst.PRIME = ok 2013265921#u32 ∧            -- 0x78000001
  inst.MONTY_BITS = ok 32#u32 ∧
  inst.MONTY_MU = ok 2281701377#u32 ∧         -- 0x88000001
  inst.MONTY_MASK = data_traits.MontyParameters.MONTY_MASK.default inst

/-! ## Conversions into / out of Montgomery form -/

/-- PBT `utils::tests::kb_to_from_monty_roundtrip` (monty-31/src/utils.rs:267):
`prop_assert_eq!(from_monty::<KB>(to_monty::<KB>(x)), x)`. -/
def kb_to_from_monty_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  (do
    let m ← utils.to_monty inst x
    utils.from_monty inst m) ⦃ r => r.val = x.val ⦄

/-- PBT `utils::tests::bb_from_to_monty_roundtrip` (monty-31/src/utils.rs:285):
`prop_assert_eq!(to_monty::<BB>(from_monty::<BB>(m)), m)`. -/
def bb_from_to_monty_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (m : Std.U32) : Prop :=
  (do
    let x ← utils.from_monty inst m
    utils.to_monty inst x) ⦃ r => r.val = m.val ⦄

/-- PBT `utils::tests::kb_to_monty_output_range` (monty-31/src/utils.rs:294):
`prop_assert!(to_monty::<KB>(x) < KB_P)`. -/
def kb_to_monty_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  utils.to_monty inst x ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::bb_to_monty_64_extends_32` (monty-31/src/utils.rs:364):
`prop_assert_eq!(to_monty_64::<BB>(x as u64), to_monty::<BB>(x))`. -/
def bb_to_monty_64_extends_32_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  (do
    let wide ← utils.to_monty_64 inst (UScalar.cast .U64 x)
    let narrow ← utils.to_monty inst x
    ok (wide, narrow)) ⦃ p => p.1.val = p.2.val ⦄

/-! ## Modular addition / subtraction -/

/-- PBT `utils::tests::kb_add_commutative` (monty-31/src/utils.rs:392):
`prop_assert_eq!(add::<KB>(a, b), add::<KB>(b, a))`. -/
def kb_add_commutative_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let ab ← utils.add inst a b
    let ba ← utils.add inst b a
    ok (ab, ba)) ⦃ p => p.1.val = p.2.val ⦄

/-- PBT `utils::tests::bb_add_sub_roundtrip` (monty-31/src/utils.rs:413):
`prop_assert_eq!(sub::<BB>(add::<BB>(a, b), b), a)`. -/
def bb_add_sub_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let s ← utils.add inst a b
    utils.sub inst s b) ⦃ r => r.val = a.val ⦄

/-- PBT `utils::tests::kb_sub_add_roundtrip` (monty-31/src/utils.rs:418):
`prop_assert_eq!(add::<KB>(sub::<KB>(a, b), b), a)`. -/
def kb_sub_add_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let d ← utils.sub inst a b
    utils.add inst d b) ⦃ r => r.val = a.val ⦄

/-! ## Montgomery reduction -/

/-- PBT `utils::tests::bb_monty_reduce_output_range` (monty-31/src/utils.rs:442):
`prop_assert!(monty_reduce::<BB>(x) < BB_P)`. -/
def bb_monty_reduce_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val < 2013265921 ⦄

/-- PBT `utils::tests::kb_monty_reduce_identity` (monty-31/src/utils.rs:447):
`let result = monty_reduce::<KB>(x) as u64;
prop_assert_eq!((result * R) % KB_P as u64, x % KB_P as u64)` with `R = 1u64 << 32`.
(`result * R` cannot overflow `u64`: `result < 2^32`, so it is stated in `Nat`.) -/
def kb_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄

/-- PBT `utils::tests::kb_large_agrees_with_standard` (monty-31/src/utils.rs:465):
`prop_assert_eq!(large_monty_reduce::<KB>(x), monty_reduce::<KB>(x))`. -/
def kb_large_agrees_with_standard_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  (do
    let large ← utils.large_monty_reduce inst x
    let standard ← utils.monty_reduce inst x
    ok (large, standard)) ⦃ p => p.1.val = p.2.val ⦄

/-- PBT `utils::tests::kb_large_monty_reduce_output_range` (monty-31/src/utils.rs:475):
`prop_assert!(large_monty_reduce::<KB>(x) < KB_P)`. -/
def kb_large_monty_reduce_output_range_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::bb_large_monty_reduce_identity` (monty-31/src/utils.rs:491):
`let result = large_monty_reduce::<BB>(x) as u64;
prop_assert_eq!((result * R) % BB_P as u64, x % BB_P as u64)` with `R = 1u64 << 32`.
(`result * R` cannot overflow `u64`: `result < 2^32`, so it is stated in `Nat`.) -/
def bb_large_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val * 2^32 % 2013265921 = x.val % 2013265921 ⦄

/-! ## 128-bit Montgomery reduction -/

/-- PBT `utils::tests::kb_monty_reduce_u128_output_range` (monty-31/src/utils.rs:502):
`let x = (hi as u128) << 64 | lo as u128; prop_assert!(monty_reduce_u128::<KB>(x) < KB_P)`.
The test's construction of `x` is executed with the Rust primitives (`as u128`, `<< 64`
with an `i32` shift amount, `|`). -/
def kb_monty_reduce_u128_output_range_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (lo : Std.U64) (hi : Std.U32) : Prop :=
  (do
    let hi_shifted ← UScalar.cast .U128 hi <<< 64#i32
    let x := hi_shifted ||| UScalar.cast .U128 lo
    utils.monty_reduce_u128 inst x) ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::kb_monty_reduce_u128_identity` (monty-31/src/utils.rs:514):
`let x = (hi as u128) << 64 | lo as u128; let result = monty_reduce_u128::<KB>(x) as u128;
prop_assert_eq!((result * R as u128) % KB_P as u128, x % KB_P as u128)`.
(`result * R` cannot overflow `u128`: `result < 2^32`, so it is stated in `Nat`.) -/
def kb_monty_reduce_u128_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (lo : Std.U64) (hi : Std.U32) : Prop :=
  (do
    let hi_shifted ← UScalar.cast .U128 hi <<< 64#i32
    let x := hi_shifted ||| UScalar.cast .U128 lo
    let result ← utils.monty_reduce_u128 inst x
    ok (x, result)) ⦃ p => p.2.val * 2^32 % 2130706433 = p.1.val % 2130706433 ⦄

/-- PBT `utils::tests::bb_monty_reduce_u128_agrees_with_u64` (monty-31/src/utils.rs:536):
`prop_assert_eq!(monty_reduce_u128::<BB>(x as u128), monty_reduce::<BB>(x))`. -/
def bb_monty_reduce_u128_agrees_with_u64_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  (do
    let wide ← utils.monty_reduce_u128 inst (UScalar.cast .U128 x)
    let narrow ← utils.monty_reduce inst x
    ok (wide, narrow)) ⦃ p => p.1.val = p.2.val ⦄

/-! ## Montgomery multiplication -/

/-- PBT `utils::tests::kb_monty_mul_correct` (monty-31/src/utils.rs:555):
```rust
let product = to_monty::<KB>(a) as u64 * to_monty::<KB>(b) as u64;
let expected = to_monty::<KB>(((a as u64 * b as u64) % KB_P as u64) as u32);
prop_assert_eq!(monty_reduce::<KB>(product), expected);
```
The test's own arithmetic (`*` and `%` on `u64`, `as` casts) is executed with the
Rust primitives, in the test's evaluation order. -/
def kb_monty_mul_correct_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let ma ← utils.to_monty inst a
    let mb ← utils.to_monty inst b
    let product ← UScalar.cast .U64 ma * UScalar.cast .U64 mb
    let ab ← UScalar.cast .U64 a * UScalar.cast .U64 b
    let ab_mod ← ab % 2130706433#u64
    let expected ← utils.to_monty inst (UScalar.cast .U32 ab_mod)
    let reduced ← utils.monty_reduce inst product
    ok (reduced, expected)) ⦃ p => p.1.val = p.2.val ⦄

end Benchmark.Cases.Plonky3.Monty31Utils
