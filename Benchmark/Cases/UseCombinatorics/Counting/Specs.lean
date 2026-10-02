import UseCombinatoricsCounting.Extraction

/-!
# use-combinatorics (RustUse/use-math) — specifications

Implementation: `extracted/UseCombinatoricsCounting` (verbatim `cargo hax extract
use-combinatorics-counting` output for RustUse/use-math@183d26ec, crate
`crates/use-combinatorics`): `use_combinatorics.counting.factorial` and
`use_combinatorics.counting.permutations` with their loops.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The property tests compare the library against test-local reference helpers
(`factorial_reference`, `permutations_reference` in
`tests/property_counting.rs`). Those helpers live in an integration-test file,
which hax does not extract, so they are transcribed below line by line:
`u128::checked_mul` becomes `checkedMulU128` (a `u128` is a natural number
`< 2^128`; `checked_mul` returns `None` exactly when the product does not fit),
the `for factor in a..=b { result = result.checked_mul(factor)?; }` loop becomes
a `List.foldlM` in the `Option` monad over `List.range' a (b + 1 - a)` (the
`?` short-circuits on the first `None`, as `Option.bind` does).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.UseCombinatorics.Counting

open use_combinatorics

/-- `u128::checked_mul` on the values of two `u128`s: `Some (a * b)` if the product
fits in 128 bits, `None` otherwise. -/
def checkedMulU128 (a b : Nat) : Option Nat :=
  if a * b < 2^128 then some (a * b) else none

/-- Transcription of the test helper (tests/property_counting.rs:4-12)
```rust
fn factorial_reference(n: u8) -> Option<u128> {
    let mut result = 1_u128;
    for factor in 2..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }
    Some(result)
}
```
`2..=n` enumerates `List.range' 2 (n + 1 - 2)`. -/
def factorial_reference (n : Nat) : Option Nat :=
  (List.range' 2 (n + 1 - 2)).foldlM checkedMulU128 1

/-- Transcription of the test helper (tests/property_counting.rs:14-27)
```rust
fn permutations_reference(n: u8, k: u8) -> Option<u128> {
    if k > n {
        return None;
    }
    let mut result = 1_u128;
    let start = u64::from(n - k) + 1;
    for factor in start..=u64::from(n) {
        result = result.checked_mul(u128::from(factor))?;
    }
    Some(result)
}
```
(`n - k` cannot underflow after the `k > n` guard; `start ≤ 256` cannot overflow.)
`start..=n` enumerates `List.range' start (n + 1 - start)`. -/
def permutations_reference (n k : Nat) : Option Nat :=
  if k > n then none
  else
    let start := (n - k) + 1
    (List.range' start (n + 1 - start)).foldlM checkedMulU128 1

/-- PBT `factorial_matches_checked_reference` (tests/property_counting.rs:50-59):
```rust
let n_u64 = u64::from(n);
if let Some(expected) = factorial_reference(n) {
    prop_assert_eq!(factorial(n_u64), Ok(expected));
} else {
    prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
}
```
The do-block performs the conversion `u64::from(n)` and the call; the
postcondition is the branch selected by the reference. -/
def factorial_matches_checked_reference_spec (n : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let result ← counting.factorial n_u64
    ok (n_u64, result)) ⦃ out =>
      match out with
      | (n_u64, result) =>
        match factorial_reference n.val with
        | some expected =>
          ∃ v : Std.U128, result = core.result.Result.Ok v ∧ v.val = expected
        | none =>
          result = core.result.Result.Err (error.CombinatoricsError.FactorialOverflow n_u64) ⦄

/-- PBT `factorial_overflow_boundary_is_exact` (tests/property_counting.rs:61-70):
```rust
let n_u64 = u64::from(n);
if n <= 34 {
    prop_assert!(factorial(n_u64).is_ok());
} else {
    prop_assert_eq!(factorial(n_u64), Err(CombinatoricsError::FactorialOverflow(n_u64)));
}
```
`is_ok()` holds exactly when the result is an `Ok _`. -/
def factorial_overflow_boundary_is_exact_spec (n : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let result ← counting.factorial n_u64
    ok (n_u64, result)) ⦃ out =>
      match out with
      | (n_u64, result) =>
        if n.val ≤ 34 then
          ∃ v : Std.U128, result = core.result.Result.Ok v
        else
          result = core.result.Result.Err (error.CombinatoricsError.FactorialOverflow n_u64) ⦄

/-- PBT `permutations_match_checked_reference` (tests/property_counting.rs:72-90):
```rust
let n_u64 = u64::from(n);
let k_u64 = u64::from(k);
if k > n {
    prop_assert_eq!(permutations(n_u64, k_u64),
        Err(CombinatoricsError::KExceedsN { n: n_u64, k: k_u64 }));
} else if let Some(expected) = permutations_reference(n, k) {
    prop_assert_eq!(permutations(n_u64, k_u64), Ok(expected));
} else {
    prop_assert_eq!(permutations(n_u64, k_u64),
        Err(CombinatoricsError::PermutationOverflow { n: n_u64, k: k_u64 }));
}
``` -/
def permutations_match_checked_reference_spec (n k : Std.U8) : Prop :=
  (do
    let n_u64 ← core.U64.Insts.CoreConvertFromU8.from n
    let k_u64 ← core.U64.Insts.CoreConvertFromU8.from k
    let result ← counting.permutations n_u64 k_u64
    ok (n_u64, k_u64, result)) ⦃ out =>
      match out with
      | (n_u64, k_u64, result) =>
        if k.val > n.val then
          result = core.result.Result.Err (error.CombinatoricsError.KExceedsN n_u64 k_u64)
        else
          match permutations_reference n.val k.val with
          | some expected =>
            ∃ v : Std.U128, result = core.result.Result.Ok v ∧ v.val = expected
          | none =>
            result = core.result.Result.Err
              (error.CombinatoricsError.PermutationOverflow n_u64 k_u64) ⦄

end Benchmark.Cases.UseCombinatorics.Counting
