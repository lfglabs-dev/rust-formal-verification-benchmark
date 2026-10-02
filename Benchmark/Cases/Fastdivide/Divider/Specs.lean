import FastdivideDivider.Extraction

/-!
# fastdivide — specifications

Implementation: `extracted/FastdivideDivider` (verbatim `cargo hax extract
fastdivide-divider` output for fulmicoton/fastdivide@1e9a5295).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Fastdivide.Divider

open fastdivide

/-- PBT `tests::test_proptest` (src/lib.rs:236):
`DividerU64::divide_by(d).divide(n) == n / d`. -/
def divide_matches_native_division_spec (n d : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by d
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / d.val ⦄

/-- PBT `tests::test_proptest_divide_by_7` (src/lib.rs:246):
`DividerU64::divide_by(7).divide(n) == n / 7` (exercises the `General` path). -/
def divide_by_7_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 7#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 7 ⦄

/-- PBT `tests::test_proptest_divide_by_11` (src/lib.rs:256):
`DividerU64::divide_by(11).divide(n) == n / 11` (exercises the `Fast` path). -/
def divide_by_11_matches_native_division_spec (n : Std.U64) : Prop :=
  (do
    let divider ← DividerU64.divide_by 11#u64
    DividerU64.divide divider n) ⦃ quotient => quotient.val = n.val / 11 ⦄

end Benchmark.Cases.Fastdivide.Divider
