import QuantilesGreenwaldKhanna.Extraction

/-!
# quantiles (Greenwald-Khanna insertion position) — specifications

Implementation: `extracted/QuantilesGreenwaldKhanna` (verbatim `cargo hax extract
quantiles-greenwald-khanna` output for postmates/quantiles@400abb05).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The Rust functions are generic over `T: Ord`; the PBT instantiates them at
`i32`, whose `Ord` dictionary is the CoreModels instance
`core.I32.Insts.CoreCmpOrd` (comparison of the integer values).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Quantiles.GreenwaldKhanna

open quantiles

/-- PBT `greenwald_khanna::test::find_insert_pos_log_equals_find_insert_pos_linear`
(src/greenwald_khanna.rs:484), one iteration `v` of its `for v in -100..100` loop
over the sorted vector `vs`:
`find_insert_pos(&vs, &v) == find_insert_pos_linear(&vs, &v)` (the test returns
`false` otherwise). Both calls are evaluated in the Rust order; a panic in either
falsifies the spec. -/
def find_insert_pos_matches_linear_spec (vs : Slice Std.I32) (v : Std.I32) : Prop :=
  (do
    let log ← greenwald_khanna.find_insert_pos core.I32.Insts.CoreCmpOrd vs v
    let lin ← greenwald_khanna.find_insert_pos_linear core.I32.Insts.CoreCmpOrd vs v
    ok (log, lin)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Quantiles.GreenwaldKhanna
