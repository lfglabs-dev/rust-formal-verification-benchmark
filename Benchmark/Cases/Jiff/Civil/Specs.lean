import JiffCivil.Extraction

/-!
# jiff (jiff-core) civil time — specifications

Implementation: `extracted/JiffCivil` (verbatim `cargo hax extract jiff-civil`
output for BurntSushi/jiff@7bd0c363, crate `crates/jiff-core`, root module
`jiff_core::civil::time`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Jiff.Civil

open jiff_core

/-- PBT `civil::time::tests::prop_time_to_nanosecond_roundtrip`
(crates/jiff-core/src/civil/time.rs:672):
`t == t.to_nanosecond().to_time()` — converting a civil time to its
nanosecond-of-day and back yields the same `Time` (derived `PartialEq`). -/
def time_to_nanosecond_roundtrip_spec (t : civil.time.Time) : Prop :=
  (do
    let n ← civil.time.Time.to_nanosecond t
    let t' ← civil.time.TimeNanosecond.to_time n
    civil.time.Time.Insts.CoreCmpPartialEqTime.eq t t') ⦃ b => b = true ⦄

end Benchmark.Cases.Jiff.Civil
