import StaticFilezSlice.Extraction

/-!
# static-filez — specifications

Implementation: `extracted/StaticFilezSlice` (verbatim `cargo hax extract
static-filez-slice` output for killercup/static-filez@8bafef57, library target;
see `cases/static_filez/slice/case.yaml`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
`usize` keeps Aeneas' abstract platform width (`System.Platform.numBits` is 32
or 64); no assumption on it is made here.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.StaticFilez.Slice

open static_filez

/-- PBT `slice::tests::slice_encoding_roundtrip` (src/slice.rs:15-18):
`prop_assert_eq!((i as usize, l as usize),
unpack_from_u64(pack_in_u64(i as usize, l as usize)))`.
The test's own `i as usize` / `l as usize` casts are modelled with
`UScalar.cast .Usize`, the operation the extraction uses for Rust `as usize`. -/
def slice_encoding_roundtrip_spec (i l : Std.U32) : Prop :=
  (do
    let packed ← slice.pack_in_u64 (UScalar.cast .Usize i) (UScalar.cast .Usize l)
    slice.unpack_from_u64 packed)
    ⦃ r => r = (UScalar.cast .Usize i, UScalar.cast .Usize l) ⦄

end Benchmark.Cases.StaticFilez.Slice
