import TinysetFits64.Extraction

/-!
# tinyset (Fits64) — specifications

Implementation: `extracted/TinysetFits64` (verbatim `cargo hax extract
tinyset-fits64` output for droundy/tinyset@c21d0dee, rooted at every
`impl Fits64 for _` of src/set64.rs except the `char` one).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Tinyset.Fits64

open tinyset

/-- PBT `set64::fits_i64` (src/set64.rs:112-118, instantiated by
`define_ifits!(i64, u64, fits_i64)` at src/set64.rs:124), which calls
`test_fits64(x)` (src/set64.rs:29-35):
```
let x64 = x.to_u64();
let y = unsafe { T::from_u64(x64) };
let y64 = y.to_u64();
assert_eq!(x, y);
assert_eq!(x64, y64);
```
with `T = i64`: the `Fits64` encoding of an `i64` into a `u64` (zig-zag style:
non-negative `x ↦ 2x`, negative `x ↦ 2(!x) + 1`, computed with bit masks) is
decoded back to `x`, and re-encoding the decoded value gives the same word. -/
def fits_i64_roundtrip_spec (x : Std.I64) : Prop :=
  (do
    let x64 ← I64.Insts.TinysetSet64Fits64.to_u64 x
    let y ← I64.Insts.TinysetSet64Fits64.from_u64 x64
    let y64 ← I64.Insts.TinysetSet64Fits64.to_u64 y
    ok (x64, y, y64)) ⦃ r => r.2.1 = x ∧ r.1 = r.2.2 ⦄

end Benchmark.Cases.Tinyset.Fits64
