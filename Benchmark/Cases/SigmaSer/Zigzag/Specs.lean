import SigmaSerZigzag.Extraction

/-!
# sigma_ser — zigzag specifications

Implementation: `extracted/SigmaSerZigzag` (verbatim `cargo hax extract
sigma-ser-zigzag` output for ergoplatform/sigma-rust@1633e018, crate
`sigma-ser` 0.20.0, module `sigma_ser::zig_zag_encode`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. The extracted
functions are pure integer code; shifts by a constant amount never panic
(amount < bit width), and the negations `-.` act on `0`/`1`, so the only way
the do-blocks below could fail is inside the extracted callee bodies.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.SigmaSer.Zigzag

open sigma_ser

/-- PBT `zig_zag_encode::tests::encode_i64_roundtrip`
(sigma-ser/src/zig_zag_encode.rs:81):
`decode_u64(encode_i64(i)) == i` for `i` over the full `i64` domain
(`i64::ANY` strategy: no bounds). -/
def encode_i64_roundtrip_spec (i : Std.I64) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i64 i
    zig_zag_encode.decode_u64 enc) ⦃ dec => dec.val = i.val ⦄

/-- PBT `zig_zag_encode::tests::encode_i32_roundtrip`
(sigma-ser/src/zig_zag_encode.rs:75):
`decode_u32(encode_i32(i)) == i` for `i` over the full `i32` domain
(`i32::ANY` strategy: no bounds). -/
def encode_i32_roundtrip_spec (i : Std.I32) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i32 i
    zig_zag_encode.decode_u32 enc) ⦃ dec => dec.val = i.val ⦄

end Benchmark.Cases.SigmaSer.Zigzag
