import Crc32fastBaseline.Extraction

/-!
# crc32fast — baseline (table-driven) implementation — specifications

Implementation: `extracted/Crc32fastBaseline` (verbatim `cargo hax extract
crc32fast-baseline` output for srijs/rust-crc32fast@ad14266c): the portable
CRC-32 (IEEE, reflected polynomial `0xEDB88320`) update functions
`crc32fast.baseline.update_slow` (byte-at-a-time, table row 0) and
`crc32fast.baseline.update_fast_16` (slicing-by-16 with the 16×256 table
`crc32fast.table.CRC32_TABLE`, unrolled 4×16 bytes, then 16-byte blocks, then
a byte-wise tail).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic,
indexing and slicing in the extracted code follow Rust debug-build semantics
(out-of-bounds index/slice or overflow panics), which is the configuration
`cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Crc32fast.Baseline

open crc32fast

/-- PBT `baseline::test::fast_16_is_the_same_as_slow` (src/baseline.rs:79-83), quickcheck:
```rust
fn fast_16_is_the_same_as_slow(crc: u32, bytes: Vec<u8>) -> bool {
    super::update_fast_16(crc, &bytes) == super::update_slow(crc, &bytes)
}
```
Both calls receive `&bytes` (the `Vec<u8>` dereferenced to a `&[u8]`, CoreModels
`Deref for Vec`); the test's `bool` result is `true` iff the two `u32`
checksums are equal. -/
def fast_16_is_the_same_as_slow_spec (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) : Prop :=
  (do
    let s1 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let fast ← baseline.update_fast_16 crc s1
    let s2 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let slow ← baseline.update_slow crc s2
    ok (fast, slow)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Crc32fast.Baseline
