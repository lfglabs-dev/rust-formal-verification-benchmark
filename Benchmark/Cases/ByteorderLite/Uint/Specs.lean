import ByteorderLiteUint.Extraction

/-!
# byteorder-lite — specifications (variable-width unsigned integers)

Implementation: `extracted/ByteorderLiteUint` (verbatim `cargo hax extract
byteorder-lite-uint` output for image-rs/byteorder-lite@7d44da06): the methods
`read_uint`, `write_uint`, `read_uint128`, `write_uint128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`, and the
private helpers `pack_size` / `pack_size128` they call.

The property tests are the first arm of the `qc_byte_order!` macro in
`src/lib.rs` (`mod test`, macro template at lines 2384-2428; the
`big_endian`/`little_endian` bodies are at lines 2396-2403 / 2406-2413),
instantiated as `prop_uint_N` (`u64`, `read_uint`/`write_uint`, N = 1..8) and
`prop_uint128_N` (`Wi128<u128>`, `read_uint128`/`write_uint128`, N = 1..16):

```rust
fn prop(n: $ty_int) -> bool {
    let mut buf = [0; 16];
    BigEndian::$write(&mut buf, n.clone(), $bytes);      // resp. LittleEndian
    n == BigEndian::$read(&buf[..$bytes], $bytes)
}
qc_sized(prop as fn($ty_int) -> bool, $max);
```

Each spec executes this body in the extracted semantics:

* `let mut buf = [0; 16]` is `Array.repeat 16#usize 0#u8`;
* `&mut buf` passed where `&mut [u8]` is expected is the array-to-slice
  unsizing coercion, which Aeneas translates as
  `let (s, back) ← lift (Array.to_slice_mut buf)`; the updated array after the
  call is `back s'`;
* `&buf[..N]` is CoreModels' `Index` for arrays with a `RangeTo` index;
* `BigEndian::write_uint(..)` / `read_uint(..)` (and the `128`/`LittleEndian`
  variants) are the extracted impl methods, called with the literal byte count
  `N` of the macro instance;
* `n.clone()` is `n` (`u64` is `Copy`; for `Wi128<u128>` the test's inherent
  `clone` returns the wrapped `u128`), and `n == r` is equality of the values
  (for `Wi128<u128>`, `PartialEq<u128>` compares the wrapped value).

Generated inputs (the theorems' hypotheses): `write_uint(buf, n, N)` asserts
`pack_size(n) <= N`, i.e. `n < 2^(8N)`, so the round trip is false without a
bound; the tests bound `n` through their generator:

* `prop_uint_N`: quickcheck 0.9 `Arbitrary for u64` samples
  `gen_range(0, size)` with `size = calc_max!(u64::MAX, N) = (2^64 - 2) >> (8 * (8 - N))`,
  i.e. `n ∈ [0, 2^(8N) - 2]` for `N < 8` and `n ∈ [0, 2^64 - 3]` for `N = 8`;
* `prop_uint128_N`: `Arbitrary for Wi128<u128>` draws a uniform `u128`
  `output` and returns `output & (max - 1)` with
  `max = calc_max!(u128::MAX, N, 16) = (2^128 - 2) >> (8 * (16 - N))`,
  i.e. the value is masked to `n < 2^(8N)` (and, as an artefact of the
  `max - 1`, one low bit is always cleared).

The theorems take the exact no-panic domain of the writer, `n < 2^(8N)`, as
hypothesis (no hypothesis for the full widths `N = 8` / `N = 16`): a superset
of every sampled value, so each theorem implies the property on the test's
domain.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Any panic (the
`assert!`s of `write_uint`/`read_uint`, out-of-range slicing, a length mismatch
in `copy_from_slice`, an arithmetic overflow) makes the spec false, exactly as
it would make the quickcheck property fail.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.ByteorderLite.Uint

open byteorder_lite

/-- PBT `test::prop_uint_1::little_endian` (src/lib.rs:2406-2413, instance
`qc_byte_order!(prop_uint_1, u64, calc_max!(super::U64_MAX, 1), 1, read_uint, write_uint)`
at src/lib.rs:2561-2568):
```rust
fn prop(n: u64) -> bool {
    let mut buf = [0; 16];
    LittleEndian::write_uint(&mut buf, n.clone(), 1);
    n == LittleEndian::read_uint(&buf[..1], 1)
}
```
Writing `n` as a 1-byte little-endian integer into the zero-initialised 16-byte
buffer and reading the first byte back never panics and returns `n`. -/
def uint_1_little_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← LittleEndian.Insts.Byteorder_liteByteOrder.write_uint s n 1#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..1]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 1#usize }
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint s2 1#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint_3::big_endian` (src/lib.rs:2396-2403, instance
`qc_byte_order!(prop_uint_3, u64, calc_max!(super::U64_MAX, 3), 3, read_uint, write_uint)`
at src/lib.rs:2577-2584):
```rust
fn prop(n: u64) -> bool {
    let mut buf = [0; 16];
    BigEndian::write_uint(&mut buf, n.clone(), 3);
    n == BigEndian::read_uint(&buf[..3], 3)
}
```
Writing `n` as a 3-byte big-endian integer into the zero-initialised 16-byte
buffer and reading the first 3 bytes back never panics and returns `n`. -/
def uint_3_big_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← BigEndian.Insts.Byteorder_liteByteOrder.write_uint s n 3#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..3]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 3#usize }
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint s2 3#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint_5::little_endian` (src/lib.rs:2406-2413, instance
`qc_byte_order!(prop_uint_5, u64, calc_max!(super::U64_MAX, 5), 5, read_uint, write_uint)`
at src/lib.rs:2593-2600):
```rust
fn prop(n: u64) -> bool {
    let mut buf = [0; 16];
    LittleEndian::write_uint(&mut buf, n.clone(), 5);
    n == LittleEndian::read_uint(&buf[..5], 5)
}
```
Writing `n` as a 5-byte little-endian integer into the zero-initialised 16-byte
buffer and reading the first 5 bytes back never panics and returns `n`. -/
def uint_5_little_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← LittleEndian.Insts.Byteorder_liteByteOrder.write_uint s n 5#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..5]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 5#usize }
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint s2 5#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint_8::big_endian` (src/lib.rs:2396-2403, instance
`qc_byte_order!(prop_uint_8, u64, calc_max!(super::U64_MAX, 8), 8, read_uint, write_uint)`
at src/lib.rs:2617-2624):
```rust
fn prop(n: u64) -> bool {
    let mut buf = [0; 16];
    BigEndian::write_uint(&mut buf, n.clone(), 8);
    n == BigEndian::read_uint(&buf[..8], 8)
}
```
Writing any `u64` as an 8-byte big-endian integer into the zero-initialised
16-byte buffer and reading the first 8 bytes back never panics and returns
`n`. -/
def uint_8_big_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← BigEndian.Insts.Byteorder_liteByteOrder.write_uint s n 8#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..8]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 8#usize }
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint s2 8#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint128_4::big_endian` (src/lib.rs:2396-2403, instance
`qc_byte_order!(prop_uint128_4, Wi128<u128>, 4, 4, read_uint128, write_uint128)`
at src/lib.rs:2650-2657):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let mut buf = [0; 16];
    BigEndian::write_uint128(&mut buf, n.clone(), 4);
    n == BigEndian::read_uint128(&buf[..4], 4)
}
```
Writing `n` as a 4-byte big-endian integer into the zero-initialised 16-byte
buffer and reading the first 4 bytes back never panics and returns `n`. -/
def uint128_4_big_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n 4#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..4]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 4#usize }
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 s2 4#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint128_9::little_endian` (src/lib.rs:2406-2413, instance
`qc_byte_order!(prop_uint128_9, Wi128<u128>, 9, 9, read_uint128, write_uint128)`
at src/lib.rs:2690-2697):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let mut buf = [0; 16];
    LittleEndian::write_uint128(&mut buf, n.clone(), 9);
    n == LittleEndian::read_uint128(&buf[..9], 9)
}
```
Writing `n` as a 9-byte little-endian integer into the zero-initialised 16-byte
buffer and reading the first 9 bytes back never panics and returns `n`. -/
def uint128_9_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n 9#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..9]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 9#usize }
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 s2 9#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint128_14::big_endian` (src/lib.rs:2396-2403, instance
`qc_byte_order!(prop_uint128_14, Wi128<u128>, 14, 14, read_uint128, write_uint128)`
at src/lib.rs:2730-2737):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let mut buf = [0; 16];
    BigEndian::write_uint128(&mut buf, n.clone(), 14);
    n == BigEndian::read_uint128(&buf[..14], 14)
}
```
Writing `n` as a 14-byte big-endian integer into the zero-initialised 16-byte
buffer and reading the first 14 bytes back never panics and returns `n`. -/
def uint128_14_big_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← BigEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n 14#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..14]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 14#usize }
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint128 s2 14#usize) ⦃ r => n = r ⦄

/-- PBT `test::prop_uint128_16::little_endian` (src/lib.rs:2406-2413, instance
`qc_byte_order!(prop_uint128_16, Wi128<u128>, 16, 16, read_uint128, write_uint128)`
at src/lib.rs:2746-2753):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let mut buf = [0; 16];
    LittleEndian::write_uint128(&mut buf, n.clone(), 16);
    n == LittleEndian::read_uint128(&buf[..16], 16)
}
```
Writing any `u128` as a 16-byte little-endian integer into the zero-initialised
16-byte buffer and reading all 16 bytes back never panics and returns `n`. -/
def uint128_16_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n 16#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..16]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 16#usize }
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 s2 16#usize) ⦃ r => n = r ⦄

end Benchmark.Cases.ByteorderLite.Uint
