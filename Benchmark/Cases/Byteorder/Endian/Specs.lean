import ByteorderEndian.Extraction

/-!
# byteorder — specifications

Implementation: `extracted/ByteorderEndian` (verbatim `cargo hax extract
byteorder-endian` output for BurntSushi/byteorder@5a82625f): the methods
`read_u16/u32/u64/u128` and `write_u16/u32/u64/u128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`.

The property tests are the `qc_byte_order!` round trips of `src/lib.rs`
(`mod test`, macro template at lines 2349-2393). Each spec executes the test
body in the extracted semantics:

* `let mut buf = [0; 16]` is `Array.repeat 16#usize 0#u8`;
* `&mut buf[a..]` / `&mut buf[..b]` is CoreModels' `IndexMut` for arrays with a
  `RangeFrom`/`RangeTo` index (it returns the sub-slice and the write-back
  function that puts the updated sub-slice back into the array);
* `&buf[a..]` / `&buf[..b]` is CoreModels' `Index` for arrays;
* `BigEndian::write_uN(..)` / `read_uN(..)` are the extracted impl methods;
* `size_of::<uN>()` is the compile-time constant `N/8` (written as a numeral),
  and the big-endian offset `16 - size_of::<uN>()` is computed with the Rust
  `usize` subtraction of the extracted semantics;
* `n.clone()` is `n` (`Copy` integers; for `Wi128<u128>` the test's inherent
  `clone` returns the wrapped `u128`), and `n == r` is equality of the values
  (for `Wi128<u128>`, `PartialEq<u128>` compares the wrapped value).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Any panic
(out-of-range slicing, the `unwrap` of `<[u8; N]>::try_from`, a length
mismatch in `copy_from_slice`) makes the spec false, exactly as it would make
the quickcheck property fail.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Byteorder.Endian

open byteorder

/-- PBT `test::prop_u16::big_endian` (src/lib.rs:2360-2369, instance
`qc_byte_order!(prop_u16, u16, ..)` at src/lib.rs:2396):
```rust
fn prop(n: u16) -> bool {
    let bytes = size_of::<u16>();
    let mut buf = [0; 16];
    BigEndian::write_u16(&mut buf[16 - bytes..], n.clone());
    n == BigEndian::read_u16(&buf[16 - bytes..])
}
```
Writing `n` with `BigEndian::write_u16` into the zero-initialised 16-byte buffer and
reading it back with `BigEndian::read_u16` never panics and returns `n`. -/
def u16_big_endian_roundtrip_spec (n : Std.U16) : Prop :=
  (do
    let start ← 16#usize - 2#usize  -- `16 - size_of::<u16>()`, size 2
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { start }
    let s1 ← BigEndian.Insts.ByteorderByteOrder.write_u16 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { start }
    BigEndian.Insts.ByteorderByteOrder.read_u16 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u16::little_endian` (src/lib.rs:2371-2380, instance
`qc_byte_order!(prop_u16, u16, ..)` at src/lib.rs:2396):
```rust
fn prop(n: u16) -> bool {
    let bytes = size_of::<u16>();
    let mut buf = [0; 16];
    LittleEndian::write_u16(&mut buf[..bytes], n.clone());
    n == LittleEndian::read_u16(&buf[..bytes])
}
```
Writing `n` with `LittleEndian::write_u16` into the zero-initialised 16-byte buffer and
reading it back with `LittleEndian::read_u16` never panics and returns `n`. -/
def u16_little_endian_roundtrip_spec (n : Std.U16) : Prop :=
  (do
    let bytes := 2#usize  -- `size_of::<u16>()`
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { «end» := bytes }
    let s1 ← LittleEndian.Insts.ByteorderByteOrder.write_u16 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := bytes }
    LittleEndian.Insts.ByteorderByteOrder.read_u16 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u32::big_endian` (src/lib.rs:2360-2369, instance
`qc_byte_order!(prop_u32, u32, ..)` at src/lib.rs:2424):
```rust
fn prop(n: u32) -> bool {
    let bytes = size_of::<u32>();
    let mut buf = [0; 16];
    BigEndian::write_u32(&mut buf[16 - bytes..], n.clone());
    n == BigEndian::read_u32(&buf[16 - bytes..])
}
```
Writing `n` with `BigEndian::write_u32` into the zero-initialised 16-byte buffer and
reading it back with `BigEndian::read_u32` never panics and returns `n`. -/
def u32_big_endian_roundtrip_spec (n : Std.U32) : Prop :=
  (do
    let start ← 16#usize - 4#usize  -- `16 - size_of::<u32>()`, size 4
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { start }
    let s1 ← BigEndian.Insts.ByteorderByteOrder.write_u32 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { start }
    BigEndian.Insts.ByteorderByteOrder.read_u32 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u32::little_endian` (src/lib.rs:2371-2380, instance
`qc_byte_order!(prop_u32, u32, ..)` at src/lib.rs:2424):
```rust
fn prop(n: u32) -> bool {
    let bytes = size_of::<u32>();
    let mut buf = [0; 16];
    LittleEndian::write_u32(&mut buf[..bytes], n.clone());
    n == LittleEndian::read_u32(&buf[..bytes])
}
```
Writing `n` with `LittleEndian::write_u32` into the zero-initialised 16-byte buffer and
reading it back with `LittleEndian::read_u32` never panics and returns `n`. -/
def u32_little_endian_roundtrip_spec (n : Std.U32) : Prop :=
  (do
    let bytes := 4#usize  -- `size_of::<u32>()`
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { «end» := bytes }
    let s1 ← LittleEndian.Insts.ByteorderByteOrder.write_u32 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := bytes }
    LittleEndian.Insts.ByteorderByteOrder.read_u32 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u64::big_endian` (src/lib.rs:2360-2369, instance
`qc_byte_order!(prop_u64, u64, ..)` at src/lib.rs:2452):
```rust
fn prop(n: u64) -> bool {
    let bytes = size_of::<u64>();
    let mut buf = [0; 16];
    BigEndian::write_u64(&mut buf[16 - bytes..], n.clone());
    n == BigEndian::read_u64(&buf[16 - bytes..])
}
```
Writing `n` with `BigEndian::write_u64` into the zero-initialised 16-byte buffer and
reading it back with `BigEndian::read_u64` never panics and returns `n`. -/
def u64_big_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let start ← 16#usize - 8#usize  -- `16 - size_of::<u64>()`, size 8
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { start }
    let s1 ← BigEndian.Insts.ByteorderByteOrder.write_u64 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { start }
    BigEndian.Insts.ByteorderByteOrder.read_u64 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u64::little_endian` (src/lib.rs:2371-2380, instance
`qc_byte_order!(prop_u64, u64, ..)` at src/lib.rs:2452):
```rust
fn prop(n: u64) -> bool {
    let bytes = size_of::<u64>();
    let mut buf = [0; 16];
    LittleEndian::write_u64(&mut buf[..bytes], n.clone());
    n == LittleEndian::read_u64(&buf[..bytes])
}
```
Writing `n` with `LittleEndian::write_u64` into the zero-initialised 16-byte buffer and
reading it back with `LittleEndian::read_u64` never panics and returns `n`. -/
def u64_little_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let bytes := 8#usize  -- `size_of::<u64>()`
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { «end» := bytes }
    let s1 ← LittleEndian.Insts.ByteorderByteOrder.write_u64 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := bytes }
    LittleEndian.Insts.ByteorderByteOrder.read_u64 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u128::big_endian` (src/lib.rs:2360-2369, instance
`qc_byte_order!(prop_u128, Wi128<u128>, ..)` at src/lib.rs:2481):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let bytes = size_of::<Wi128<u128>>();
    let mut buf = [0; 16];
    BigEndian::write_u128(&mut buf[16 - bytes..], n.clone());
    n == BigEndian::read_u128(&buf[16 - bytes..])
}
```
Writing `n` with `BigEndian::write_u128` into the zero-initialised 16-byte buffer and
reading it back with `BigEndian::read_u128` never panics and returns `n`. -/
def u128_big_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let start ← 16#usize - 16#usize  -- `16 - size_of::<Wi128<u128>>()`, size 16
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { start }
    let s1 ← BigEndian.Insts.ByteorderByteOrder.write_u128 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { start }
    BigEndian.Insts.ByteorderByteOrder.read_u128 s2) ⦃ r => n = r ⦄

/-- PBT `test::prop_u128::little_endian` (src/lib.rs:2371-2380, instance
`qc_byte_order!(prop_u128, Wi128<u128>, ..)` at src/lib.rs:2481):
```rust
fn prop(n: Wi128<u128>) -> bool {
    let bytes = size_of::<Wi128<u128>>();
    let mut buf = [0; 16];
    LittleEndian::write_u128(&mut buf[..bytes], n.clone());
    n == LittleEndian::read_u128(&buf[..bytes])
}
```
Writing `n` with `LittleEndian::write_u128` into the zero-initialised 16-byte buffer and
reading it back with `LittleEndian::read_u128` never panics and returns `n`. -/
def u128_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let bytes := 16#usize  -- `size_of::<Wi128<u128>>()`
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { «end» := bytes }
    let s1 ← LittleEndian.Insts.ByteorderByteOrder.write_u128 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := bytes }
    LittleEndian.Insts.ByteorderByteOrder.read_u128 s2) ⦃ r => n = r ⦄

end Benchmark.Cases.Byteorder.Endian
