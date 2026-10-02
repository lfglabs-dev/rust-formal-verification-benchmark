import EtherparseLink.Extraction

/-!
# etherparse (link layer) — specifications

Implementation: `extracted/EtherparseLink` (verbatim `cargo hax extract
etherparse-link` output for JulianSchmid/etherparse@70f72bee, crate
`etherparse` 0.21.0, `--no-default-features`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow and
`debug_assert!` failures panic), which is the configuration `cargo test` runs
the original property tests under.

Conventions used below:
* newtype wrappers (`EtherType(u16)`, `LinuxSllPacketType(u16)`,
  `ArpHardwareId(u16)`, `MacsecShortLen(u8)`, ...) are extracted as reducible
  aliases of the wrapped scalar, so `x.0` / `x.value()` is the scalar itself;
* `&mut self` methods return the updated value (`set_payload_len`);
* `x.clone()` of the derived `Clone` impls is `x` itself;
* `.unwrap()` / `.unwrap_err()` succeed iff the result is `Ok` / `Err`, so the
  postconditions require the corresponding constructor.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Etherparse.Link

open etherparse

/-- PBT `link::linux_sll_header::test::from_bytes`
(etherparse/src/link/linux_sll_header.rs:185-190):
```
assert_eq!(input, LinuxSllHeader::from_bytes(input.to_bytes()).unwrap());
```
Serialising a Linux "cooked capture" (SLL) header and parsing the 16 bytes back
never panics and yields `Ok(input)`. -/
def linux_sll_from_bytes_roundtrip_spec
    (input : link.linux_sll_header.LinuxSllHeader) : Prop :=
  (do
    let bytes ← link.linux_sll_header.LinuxSllHeader.to_bytes input
    link.linux_sll_header.LinuxSllHeader.from_bytes bytes)
    ⦃ r => r = core.result.Result.Ok input ⦄

/-- PBT `link::ethernet2_header::test::from_bytes`
(etherparse/src/link/ethernet2_header.rs:181-186):
```
assert_eq!(input, Ethernet2Header::from_bytes(input.to_bytes()));
```
Serialising an Ethernet II header to its 14 wire bytes and parsing them back
never panics and yields the original header. -/
def ethernet2_from_bytes_roundtrip_spec
    (input : link.ethernet2_header.Ethernet2Header) : Prop :=
  (do
    let bytes ← link.ethernet2_header.Ethernet2Header.to_bytes input
    link.ethernet2_header.Ethernet2Header.from_bytes bytes)
    ⦃ r => r = input ⦄

/-- PBT `link::ethernet2_header::test::write_to_slice`
(etherparse/src/link/ethernet2_header.rs:222-243):
```
{ let mut buffer: [u8;14] = [0;14];
  input.write_to_slice(&mut buffer).unwrap();
  assert_eq!(buffer, input.to_bytes()); }
for len in 0..14 {
  let mut buffer: [u8;14] = [0;14];
  assert_eq!(SliceWriteSpaceError { required_len: Ethernet2Header::LEN, len,
      layer: Layer::Ethernet2Header, layer_start_offset: 0 },
    input.write_to_slice(&mut buffer[..len]).unwrap_err()); }
```
`[0;14]` is `Array.repeat`; `&mut buffer` is `Array.to_slice_mut`; `&mut buffer[..len]`
is `IndexMut` for `RangeTo`. `write_to_slice` returns the `Result` together with
the write-back that rebuilds the borrowed slice (`unwrap` / `unwrap_err` require
`Ok` / `Err`). The mutated array is that write-back applied to the `Result`,
then `Array.from_slice`. -/
def ethernet2_write_to_slice_spec (input : link.ethernet2_header.Ethernet2Header) : Prop :=
  (do
    let buf := Array.repeat 14#usize 0#u8
    let (s, backArr) ← lift (Array.to_slice_mut buf)
    let (r, back) ← link.ethernet2_header.Ethernet2Header.write_to_slice input s
    let full := back r
    let arr := backArr full
    let expected ← link.ethernet2_header.Ethernet2Header.to_bytes input
    ok (r, arr, expected))
    ⦃ t => ∃ rest, t.1 = core.result.Result.Ok rest ∧ t.2.1 = t.2.2 ⦄ ∧
  (∀ len : Std.Usize, len.val < 14 →
    (do
      let buf := Array.repeat 14#usize 0#u8
      let (s, _backArr) ←
        core.Array.Insts.CoreOpsIndexIndexMut.index_mut
          (core.Slice.Insts.CoreOpsIndexIndexMut
            (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
          buf { «end» := len }
      let (r, _back) ← link.ethernet2_header.Ethernet2Header.write_to_slice input s
      ok r)
      ⦃ r => r = core.result.Result.Err {
        required_len := link.ethernet2_header.Ethernet2Header.LEN,
        len := len,
        layer := err.layer.Layer.Ethernet2Header,
        layer_start_offset := 0#usize } ⦄)

end Benchmark.Cases.Etherparse.Link
