import Benchmark.Cases.Etherparse.Link.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

theorem e2r_toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

theorem e2r_toNat_fromBEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat := by
  subst h; rfl

theorem e2r_toNat_fromBEBytes_toBEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  simp only [BitVec.fromBEBytes, BitVec.toBEBytes, BitVec.toNat_cast]
  rw [e2r_toNat_fromLEBytes_congr (List.reverse_reverse _), BitVec.fromLEBytes_toLEBytes h,
    BitVec.toNat_cast]

/-- `u16::from_be_bytes(x.to_be_bytes()) == x` in the Aeneas byte-order model. -/
theorem e2r_be_from_to_U16 (n : Std.U16) :
    Std.core.num.U16.from_be_bytes (Std.core.num.U16.to_be_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U16.to_be_bytes n).val = n.bv.toBEBytes := by
    simp [Std.core.num.U16.to_be_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U16.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  rw [e2r_toNat_fromBEBytes_congr hl, e2r_toNat_fromBEBytes_toBEBytes (by simp)]

theorem e2r_list2 {α : Type} (l : List α) (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem e2r_list6 {α : Type} (l : List α) (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

@[simp] theorem e2r_make_val {α : Type} (n : Std.Usize) (l : List α) (h : l.length = n.val) :
    (Array.make n l h).val = l := rfl

/--
Serialising an Ethernet II header to its 14 wire bytes and parsing them back
never panics and yields the original header.
-/
theorem ethernet2_from_bytes_roundtrip (input : link.ethernet2_header.Ethernet2Header) :
    ethernet2_from_bytes_roundtrip_spec input := by
  obtain ⟨e0, e1, he⟩ := e2r_list2 (Std.core.num.U16.to_be_bytes input.ether_type).val (by simp)
  obtain ⟨d0, d1, d2, d3, d4, d5, hd⟩ := e2r_list6 input.destination.val (by simp)
  obtain ⟨s0, s1, s2, s3, s4, s5, hs⟩ := e2r_list6 input.source.val (by simp)
  have het : Std.core.num.U16.from_be_bytes (Array.make 2#usize [e0, e1]) = input.ether_type := by
    have : (Array.make 2#usize [e0, e1] : Std.Array Std.U8 2#usize) =
        Std.core.num.U16.to_be_bytes input.ether_type := Subtype.ext (by simp [he])
    rw [this, e2r_be_from_to_U16]
  have hdst : (Array.make 6#usize [d0, d1, d2, d3, d4, d5] : Std.Array Std.U8 6#usize) =
      input.destination := Subtype.ext (by simp [hd])
  have hsrc : (Array.make 6#usize [s0, s1, s2, s3, s4, s5] : Std.Array Std.U8 6#usize) =
      input.source := Subtype.ext (by simp [hs])
  unfold ethernet2_from_bytes_roundtrip_spec link.ethernet2_header.Ethernet2Header.to_bytes
    link.ethernet2_header.Ethernet2Header.from_bytes
  simp only [core.num.U16.to_be_bytes, core.num.U16.from_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_u16, rust_primitives.arithmetic.from_be_bytes_u16,
    bind_tc_ok, Array.index_usize, Array.getElem?_Usize_eq, he, hd, hs]
  simp [het, hdst, hsrc]

end Benchmark.Cases.Etherparse.Link
