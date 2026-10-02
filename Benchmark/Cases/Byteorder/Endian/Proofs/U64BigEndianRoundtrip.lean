import Benchmark.Cases.Byteorder.Endian.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder

namespace Benchmark.Cases.Byteorder.Endian

set_option linter.unusedSimpArgs false

/-! ### Helper lemmas (CoreModels slice/array primitives on `u8`) -/

/-- `clone` on `u8` is the identity, so cloning a list element-wise succeeds. -/
theorem clone_u8_mapM (l : List Std.U8) :
    List.mapM core.U8.Insts.CoreCloneClone.clone l = ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, ih, bind_tc_ok]
    rfl

/-- `dst.copy_from_slice(src)` on equal-length `u8` slices returns `src`. -/
theorem copy_from_slice_u8 (s src : Slice Std.U8) (h : s.length = src.length) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s src = ok src := by
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  rw [if_pos h]
  split
  · rename_i cloned hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc; rfl
  · rename_i e hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc
  · rename_i hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc

/-- The `array_from_fn` worker used by `<[u8; N]>::try_from(&[u8])` copies a prefix. -/
theorem array_from_fn_go_u8 (s : Slice Std.U8) (N : Std.Usize) :
    ∀ n, n ≤ s.length →
    rust_primitives.slice.array_from_fn_go
      (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        N core.U8.Insts.CoreMarkerCopy) s n = ok (s.val.take n, s) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [rust_primitives.slice.array_from_fn_go, ih (by omega)]
    simp only [bind_tc_ok,
      core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT,
      core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      rust_primitives.slice.slice_index, Slice.index_usize, Slice.getElem?_Usize_eq]
    have hlt : n < s.val.length := by simp [Slice.length] at hn; omega
    have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
      have := s.property
      simp only [UScalar.val, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      scalar_tac
    rw [hv, List.getElem?_eq_getElem hlt]
    simp only [bind_tc_ok, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]

/-- `<[u8; N]>::try_from(s)` succeeds with the slice contents when `s.len() == N`. -/
theorem try_from_u8 (N : Std.Usize) (s : Slice Std.U8) (h : s.length = N.val) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N
      core.U8.Insts.CoreMarkerCopy s = ok (core.result.Result.Ok ⟨s.val, h⟩) := by
  unfold core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  have hlen : s.len = N := by
    apply UScalar.val_eq_imp
    simp [Slice.len, h]
  simp only [rust_primitives.slice.slice_length, hlen, bind_tc_ok, if_true,
    rust_primitives.slice.array_from_fn]
  rw [array_from_fn_go_u8 s N N.val (by omega)]
  simp [List.take_of_length_le (by simp [Slice.length] at h; omega : s.val.length ≤ N.val), h]

/-! ### List lemmas -/

theorem setSlice!_eq_append {α : Type} (s l : List α) (i : Nat) (h : i + l.length ≤ s.length) :
    s.setSlice! i l = s.take i ++ l ++ s.drop (i + l.length) := by
  simp only [List.setSlice!]
  have hmin : min l.length (s.length - i) = l.length := by omega
  rw [hmin, List.take_of_length_le (le_refl _)]

theorem slice_setSlice! {α : Type} (s l : List α) (i j : Nat) (h : i + l.length ≤ s.length)
    (hj : j = i + l.length) :
    List.slice i j (s.setSlice! i l) = l := by
  subst hj
  rw [setSlice!_eq_append s l i h]
  have hi : (s.take i).length = i := by simp; omega
  simp only [List.slice, List.append_assoc, Nat.add_sub_cancel_left]
  rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
  simp

theorem take_setSlice!_zero {α : Type} (s l : List α) (k : Nat) (h : l.length ≤ s.length)
    (hk : k = l.length) :
    List.take k (s.setSlice! 0 l) = l := by
  subst hk
  rw [setSlice!_eq_append s l 0 (by simpa using h)]
  simp

/-! ### Byte-order conversions: `from_be_bytes ∘ to_be_bytes = id` -/

theorem toNat_fromBEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat := by
  subst h; rfl

theorem toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

theorem toNat_fromBEBytes_toBEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  simp only [BitVec.fromBEBytes, BitVec.toBEBytes, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr (List.reverse_reverse _), BitVec.fromLEBytes_toLEBytes h,
    BitVec.toNat_cast]

theorem be_from_to_U64 (n : Std.U64) :
    Std.core.num.U64.from_be_bytes (Std.core.num.U64.to_be_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U64.to_be_bytes n).val = n.bv.toBEBytes := by
    simp [Std.core.num.U64.to_be_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U64.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromBEBytes_congr hl, toNat_fromBEBytes_toBEBytes (by simp)]

/-! ### The two functions under test, in closed form -/

theorem read_u64_eq (s : Slice Std.U8) (h : 8 ≤ s.length) :
    BigEndian.Insts.ByteorderByteOrder.read_u64 s =
      ok (Std.core.num.U64.from_be_bytes ⟨s.val.take 8, by simp [Slice.length] at h ⊢; omega⟩) := by
  unfold BigEndian.Insts.ByteorderByteOrder.read_u64
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice]
  have h2 : (8#usize : Std.Usize) ≤ s.len := by scalar_tac
  have h3 : 8 ≤ s.length := h
  simp [h2, h3]
  rw [try_from_u8 8#usize _ (by simp [Slice.length]; omega)]
  simp [core.result.Result.unwrap, core.num.U64.from_be_bytes,
    rust_primitives.arithmetic.from_be_bytes_u64]

theorem write_u64_eq (s : Slice Std.U8) (n : Std.U64) (h : 8 ≤ s.length) :
    BigEndian.Insts.ByteorderByteOrder.write_u64 s n =
      ok ⟨s.val.setSlice! 0 (Std.core.num.U64.to_be_bytes n).val,
        by simp [Slice.length] at h ⊢; scalar_tac⟩ := by
  unfold BigEndian.Insts.ByteorderByteOrder.write_u64
  simp only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice_mut, Slice.subslice,
    core.num.U64.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u64]
  simp [h, lift]
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, Array.to_slice]; omega)]
  simp [Array.to_slice]

/--
Writing any `u64` with `BigEndian::write_u64` into a zeroed 16-byte buffer (right-aligned: `buf[16 - size_of::<u64>()..]`) and reading it back with `BigEndian::read_u64` never panics and returns the same value.
-/
theorem u64_big_endian_roundtrip (n : Std.U64) :
    u64_big_endian_roundtrip_spec n := by
  unfold u64_big_endian_roundtrip_spec
  step as ⟨start, hstart⟩
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndexMut,
    core.Array.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_slice, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_slice, rust_primitives.slice.array_as_mut_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut,
    Slice.subslice, Array.to_slice_mut, Array.to_slice, Array.from_slice, hstart]
  have hx : (Std.core.num.U64.to_be_bytes n).val.length = 8 := by simp
  rw [write_u64_eq _ _ (by simp [Slice.length])]
  simp only [bind_tc_ok]
  have h1 : [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8].setSlice! 0 (Std.core.num.U64.to_be_bytes n).val =
      (Std.core.num.U64.to_be_bytes n).val := by
    rw [setSlice!_eq_append _ _ _ (by simp [hx])]; simp [hx]
  rw [read_u64_eq _ (by
    simp only [Slice.length, h1]
    rw [slice_setSlice! _ _ _ _ (by simp [hx]) (by simp [hx])]
    simp [hx])]
  simp only [WP.spec_ok]
  have key : ∀ a : Std.Array Std.U8 8#usize, a.val = (Std.core.num.U64.to_be_bytes n).val →
      n = Std.core.num.U64.from_be_bytes a := by
    intro a ha
    have : a = Std.core.num.U64.to_be_bytes n := Subtype.ext ha
    rw [this, be_from_to_U64]
  apply key
  simp only [h1]
  rw [slice_setSlice! _ _ _ _ (by simp [hx]) (by simp [hx])]
  simp [hx, List.take_of_length_le]

end Benchmark.Cases.Byteorder.Endian
