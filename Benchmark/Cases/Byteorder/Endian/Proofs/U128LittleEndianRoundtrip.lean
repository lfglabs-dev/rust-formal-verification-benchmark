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

/-! ### Byte-order conversions: `from_le_bytes ∘ to_le_bytes = id` -/

theorem toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

theorem toNat_fromLEBytes_toLEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromLEBytes b.toLEBytes).toNat = b.toNat := by
  rw [BitVec.fromLEBytes_toLEBytes h, BitVec.toNat_cast]

theorem le_from_to_U128 (n : Std.U128) :
    Std.core.num.U128.from_le_bytes (Std.core.num.U128.to_le_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U128.to_le_bytes n).val = n.bv.toLEBytes := by
    simp [Std.core.num.U128.to_le_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U128.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr hl, toNat_fromLEBytes_toLEBytes (by simp)]

/-! ### CoreModels' `to_le_bytes` (an `array::from_fn` over a shifting closure) agrees with Aeneas' `to_le_bytes` -/

theorem eq_ok_of_spec {α : Type} {e : RustM α} {v : α} (h : e ⦃ r => r = v ⦄) : e = ok v := by
  cases e with
  | ok x => simp only [WP.spec_ok] at h; rw [h]
  | fail _ => simp only [WP.spec_fail] at h
  | div => simp only [WP.spec_div] at h

theorem toLEBytes_getElem!_eq {w : Nat} (v : BitVec w) (i : Nat) :
    v.toLEBytes[i]! = (v >>> (8 * i)).setWidth 8 := by
  rw [Byte.eq_iff]
  intro j hj
  rw [BitVec.toLEBytes_getElem!_testBit v i j hj, BitVec.getElem!_eq_testBit_toNat]
  simp only [Byte.testBit, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, hj, decide_true, Bool.true_and]

theorem toLEBytes_eq_map_range {w : Nat} (v : BitVec w) :
    v.toLEBytes = (List.range ((w + 7) / 8)).map (fun k => (v >>> (8 * k)).setWidth 8) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [← getElem!_pos v.toLEBytes i h1, toLEBytes_getElem!_eq]
    simp
theorem usize_ofNat_val (k : Nat) (hk : k < 16) :
    (⟨BitVec.ofNat UScalarTy.Usize.numBits k⟩ : Std.Usize).val = k := by
  simp only [UScalar.val, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    apply Nat.pow_le_pow_right (by omega)
    simp [UScalarTy.numBits]
  omega

theorem closure_spec (n : Std.U128) (k : Nat) (hk : k < 16) :
    core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut n
      ⟨BitVec.ofNat _ k⟩ ⦃ r => r = (⟨(n.bv >>> (8 * k)).setWidth 8⟩, n) ⦄ := by
  unfold core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  have hk' := usize_ofNat_val k (by omega)
  have hi : (UScalar.cast UScalarTy.U32 (⟨BitVec.ofNat UScalarTy.Usize.numBits k⟩ : Std.Usize)).val = k := by
    rw [UScalar.cast_val_eq, hk']; simp; omega
  step*
  · have h2 : i2.val = 8 * k := by rw [i2_post, i1_post, i_post, hi]; omega
    rw [i4_post]
    apply U8.bv_eq_imp_eq
    rw [UScalar.cast_bv_eq, i3_post2, h2]
    rfl

theorem closure_eq (n : Std.U128) (k : Nat) (hk : k < 16) :
    core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut n
      ⟨BitVec.ofNat _ k⟩ = ok (⟨(n.bv >>> (8 * k)).setWidth 8⟩, n) :=
  eq_ok_of_spec (closure_spec n k hk)

theorem to_le_bytes_go (n : Std.U128) : ∀ m, m ≤ 16 →
    rust_primitives.slice.array_from_fn_go
      core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 n m =
      ok ((List.range m).map (fun k => (⟨(n.bv >>> (8 * k)).setWidth 8⟩ : Std.U8)), n) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [rust_primitives.slice.array_from_fn_go, ih (by omega)]
    simp only [bind_tc_ok, core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8]
    rw [closure_eq n m (by omega)]
    simp [List.range_succ]

theorem to_le_bytes_eq (n : Std.U128) :
    core.num.U128.to_le_bytes n = ok (Std.core.num.U128.to_le_bytes n) := by
  unfold core.num.U128.to_le_bytes rust_primitives.slice.array_from_fn
  rw [to_le_bytes_go n _ (by simp)]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp)]
  congr 1
  apply Subtype.ext
  simp only [Std.core.num.U128.to_le_bytes]
  rw [toLEBytes_eq_map_range]
  simp

/-! ### The two functions under test, in closed form -/

theorem read_u128_eq (s : Slice Std.U8) (h : 16 ≤ s.length) :
    LittleEndian.Insts.ByteorderByteOrder.read_u128 s =
      ok (Std.core.num.U128.from_le_bytes ⟨s.val.take 16, by simp [Slice.length] at h ⊢; omega⟩) := by
  unfold LittleEndian.Insts.ByteorderByteOrder.read_u128
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice]
  have h2 : (16#usize : Std.Usize) ≤ s.len := by scalar_tac
  have h3 : 16 ≤ s.length := h
  simp [h2, h3]
  rw [try_from_u8 16#usize _ (by simp [Slice.length]; omega)]
  simp [core.result.Result.unwrap, core.num.U128.from_le_bytes,
    rust_primitives.arithmetic.from_le_bytes_u128]

theorem write_u128_eq (s : Slice Std.U8) (n : Std.U128) (h : 16 ≤ s.length) :
    LittleEndian.Insts.ByteorderByteOrder.write_u128 s n =
      ok ⟨s.val.setSlice! 0 (Std.core.num.U128.to_le_bytes n).val,
        by simp [Slice.length] at h ⊢; scalar_tac⟩ := by
  unfold LittleEndian.Insts.ByteorderByteOrder.write_u128
  simp only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice_mut, Slice.subslice,
    to_le_bytes_eq]
  simp [h, lift]
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, Array.to_slice]; omega)]
  simp [Array.to_slice]

/--
Writing any `u128` with `LittleEndian::write_u128` into a zeroed 16-byte buffer (left-aligned: `buf[..size_of::<u128>()]`) and reading it back with `LittleEndian::read_u128` never panics and returns the same value.
-/
theorem u128_little_endian_roundtrip (n : Std.U128) :
    u128_little_endian_roundtrip_spec n := by
  unfold u128_little_endian_roundtrip_spec
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndexMut,
    core.Array.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_slice, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_slice, rust_primitives.slice.array_as_mut_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut,
    Slice.subslice, Array.to_slice_mut, Array.to_slice, Array.from_slice]
  have hx : (Std.core.num.U128.to_le_bytes n).val.length = 16 := by simp
  rw [write_u128_eq _ _ (by simp [Slice.length])]
  simp only [bind_tc_ok]
  have h1 : [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8].setSlice! 0 (Std.core.num.U128.to_le_bytes n).val =
      (Std.core.num.U128.to_le_bytes n).val := by
    rw [setSlice!_eq_append _ _ _ (by simp [hx])]; simp [hx]
  rw [read_u128_eq _ (by
    simp only [Slice.length, h1]
    simp [hx])]
  simp only [WP.spec_ok]
  have key : ∀ a : Std.Array Std.U8 16#usize, a.val = (Std.core.num.U128.to_le_bytes n).val →
      n = Std.core.num.U128.from_le_bytes a := by
    intro a ha
    have : a = Std.core.num.U128.to_le_bytes n := Subtype.ext ha
    rw [this, le_from_to_U128]
  apply key
  simp only [h1]
  simp [hx, List.take_of_length_le]

end Benchmark.Cases.Byteorder.Endian
