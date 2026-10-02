import Benchmark.Cases.ByteorderLite.Uint.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/-! ### Slice / list helpers (CoreModels `copy_from_slice`, `setSlice!`) -/

set_option linter.unusedSimpArgs false

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

theorem setSlice!_eq_append {α : Type} (s l : List α) (i : Nat) (h : i + l.length ≤ s.length) :
    s.setSlice! i l = s.take i ++ l ++ s.drop (i + l.length) := by
  simp only [List.setSlice!]
  have hmin : min l.length (s.length - i) = l.length := by omega
  rw [hmin, List.take_of_length_le (le_refl _)]

theorem replicate_setSlice! {α : Type} (x : α) (l : List α) (k : Nat) (h : l.length ≤ k) :
    (List.replicate k x).setSlice! (k - l.length) l = List.replicate (k - l.length) x ++ l := by
  rw [setSlice!_eq_append _ _ _ (by simp; omega)]
  simp [List.take_replicate, List.drop_replicate]
  omega

/-! ### Bytes of a bounded value -/

theorem toLEBytes_getElem!_eq {w : Nat} (v : BitVec w) (i : Nat) :
    v.toLEBytes[i]! = (v >>> (8 * i)).setWidth 8 := by
  rw [Byte.eq_iff]
  intro j hj
  rw [BitVec.toLEBytes_getElem!_testBit v i j hj, BitVec.getElem!_eq_testBit_toNat]
  simp only [Byte.testBit, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, hj, decide_true, Bool.true_and]

/-- Bytes of `v` at positions `≥ N` are zero when `v < 2^(8N)`. -/
theorem toLEBytes_getElem_eq_zero {w : Nat} (v : BitVec w) (N i : Nat)
    (hv : v.toNat < 2^(8*N)) (hi : N ≤ i) (hlt : i < v.toLEBytes.length) :
    v.toLEBytes[i] = 0#8 := by
  rw [← getElem!_pos v.toLEBytes i hlt, toLEBytes_getElem!_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  have : 2^(8*N) ≤ 2^(8*i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.div_eq_of_lt (by omega)]

theorem toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

/-! ### `pack_size128`: the writer's `assert!(pack_size128(n) <= nbytes)` holds for `n < 2^(8 nbytes)` -/

theorem lz128_val (d : Std.U128) (h : d.val ≠ 0) :
    (Aeneas.Std.core.num.U128.leading_zeros d).val = 127 - Nat.log 2 d.val := by
  unfold Aeneas.Std.core.num.U128.leading_zeros Aeneas.Std.BitVec.leadingZeros
  have h1 : d.bv ≠ 0 := by
    intro h2; apply h; simp [UScalar.val, h2]
  have h2 : Nat.log 2 d.val < 128 := Nat.log_lt_of_lt_pow h (by simpa using d.hBounds)
  simp only [h1, if_false]
  change (BitVec.ofNat 32 (128 - Nat.log 2 d.val - 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  omega

theorem pack_size128_spec (n : Std.U128) (N : Nat) (hN : 1 ≤ N) (hN8 : N ≤ 16)
    (hn : n.val < 2^(8*N)) : pack_size128 n ⦃ r => r.val ≤ N ⦄ := by
  unfold pack_size128
  simp only [core.num.U128.leading_zeros, rust_primitives.arithmetic.leading_zeros_u128]
  step*
  · have hi : i.val = n.val ||| 1 := by rw [i_post1, UScalar.val_or]; rfl
    have hi0 : i.val ≠ 0 := by rw [hi]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.right_le_or))
    have h8 : (16#u32 : Std.U32).val = 16 := rfl
    rw [h8, i2_post1, lz128_val i hi0, Nat.shiftRight_eq_div_pow]
    omega
  · have hi : i.val = n.val ||| 1 := by rw [i_post1, UScalar.val_or]; rfl
    have hi0 : i.val ≠ 0 := by rw [hi]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.right_le_or))
    have hlt : i.val < 2^(8*N) := by
      rw [hi]; apply Nat.or_lt_two_pow hn
      exact Nat.one_lt_two_pow (by omega)
    have hlog : Nat.log 2 i.val < 8 * N := Nat.log_lt_of_lt_pow hi0 hlt
    rw [UScalar.cast_val_eq, i3_post1, i2_post1, lz128_val i hi0, Nat.shiftRight_eq_div_pow]
    have : (16 - (127 - Nat.log 2 i.val) / 2^3) ≤ N := by
      simp only [Nat.reducePow]; omega
    exact Nat.le_trans (Nat.mod_le _ _) (by simpa using this)

/-! ### Little-endian bytes of a bounded value -/

theorem toNat_fromLEBytes_toLEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromLEBytes b.toLEBytes).toNat = b.toNat := by
  rw [BitVec.fromLEBytes_toLEBytes h, BitVec.toNat_cast]

theorem eq_ok_of_spec {α : Type} {e : RustM α} {v : α} (h : e ⦃ r => r = v ⦄) : e = ok v := by
  cases e with
  | ok x => simp only [WP.spec_ok] at h; rw [h]
  | fail _ => simp only [WP.spec_fail] at h
  | div => simp only [WP.spec_div] at h

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

/-- Little-endian: the trailing `W - N` bytes of a value `< 2^(8N)` are zero. -/
theorem toLEBytes_eq_take_append_zeros {w : Nat} (v : BitVec w) (N : Nat)
    (hv : v.toNat < 2^(8*N)) (hN : N ≤ (w + 7) / 8) :
    v.toLEBytes.take N ++ List.replicate ((w + 7) / 8 - N) 0#8 = v.toLEBytes := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    by_cases hi : i < N
    · rw [List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_replicate]
      rw [toLEBytes_getElem_eq_zero v N _ hv (by omega)]

/-! ### `LittleEndian::write_uint128` / `read_uint128` in closed form -/

theorem le_from_to_U128 (n : Std.U128) :
    Std.core.num.U128.from_le_bytes (Std.core.num.U128.to_le_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U128.to_le_bytes n).val = n.bv.toLEBytes := by
    simp [Std.core.num.U128.to_le_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U128.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr hl, toNat_fromLEBytes_toLEBytes (by simp)]

theorem closure128_spec (n : Std.U128) (k : Nat) (hk : k < 16) :
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

theorem to_le_bytes128_go (n : Std.U128) : ∀ m, m ≤ 16 →
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
    rw [eq_ok_of_spec (closure128_spec n m (by omega))]
    simp [List.range_succ]

theorem to_le_bytes128_eq (n : Std.U128) :
    core.num.U128.to_le_bytes n = ok (Std.core.num.U128.to_le_bytes n) := by
  unfold core.num.U128.to_le_bytes rust_primitives.slice.array_from_fn
  rw [to_le_bytes128_go n _ (by simp)]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp)]
  congr 1
  apply Subtype.ext
  simp only [Std.core.num.U128.to_le_bytes]
  rw [toLEBytes_eq_map_range]
  simp

theorem to_le_bytes_U128_zeros (n : Std.U128) (N : Nat) (hN : N ≤ 16) (hn : n.val < 2^(8*N)) :
    (Std.core.num.U128.to_le_bytes n).val.take N ++ List.replicate (16 - N) 0#u8 =
      (Std.core.num.U128.to_le_bytes n).val := by
  have h := toLEBytes_eq_take_append_zeros n.bv N (by simpa using hn) (by simpa using hN)
  simp only [Std.core.num.U128.to_le_bytes]
  simp only [show (128 + 7) / 8 = 16 by rfl] at h
  conv => rhs; rw [← h]
  simp [List.map_append, List.map_replicate, List.map_take]
  right; rfl

theorem write_uint128_le_spec (s : Slice Std.U8) (n : Std.U128) (N : Std.Usize) (hN : 1 ≤ N.val)
    (hN8 : N.val ≤ 16) (hs : N.val ≤ s.length) (hn : n.val < 2^(8*N.val)) :
    LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n N ⦃ r =>
      r.val = s.val.setSlice! 0 ((Std.core.num.U128.to_le_bytes n).val.take N.val) ⦄ := by
  unfold LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128
  have hp := pack_size128_spec n N.val hN hN8 hn
  step as ⟨i, hi⟩
  simp only [core.slice.Slice.len, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.Array.Insts.CoreOpsIndexIndex.index,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, to_le_bytes128_eq]
  have h8 : N ≤ 16#usize := by scalar_tac
  have hlen : (Std.core.num.U128.to_le_bytes n).val.length = 16 := by simp
  have hs' : N.val ≤ s.val.length := hs
  simp [massert, hi, h8, hs, Slice.len, Slice.length, Array.to_slice, hlen, hN8]
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, List.slice, hlen]; omega)]
  simp [WP.spec_ok]

theorem read_uint128_le_spec (buf : Slice Std.U8) (N : Std.Usize) (hN : 1 ≤ N.val)
    (hN8 : N.val ≤ 16) (hb : N.val ≤ buf.length) :
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 buf N ⦃ r =>
      ∃ a : Std.Array Std.U8 16#usize,
        a.val = buf.val.take N.val ++ List.replicate (16 - N.val) 0#u8 ∧
        r = Std.core.num.U128.from_le_bytes a ⦄ := by
  unfold LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128
  have h1 : 1#usize ≤ N := by scalar_tac
  have hb' : N.val ≤ buf.val.length := hb
  simp [massert, h1, core.slice.Slice.len, Slice.len, Array.to_slice, lift,
    rust_primitives.slice.slice_length, hN8, hb', Slice.length]
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndexMut,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_mut_slice, rust_primitives.slice.array_as_mut_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, Array.to_slice_mut, Array.to_slice,
    Array.from_slice, hb', Slice.length, hN8]
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, List.slice]; omega)]
  have hz : [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] = List.replicate 16 0#u8 := rfl
  have hl : (List.take N.val buf.val).length = N.val := by simp; omega
  simp only [bind_tc_ok, core.num.U128.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u128,
    WP.spec_ok, hz]
  refine ⟨_, ?_, rfl⟩
  change (List.replicate 16 0#u8).setSlice! 0 (List.take N.val buf.val) = _
  rw [setSlice!_eq_append _ _ _ (by simp; omega)]
  simp only [List.take_zero, List.nil_append, hl, Nat.zero_add, List.drop_replicate]

/--
Writing any `n < 2^72` with `LittleEndian::write_uint128(&mut buf, n, 9)` into a zeroed 16-byte buffer and reading the first 9 bytes back with `LittleEndian::read_uint128(&buf[..9], 9)` never panics and returns the same value.
-/
theorem uint128_9_little_endian_roundtrip (n : Std.U128) (h_n : n.val < 2^72) :
    uint128_9_little_endian_roundtrip_spec n := by
  unfold uint128_9_little_endian_roundtrip_spec
  step as ⟨s, back, hs, hback⟩
  have hsl : s.length = 16 := by simp [Slice.length, hs]
  have hn : n.val < 2^(8*(9#usize).val) := by simpa using h_n
  step with write_uint128_le_spec s n 9#usize (by simp) (by simp) (by simp [hsl]) hn as ⟨s1, hs1⟩
  have hl8 : (Std.core.num.U128.to_le_bytes n).val.length = 16 := by simp
  have hbuf1 : (back s1).val = s1.val := by
    rw [hback, Array.from_slice_val]; simp [hs1, hs]
  simp only [core.Array.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice,
    Array.to_slice, hbuf1]
  have hs1l : s1.val.length = 16 := by simp [hs1, hs]
  simp only [bind_tc_ok, Slice.len, Slice.length, hs1l, UScalar.le_equiv]
  simp
  apply WP.spec_mono (read_uint128_le_spec _ 9#usize (by simp) (by simp) (by simp [Slice.length]; omega))
  rintro r ⟨a, ha, rfl⟩
  have : a = Std.core.num.U128.to_le_bytes n := by
    apply Subtype.ext
    rw [ha]
    simp only [List.take_take, hs1, hs]
    have h0 := to_le_bytes_U128_zeros n 9 (by omega) (by simpa using h_n)
    conv => rhs; rw [← h0]
    congr 1
    rw [setSlice!_eq_append _ _ _ (by simp [hl8])]
    simp [hl8]
  rw [this, le_from_to_U128]

end Benchmark.Cases.ByteorderLite.Uint
