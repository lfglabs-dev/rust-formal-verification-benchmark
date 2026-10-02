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

/-! ### `pack_size`: the writer's `assert!(pack_size(n) <= nbytes)` holds for `n < 2^(8 nbytes)` -/

theorem lz64_val (d : Std.U64) (h : d.val ≠ 0) :
    (Aeneas.Std.core.num.U64.leading_zeros d).val = 63 - Nat.log 2 d.val := by
  unfold Aeneas.Std.core.num.U64.leading_zeros Aeneas.Std.BitVec.leadingZeros
  have h1 : d.bv ≠ 0 := by
    intro h2; apply h; simp [UScalar.val, h2]
  have h2 : Nat.log 2 d.val < 64 := Nat.log_lt_of_lt_pow h (by simpa using d.hBounds)
  simp only [h1, if_false]
  change (BitVec.ofNat 32 (64 - Nat.log 2 d.val - 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  omega

theorem pack_size_spec (n : Std.U64) (N : Nat) (hN : 1 ≤ N) (hN8 : N ≤ 8)
    (hn : n.val < 2^(8*N)) : pack_size n ⦃ r => r.val ≤ N ⦄ := by
  unfold pack_size
  simp only [core.num.U64.leading_zeros, rust_primitives.arithmetic.leading_zeros_u64]
  step*
  · have hi : i.val = n.val ||| 1 := by rw [i_post1, UScalar.val_or]; rfl
    have hi0 : i.val ≠ 0 := by rw [hi]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.right_le_or))
    have h8 : (8#u32 : Std.U32).val = 8 := rfl
    rw [h8, i2_post1, lz64_val i hi0, Nat.shiftRight_eq_div_pow]
    omega
  · have hi : i.val = n.val ||| 1 := by rw [i_post1, UScalar.val_or]; rfl
    have hi0 : i.val ≠ 0 := by rw [hi]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.right_le_or))
    have hlt : i.val < 2^(8*N) := by
      rw [hi]; apply Nat.or_lt_two_pow hn
      exact Nat.one_lt_two_pow (by omega)
    have hlog : Nat.log 2 i.val < 8 * N := Nat.log_lt_of_lt_pow hi0 hlt
    rw [UScalar.cast_val_eq, i3_post1, i2_post1, lz64_val i hi0, Nat.shiftRight_eq_div_pow]
    have : (8 - (63 - Nat.log 2 i.val) / 2^3) ≤ N := by
      simp only [Nat.reducePow]; omega
    exact Nat.le_trans (Nat.mod_le _ _) (by simpa using this)

/-! ### Big-endian bytes of a bounded value -/

/-- Big-endian: the leading `W - N` bytes of a value `< 2^(8N)` are zero. -/
theorem toBEBytes_eq_zeros_append {w : Nat} (v : BitVec w) (N : Nat)
    (hv : v.toNat < 2^(8*N)) (hN : N ≤ (w + 7) / 8) :
    List.replicate ((w + 7) / 8 - N) 0#8 ++ v.toBEBytes.drop ((w + 7) / 8 - N) = v.toBEBytes := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hi : i < (w + 7) / 8 - N
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_replicate, BitVec.toBEBytes, List.getElem_reverse]
      rw [toLEBytes_getElem_eq_zero v N _ hv (by simp; omega)]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_replicate, List.getElem_drop]
      congr 1; omega


theorem toNat_fromBEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat := by
  subst h; rfl

theorem toNat_fromBEBytes_toBEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  simp only [BitVec.fromBEBytes, BitVec.toBEBytes, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr (List.reverse_reverse _), BitVec.fromLEBytes_toLEBytes h,
    BitVec.toNat_cast]

/-! ### `BigEndian::write_uint` / `read_uint` in closed form -/

theorem write_uint_be_spec (s : Slice Std.U8) (n : Std.U64) (N : Std.Usize) (hN : 1 ≤ N.val)
    (hN8 : N.val ≤ 8) (hs : N.val ≤ s.length) (hn : n.val < 2^(8*N.val)) :
    BigEndian.Insts.Byteorder_liteByteOrder.write_uint s n N ⦃ r =>
      r.val = s.val.setSlice! 0 ((Std.core.num.U64.to_be_bytes n).val.drop (8 - N.val)) ⦄ := by
  unfold BigEndian.Insts.Byteorder_liteByteOrder.write_uint
  have hp := pack_size_spec n N.val hN hN8 hn
  step as ⟨i, hi⟩
  simp only [core.slice.Slice.len, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.Array.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex,
    core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut, Slice.subslice,
    core.num.U64.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u64]
  have h8 : N ≤ 8#usize := by scalar_tac
  have hlen : (Std.core.num.U64.to_be_bytes n).val.length = 8 := by simp
  have hsub : (8#usize - N) ⦃ r => r.val = 8 - N.val ⦄ := by step*
  simp [massert, hi, h8, hs, Slice.len, Slice.length]
  step as ⟨i2, hi2⟩
  have hc : (8 - N.val) ≤ 8 := by omega
  simp only [hi2, hc, if_true, bind_tc_ok]
  have hs' : N.val ≤ s.val.length := hs
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, List.slice, hlen]; omega)]
  have ht : List.take (8 - (8 - N.val)) (List.drop (8 - N.val) (Std.core.num.U64.to_be_bytes n).val) =
      List.drop (8 - N.val) (Std.core.num.U64.to_be_bytes n).val := by
    apply List.take_of_length_le; simp [hlen]
  simp only [bind_tc_ok, WP.spec_ok, List.slice, hlen, ht]

theorem read_uint_be_spec (buf : Slice Std.U8) (N : Std.Usize) (hN : 1 ≤ N.val)
    (hN8 : N.val ≤ 8) (hb : N.val ≤ buf.length) :
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint buf N ⦃ r =>
      ∃ a : Std.Array Std.U8 8#usize,
        a.val = List.replicate (8 - N.val) 0#u8 ++ buf.val.take N.val ∧
        r = Std.core.num.U64.from_be_bytes a ⦄ := by
  unfold BigEndian.Insts.Byteorder_liteByteOrder.read_uint
  have h1 : 1#usize ≤ N := by scalar_tac
  have hb' : N.val ≤ buf.val.length := hb
  simp [massert, h1, core.slice.Slice.len, Slice.len, Array.to_slice, lift,
    rust_primitives.slice.slice_length, hN8, hb', Slice.length]
  step as ⟨start, hstart⟩
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndexMut,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    core.array.Array.as_mut_slice, rust_primitives.slice.array_as_mut_slice,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, Array.to_slice_mut, Array.to_slice,
    Array.from_slice, hstart, hb', Slice.length]
  rw [copy_from_slice_u8 _ _ (by simp [Slice.length, List.slice]; omega)]
  have hz : [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] = List.replicate 8 0#u8 := rfl
  have hl : (List.take N.val buf.val).length = N.val := by simp; omega
  simp only [bind_tc_ok, core.num.U64.from_be_bytes, rust_primitives.arithmetic.from_be_bytes_u64,
    WP.spec_ok, hz]
  refine ⟨_, ?_, rfl⟩
  have := replicate_setSlice! 0#u8 (List.take N.val buf.val) 8 (by omega)
  rw [hl] at this
  exact this

theorem be_from_to_U64 (n : Std.U64) :
    Std.core.num.U64.from_be_bytes (Std.core.num.U64.to_be_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U64.to_be_bytes n).val = n.bv.toBEBytes := by
    simp [Std.core.num.U64.to_be_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U64.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromBEBytes_congr hl, toNat_fromBEBytes_toBEBytes (by simp)]

/-- `to_be_bytes n` of a `u64` below `2^(8N)` starts with `8 - N` zero bytes. -/
theorem to_be_bytes_U64_zeros (n : Std.U64) (N : Nat) (hN : N ≤ 8) (hn : n.val < 2^(8*N)) :
    List.replicate (8 - N) 0#u8 ++ (Std.core.num.U64.to_be_bytes n).val.drop (8 - N) =
      (Std.core.num.U64.to_be_bytes n).val := by
  have h := toBEBytes_eq_zeros_append n.bv N (by simpa using hn) (by simpa using hN)
  simp only [Std.core.num.U64.to_be_bytes]
  simp only [show (64 + 7) / 8 = 8 by rfl] at h
  conv => rhs; rw [← h]
  simp [List.map_append, List.map_replicate, List.map_drop]
  right; rfl

/--
Writing any `n < 2^24` with `BigEndian::write_uint(&mut buf, n, 3)` into a zeroed 16-byte buffer and reading the first 3 bytes back with `BigEndian::read_uint(&buf[..3], 3)` never panics and returns the same value.
-/
theorem uint_3_big_endian_roundtrip (n : Std.U64) (h_n : n.val < 2^24) :
    uint_3_big_endian_roundtrip_spec n := by
  unfold uint_3_big_endian_roundtrip_spec
  step as ⟨s, back, hs, hback⟩
  have hsl : s.length = 16 := by simp [Slice.length, hs]
  have hn : n.val < 2^(8*(3#usize).val) := by simpa using h_n
  step with write_uint_be_spec s n 3#usize (by simp) (by simp) (by simp [hsl]) hn as ⟨s1, hs1⟩
  have hl8 : (Std.core.num.U64.to_be_bytes n).val.length = 8 := by simp
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
  apply WP.spec_mono (read_uint_be_spec _ 3#usize (by simp) (by simp) (by simp [Slice.length]; omega))
  rintro r ⟨a, ha, rfl⟩
  have : a = Std.core.num.U64.to_be_bytes n := by
    apply Subtype.ext
    rw [ha]
    simp only [List.take_take, hs1, hs]
    have h0 := to_be_bytes_U64_zeros n 3 (by omega) (by simpa using h_n)
    conv => rhs; rw [← h0]
    congr 1
    rw [setSlice!_eq_append _ _ _ (by simp [hl8])]
    simp [hl8]
  rw [this, be_from_to_U64]

end Benchmark.Cases.ByteorderLite.Uint
