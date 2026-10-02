import Benchmark.Cases.Varing.Packable.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

theorem sshift_msb_w {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0#w := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  split
  · have : i = 0 := by omega
    subst this
    have hl : x[w - 1] = x.msb := by simp [BitVec.msb_eq_getLsbD_last, hw]
    simp only [Nat.add_zero, hl]
    cases x.msb <;> simp
  · cases h : x.msb
    · simp
    · simp only [↓reduceIte, BitVec.getElem_allOnes]

theorem zz_w {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x <<< 1 ^^^ x.sshiftRight (w - 1)) >>> 1) ^^^ -((x <<< 1 ^^^ x.sshiftRight (w - 1)) &&& 1#w) = x := by
  have hlast : x[w - 1] = x.msb := by simp [BitVec.msb_eq_getLsbD_last, hw]
  rw [sshift_msb_w hw]
  cases hm : x.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    have h1 : x <<< 1 &&& 1#w = 0#w := by
      ext i hi; simp; omega
    rw [h1, BitVec.neg_zero, BitVec.xor_zero]
    ext i hi
    simp
    by_cases h : 1 + i < w
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = w - 1 := by omega
      subst this; simp [hlast, hm]; intro h'; omega
  · simp only [↓reduceIte, BitVec.xor_allOnes]
    have h1 : ~~~(x <<< 1) &&& 1#w = 1#w := by
      ext i hi; simp; intro h; left; exact h
    rw [h1, BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
    ext i hi
    simp
    by_cases h : 1 + i < w
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = w - 1 := by omega
      subst this; simp [hlast, hm]; left; omega

theorem and_one_cases_w {w : Nat} (v : BitVec w) : v &&& 1#w = 0#w ∨ v &&& 1#w = 1#w := by
  cases w with
  | zero => left; exact Subsingleton.elim _ _
  | succ n =>
    cases h : v[0]
    · left; ext i hi; simp
      intro h1 h2; subst h2; simp_all
    · right; ext i hi; simp
      intro h2; subst h2; exact h

theorem zigzag_encode_i16_spec' (x : Std.I16) :
    utils.zigzag_encode_i16 x ⦃ u => u.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 15 ⦄ := by
  unfold utils.zigzag_encode_i16
  step*

theorem zigzag_decode_i16_spec' (u : Std.U16) :
    utils.zigzag_decode_i16 u ⦃ y => y.bv = (u.bv >>> 1) ^^^ -(u.bv &&& 1#16) ⦄ := by
  unfold utils.zigzag_decode_i16
  step*
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#16 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    rw [← IScalar.bv_toInt_eq, hi3]
    rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> simp <;> scalar_tac
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#16 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    have hi1 : IScalar.bv i1 = u.bv >>> 1 := by
      subst i1_post; simp [UScalar.hcast_bv_eq, i_post2]
    have hi4 : IScalar.bv i4 = -(u.bv &&& 1#16) := by
      apply BitVec.eq_of_toInt_eq
      rw [IScalar.bv_toInt_eq, i4_post, ← IScalar.bv_toInt_eq, hi3]
      rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> decide
    simp only [IScalar.bv_xor, hi1, hi4]

/-- Zigzag decoding inverts zigzag encoding (`16`-bit). -/
theorem zigzag_roundtrip_i16 (x : Std.I16) (e : Std.U16) (y : Std.I16)
    (he : e.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 15)
    (hy : y.bv = (e.bv >>> 1) ^^^ -(e.bv &&& 1#16)) : x = y := by
  have k : (e.bv >>> 1) ^^^ -(e.bv &&& 1#16) = x.bv := by
    rw [he]; exact zz_w (by decide) x.bv
  exact (IScalar.eq_equiv_bv_eq _ _).mpr (hy.trans k).symm

theorem zigzag_encode_i64_spec' (x : Std.I64) :
    utils.zigzag_encode_i64 x ⦃ u => u.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 63 ⦄ := by
  unfold utils.zigzag_encode_i64
  step*

theorem zigzag_decode_i64_spec' (u : Std.U64) :
    utils.zigzag_decode_i64 u ⦃ y => y.bv = (u.bv >>> 1) ^^^ -(u.bv &&& 1#64) ⦄ := by
  unfold utils.zigzag_decode_i64
  step*
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#64 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    rw [← IScalar.bv_toInt_eq, hi3]
    rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> simp <;> scalar_tac
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#64 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    have hi1 : IScalar.bv i1 = u.bv >>> 1 := by
      subst i1_post; simp [UScalar.hcast_bv_eq, i_post2]
    have hi4 : IScalar.bv i4 = -(u.bv &&& 1#64) := by
      apply BitVec.eq_of_toInt_eq
      rw [IScalar.bv_toInt_eq, i4_post, ← IScalar.bv_toInt_eq, hi3]
      rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> decide
    simp only [IScalar.bv_xor, hi1, hi4]

/-- Zigzag decoding inverts zigzag encoding (`64`-bit). -/
theorem zigzag_roundtrip_i64 (x : Std.I64) (e : Std.U64) (y : Std.I64)
    (he : e.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 63)
    (hy : y.bv = (e.bv >>> 1) ^^^ -(e.bv &&& 1#64)) : x = y := by
  have k : (e.bv >>> 1) ^^^ -(e.bv &&& 1#64) = x.bv := by
    rw [he]; exact zz_w (by decide) x.bv
  exact (IScalar.eq_equiv_bv_eq _ _).mpr (hy.trans k).symm

theorem pack_u16_u64_spec' (a : Std.U16) (b : Std.U64) :
    packable.builtin.pack_u16_u64 a b ⦃ p => p.val = b.val * 2^16 + a.val ⦄ := by
  unfold packable.builtin.pack_u16_u64
  simp only [core.num.U16.BITS]
  step*
  have ha : a.val < 2^16 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hs : small.val = a.val := by
    rw [small_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hl : large.val = b.val := by
    rw [large_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hi : i.val = b.val * 2^16 := by
    rw [i_post1, hl]; simp only [UScalarTy.numBits]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    simp [U128.size, U128.numBits]; omega
  rw [UScalar.val_or, hs, hi, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha]

theorem unpack_u16_u64_spec' (p : Std.U128) :
    packable.builtin.unpack_u16_u64 p ⦃ r => r.1.val = p.val % 2^16 ∧ r.2.val = p.val / 2^16 % 2^64 ⦄ := by
  unfold packable.builtin.unpack_u16_u64
  simp only [core.num.U16.BITS]
  step*
  · have hi : i.val = 2^16 := by
      rw [i_post1]; simp [UScalarTy.numBits, U128.size, U128.numBits]
    have hm : small_mask.val = 2^16 - 1 := by rw [small_mask_post1, hi]
    have hs : small.val = p.val % 2^16 := by
      rw [small_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    have hl : large.val = p.val / 2^16 := by
      rw [large_post1, Nat.shiftRight_eq_div_pow]; simp [UScalarTy.numBits]
    constructor
    · rw [i1_post, UScalar.cast_val_eq, hs]; simp [UScalarTy.numBits]
    · rw [i2_post, UScalar.cast_val_eq, hl]; simp [UScalarTy.numBits]

/--
Packing an `i16` and an `i64` into a `u128` in either order (zigzag-encoding both halves) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions.
-/
theorem mix_roundtrip_i16_i64 (a : Std.I16) (b : Std.I64) :
    mix_roundtrip_i16_i64_spec a b := by
  unfold mix_roundtrip_i16_i64_spec I16.Insts.VaringPackablePackableI64U128.pack
    I16.Insts.VaringPackablePackableI64U128.unpack I64.Insts.VaringPackablePackableI16U128.pack
    I64.Insts.VaringPackablePackableI16U128.unpack packable.builtin.pack_i64_i16
    packable.builtin.unpack_i64_i16 packable.builtin.pack_i16_i64 packable.builtin.unpack_i16_i64
  step with zigzag_encode_i16_spec' as ⟨ea, hea⟩
  step with zigzag_encode_i64_spec' as ⟨eb, heb⟩
  have hea' : ea.val < 2^16 := ea.hBounds
  have heb' : eb.val < 2^64 := eb.hBounds
  step with pack_u16_u64_spec' as ⟨p, hp⟩
  step with unpack_u16_u64_spec' as ⟨r, hr1, hr2⟩
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1 hr2
  have h1 : r1 = ea := by rw [UScalar.eq_equiv, hr1, hp]; omega
  have h2 : r2 = eb := by rw [UScalar.eq_equiv, hr2, hp]; omega
  subst h1 h2
  step with zigzag_decode_i16_spec' as ⟨da, hda⟩
  step with zigzag_decode_i64_spec' as ⟨db, hdb⟩
  step with zigzag_encode_i16_spec' as ⟨fa, hfa⟩
  step with zigzag_encode_i64_spec' as ⟨fb, hfb⟩
  have hfa' : fa.val < 2^16 := fa.hBounds
  have hfb' : fb.val < 2^64 := fb.hBounds
  step with pack_u16_u64_spec' as ⟨q, hq⟩
  step with unpack_u16_u64_spec' as ⟨s, hs1, hs2⟩
  obtain ⟨s1, s2⟩ := s
  dsimp only at hs1 hs2
  have h3 : s1 = fa := by rw [UScalar.eq_equiv, hs1, hq]; omega
  have h4 : s2 = fb := by rw [UScalar.eq_equiv, hs2, hq]; omega
  subst h3 h4
  step with zigzag_decode_i16_spec' as ⟨ga, hga⟩
  step with zigzag_decode_i64_spec' as ⟨gb, hgb⟩
  step*
  exact ⟨zigzag_roundtrip_i16 a _ da hea hda, zigzag_roundtrip_i64 b _ db heb hdb,
    zigzag_roundtrip_i16 a _ ga hfa hga, zigzag_roundtrip_i64 b _ gb hfb hgb⟩

end Benchmark.Cases.Varing.Packable
