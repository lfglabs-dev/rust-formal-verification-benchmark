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

theorem zigzag_encode_i8_spec' (x : Std.I8) :
    utils.zigzag_encode_i8 x ⦃ u => u.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 7 ⦄ := by
  unfold utils.zigzag_encode_i8
  step*

theorem zigzag_decode_i8_spec' (u : Std.U8) :
    utils.zigzag_decode_i8 u ⦃ y => y.bv = (u.bv >>> 1) ^^^ -(u.bv &&& 1#8) ⦄ := by
  unfold utils.zigzag_decode_i8
  step*
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#8 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    rw [← IScalar.bv_toInt_eq, hi3]
    rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> simp <;> scalar_tac
  · have hi3 : IScalar.bv i3 = u.bv &&& 1#8 := by
      subst i3_post; simp [UScalar.hcast_bv_eq, i2_post2]
    have hi1 : IScalar.bv i1 = u.bv >>> 1 := by
      subst i1_post; simp [UScalar.hcast_bv_eq, i_post2]
    have hi4 : IScalar.bv i4 = -(u.bv &&& 1#8) := by
      apply BitVec.eq_of_toInt_eq
      rw [IScalar.bv_toInt_eq, i4_post, ← IScalar.bv_toInt_eq, hi3]
      rcases and_one_cases_w u.bv with h | h <;> rw [h] <;> decide
    simp only [IScalar.bv_xor, hi1, hi4]

/-- Zigzag decoding inverts zigzag encoding (`8`-bit). -/
theorem zigzag_roundtrip_i8 (x : Std.I8) (e : Std.U8) (y : Std.I8)
    (he : e.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 7)
    (hy : y.bv = (e.bv >>> 1) ^^^ -(e.bv &&& 1#8)) : x = y := by
  have k : (e.bv >>> 1) ^^^ -(e.bv &&& 1#8) = x.bv := by
    rw [he]; exact zz_w (by decide) x.bv
  exact (IScalar.eq_equiv_bv_eq _ _).mpr (hy.trans k).symm

theorem pack_u8_u64_spec' (a : Std.U8) (b : Std.U64) :
    packable.builtin.pack_u8_u64 a b ⦃ p => p.val = b.val * 2^8 + a.val ⦄ := by
  unfold packable.builtin.pack_u8_u64
  simp only [core.num.U8.BITS]
  step*
  have ha : a.val < 2^8 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hs : small.val = a.val := by
    rw [small_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hl : large.val = b.val := by
    rw [large_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hi : i.val = b.val * 2^8 := by
    rw [i_post1, hl]; simp only [UScalarTy.numBits]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    simp [U128.size, U128.numBits]; omega
  rw [UScalar.val_or, hs, hi, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha]

theorem unpack_u8_u64_spec' (p : Std.U128) :
    packable.builtin.unpack_u8_u64 p ⦃ r => r.1.val = p.val % 2^8 ∧ r.2.val = p.val / 2^8 % 2^64 ⦄ := by
  unfold packable.builtin.unpack_u8_u64
  simp only [core.num.U8.BITS]
  step*
  · have hi : i.val = 2^8 := by
      rw [i_post1]; simp [UScalarTy.numBits, U128.size, U128.numBits]
    have hm : small_mask.val = 2^8 - 1 := by rw [small_mask_post1, hi]
    have hs : small.val = p.val % 2^8 := by
      rw [small_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    have hl : large.val = p.val / 2^8 := by
      rw [large_post1, Nat.shiftRight_eq_div_pow]; simp [UScalarTy.numBits]
    constructor
    · rw [i1_post, UScalar.cast_val_eq, hs]; simp [UScalarTy.numBits]
    · rw [i2_post, UScalar.cast_val_eq, hl]; simp [UScalarTy.numBits]

/--
Packing an `i8` and a `u64` into a `u128` in either order (zigzag-encoding the `i8` into the low byte) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions.
-/
theorem mix_roundtrip_i8_u64 (a : Std.I8) (b : Std.U64) :
    mix_roundtrip_i8_u64_spec a b := by
  unfold mix_roundtrip_i8_u64_spec I8.Insts.VaringPackablePackableU64U128.pack
    I8.Insts.VaringPackablePackableU64U128.unpack U64.Insts.VaringPackablePackableI8U128.pack
    U64.Insts.VaringPackablePackableI8U128.unpack packable.builtin.pack_u64_i8
    packable.builtin.unpack_u64_i8 packable.builtin.pack_i8_u64 packable.builtin.unpack_i8_u64
  have hb : b.val < 2^64 := b.hBounds
  step with zigzag_encode_i8_spec' as ⟨ea, hea⟩
  have hea' : ea.val < 2^8 := ea.hBounds
  step with pack_u8_u64_spec' as ⟨p, hp⟩
  step with unpack_u8_u64_spec' as ⟨r, hr1, hr2⟩
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1 hr2
  have h1 : r1 = ea := by rw [UScalar.eq_equiv, hr1, hp]; omega
  have h2 : b = r2 := by rw [UScalar.eq_equiv, hr2, hp]; omega
  subst h1
  step with zigzag_decode_i8_spec' as ⟨da, hda⟩
  step with zigzag_encode_i8_spec' as ⟨fa, hfa⟩
  have hfa' : fa.val < 2^8 := fa.hBounds
  step with pack_u8_u64_spec' as ⟨q, hq⟩
  step with unpack_u8_u64_spec' as ⟨s, hs1, hs2⟩
  obtain ⟨s1, s2⟩ := s
  dsimp only at hs1 hs2
  have h3 : s1 = fa := by rw [UScalar.eq_equiv, hs1, hq]; omega
  have h4 : b = s2 := by rw [UScalar.eq_equiv, hs2, hq]; omega
  subst h3
  step with zigzag_decode_i8_spec' as ⟨ga, hga⟩
  step*
  exact ⟨zigzag_roundtrip_i8 a _ da hea hda, h2, zigzag_roundtrip_i8 a _ ga hfa hga, h4⟩

end Benchmark.Cases.Varing.Packable
