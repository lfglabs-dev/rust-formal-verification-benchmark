import Benchmark.Cases.SigmaSer.Zigzag.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sigma_ser

namespace Benchmark.Cases.SigmaSer.Zigzag

theorem sshift_msb32 (x : BitVec 32) :
    x.sshiftRight 31 = if x.msb then BitVec.allOnes 32 else 0#32 := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  split
  · have : i = 0 := by omega
    subst this
    cases h : x.msb <;> simp [BitVec.msb_eq_getLsbD_last] at h ⊢ <;> simp [h]
  · cases h : x.msb
    · simp
    · simp only [↓reduceIte, BitVec.getElem_allOnes]

theorem and_one_cases32 (v : BitVec 32) : v &&& 1#32 = 0#32 ∨ v &&& 1#32 = 1#32 := by
  cases h : v[0]
  · left; ext i hi; simp
    intro h1 h2; subst h2; simp_all
  · right; ext i hi; simp
    intro h2; subst h2; exact h

/-- Truncating a zero/sign-extended 32-bit value back to 32 bits is the identity. -/
theorem setWidth_signExtend64 (z : BitVec 32) : (z.signExtend 64).setWidth 32 = z := by
  ext i hi
  rw [BitVec.getElem_setWidth _ _ _ hi, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 from by omega]

/-- The zigzag roundtrip identity at the bit-vector level (32-bit variant). -/
theorem zz32 (x : BitVec 32) :
    ((x <<< 1 ^^^ x.sshiftRight 31) >>> 1) ^^^ -((x <<< 1 ^^^ x.sshiftRight 31) &&& 1#32) = x := by
  have h31 : x[31] = x.msb := by simp [BitVec.msb_eq_getLsbD_last]
  rw [sshift_msb32]
  cases hm : x.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    have h1 : x <<< 1 &&& 1#32 = 0#32 := by
      ext i hi; simp; omega
    rw [h1, BitVec.neg_zero, BitVec.xor_zero]
    ext i hi
    simp
    by_cases h : 1 + i < 32
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = 31 := by omega
      subst this; simp [h31, hm]
  · simp only [↓reduceIte, BitVec.xor_allOnes]
    have h1 : ~~~(x <<< 1) &&& 1#32 = 1#32 := by
      ext i hi; simp; intro h; left; exact h
    rw [h1, BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
    ext i hi
    simp
    by_cases h : 1 + i < 32
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = 31 := by omega
      subst this; simp [h31, hm]

theorem encode_i32_spec' (x : Std.I32) :
    zig_zag_encode.encode_i32 x ⦃ u =>
      u.bv = ((x.bv <<< 1) ^^^ x.bv.sshiftRight 31).signExtend 64 ⦄ := by
  unfold zig_zag_encode.encode_i32
  step*

theorem decode_u32_spec' (u : Std.U64) :
    zig_zag_encode.decode_u32 u ⦃ y =>
      y.bv = (u.bv.setWidth 32 >>> 1) ^^^ -(u.bv.setWidth 32 &&& 1#32) ⦄ := by
  unfold zig_zag_encode.decode_u32
  step*
  case h_fail =>
    have hmin : I32.min = -(2 ^ 31 : Int) := I32.min_eq
    have h0 : IScalar.bv i3 &&& 1#32 = 0#32 ∨ IScalar.bv i3 &&& 1#32 = 1#32 :=
      and_one_cases32 (IScalar.bv i3)
    have hi4v : (IScalar.bv i4).toInt = (IScalar.bv i3 &&& 1#32).toInt := by
      rw [i4_post2]
      simp
    have hi4w : ↑i4 = (IScalar.bv i4).toInt := (IScalar.bv_toInt_eq (x := i4)).symm
    rcases h0 with h | h <;> rw [hi4w, hi4v] <;> simp [h, hmin]
  have hi : UScalar.bv i = u.bv.setWidth 32 := by
    rw [i_post, UScalar.cast_bv_eq]
    simp
  have hi1 : UScalar.bv i1 = u.bv.setWidth 32 >>> 1 := by
    rw [i1_post2]
    simp [hi]
  have hi2 : IScalar.bv i2 = u.bv.setWidth 32 >>> 1 := by
    rw [i2_post, UScalar.hcast_bv_eq, hi1]
    simp
  have hi3 : IScalar.bv i3 = u.bv.setWidth 32 := by
    rw [i3_post, UScalar.hcast_bv_eq]
    simp
  have hi4 : IScalar.bv i4 = u.bv.setWidth 32 &&& 1#32 := by
    rw [i4_post2]
    simp [hi3]
  have hi5 : IScalar.bv i5 = -(u.bv.setWidth 32 &&& 1#32) := by
    apply BitVec.eq_of_toInt_eq
    rw [IScalar.bv_toInt_eq, i5_post, ← IScalar.bv_toInt_eq, hi4]
    rcases and_one_cases32 (u.bv.setWidth 32) with h | h <;> rw [h] <;> simp
  simp only [IScalar.bv_xor, hi2, hi5]

/--
ZigZag-encoding an `i32` and decoding the result never panics and returns the
original value (PBT `zig_zag_encode::tests::encode_i32_roundtrip`).
-/
theorem encode_i32_roundtrip (i : Std.I32) :
    encode_i32_roundtrip_spec i := by
  unfold encode_i32_roundtrip_spec
  step with encode_i32_spec' as ⟨enc, henc⟩
  step with decode_u32_spec' as ⟨dec, hdec⟩
  have hw : enc.bv.setWidth 32 = i.bv <<< 1 ^^^ i.bv.sshiftRight 31 := by
    rw [henc, setWidth_signExtend64]
  have hbeq : dec.bv = i.bv := by rw [hdec, hw]; exact zz32 i.bv
  rw [(IScalar.eq_equiv_bv_eq dec i).mpr hbeq]

end Benchmark.Cases.SigmaSer.Zigzag
