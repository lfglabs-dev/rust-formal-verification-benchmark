import Benchmark.Cases.SigmaSer.Zigzag.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sigma_ser

namespace Benchmark.Cases.SigmaSer.Zigzag

theorem sshift_msb (x : BitVec 64) :
    x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else 0#64 := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  split
  · have : i = 0 := by omega
    subst this
    cases h : x.msb <;> simp [BitVec.msb_eq_getLsbD_last] at h ⊢ <;> simp [h]
  · cases h : x.msb
    · simp
    · simp only [↓reduceIte, BitVec.getElem_allOnes]

theorem and_one_cases (v : BitVec 64) : v &&& 1#64 = 0#64 ∨ v &&& 1#64 = 1#64 := by
  cases h : v[0]
  · left; ext i hi; simp
    intro h1 h2; subst h2; simp_all
  · right; ext i hi; simp
    intro h2; subst h2; exact h

/-- The zigzag roundtrip identity at the bit-vector level. -/
theorem zz64 (x : BitVec 64) :
    ((x <<< 1 ^^^ x.sshiftRight 63) >>> 1) ^^^ -((x <<< 1 ^^^ x.sshiftRight 63) &&& 1#64) = x := by
  have h63 : x[63] = x.msb := by simp [BitVec.msb_eq_getLsbD_last]
  rw [sshift_msb]
  cases hm : x.msb
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    have h1 : x <<< 1 &&& 1#64 = 0#64 := by
      ext i hi; simp; omega
    rw [h1, BitVec.neg_zero, BitVec.xor_zero]
    ext i hi
    simp
    by_cases h : 1 + i < 64
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = 63 := by omega
      subst this; simp [h63, hm]
  · simp only [↓reduceIte, BitVec.xor_allOnes]
    have h1 : ~~~(x <<< 1) &&& 1#64 = 1#64 := by
      ext i hi; simp; intro h; left; exact h
    rw [h1, BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
    ext i hi
    simp
    by_cases h : 1 + i < 64
    · simp [h, BitVec.getLsbD_eq_getElem hi]
    · have : i = 63 := by omega
      subst this; simp [h63, hm]

theorem encode_i64_spec' (x : Std.I64) :
    zig_zag_encode.encode_i64 x ⦃ u => u.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 63 ⦄ := by
  unfold zig_zag_encode.encode_i64
  step*

theorem decode_u64_spec' (u : Std.U64) :
    zig_zag_encode.decode_u64 u ⦃ y => y.bv = (u.bv >>> 1) ^^^ -(u.bv &&& 1#64) ⦄ := by
  unfold zig_zag_encode.decode_u64
  step*
  case h_fail =>
    have hmin : I64.min = -(2 ^ 63 : Int) := I64.min_eq
    have h0 : u.bv &&& 1#64 = 0#64 ∨ u.bv &&& 1#64 = 1#64 := and_one_cases u.bv
    have hi2v : (IScalar.bv i2).toInt = (u.bv &&& 1#64).toInt := by
      rw [i2_post, UScalar.hcast_bv_eq, i1_post2]
      simp
    have hi2w : ↑i2 = (IScalar.bv i2).toInt := (IScalar.bv_toInt_eq (x := i2)).symm
    rcases h0 with h | h <;> rw [hi2w, hi2v, h] <;> simp [hmin]
  have hi2 : IScalar.bv i2 = u.bv &&& 1#64 := by
    rw [i2_post, UScalar.hcast_bv_eq, i1_post2]
    simp
  have hi3 : IScalar.bv i3 = -(IScalar.bv i2) := by
    apply BitVec.eq_of_toInt_eq
    rw [IScalar.bv_toInt_eq, i3_post, ← IScalar.bv_toInt_eq, hi2]
    rcases and_one_cases u.bv with h | h <;> rw [h] <;> simp
  have hi4 : UScalar.bv i4 = -(u.bv &&& 1#64) := by
    rw [i4_post, IScalar.hcast_bv_eq, hi3, hi2]
    simp
  rw [← Aeneas.Bvify.I64.IScalar_bv, UScalar.hcast_bv_eq, i5_post2, i_post2, hi4]
  simp

/--
ZigZag-encoding an `i64` and decoding the result never panics and returns the
original value (PBT `zig_zag_encode::tests::encode_i64_roundtrip`).
-/
theorem encode_i64_roundtrip (i : Std.I64) :
    encode_i64_roundtrip_spec i := by
  unfold encode_i64_roundtrip_spec
  step with encode_i64_spec' as ⟨enc, henc⟩
  step with decode_u64_spec' as ⟨dec, hdec⟩
  have hbeq : dec.bv = i.bv := by rw [hdec, henc]; exact zz64 i.bv
  rw [(IScalar.eq_equiv_bv_eq dec i).mpr hbeq]

end Benchmark.Cases.SigmaSer.Zigzag
