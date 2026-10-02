import Benchmark.Cases.Tinyset.Fits64.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open tinyset

namespace Benchmark.Cases.Tinyset.Fits64

theorem sub_one_of_one : ((⟨1#64⟩ : Std.I64) - 1#i64 : RustM Std.I64) = ok ⟨0#64⟩ := by
  rfl

theorem sub_one_of_zero : ((⟨0#64⟩ : Std.I64) - 1#i64 : RustM Std.I64) = ok ⟨BitVec.allOnes 64⟩ := by
  rfl

theorem hcast_bv (x : Std.I64) : (IScalar.hcast UScalarTy.U64 x).bv = x.bv :=
  BitVec.signExtend_eq _

theorem uhcast_bv (x : Std.U64) : (UScalar.hcast IScalarTy.I64 x).bv = x.bv := by
  show BitVec.zeroExtend 64 x.bv = x.bv
  simp

theorem shl1_shr1 (b : BitVec 64) (h : b.msb = false) : (b <<< 1) >>> 1 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp
  by_cases hi' : i = 63
  · subst hi'; rw [BitVec.msb_eq_getLsbD_last] at h; simpa using h.symm
  · have : 1 + i < 64 := by omega
    simp [this]

theorem to_u64_nonneg (x : Std.I64) (hx : 0 ≤ x.val) :
    I64.Insts.TinysetSet64Fits64.to_u64 x = ok ⟨x.bv <<< 1⟩ := by
  unfold I64.Insts.TinysetSet64Fits64.to_u64
  simp only [set64.USE_BRANCHES, HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  simp [IScalar.cast_fromBool, lift]
  simp only [hx, ↓reduceIte, sub_one_of_one, bind_tc_ok, ok.injEq]
  rw [UScalar.eq_equiv_bv_eq]
  simp [hcast_bv]
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

theorem to_u64_neg (x : Std.I64) (hx : x.val < 0) :
    I64.Insts.TinysetSet64Fits64.to_u64 x = ok ⟨(~~~x.bv) <<< 1 ||| 1#64⟩ := by
  unfold I64.Insts.TinysetSet64Fits64.to_u64
  simp only [set64.USE_BRANCHES, HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  have hx' : ¬ (0 ≤ x.val) := by omega
  simp [IScalar.cast_fromBool, lift]
  simp only [hx', ↓reduceIte, sub_one_of_zero, bind_tc_ok, ok.injEq]
  rw [UScalar.eq_equiv_bv_eq]
  simp [hcast_bv]
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

theorem shl1_and1 (b : BitVec 64) : ((⟨b <<< 1⟩ : Std.U64) &&& 1#u64) = ⟨0#64⟩ := by
  rw [UScalar.eq_equiv_bv_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp
  intro _ h _; exact h

theorem from_u64_nonneg (x : Std.I64) (hx : 0 ≤ x.val) :
    I64.Insts.TinysetSet64Fits64.from_u64 ⟨x.bv <<< 1⟩ = ok x := by
  unfold I64.Insts.TinysetSet64Fits64.from_u64
  simp only [set64.USE_BRANCHES, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  simp [lift]
  rw [shl1_and1, show UScalar.hcast IScalarTy.I64 (⟨0#64⟩ : Std.U64) = ⟨0#64⟩ from rfl, sub_one_of_zero]
  simp only [bind_tc_ok, ok.injEq]
  have hm : x.bv.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp; exact hx
  rw [IScalar.eq_equiv_bv_eq]
  simp [uhcast_bv, shl1_shr1 _ hm]
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

theorem shl1_or1_and1 (b : BitVec 64) : ((⟨b <<< 1 ||| 1#64⟩ : Std.U64) &&& 1#u64) = ⟨1#64⟩ := by
  rw [UScalar.eq_equiv_bv_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp
  intro h; exact Or.inr h

theorem shl1_or1_shr1 (b : BitVec 64) (h : b.msb = false) : (b <<< 1 ||| 1#64) >>> 1 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp
  by_cases hi' : i = 63
  · subst hi'; rw [BitVec.msb_eq_getLsbD_last] at h; simpa using h.symm
  · have : 1 + i < 64 := by omega
    simp [this]

theorem from_u64_neg (x : Std.I64) (hx : x.val < 0) :
    I64.Insts.TinysetSet64Fits64.from_u64 ⟨(~~~x.bv) <<< 1 ||| 1#64⟩ = ok x := by
  unfold I64.Insts.TinysetSet64Fits64.from_u64
  simp only [set64.USE_BRANCHES, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  simp [lift]
  rw [shl1_or1_and1, show UScalar.hcast IScalarTy.I64 (⟨1#64⟩ : Std.U64) = ⟨1#64⟩ from rfl, sub_one_of_one]
  simp only [bind_tc_ok, ok.injEq]
  have hm : (~~~x.bv).msb = false := by
    rw [BitVec.msb_not, BitVec.msb_eq_toInt]; simp; exact hx
  rw [IScalar.eq_equiv_bv_eq]
  simp [uhcast_bv, shl1_or1_shr1 _ hm]
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

/--
For every `i64` value `x`, the branch-free `Fits64` encoding into a `u64`
(`x ↦ 2x` for `x ≥ 0`, `x ↦ 2·!x + 1` for `x < 0`, selected with bit masks)
never panics, `from_u64` decodes it back to `x`, and re-encoding the decoded
value reproduces the same word.
-/
theorem fits_i64_roundtrip (x : Std.I64) :
    fits_i64_roundtrip_spec x := by
  unfold fits_i64_roundtrip_spec
  by_cases hx : 0 ≤ x.val
  · simp only [to_u64_nonneg x hx, from_u64_nonneg x hx, bind_tc_ok, WP.spec_ok]
    simp
  · have hx' : x.val < 0 := by omega
    simp only [to_u64_neg x hx', from_u64_neg x hx', bind_tc_ok, WP.spec_ok]
    simp

end Benchmark.Cases.Tinyset.Fits64
