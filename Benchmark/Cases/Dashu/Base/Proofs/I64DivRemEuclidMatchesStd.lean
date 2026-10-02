import Benchmark.Cases.Dashu.Base.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/-- `div_rem_euclid` never panics and returns the Euclidean quotient/remainder pair
(`r + b * q = a`, `0 ≤ r < |b|`). -/
theorem dre_core (a b : Std.I64)
    (hb0 : b.val ≠ 0)
    (hov : ¬ (a.val = -2^63 ∧ b.val = -1)) :
    I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid a b ⦃ res =>
      res.2.val + b.val * res.1.val = a.val ∧ 0 ≤ res.2.val ∧ res.2.val < |b.val| ⦄ := by
  unfold I64.Insts.Dashu_baseRingDivRemEuclidI64I64I64.div_rem_euclid
  have hid := Int.tmod_add_tdiv_mul a.val b.val
  have habs : |Int.tmod a.val b.val| < |b.val| := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_tmod]
    exact_mod_cast Nat.mod_lt _ (Int.natAbs_pos.mpr hb0)
  have hle : |Int.tmod a.val b.val| ≤ |a.val| := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_tmod]
    exact_mod_cast Nat.mod_le _ _
  have hnn : 0 ≤ a.val → 0 ≤ Int.tmod a.val b.val := fun h => Int.tmod_nonneg _ h
  have ha := a.hBounds
  have hbb := b.hBounds
  have ha' : -2^63 ≤ a.val := by scalar_tac
  have hb' : -2^63 ≤ b.val := by scalar_tac
  step as ⟨q, hq⟩
  step as ⟨r, hr⟩
  rw [← hq, ← hr] at hid
  rw [← hr] at habs hle hnn
  split
  · rename_i hr0
    simp only [WP.spec_ok]
    have : 0 ≤ r.val := by scalar_tac
    refine ⟨by linarith, this, by rw [abs_of_nonneg this] at habs; exact habs⟩
  · rename_i hr0
    have hrneg : r.val < 0 := by scalar_tac
    have ha_neg : a.val < 0 := by
      by_contra h; have := hnn (by omega); omega
    split
    · rename_i hbpos
      have hbpos' : 0 < b.val := by scalar_tac
      rw [abs_of_neg hrneg, abs_of_pos hbpos'] at habs
      have hqle : q.val ≤ 0 := by nlinarith
      have hqb : q.val * b.val ≤ q.val := by nlinarith
      have hqlo : -2^63 < q.val := by linarith
      step as ⟨q1, hq1⟩
      step as ⟨r1, hr1⟩
      rw [hq1, hr1, abs_of_pos hbpos']
      refine ⟨?_, by linarith, by linarith⟩
      rw [Int.mul_sub, Int.mul_one, Int.mul_comm b.val q.val]
      omega
    · rename_i hbneg
      have hbneg' : b.val < 0 := by scalar_tac
      rw [abs_of_neg hrneg, abs_of_neg hbneg'] at habs
      rw [abs_of_neg hrneg, abs_of_neg ha_neg] at hle
      have hb2 : b.val ≤ -2 := by omega
      have hqhi : q.val < 2^63 - 1 := by
        by_contra hcon
        have hq0 : 0 ≤ q.val := by omega
        have : q.val * b.val ≤ -2 * q.val := by nlinarith
        linarith
      step as ⟨q1, hq1⟩
      step as ⟨r1, hr1⟩
      rw [hq1, hr1, abs_of_neg hbneg']
      refine ⟨?_, by linarith, by linarith⟩
      rw [Int.mul_add, Int.mul_one, Int.mul_comm b.val q.val]
      omega

/--
For `i64` operands with a nonzero divisor (excluding `i64::MIN / -1`),
dashu's `DivRemEuclid::div_rem_euclid` never panics, its result reconstructs
the dividend with wrapping `i64` arithmetic, its remainder lies in
`[0, |b|)`, and quotient and remainder agree with the Euclidean division
`div_euclid` / `rem_euclid`.
-/
theorem i64_div_rem_euclid_matches_std (a b : Std.I64)
    (h_assume_b_nonzero : b.val ≠ 0)
    (h_assume_no_overflow : ¬ (a.val = -2^63 ∧ b.val = -1)) :
    i64_div_rem_euclid_matches_std_spec a b := by
  unfold i64_div_rem_euclid_matches_std_spec
  apply spec_bind (dre_core a b h_assume_b_nonzero h_assume_no_overflow)
  rintro ⟨q, r⟩ hpost
  simp only at hpost
  obtain ⟨hid, hr0, hrb⟩ := hpost
  simp only [core.num.I64.wrapping_mul, core.num.I64.wrapping_add,
    rust_primitives.arithmetic.wrapping_mul_i64, rust_primitives.arithmetic.wrapping_add_i64,
    bind_tc_ok]
  have ha' : -2^63 ≤ a.val ∧ a.val < 2^63 := by scalar_tac
  have hdm : Int.ediv a.val b.val = q.val ∧ Int.emod a.val b.val = r.val := by
    rcases lt_or_gt_of_ne h_assume_b_nonzero with hneg | hpos
    · rw [abs_of_neg hneg] at hrb
      exact (Int.ediv_emod_unique' hneg).mpr ⟨hid, hr0, hrb⟩
    · rw [abs_of_pos hpos] at hrb
      exact (Int.ediv_emod_unique hpos).mpr ⟨hid, hr0, hrb⟩
  refine ⟨?_, ⟨hr0, hrb⟩, hdm.1.symm, hdm.2.symm⟩
  apply IScalar.eq_of_val_eq
  rw [I64.wrapping_add_val_eq, I64.wrapping_mul_val_eq, Int.bmod_add_bmod]
  have : q.val * b.val + r.val = a.val := by rw [Int.mul_comm]; omega
  rw [this]
  apply Int.bmod_eq_of_le
  · omega
  · omega

end Benchmark.Cases.Dashu.Base
