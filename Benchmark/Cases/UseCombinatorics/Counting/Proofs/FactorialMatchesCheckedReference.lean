import Benchmark.Cases.UseCombinatorics.Counting.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

theorem checked_mul_ok (x y : Std.U128) (h : x.val * y.val < 2^128) :
    ∃ v : Std.U128, core.num.U128.checked_mul x y = ok (core.option.Option.Some v) ∧ v.val = x.val * y.val := by
  simp only [core.num.U128.checked_mul, core.num.U128.overflowing_mul,
    rust_primitives.arithmetic.overflowing_mul_u128, uoverflowing_mul]
  have h' : ¬ (340282366920938463463374607431768211456 ≤ x.val * y.val) := by
    norm_num at h; omega
  simp [h']
  change (x.bv * y.bv).toNat = x.val * y.val
  rw [BitVec.toNat_mul]
  change x.val * y.val % 2^128 = _
  exact Nat.mod_eq_of_lt h

theorem checked_mul_none (x y : Std.U128) (h : 2^128 ≤ x.val * y.val) :
    core.num.U128.checked_mul x y = ok core.option.Option.None := by
  simp only [core.num.U128.checked_mul, core.num.U128.overflowing_mul,
    rust_primitives.arithmetic.overflowing_mul_u128, uoverflowing_mul]
  simpa using h

theorem asc_mono (a j m : Nat) (ha : 1 ≤ a) : a.ascFactorial j ≤ a.ascFactorial (j + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, Nat.ascFactorial_succ]
    calc a.ascFactorial j ≤ a.ascFactorial (j + m) := ih
      _ ≤ (a + (j + m)) * a.ascFactorial (j + m) := Nat.le_mul_of_pos_left _ (by omega)

theorem fl_spec (n : Std.U64) (j : Nat) (result : Std.U128) (factor : Std.U64)
    (hf : factor.val = j + 2) (hr : result.val = Nat.ascFactorial 2 j) (hj : j + 1 ≤ max n.val 1) :
    counting.factorial_loop n result factor ⦃ r =>
      if Nat.ascFactorial 2 (n.val - 1) < 2^128 then
        ∃ v : Std.U128, r = core.result.Result.Ok v ∧ v.val = Nat.ascFactorial 2 (n.val - 1)
      else r = core.result.Result.Err (error.CombinatoricsError.FactorialOverflow n) ⦄ := by
  unfold counting.factorial_loop
  apply loop.spec_decr_nat (measure := fun p => n.val + 2 - p.2.val)
    (inv := fun p => ∃ j, p.2.val = j + 2 ∧ p.1.val = Nat.ascFactorial 2 j ∧ j + 1 ≤ max n.val 1)
  · rintro ⟨res, fac⟩ ⟨j, hf, hr, hj⟩
    simp only at hf hr
    simp only [counting.factorial_loop.body]
    split
    · rename_i hle
      have hle' : fac.val ≤ n.val := hle
      simp only [lift, bind_tc_ok]
      have hcast : (UScalar.cast UScalarTy.U128 fac).val = j + 2 := by
        have hb := fac.hBounds
        rw [UScalar.cast_val_eq]; simp at hb ⊢; omega
      by_cases hov : res.val * (UScalar.cast UScalarTy.U128 fac).val < 2^128
      · obtain ⟨v, hv, hvv⟩ := checked_mul_ok _ _ hov
        rw [hv, bind_tc_ok]
        simp only []
        have hvj : v.val = Nat.ascFactorial 2 (j + 1) := by
          rw [hvv, hcast, hr, Nat.ascFactorial_succ]; ring
        have hpow : 2^(j+1) ≤ Nat.ascFactorial 2 (j + 1) := Nat.pow_succ_le_ascFactorial 2 (j+1)
        have hj128 : j + 1 < 128 := by
          have : 2^(j+1) < 2^128 := by
            have := v.hBounds
            simp at this
            omega
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
        step*
        exact ⟨⟨j + 1, by omega, hvj, le_max_of_le_left (by omega)⟩, by omega⟩
      · rw [checked_mul_none _ _ (by omega), bind_tc_ok]
        simp only [WP.spec_ok]
        have hbig : 2^128 ≤ Nat.ascFactorial 2 (n.val - 1) := by
          have h1 : res.val * (UScalar.cast UScalarTy.U128 fac).val = Nat.ascFactorial 2 (j + 1) := by
            rw [hcast, hr, Nat.ascFactorial_succ]; ring
          have h2 := asc_mono 2 (j + 1) (n.val - 1 - (j + 1)) (by norm_num)
          rw [show j + 1 + (n.val - 1 - (j + 1)) = n.val - 1 by omega] at h2
          omega
        rw [if_neg (by omega)]
        trivial
    · rename_i hgt
      have hgt' : ¬ fac.val ≤ n.val := hgt
      simp only [WP.spec_ok]
      have hjn : j = n.val - 1 := by
        rcases le_total n.val 1 with h | h
        · rw [max_eq_right h] at hj; omega
        · rw [max_eq_left h] at hj; omega
      subst hjn
      split
      · exact ⟨res, rfl, hr⟩
      · rename_i h; exact absurd (hr ▸ res.hBounds) (by simpa using h)
  · exact ⟨j, hf, hr, hj⟩

theorem ref_fold (a j : Nat) (ha : 1 ≤ a) :
    (List.range' a j).foldlM checkedMulU128 1 =
      if a.ascFactorial j < 2^128 then some (a.ascFactorial j) else none := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range'_concat, List.foldlM_append, ih]
    by_cases h : a.ascFactorial j < 2^128
    · rw [if_pos h]
      simp only [List.foldlM_cons, List.foldlM_nil, checkedMulU128]
      rw [Nat.ascFactorial_succ, one_mul, Nat.mul_comm (a + j)]
      simp
    · rw [if_neg h]
      have : ¬ a.ascFactorial (j + 1) < 2^128 := by
        have := asc_mono a j 1 ha
        omega
      rw [if_neg this]
      rfl

/--
For every `n` drawn from `0_u8..41`, `factorial(u64::from(n))` never panics and
agrees with the test's checked `u128` reference: it returns `Ok(expected)` when
`factorial_reference(n)` is `Some(expected)` and `Err(FactorialOverflow(n))`
when the reference overflows (`None`).
-/
theorem factorial_matches_checked_reference (n : Std.U8)
    (h_n : n.val < 41) :
    factorial_matches_checked_reference_spec n := by
  unfold factorial_matches_checked_reference_spec
  simp only [core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok, counting.factorial]
  have hc : (UScalar.cast UScalarTy.U64 n).val = n.val := by
    have hb := n.hBounds
    rw [UScalar.cast_val_eq]; simp at hb ⊢; omega
  apply spec_bind (fl_spec _ 0 1#u128 2#u64 (by simp) (by simp) (le_max_right _ _))
  intro r hr
  rw [spec_ok]
  simp only []
  rw [factorial_reference, ref_fold 2 _ (by norm_num), show n.val + 1 - 2 = n.val - 1 by omega]
  rw [hc] at hr
  split at hr
  · rename_i h; rw [if_pos h]; exact hr
  · rename_i h; rw [if_neg h]; exact hr

end Benchmark.Cases.UseCombinatorics.Counting
