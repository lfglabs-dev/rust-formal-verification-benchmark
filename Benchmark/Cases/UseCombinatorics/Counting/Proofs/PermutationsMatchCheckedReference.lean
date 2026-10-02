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

theorem pl_spec (n k : Std.U64) (a j : Nat) (result : Std.U128) (factor : Std.U64)
    (ha : 1 ≤ a) (hn : n.val < 2^64 - 1) (hk : a + k.val = n.val + 1)
    (hf : factor.val = a + j) (hr : result.val = a.ascFactorial j) (hj : j ≤ k.val) :
    counting.permutations_loop n k result factor ⦃ r =>
      if a.ascFactorial k.val < 2^128 then
        ∃ v : Std.U128, r = core.result.Result.Ok v ∧ v.val = a.ascFactorial k.val
      else r = core.result.Result.Err (error.CombinatoricsError.PermutationOverflow n k) ⦄ := by
  unfold counting.permutations_loop
  apply loop.spec_decr_nat (measure := fun p => n.val + 1 - p.2.val)
    (inv := fun p => ∃ j, p.2.val = a + j ∧ p.1.val = a.ascFactorial j ∧ j ≤ k.val)
  · rintro ⟨res, fac⟩ ⟨j, hf, hr, hj⟩
    simp only at hf hr
    simp only [counting.permutations_loop.body]
    split
    · rename_i hle
      have hle' : fac.val ≤ n.val := hle
      simp only [lift, bind_tc_ok]
      have hcast : (UScalar.cast UScalarTy.U128 fac).val = a + j := by
        have hb := fac.hBounds
        rw [UScalar.cast_val_eq]; simp at hb ⊢; omega
      have hstep : res.val * (UScalar.cast UScalarTy.U128 fac).val = a.ascFactorial (j + 1) := by
        rw [hcast, hr, Nat.ascFactorial_succ]; ring
      by_cases hov : res.val * (UScalar.cast UScalarTy.U128 fac).val < 2^128
      · obtain ⟨v, hv, hvv⟩ := checked_mul_ok _ _ hov
        rw [hv, bind_tc_ok]
        simp only []
        have hvj : v.val = a.ascFactorial (j + 1) := by rw [hvv, hstep]
        step*
        exact ⟨⟨j + 1, by omega, hvj, by omega⟩, by omega⟩
      · rw [checked_mul_none _ _ (by omega), bind_tc_ok]
        simp only [WP.spec_ok]
        have hbig : 2^128 ≤ a.ascFactorial k.val := by
          have h2 := asc_mono a (j + 1) (k.val - (j + 1)) ha
          rw [show j + 1 + (k.val - (j + 1)) = k.val by omega] at h2
          omega
        rw [if_neg (by omega)]
        trivial
    · rename_i hgt
      have hgt' : ¬ fac.val ≤ n.val := hgt
      simp only [WP.spec_ok]
      have hjk : j = k.val := by omega
      subst hjk
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
For every `n, k` drawn from `0_u8..81`, `permutations(u64::from(n), u64::from(k))`
never panics and returns `Err(KExceedsN { n, k })` when `k > n`, otherwise
`Ok(expected)` when the checked `u128` reference `permutations_reference(n, k)`
is `Some(expected)`, and `Err(PermutationOverflow { n, k })` when it overflows.
-/
theorem permutations_match_checked_reference (n k : Std.U8)
    (h_n : n.val < 81) (h_k : k.val < 81) :
    permutations_match_checked_reference_spec n k := by
  unfold permutations_match_checked_reference_spec
  simp only [core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok]
  have hcn : (UScalar.cast UScalarTy.U64 n).val = n.val := by
    have hb := n.hBounds
    rw [UScalar.cast_val_eq]; simp at hb ⊢; omega
  have hck : (UScalar.cast UScalarTy.U64 k).val = k.val := by
    have hb := k.hBounds
    rw [UScalar.cast_val_eq]; simp at hb ⊢; omega
  unfold counting.permutations
  by_cases hkn : k.val > n.val
  · have : UScalar.cast UScalarTy.U64 k > UScalar.cast UScalarTy.U64 n := by
      show (UScalar.cast UScalarTy.U64 n).val < (UScalar.cast UScalarTy.U64 k).val
      omega
    simp only [this, if_true, bind_tc_ok, spec_ok, hkn]
  · have : ¬ UScalar.cast UScalarTy.U64 k > UScalar.cast UScalarTy.U64 n := by
      show ¬ (UScalar.cast UScalarTy.U64 n).val < (UScalar.cast UScalarTy.U64 k).val
      omega
    simp only [this, if_false, hkn]
    rw [permutations_reference, if_neg hkn]
    simp only []
    rw [show n.val + 1 - (n.val - k.val + 1) = k.val by omega,
      ref_fold _ _ (by omega)]
    split
    · rename_i h0
      have hk0 : k.val = 0 := by rw [← hck, h0]; rfl
      simp only [hk0, Nat.ascFactorial_zero]
      simp
    · rename_i h0
      have hk0 : k.val ≠ 0 := by
        intro hk; apply h0
        apply UScalar.eq_of_val_eq
        rw [hck, hk]; rfl
      step as ⟨i, hi⟩
      step as ⟨factor, hfac⟩
      apply spec_bind (pl_spec _ _ (n.val - k.val + 1) 0 1#u128 factor (by omega)
        (by omega) (by omega) (by omega) (by simp) (by omega))
      intro r hr
      rw [spec_ok]
      rw [hck] at hr
      split at hr
      · rename_i h; rw [if_pos h]; exact hr
      · rename_i h; rw [if_neg h]; exact hr

end Benchmark.Cases.UseCombinatorics.Counting
