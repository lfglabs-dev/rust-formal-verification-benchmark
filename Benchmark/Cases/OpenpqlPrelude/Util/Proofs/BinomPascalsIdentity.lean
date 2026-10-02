import Benchmark.Cases.OpenpqlPrelude.Util.Specs
import Mathlib.Data.Nat.Choose.Bounds

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

theorem bp_n_cards : card.card.Card.N_CARDS = ok 52#u8 := by
  unfold card.card.Card.N_CARDS
  rw [card.suit.Suit.N_SUITS.eq_1, card.rank.Rank.N_RANKS.eq_1]
  rfl

theorem bp_usize_max (h : System.Platform.numBits = 64) : Usize.max = 2^64 - 1 := by
  simp [Usize.max, Usize.numBits, h]

/-- One step of the multiplicative formula: `C(m, j) * (m + 1) = C(m + 1, j + 1) * (j + 1)`. -/
theorem bp_step (m j : Nat) : m.choose j * (m + 1) = (m + 1).choose (j + 1) * (j + 1) := by
  rw [Nat.mul_comm, Nat.add_one_mul_choose_eq]

theorem bp_loop_spec (h64 : System.Platform.numBits = 64) (n k : Std.Usize)
    (hkn : k.val ≤ n.val) (hn : n.val ≤ 52) :
    ∀ (r i : Std.Usize), 1 ≤ i.val → i.val ≤ k.val + 1 →
      r.val = (n.val - k.val + (i.val - 1)).choose (i.val - 1) →
      iterator.binomial.coefficient.binom_loop n k r i ⦃ v => v.val = n.val.choose k.val ⦄ := by
  intro r i hi1 hik hr
  unfold iterator.binomial.coefficient.binom_loop
  apply loop.spec_decr_nat (fun p : Std.Usize × Std.Usize => k.val + 1 - p.2.val)
    (fun p => 1 ≤ p.2.val ∧ p.2.val ≤ k.val + 1 ∧
      p.1.val = (n.val - k.val + (p.2.val - 1)).choose (p.2.val - 1))
  · rintro ⟨r, i⟩ ⟨hi1, hik, hr⟩
    unfold iterator.binomial.coefficient.binom_loop.body
    simp only
    split
    · rename_i hle
      have hmax := bp_usize_max h64
      simp only at hi1 hik hr
      have hle' : i.val ≤ k.val := hle
      -- r = C(M, j) with M = n - k + j, j = i - 1
      obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
      have hstep := bp_step (n.val - k.val + j) j
      have hbound : (n.val - k.val + j + 1).choose (j + 1) ≤ 2 ^ 52 := by
        calc (n.val - k.val + j + 1).choose (j + 1) ≤ 2 ^ (n.val - k.val + j + 1) :=
              Nat.choose_le_two_pow _ _
          _ ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hprod : r.val * (n.val - k.val + i.val) ≤ 2 ^ 64 - 1 := by
        rw [hr, hj, Nat.add_sub_cancel]
        have : n.val - k.val + (j + 1) = n.val - k.val + j + 1 := by omega
        rw [this, hstep]
        calc (n.val - k.val + j + 1).choose (j + 1) * (j + 1) ≤ 2 ^ 52 * 52 :=
              Nat.mul_le_mul hbound (by omega)
          _ ≤ 2 ^ 64 - 1 := by norm_num
      step*
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [r1_post, i3_post, i2_post, i1_post1, hr, i4_post, hj]
      simp only [Nat.add_sub_cancel]
      have : n.val - k.val + (j + 1) = n.val - k.val + j + 1 := by omega
      rw [this, hstep, Nat.mul_div_cancel _ (by omega)]
    · rename_i hgt
      simp only [WP.spec_ok]
      simp only at hi1 hik hr
      have hgt' : ¬ i.val ≤ k.val := hgt
      have hi : i.val = k.val + 1 := by omega
      rw [hr, hi, Nat.add_sub_cancel, Nat.sub_add_cancel hkn]
  · exact ⟨hi1, hik, hr⟩

/-- `binom n r` never panics for `n ≤ 52` (on a 64-bit target) and returns `C(n, r)`. -/
theorem bp_binom_spec (h64 : System.Platform.numBits = 64) (n r : Std.Usize) (hn : n.val ≤ 52) :
    iterator.binomial.coefficient.binom n r ⦃ v => v.val = n.val.choose r.val ⦄ := by
  unfold iterator.binomial.coefficient.binom
  rw [bp_n_cards]
  simp only [bind_tc_ok]
  step*
  · rename_i hrn
    have : n.val < r.val := hrn
    rw [Nat.choose_eq_zero_of_lt this]
    rfl
  · have hloop : ∀ k : Std.Usize, k.val ≤ n.val → n.val.choose k.val = n.val.choose r.val →
        iterator.binomial.coefficient.binom_loop n k 1#usize 1#usize ⦃
          v => v.val = n.val.choose r.val ⦄ := by
      intro k hk hc
      rw [← hc]
      exact bp_loop_spec h64 n k hk hn 1#usize 1#usize (by simp) (by simp) (by simp)
    split
    · rename_i hlt
      simp only [bind_tc_ok]
      exact hloop r i2_post2 rfl
    · rename_i hlt
      simp only [bind_tc_ok]
      apply hloop i2 (by omega)
      rw [i2_post1, Nat.choose_symm i2_post2]

/--
For every `1 ≤ r ≤ n ≤ 52`, the multiplicative binomial-coefficient routine `binom` never panics (on a 64-bit target) and satisfies Pascal's rule `binom(n, r) = binom(n - 1, r - 1) + binom(n - 1, r)`.
-/
theorem binom_pascals_identity (n r : Std.Usize)
    (h_platform : System.Platform.numBits = 64)
    (h_assume_n_pos : n.val ≠ 0) (h_assume_n_le : n.val ≤ 52)
    (h_assume_r_pos : r.val ≠ 0) (h_assume_r_le : r.val ≤ n.val) :
    binom_pascals_identity_spec n r := by
  have _hr := h_assume_r_le
  unfold binom_pascals_identity_spec
  have hmax := bp_usize_max h_platform
  have hsum : (n.val - 1).choose (r.val - 1) + (n.val - 1).choose r.val ≤ 2 ^ 64 - 1 := by
    have h1 := Nat.choose_le_two_pow (n.val - 1) (r.val - 1)
    have h2 := Nat.choose_le_two_pow (n.val - 1) r.val
    have h3 : 2 ^ (n.val - 1) ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2:Nat) ^ 52 + 2 ^ 52 ≤ 2 ^ 64 - 1 := by norm_num
    omega
  step with bp_binom_spec h_platform n r h_assume_n_le as ⟨lhs, hlhs⟩
  step as ⟨n1, hn1⟩
  step as ⟨r1, hr1⟩
  step with bp_binom_spec h_platform n1 r1 (by omega) as ⟨rhs1, hrhs1⟩
  step with bp_binom_spec h_platform n1 r (by omega) as ⟨rhs2, hrhs2⟩
  step as ⟨rhs, hrhs⟩
  apply UScalar.eq_of_val_eq
  rw [hrhs, hrhs1, hrhs2, hlhs, hn1, hr1]
  obtain ⟨m, hm⟩ : ∃ m, n.val = m + 1 := ⟨n.val - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, r.val = s + 1 := ⟨r.val - 1, by omega⟩
  rw [hm, hs, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.choose_succ_succ]

end Benchmark.Cases.OpenpqlPrelude.Util
