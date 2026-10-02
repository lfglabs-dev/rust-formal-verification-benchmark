import Benchmark.Cases.IndexedBitvec.Word.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

theorem slow_u64_spec (n d : Std.U64) (hd : 0 < d.val) :
    ceil_div_u64_slow n d ⦃ r => r.val = n.val / d.val + (if n.val % d.val > 0 then 1 else 0) ⦄ := by
  unfold ceil_div_u64_slow
  step*
  by_cases h : n.val % d.val > 0
  · have h1 : i1 > 0#u64 := by scalar_tac
    simp only [h1, ↓reduceIte, h, bind_tc_ok]
    have hd2 : 2 ≤ d.val := by
      rcases Nat.lt_or_ge d.val 2 with h2 | h2
      · have : d.val = 1 := by omega
        rw [this, Nat.mod_one] at h; omega
      · exact h2
    have hn : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with h0 | h0
      · rw [h0, Nat.zero_mod] at h; omega
      · exact h0
    have : n.val / d.val < n.val := Nat.div_lt_self hn (by omega)
    step*
  · have h1 : ¬ (i1 > 0#u64) := by scalar_tac
    simp only [h1, ↓reduceIte, h, bind_tc_ok]
    step*

theorem ceil_nat_u64 (n d : Nat) (hd : 0 < d) :
    (n + (d - 1)) / d = n / d + (if n % d > 0 then 1 else 0) := by
  have hr := Nat.mod_lt n hd
  have e : n + (d - 1) = (n % d + (d - 1)) + d * (n / d) := by
    have := Nat.div_add_mod n d
    omega
  rw [e, Nat.add_mul_div_left _ _ hd]
  split
  · have : (n % d + (d - 1)) / d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  · have : (n % d + (d - 1)) / d = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem fast_u64_spec (n d : Std.U64) (hd : 0 < d.val) :
    ceil_div_u64 n d ⦃ r => r.val = n.val / d.val + (if n.val % d.val > 0 then 1 else 0) ⦄ := by
  unfold ceil_div_u64
  step*
  simp only [CoreModels.core.num.U64.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u64, bind_tc_ok]
  have hw := U64.wrapping_add_val_eq n i
  generalize U64.wrapping_add n i = nb at hw ⊢
  split
  · exact slow_u64_spec n d hd
  · rename_i hlt
    have hlt' : n.val ≤ nb.val := by scalar_tac
    have hn : n.val < U64.size := by scalar_tac
    have hi : i.val < U64.size := by scalar_tac
    simp only [UScalar.size_UScalarTyU64] at hw
    have hsize : n.val + i.val < U64.size := by
      by_contra hc
      have h1 : nb.val = n.val + i.val - U64.size := by
        rw [hw, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hnb : nb.val = n.val + (d.val - 1) := by
      rw [hw, Nat.mod_eq_of_lt hsize, i_post1]
    step*
    rw [r_post, hnb]
    exact ceil_nat_u64 _ _ hd

/--
For every `u64` dividend `x` and divisor `d` in `1..999999`, the wrapping
fast path `ceil_div_u64(x, d)` never panics and returns the same value as the
reference `ceil_div_u64_slow(x, d) = x / d + (x % d > 0)`.
-/
theorem ceil_div_u64_matches_slow (x d : Std.U64)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 999999) :
    ceil_div_u64_matches_slow_spec x d := by
  unfold ceil_div_u64_matches_slow_spec
  step with slow_u64_spec as ⟨a, ha⟩
  step with fast_u64_spec as ⟨b, hb⟩
  exact UScalar.eq_of_val_eq (by rw [ha, hb])

end Benchmark.Cases.IndexedBitvec.Word
