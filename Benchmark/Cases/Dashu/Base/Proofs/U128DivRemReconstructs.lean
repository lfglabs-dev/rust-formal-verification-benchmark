import Benchmark.Cases.Dashu.Base.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/--
For `u128` operands with a nonzero divisor, dashu's `DivRem::div_rem` never
panics, and its quotient and remainder reconstruct the dividend with checked
`u128` arithmetic (`q * b + r == a`, no overflow) with `r < b`.
-/
theorem u128_div_rem_reconstructs (a b : Std.U128)
    (h_assume_b_nonzero : b.val ≠ 0) :
    u128_div_rem_reconstructs_spec a b := by
  unfold u128_div_rem_reconstructs_spec U128.Insts.Dashu_baseRingDivRemU128U128U128.div_rem
  step as ⟨q, hq⟩
  step as ⟨r, hr⟩
  have h1 : q.val * b.val ≤ a.val := by rw [hq]; exact Nat.div_mul_le_self _ _
  have h2 : q.val * b.val + r.val = a.val := by rw [hq, hr]; exact Nat.div_add_mod' _ _
  have h3 : r.val < b.val := by rw [hr]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h_assume_b_nonzero)
  have hqb_le : q.val * b.val ≤ U128.max := by scalar_tac
  step as ⟨qb, hqb⟩
  have hrec_le : qb.val + r.val ≤ U128.max := by rw [hqb, h2]; scalar_tac
  step as ⟨recon, hrecon⟩
  exact ⟨by rw [hrecon, hqb, h2], h3⟩

end Benchmark.Cases.Dashu.Base
