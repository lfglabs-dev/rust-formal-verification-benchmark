import Benchmark.Cases.Dashu.Base.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/--
For `i64` operands with a nonzero divisor (excluding `i64::MIN / -1`),
dashu's truncating `DivRem::div_rem` never panics, reconstructs the dividend
(`q * b + r == a`) and returns a remainder smaller than the divisor in
absolute value.
-/
theorem i64_div_rem_reconstructs (a b : Std.I64)
    (h_assume_b_nonzero : b.val ≠ 0)
    (h_assume_no_overflow : ¬ (a.val = -2^63 ∧ b.val = -1)) :
    i64_div_rem_reconstructs_spec a b := by
  unfold i64_div_rem_reconstructs_spec I64.Insts.Dashu_baseRingDivRemI64I64I64.div_rem
  step as ⟨q, hq⟩
  step as ⟨r, hr⟩
  constructor
  · rw [hq, hr]
    have := Int.tmod_add_tdiv_mul a.val b.val
    omega
  · rw [hr, Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.natAbs_tmod]
    have hb : 0 < b.val.natAbs := Int.natAbs_pos.mpr h_assume_b_nonzero
    exact_mod_cast Nat.mod_lt _ hb

end Benchmark.Cases.Dashu.Base
