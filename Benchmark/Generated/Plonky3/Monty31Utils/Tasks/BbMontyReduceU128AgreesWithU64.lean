import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
On `[0, P * 2^32)` the 128-bit reduction `monty_reduce_u128` agrees with the 64-bit
`monty_reduce` (BabyBear), and neither panics.
-/
theorem bb_monty_reduce_u128_agrees_with_u64 {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32) :
    bb_monty_reduce_u128_agrees_with_u64_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
