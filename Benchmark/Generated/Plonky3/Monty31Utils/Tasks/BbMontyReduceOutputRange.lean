import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Montgomery reduction `monty_reduce` never panics on inputs below `P * 2^32` and returns a
canonical BabyBear value (`< P`).
-/
theorem bb_monty_reduce_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32) :
    bb_monty_reduce_output_range_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
