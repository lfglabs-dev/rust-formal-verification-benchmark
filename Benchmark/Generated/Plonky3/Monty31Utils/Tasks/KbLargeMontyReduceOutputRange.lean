import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
`large_monty_reduce` never panics on inputs below `2 * P * 2^32` and returns a canonical
KoalaBear value (`< P`).
-/
theorem kb_large_monty_reduce_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U64)
    (h_x : x.val < 2130706433 * 2^32 * 2) :
    kb_large_monty_reduce_output_range_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
