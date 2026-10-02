import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
On the common input range `[0, P * 2^32)` the wide-range Montgomery reduction
`large_monty_reduce` agrees with `monty_reduce` (KoalaBear), and neither panics.
-/
theorem kb_large_agrees_with_standard {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U64)
    (h_x : x.val < 2130706433 * 2^32) :
    kb_large_agrees_with_standard_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
