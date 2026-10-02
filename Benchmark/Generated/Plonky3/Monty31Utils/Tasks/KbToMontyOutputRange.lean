import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
For every `u32`, `to_monty` (computing `((x as u64) << 32) % P`) never panics and lands in
`[0, P)` for the KoalaBear prime.
-/
theorem kb_to_monty_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U32) :
    kb_to_monty_output_range_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
