import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Converting a canonical KoalaBear element into Montgomery form and back (`from_monty` = Montgomery
reduction `monty_reduce`) never panics and returns the element itself.
-/
theorem kb_to_from_monty_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U32)
    (h_x : x.val < 2130706433) :
    kb_to_from_monty_roundtrip_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
