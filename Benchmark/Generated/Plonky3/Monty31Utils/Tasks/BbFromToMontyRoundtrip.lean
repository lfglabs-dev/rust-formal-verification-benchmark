import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Decoding a canonical BabyBear Montgomery-form value (`from_monty`, i.e. Montgomery reduction) and
re-encoding it with `to_monty` never panics and gives back the original value.
-/
theorem bb_from_to_monty_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (m : Std.U32)
    (h_m : m.val < 2013265921) :
    bb_from_to_monty_roundtrip_spec inst m := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
