import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
The 64-bit Montgomery conversion `to_monty_64` (computing in `u128`) agrees with the 32-bit
`to_monty` (computing in `u64`) on every `u32` input, for the BabyBear parameters.
-/
theorem bb_to_monty_64_extends_32 {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U32) :
    bb_to_monty_64_extends_32_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
