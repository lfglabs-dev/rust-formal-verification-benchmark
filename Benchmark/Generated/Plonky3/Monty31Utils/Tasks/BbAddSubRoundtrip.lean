import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Modular subtraction undoes modular addition: `sub(add(a, b), b) = a` for canonical BabyBear
inputs, without panicking.
-/
theorem bb_add_sub_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (a b : Std.U32)
    (h_a : a.val < 2013265921) (h_b : b.val < 2013265921) :
    bb_add_sub_roundtrip_spec inst a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
