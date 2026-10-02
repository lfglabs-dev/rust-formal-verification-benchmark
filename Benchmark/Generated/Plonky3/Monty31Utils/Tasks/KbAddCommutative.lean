import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Modular addition `add` (checked `u32` sum followed by a conditional subtraction of `P` via
`overflowing_sub`) never panics on canonical KoalaBear inputs and is commutative.
-/
theorem kb_add_commutative {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_add_commutative_spec inst a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
