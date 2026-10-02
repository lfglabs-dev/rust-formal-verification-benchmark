import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
Montgomery multiplication is correct: reducing the product of the Montgomery forms of `a` and `b`
gives the Montgomery form of `a * b mod P` (KoalaBear), and nothing panics.
-/
theorem kb_monty_mul_correct {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_monty_mul_correct_spec inst a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
