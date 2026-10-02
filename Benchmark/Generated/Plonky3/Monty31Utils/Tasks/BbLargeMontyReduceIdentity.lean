import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
`large_monty_reduce(x) * 2^32 ≡ x (mod P)` on its whole domain `[0, 2 * P * 2^32)` (BabyBear),
without panicking.
-/
theorem bb_large_monty_reduce_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32 * 2) :
    bb_large_monty_reduce_identity_spec inst x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
