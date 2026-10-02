import Benchmark.Cases.Goldilocks.Field.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/--
Montgomery multiplication of reduced elements never panics and is commutative.
-/
theorem mul_commutative (a b : field.Field)
    (h_a : a.val < 2^64 - 2^32 + 1)
    (h_b : b.val < 2^64 - 2^32 + 1) :
    mul_commutative_spec a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Goldilocks.Field
