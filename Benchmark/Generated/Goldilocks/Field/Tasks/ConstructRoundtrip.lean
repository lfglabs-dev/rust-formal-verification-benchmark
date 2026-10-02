import Benchmark.Cases.Goldilocks.Field.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

/--
`Field::new(n)` (u128 `n * MONT_R1 % MODULUS`) and `Field::from(n)` (`mont_mul(reduce_64(n), MONT_R2)`)
produce the same Montgomery representative, and `u64::from` of it gives back `n`.
-/
theorem construct_roundtrip (n : Std.U64)
    (h_assume_n : n.val < 2^64 - 2^32 + 1) :
    construct_roundtrip_spec n := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Goldilocks.Field
