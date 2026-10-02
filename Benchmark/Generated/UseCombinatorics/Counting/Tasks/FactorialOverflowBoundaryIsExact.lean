import Benchmark.Cases.UseCombinatorics.Counting.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/--
For every `n` drawn from `0_u8..80`, `factorial(u64::from(n))` never panics; it
succeeds (`is_ok()`) exactly for `n ≤ 34` and returns
`Err(FactorialOverflow(n))` for `35 ≤ n < 80`.
-/
theorem factorial_overflow_boundary_is_exact (n : Std.U8)
    (h_n : n.val < 80) :
    factorial_overflow_boundary_is_exact_spec n := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.UseCombinatorics.Counting
