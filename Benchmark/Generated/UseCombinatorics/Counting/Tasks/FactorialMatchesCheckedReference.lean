import Benchmark.Cases.UseCombinatorics.Counting.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/--
For every `n` drawn from `0_u8..41`, `factorial(u64::from(n))` never panics and
agrees with the test's checked `u128` reference: it returns `Ok(expected)` when
`factorial_reference(n)` is `Some(expected)` and `Err(FactorialOverflow(n))`
when the reference overflows (`None`).
-/
theorem factorial_matches_checked_reference (n : Std.U8)
    (h_n : n.val < 41) :
    factorial_matches_checked_reference_spec n := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.UseCombinatorics.Counting
