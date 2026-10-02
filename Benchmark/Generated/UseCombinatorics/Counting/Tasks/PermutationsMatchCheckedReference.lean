import Benchmark.Cases.UseCombinatorics.Counting.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open use_combinatorics

namespace Benchmark.Cases.UseCombinatorics.Counting

/--
For every `n, k` drawn from `0_u8..81`, `permutations(u64::from(n), u64::from(k))`
never panics and returns `Err(KExceedsN { n, k })` when `k > n`, otherwise
`Ok(expected)` when the checked `u128` reference `permutations_reference(n, k)`
is `Some(expected)`, and `Err(PermutationOverflow { n, k })` when it overflows.
-/
theorem permutations_match_checked_reference (n k : Std.U8)
    (h_n : n.val < 81) (h_k : k.val < 81) :
    permutations_match_checked_reference_spec n k := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.UseCombinatorics.Counting
