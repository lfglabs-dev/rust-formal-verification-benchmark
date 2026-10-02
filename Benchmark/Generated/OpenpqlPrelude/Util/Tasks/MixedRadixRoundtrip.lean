import Benchmark.Cases.OpenpqlPrelude.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/--
For block sizes in `[1, 65536]` and digits below their block sizes, building `MixedRadix::new(block_sizes)`, encoding the digits and decoding the index panics exactly when all block sizes are `65536` (the product `2^64` overflows: an upstream bug) and otherwise never panics and returns the original digits.
-/
theorem mixed_radix_roundtrip (block_sizes digits : Std.Array Std.U64 4#usize)
    (h_block_sizes : ∀ b ∈ block_sizes.val, 1 ≤ b.val ∧ b.val ≤ 65536)
    (h_digits : List.Forall₂ (fun d b => d.val < b.val) digits.val block_sizes.val) :
    mixed_radix_roundtrip_spec block_sizes digits := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.OpenpqlPrelude.Util
