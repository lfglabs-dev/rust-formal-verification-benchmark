import Benchmark.Cases.OpenpqlPrelude.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/--
On every nonempty slice of `u64` values in `[1, 65535]` whose total product fits in a `u64`, the in-place `suffix_product` never panics and replaces entry `i` by the product of the entries after position `i`.
-/
theorem suffix_product_matches_reference (xs : Slice Std.U64)
    (h_nonempty : xs.val ≠ [])
    (h_elems : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 65535)
    (h_prod : (xs.val.map (·.val)).prod ≤ 2^64 - 1) :
    suffix_product_spec xs := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.OpenpqlPrelude.Util
