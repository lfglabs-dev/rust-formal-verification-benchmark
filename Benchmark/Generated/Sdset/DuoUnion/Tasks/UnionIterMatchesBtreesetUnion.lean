import Benchmark.Cases.Sdset.DuoUnion.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sdset

namespace Benchmark.Cases.Sdset.DuoUnion

/--
For any two sorted, deduplicated `i32` slices `a` and `b`, iterating
`Union { a, b }` (`into_iter`, then `next` until `None`, i.e. `collect`) never
panics and yields exactly the elements of the `BTreeSet` union of `a` and `b`,
in increasing order.
-/
theorem union_iter_matches_btreeset_union (a b : Slice Std.I32)
    (h_a : a.val.Pairwise (fun x y => x.val < y.val))
    (h_b : b.val.Pairwise (fun x y => x.val < y.val)) :
    union_iter_matches_btreeset_union_spec a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Sdset.DuoUnion
