import Benchmark.Cases.Blue.ScrunchBinarySearch.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open scrunch

namespace Benchmark.Cases.Blue.ScrunchBinarySearch

/--
For a strictly increasing `usize` vector `elements` and any position `i`,
`binary_search_by(0, elements.len() - 1, |x| elements[x].cmp(&elements[i]))`
never panics and returns `i`, which is also the partition point of
`|x| *x < elements[i]`.
-/
theorem binary_search_finds_index (elements : Slice Std.Usize)
    (h_len : elements.length < 64)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize)
    (h_i : i.val < elements.length) :
    binary_search_finds_index_spec elements i := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Blue.ScrunchBinarySearch
