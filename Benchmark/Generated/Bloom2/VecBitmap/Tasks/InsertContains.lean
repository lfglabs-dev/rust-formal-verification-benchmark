import Benchmark.Cases.Bloom2.VecBitmap.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open bloom2

namespace Benchmark.Cases.Bloom2.VecBitmap

/--
Setting the bits of a set of fewer than 20 distinct keys below 1028 in a fresh
`VecBitmap::new_with_capacity(1028)` never panics, and afterwards `get(i)`
answers exactly the membership of `i` in the set, for every `i < 1028`.
-/
theorem insert_contains (values : List Std.Usize)
    (h_nodup : values.Nodup)
    (h_len : values.length < 20)
    (h_range : ∀ v ∈ values, v.val < 1028)
    (h_platform : System.Platform.numBits = 64) :
    insert_contains_spec values := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Bloom2.VecBitmap
