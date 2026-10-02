import Benchmark.Cases.Partition.SlicePartition.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open partition

namespace Benchmark.Cases.Partition.SlicePartition

/--
Partitioning any `u32` slice in place with the predicate "is even" never
panics and returns an index `first_false ≤ len` such that the prefix
`data[..first_false]` of the rearranged slice holds exactly the even
elements of the original slice and the suffix `data[first_false..]` exactly
the odd ones (compared as sorted vectors, as the property test does).
-/
theorem partition_index_separates_even_odd {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data : Slice Std.U32) :
    partition_index_separates_even_odd_spec inst pred data := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Partition.SlicePartition
