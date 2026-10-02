import PartitionSlicePartition.Extraction

/-!
# partition — specifications

Implementation: `extracted/PartitionSlicePartition` (verbatim `cargo hax
extract partition-slice-partition` output for llogiq/partition@628b0a4c).

`partition_index<T, P: Fn(&T) -> bool>(data: &mut [T], predicate: P)` and
`partition` (which additionally splits the slice at that index with
`split_at_mut`) are generic. The property tests instantiate them at `T = u32`
with the test closure `|&e| e % 2 == 0`. In the extraction a closure argument
is a value `pred : P` together with an `Fn P u32 Bool` instance record; the
test's closure is not part of the library, so every theorem quantifies over
*any* instance satisfying `IsEvenPredicate` below, which states exactly what the
test closure computes (in particular the closure itself satisfies it; see
`cases/partition/slice_partition/review/NonVacuity.lean`). The `&mut [T]`
argument is threaded functionally: `partition_index` returns the index and the
final contents of the slice; `partition` returns the two sub-slices (and a
write-back function that the tests never use).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic and
indexing follow Rust debug-build semantics (overflow and out-of-bounds panic),
the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Partition.SlicePartition

open partition

/-- The test closure `|&e| e % 2 == 0` (src/lib.rs:97 and 109) passed as
`predicate`: calling it on `e : u32` never panics (`e % 2` has a non-zero
divisor) and returns whether `e` is even. -/
def IsEvenPredicate {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P) : Prop :=
  ∀ e : Std.U32, inst.call pred e = ok (decide (e.val % 2 = 0))

/-- The tests' `v.sort()` on a `Vec<u32>`: the list sorted in ascending order
(`List.mergeSort` with `≤` on the values; a sorted permutation of a list of
integers is unique, so this is exactly the contents after Rust's `sort`). -/
def sortU32 (l : List Std.U32) : List Std.U32 :=
  l.mergeSort (fun a b => decide (a.val ≤ b.val))

/-- The tests' reference side
`data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>()`. -/
def evens (l : List Std.U32) : List Std.U32 :=
  l.filter (fun e => decide (e.val % 2 = 0))

/-- The tests' reference side
`data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>()`. -/
def odds (l : List Std.U32) : List Std.U32 :=
  l.filter (fun e => decide (e.val % 2 ≠ 0))

/-- PBT `tests::quickcheck` / `prop_partition_index` (src/lib.rs:105-119):
```
let mut trues = data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>();
let mut falses = data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>();
let first_false = partition_index(&mut data, |&e| e % 2 == 0);
let (mut left, mut right) = (
    data[0..first_false].iter().cloned().collect::<Vec<u32>>(),
    data[first_false..].iter().cloned().collect::<Vec<u32>>());
trues.sort(); falses.sort(); left.sort(); right.sort();
trues == left && falses == right
```
`trues`/`falses` are computed from the original `data`; `left`/`right` from the
contents of `data` after the call (`r.2`). The conjunct
`first_false ≤ len` states that the test's range indexing
`data[0..first_false]` / `data[first_false..]` does not panic. -/
def partition_index_separates_even_odd_spec {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) : Prop :=
  partition_index inst data pred ⦃ r =>
    r.1.val ≤ r.2.length ∧
    sortU32 (evens data.val) = sortU32 (r.2.val.take r.1.val) ∧
    sortU32 (odds data.val) = sortU32 (r.2.val.drop r.1.val) ⦄

/-- PBT `tests::quickcheck` / `prop_partition` (src/lib.rs:93-103):
```
let mut trues = data.iter().cloned().filter(|e| e % 2 == 0).collect::<Vec<u32>>();
let mut falses = data.iter().cloned().filter(|e| e % 2 != 0).collect::<Vec<u32>>();
let (left, right) = partition(&mut data, |&e| e % 2 == 0);
trues.sort(); falses.sort(); left.sort(); right.sort();
trues == left && falses == right
```
`r.1.1` / `r.1.2` are the two sub-slices returned by `partition` (the
write-back function `r.2` is not used by the test). -/
def partition_separates_even_odd_spec {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) : Prop :=
  partition.partition inst data pred ⦃ r =>
    sortU32 (evens data.val) = sortU32 r.1.1.val ∧
    sortU32 (odds data.val) = sortU32 r.1.2.val ⦄

end Benchmark.Cases.Partition.SlicePartition
