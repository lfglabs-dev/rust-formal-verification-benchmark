import Benchmark.Cases.OrderStat.Quickselect.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open order_stat

namespace Benchmark.Cases.OrderStat.Quickselect

/--
For every `i32` slice `x` and index `k < x.len()`, quickselect's
`select(&mut x, k)` never panics and leaves at position `k` exactly the
`k`-th smallest element of the slice, i.e. the element that sorting the
resulting slice would put at position `k`.
-/
theorem select_kth_is_kth_smallest (x : Slice Std.I32) (k : Std.Usize)
    (h_assume_k : k.val < x.length) :
    select_kth_is_kth_smallest_spec x k := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.OrderStat.Quickselect
