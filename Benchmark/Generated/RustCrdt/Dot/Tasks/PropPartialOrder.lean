import Benchmark.Cases.RustCrdt.Dot.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

/--
For all `Dot<u8>` values `a` and `b`, the pair `a.partial_cmp(&b)` /
`b.partial_cmp(&a)` behaves exactly as a consistent partial order on dots
requires: both are `None` iff the actors differ, both are `Some` with mirrored
`Less`/`Greater` iff the actors are equal and the counters differ, and both
are `Some(Equal)` iff actor and counter agree.
-/
theorem prop_partial_order (a b : dot.Dot Std.U8) :
    prop_partial_order_spec a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.RustCrdt.Dot
