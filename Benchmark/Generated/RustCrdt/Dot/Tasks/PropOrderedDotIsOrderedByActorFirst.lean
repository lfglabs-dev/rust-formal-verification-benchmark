import Benchmark.Cases.RustCrdt.Dot.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

/--
For all `Dot<u8>` values `a` and `b`, converting both to `OrdDot` and
comparing: the actor comparison decides the `OrdDot` order (`Less` when
`a.actor < b.actor`, `Greater` when `a.actor > b.actor`), and on equal actors
the full `OrdDot` comparison agrees with the counter comparison.
-/
theorem prop_ordered_dot_is_ordered_by_actor_first (a b : dot.Dot Std.U8) :
    prop_ordered_dot_is_ordered_by_actor_first_spec a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.RustCrdt.Dot
