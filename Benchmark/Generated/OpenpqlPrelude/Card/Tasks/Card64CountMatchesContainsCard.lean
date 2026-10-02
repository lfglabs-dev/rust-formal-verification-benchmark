import Benchmark.Cases.OpenpqlPrelude.Card.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Card

/--
For every `Card64` produced by the property-test generator (a `u64` masked with
`Card64::ALL`), `count()` (a popcount) never panics and equals the number of the 52 cards
for which `contains_card` holds.
-/
theorem card64_count_matches_contains_card (c64 : card.card64.Card64)
    (h_c64 : c64.val &&& 0x1FFF1FFF1FFF1FFF = c64.val) :
    card64_count_spec c64 := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.OpenpqlPrelude.Card
