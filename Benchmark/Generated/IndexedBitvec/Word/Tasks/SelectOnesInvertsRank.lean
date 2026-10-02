import Benchmark.Cases.IndexedBitvec.Word.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

/--
For every word `x` and every `i` below `x.count_ones()`, `x.select_ones(i)`
returns `Some(r)` with `x.rank_ones(r) == Some(i)` and `x.get(r) == Some(true)`;
`x.select_ones(x.count_ones())` returns `None`.
-/
theorem select_ones_inverts_rank (x : word.Word) :
    select_ones_inverts_rank_spec x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.IndexedBitvec.Word
