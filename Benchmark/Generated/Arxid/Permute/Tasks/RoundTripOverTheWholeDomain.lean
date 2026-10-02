import Benchmark.Cases.Arxid.Permute.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid

namespace Benchmark.Cases.Arxid.Permute

/--
For every 64-bit key and every id in the 40-bit domain `0..=MAX_ID`
(`MAX_ID = 2^40 - 1`), obfuscating the id and then deobfuscating the code
with the same key never panics and returns the original id: the 6-round
Feistel network `feistel_n_inv` inverts `feistel_n`.
-/
theorem round_trip_over_the_whole_domain (key id : Std.U64)
    (h_id : id.val ≤ 2^40 - 1) :
    round_trip_over_the_whole_domain_spec key id := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Arxid.Permute
