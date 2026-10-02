import Benchmark.Cases.Arxid.Permute.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid

namespace Benchmark.Cases.Arxid.Permute

/--
For every 64-bit key and every 64-bit input `id`, the bits of `id` above the
40-bit domain are ignored: `obfuscate(id, key) == obfuscate(id & MAX_ID, key)`,
and deobfuscating `obfuscate(id, key)` returns exactly `id & MAX_ID`; no call
panics.
-/
theorem out_of_domain_input_is_reduced_not_rejected (key id : Std.U64) :
    out_of_domain_input_is_reduced_not_rejected_spec key id := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Arxid.Permute
