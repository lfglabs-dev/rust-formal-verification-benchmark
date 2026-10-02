import Benchmark.Cases.Arxid.Permute.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid

namespace Benchmark.Cases.Arxid.Permute

/--
For every 64-bit key and every 64-bit input, both `obfuscate(id, key)` and
`deobfuscate(id, key)` never panic and return a value in the 40-bit domain,
i.e. at most `MAX_ID = 2^40 - 1` (inputs above the domain are reduced, and
every Feistel round keeps both halves below `2^20`).
-/
theorem output_never_leaves_the_domain (key id : Std.U64) :
    output_never_leaves_the_domain_spec key id := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Arxid.Permute
