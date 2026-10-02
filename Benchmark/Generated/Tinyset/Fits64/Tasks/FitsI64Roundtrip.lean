import Benchmark.Cases.Tinyset.Fits64.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open tinyset

namespace Benchmark.Cases.Tinyset.Fits64

/--
For every `i64` value `x`, the branch-free `Fits64` encoding into a `u64`
(`x ↦ 2x` for `x ≥ 0`, `x ↦ 2·!x + 1` for `x < 0`, selected with bit masks)
never panics, `from_u64` decodes it back to `x`, and re-encoding the decoded
value reproduces the same word.
-/
theorem fits_i64_roundtrip (x : Std.I64) :
    fits_i64_roundtrip_spec x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Tinyset.Fits64
