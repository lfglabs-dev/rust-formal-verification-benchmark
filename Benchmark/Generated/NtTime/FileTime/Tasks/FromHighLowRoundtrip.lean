import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::from_high_low(high, low)` never panics and returns the file time
`high * 2^32 + low`, the value of `(u64::from(high) << u32::BITS) | u64::from(low)`.
-/
theorem from_high_low_roundtrip (high low : Std.U32) :
    from_high_low_roundtrip_spec high low := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
