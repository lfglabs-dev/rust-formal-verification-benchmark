import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
For Unix times before the NT epoch (`ts ≤ -11_644_473_601`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Negative.into())`.
-/
theorem from_unix_time_secs_before_nt_time_epoch_roundtrip (ts : Std.I64)
    (h_ts : ts.val ≤ -11644473601) :
    from_unix_time_secs_before_nt_time_epoch_roundtrip_spec ts := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
