import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
For Unix times after `+60056-05-28 05:36:10 UTC` (`ts ≥ 1_833_029_933_771`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Overflow.into())`.
-/
theorem from_unix_time_secs_with_too_big_date_time_roundtrip (ts : Std.I64)
    (h_ts : 1833029933771 ≤ ts.val) :
    from_unix_time_secs_with_too_big_date_time_roundtrip_spec ts := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
