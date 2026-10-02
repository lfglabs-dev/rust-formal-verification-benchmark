import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
For every Unix time in `-11_644_473_600..=1_833_029_933_770` seconds,
`FileTime::from_unix_time_secs(ts)` succeeds (`is_ok()`): in particular the
`duration * FILE_TIMES_PER_SEC` multiplication never overflows `u64`.
-/
theorem from_unix_time_secs_roundtrip (ts : Std.I64)
    (h_ts_lo : -11644473600 ≤ ts.val)
    (h_ts_hi : ts.val ≤ 1833029933770) :
    from_unix_time_secs_roundtrip_spec ts := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
