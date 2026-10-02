import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- Above the representable range, `from_unix_time_secs` returns `Err Overflow`. -/
theorem fuso_ovf_spec (ts : Std.I64) (h : 1833029933771 ≤ ts.val) :
    file_time.unix_time.FileTime.from_unix_time_secs ts ⦃ r =>
      r = core.result.Result.Err error.FileTimeRangeErrorKind.Overflow ⦄ := by
  unfold file_time.unix_time.FileTime.from_unix_time_secs
  have hc : ¬ ts ≤ 1833029933770#i64 := by scalar_tac
  rw [if_neg hc]
  simp [core.convert.Into.Blanket.into,
    error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind.from,
    error.FileTimeRangeError.new]

/--
For Unix times after `+60056-05-28 05:36:10 UTC` (`ts ≥ 1_833_029_933_771`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Overflow.into())`.
-/
theorem from_unix_time_secs_with_too_big_date_time_roundtrip (ts : Std.I64)
    (h_ts : 1833029933771 ≤ ts.val) :
    from_unix_time_secs_with_too_big_date_time_roundtrip_spec ts := by
  unfold from_unix_time_secs_with_too_big_date_time_roundtrip_spec
  apply spec_bind (fuso_ovf_spec ts h_ts)
  intro r hr
  simp [hr, core.convert.Into.Blanket.into,
    error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind.from,
    error.FileTimeRangeError.new]

end Benchmark.Cases.NtTime.FileTime
