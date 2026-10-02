import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- Below the NT epoch, `from_unix_time_secs` returns `Err Negative`. -/
theorem fuse_neg_spec (ts : Std.I64) (h : ts.val ≤ -11644473601) :
    file_time.unix_time.FileTime.from_unix_time_secs ts ⦃ r =>
      r = core.result.Result.Err error.FileTimeRangeErrorKind.Negative ⦄ := by
  unfold file_time.unix_time.FileTime.from_unix_time_secs
  have hc : ts ≤ 1833029933770#i64 := by scalar_tac
  rw [if_pos hc]
  step as ⟨i, hi⟩
  have hneg : i < 0#i64 := by scalar_tac
  simp only [core.U64.Insts.CoreConvertTryFromI64TryFromIntError.try_from, if_pos hneg,
    bind_tc_ok, core.result.Result.map_err,
    file_time.unix_time.FileTime.from_unix_time_secs.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorFileTimeRangeErrorKind.call_once,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind.from,
    error.FileTimeRangeError.new]
  simp

/--
For Unix times before the NT epoch (`ts ≤ -11_644_473_601`),
`FileTime::from_unix_time_secs(ts)` returns `Err(FileTimeRangeErrorKind::Negative.into())`.
-/
theorem from_unix_time_secs_before_nt_time_epoch_roundtrip (ts : Std.I64)
    (h_ts : ts.val ≤ -11644473601) :
    from_unix_time_secs_before_nt_time_epoch_roundtrip_spec ts := by
  unfold from_unix_time_secs_before_nt_time_epoch_roundtrip_spec
  apply spec_bind (fuse_neg_spec ts h_ts)
  intro r hr
  simp [hr, core.convert.Into.Blanket.into,
    error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind.from,
    error.FileTimeRangeError.new]

end Benchmark.Cases.NtTime.FileTime
