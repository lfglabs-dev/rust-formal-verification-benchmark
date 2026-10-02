import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- In range, `from_unix_time_secs` returns `Ok ((ts + 11_644_473_600) * 10^7)`. -/
theorem fus_ok_spec (ts : Std.I64) (h1 : -11644473600 ≤ ts.val) (h2 : ts.val ≤ 1833029933770) :
    file_time.unix_time.FileTime.from_unix_time_secs ts ⦃ r =>
      ∃ ft : file_time.FileTime, r = core.result.Result.Ok ft ∧
        ft.val = (ts.val + 11644473600).toNat * 10000000 ⦄ := by
  unfold file_time.unix_time.FileTime.from_unix_time_secs
  have hc : ts ≤ 1833029933770#i64 := by scalar_tac
  rw [if_pos hc]
  step as ⟨i, hi⟩
  have hnneg : ¬ i < 0#i64 := by scalar_tac
  simp only [core.U64.Insts.CoreConvertTryFromI64TryFromIntError.try_from, if_neg hnneg]
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  have hav : a.val = i.val.toNat := by
    rw [ha, IScalar.hcast_val_eq]; simp; omega
  have hbv : b.val = 2^64 - 1 := by
    rw [hb, UScalar.cast_val_eq]; simp [core.num.U64.MAX, U64.rMax]
  have hab : ¬ a > b := by scalar_tac
  rw [if_neg hab]
  step as ⟨c, hcv⟩
  have hcv' : c.val = i.val.toNat := by
    rw [hcv, IScalar.hcast_val_eq]; simp; omega
  simp only [bind_tc_ok, core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
  step as ⟨d, hd⟩
  · simp [file_time.FILE_TIMES_PER_SEC]; scalar_tac
  simp only [file_time.FileTime.new, bind_tc_ok, WP.spec_ok]
  refine ⟨d, rfl, ?_⟩
  rw [hd, hcv', hi]
  simp [file_time.FILE_TIMES_PER_SEC]

/--
For every Unix time in `-11_644_473_600..=1_833_029_933_770` seconds,
`FileTime::from_unix_time_secs(ts)` succeeds (`is_ok()`): in particular the
`duration * FILE_TIMES_PER_SEC` multiplication never overflows `u64`.
-/
theorem from_unix_time_secs_roundtrip (ts : Std.I64)
    (h_ts_lo : -11644473600 ≤ ts.val)
    (h_ts_hi : ts.val ≤ 1833029933770) :
    from_unix_time_secs_roundtrip_spec ts := by
  unfold from_unix_time_secs_roundtrip_spec
  apply spec_bind (fus_ok_spec ts h_ts_lo h_ts_hi)
  rintro r ⟨ft, hr, _⟩
  simp [hr, core.result.Result.is_ok]

end Benchmark.Cases.NtTime.FileTime
