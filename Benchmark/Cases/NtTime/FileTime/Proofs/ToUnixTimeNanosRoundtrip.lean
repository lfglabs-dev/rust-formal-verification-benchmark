import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::to_unix_time_nanos` never panics (no i128 overflow) and its result lies in
`-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500`.
-/
theorem to_unix_time_nanos_roundtrip (ft : file_time.FileTime) :
    to_unix_time_nanos_roundtrip_spec ft := by
  unfold to_unix_time_nanos_roundtrip_spec file_time.unix_time.FileTime.to_unix_time_nanos
    file_time.FileTime.to_raw core.I128.Insts.CoreConvertFromU64.from
  have hft : ft.val < 2^64 := by have := ft.hBounds; simpa using this
  have hc : (UScalar.hcast IScalarTy.I128 ft).val = (ft.val : Int) := by
    rw [UScalar.hcast_val_eq]
    apply Int.bmod_eq_of_le
    · simp
    · simp; omega
  step as ⟨i2, hi2⟩
  step as ⟨ts, hts⟩
  rw [hts, hi2, hc]
  constructor
  · simp
  · simp; omega

end Benchmark.Cases.NtTime.FileTime
