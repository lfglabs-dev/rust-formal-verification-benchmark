import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::to_high_low` never panics and returns `(raw / 2^32, raw % 2^32)`, the
value of `((raw >> u32::BITS) as u32, raw as u32)`.
-/
theorem to_high_low_roundtrip (ft : file_time.FileTime) :
    to_high_low_roundtrip_spec ft := by
  unfold to_high_low_roundtrip_spec file_time.FileTime.to_high_low file_time.FileTime.to_raw
  simp only [core.num.U32.BITS]
  have hft : ft.val < 2^64 := by have := ft.hBounds; simpa using this
  step as ⟨s, hs1, hs2, hs3⟩
  step as ⟨hi, hhi⟩
  step as ⟨lo, hlo⟩
  rw [hhi, hlo, UScalar.cast_val_eq, UScalar.cast_val_eq, hs1, Nat.shiftRight_eq_div_pow]
  simp only [UScalarTy.U32_numBits_eq]
  refine ⟨Nat.mod_eq_of_lt ?_, trivial⟩
  omega

end Benchmark.Cases.NtTime.FileTime
