import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

theorem fhl_u64_size : U64.size = 2^64 := by simp [U64.size, U64.numBits]

/--
`FileTime::from_high_low(high, low)` never panics and returns the file time
`high * 2^32 + low`, the value of `(u64::from(high) << u32::BITS) | u64::from(low)`.
-/
theorem from_high_low_roundtrip (high low : Std.U32) :
    from_high_low_roundtrip_spec high low := by
  unfold from_high_low_roundtrip_spec file_time.FileTime.from_high_low file_time.FileTime.new
  simp only [core.num.U32.BITS]
  have hh : high.val < 2^32 := by have := high.hBounds; simpa using this
  have hl : low.val < 2^32 := by have := low.hBounds; simpa using this
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1', hi1''⟩
  step as ⟨i2, hi2⟩
  step as ⟨raw, hraw, hraw'⟩
  have e1 : i.val = high.val := by
    rw [hi, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : i2.val = low.val := by
    rw [hi2, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have e3 : i1.val = high.val * 2^32 := by
    rw [hi1, e1, fhl_u64_size, UScalarTy.U32_numBits_eq, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hraw, UScalar.val_or, e3, e2, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hl]

end Benchmark.Cases.NtTime.FileTime
