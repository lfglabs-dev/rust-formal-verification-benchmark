import Benchmark.Cases.Jiff.Civil.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open jiff_core

namespace Benchmark.Cases.Jiff.Civil

/-- `Time::to_nanosecond` never overflows on a valid time and computes the
nanosecond of the day. -/
theorem tnr_to_nanosecond_spec (t : civil.time.Time)
    (h_hour : 0 ≤ t.hour.val ∧ t.hour.val ≤ 23)
    (h_minute : 0 ≤ t.minute.val ∧ t.minute.val ≤ 59)
    (h_second : 0 ≤ t.second.val ∧ t.second.val ≤ 59)
    (h_subsec : 0 ≤ t.subsec_nanosecond.val ∧ t.subsec_nanosecond.val ≤ 999999999) :
    civil.time.Time.to_nanosecond t ⦃ n => n.nanosecond.val =
      t.hour.val * 3600000000000 + t.minute.val * 60000000000 +
      t.second.val * 1000000000 + t.subsec_nanosecond.val ⦄ := by
  unfold civil.time.Time.to_nanosecond
  simp only [civil.time.Time.impl.hour, civil.time.Time.impl.minute,
    civil.time.Time.impl.second, civil.time.Time.impl.subsec_nanosecond]
  step*

/-- `x as u64` for a non-negative `i64`. -/
theorem tnr_hcast_u64_val (x : Std.I64) (h0 : 0 ≤ x.val) :
    ((IScalar.hcast UScalarTy.U64 x).val : Int) = x.val := by
  have hb := x.hBounds
  rw [IScalar.hcast_val_eq]
  have : x.val % 2 ^ UScalarTy.U64.numBits = x.val := by
    apply Int.emod_eq_of_lt h0
    simp [UScalarTy.numBits] at *; omega
  rw [this]; omega

/-- `i as i8` for a `u64` below `2^7`. -/
theorem tnr_hcast_i8_val (i : Std.U64) (h : i.val < 128) :
    (UScalar.hcast IScalarTy.I8 i).val = (i.val : Int) := by
  rw [UScalar.hcast_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' <;> simp [IScalarTy.numBits]; omega

/-- `i as i32` for a `u64` below `2^31`. -/
theorem tnr_hcast_i32_val (i : Std.U64) (h : i.val < 2^31) :
    (UScalar.hcast IScalarTy.I32 i).val = (i.val : Int) := by
  rw [UScalar.hcast_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' <;> simp [IScalarTy.numBits]; omega

/-- `TimeNanosecond::to_time` splits a nanosecond of the day into its
hour/minute/second/subsecond components (all four branches, including the
early exits on a zero remainder that return fields of `Time::MIN`). -/
theorem tnr_to_time_spec (n : civil.time.TimeNanosecond)
    (h0 : 0 ≤ n.nanosecond.val) (h1 : n.nanosecond.val < 86400000000000) :
    civil.time.TimeNanosecond.to_time n ⦃ t =>
      t.hour.val = n.nanosecond.val / 3600000000000 ∧
      t.minute.val = n.nanosecond.val % 3600000000000 / 60000000000 ∧
      t.second.val = n.nanosecond.val % 60000000000 / 1000000000 ∧
      t.subsec_nanosecond.val = n.nanosecond.val % 1000000000 ⦄ := by
  unfold civil.time.TimeNanosecond.to_time
  step*
  all_goals
    have hv := tnr_hcast_u64_val n.nanosecond h0
    rw [← nanosecond_post] at hv
    simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv, Decidable.not_not] at *
    try simp only [civil.time.Time.MIN]
  · rw [i1_post, i3_post, i5_post, i7_post, tnr_hcast_i8_val _ (by omega),
      tnr_hcast_i8_val _ (by omega), tnr_hcast_i8_val _ (by omega),
      tnr_hcast_i32_val _ (by omega)]
    omega
  · rw [i1_post, i3_post, tnr_hcast_i8_val _ (by omega), tnr_hcast_i8_val _ (by omega)]
    simp at *; omega
  · rw [i1_post, tnr_hcast_i8_val _ (by omega)]
    simp at *; omega
  · simp at *; omega

/--
Converting a valid civil `Time` to its nanosecond of the day
(`Time::to_nanosecond`) and back (`TimeNanosecond::to_time`, a chain of
unsigned divisions/remainders with early exits on zero remainders) never
panics and returns a time equal to the original one.
-/
theorem time_to_nanosecond_roundtrip (t : civil.time.Time)
    (h_hour : 0 ≤ t.hour.val ∧ t.hour.val ≤ 23)
    (h_minute : 0 ≤ t.minute.val ∧ t.minute.val ≤ 59)
    (h_second : 0 ≤ t.second.val ∧ t.second.val ≤ 59)
    (h_subsec : 0 ≤ t.subsec_nanosecond.val ∧ t.subsec_nanosecond.val ≤ 999999999) :
    time_to_nanosecond_roundtrip_spec t := by
  unfold time_to_nanosecond_roundtrip_spec
  apply spec_bind (tnr_to_nanosecond_spec t h_hour h_minute h_second h_subsec)
  intro n hn
  apply spec_bind (tnr_to_time_spec n (by omega) (by omega))
  rintro t' ⟨e1, e2, e3, e4⟩
  have f1 : t.hour = t'.hour := by rw [IScalar.eq_equiv]; omega
  have f2 : t.minute = t'.minute := by rw [IScalar.eq_equiv]; omega
  have f3 : t.second = t'.second := by rw [IScalar.eq_equiv]; omega
  have f4 : t.subsec_nanosecond = t'.subsec_nanosecond := by
    rw [IScalar.eq_equiv]; omega
  unfold civil.time.Time.Insts.CoreCmpPartialEqTime.eq
  simp [f1, f2, f3, f4]

end Benchmark.Cases.Jiff.Civil
