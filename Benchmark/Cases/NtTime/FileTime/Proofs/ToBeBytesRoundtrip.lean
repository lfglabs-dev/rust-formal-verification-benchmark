import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- Value of Aeneas' `BitVec.toLEBytes`: byte `i` is `x / 256^i % 256`. -/
theorem tbb_toLE_toNat (w : Nat) : ∀ (x : BitVec w),
    x.toLEBytes.map BitVec.toNat =
      (List.range ((w + 7) / 8)).map (fun i => x.toNat / 256^i % 256) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x
    rw [BitVec.toLEBytes]
    by_cases hw : w > 0
    · rw [if_pos hw]
      by_cases h8 : w < 8
      · have hr : (w + 7) / 8 = 1 := by omega
        rw [hr]
        have : ((x >>> 8).setWidth (w - 8)).toLEBytes = [] := by
          rw [BitVec.toLEBytes, if_neg (by omega)]
        rw [List.map_cons, this]
        simp [BitVec.toNat_setWidth]
      · have hr : (w + 7) / 8 = (w - 8 + 7) / 8 + 1 := by omega
        rw [hr, List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map,
          ih (w - 8) (by omega)]
        have hx := x.isLt
        have hy : ((x >>> 8).setWidth (w - 8)).toNat = x.toNat / 256 := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          apply Nat.mod_eq_of_lt
          have : 2 ^ w = 2^8 * 2^(w-8) := by rw [← Nat.pow_add]; congr 1; omega
          rw [this] at hx
          exact Nat.div_lt_of_lt_mul hx
        rw [hy, BitVec.toNat_setWidth]
        congr 1
        · simp
        · apply List.map_congr_left
          intro i _
          simp only [Function.comp, Nat.div_div_eq_div_mul, pow_succ]
          ring_nf
    · rw [if_neg hw]
      have : w = 0 := by omega
      subst this
      simp

/--
`FileTime::to_be_bytes` never panics and returns the big-endian base-256 digits of the
raw tick count (the value of `ft.to_raw().to_be_bytes()`).
-/
theorem to_be_bytes_roundtrip (ft : file_time.FileTime) :
    to_be_bytes_roundtrip_spec ft := by
  unfold to_be_bytes_roundtrip_spec file_time.FileTime.to_be_bytes file_time.FileTime.to_raw
    core.num.U64.to_be_bytes rust_primitives.arithmetic.to_be_bytes_u64
  simp only [bind_tc_ok, WP.spec_ok]
  simp only [Aeneas.Std.core.num.U64.to_be_bytes, List.map_map]
  have h := tbb_toLE_toNat 64 ft.bv
  have e : (fun (x : UScalar .U8) => x.val) ∘ (@UScalar.mk UScalarTy.U8) = BitVec.toNat := rfl
  rw [e, BitVec.toBEBytes, List.map_reverse, h]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.reverse_cons, List.reverse_nil]
  simp only [U64.bv, UScalar.bv_toNat]
  norm_num

end Benchmark.Cases.NtTime.FileTime
