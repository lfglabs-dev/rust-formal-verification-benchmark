import Mathlib.Tactic.IntervalCases
import Benchmark.Cases.Etherparse.Transport.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Transport

set_option linter.unusedSimpArgs false

theorem getLsbD_ge8 (x : BitVec 8) (i : Nat) (hi : 8 ≤ i) : x.getLsbD i = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le x.toFin.isLt (Nat.pow_le_pow_right (by decide) hi))

theorem getLsbD_bv240 (i : Nat) (hi : i < 8) :
    (240#8).getLsbD i = decide (4 ≤ i) := by
  interval_cases i <;> decide

theorem getLsbD_bv15 (i : Nat) (hi : i < 8) :
    (15#8).getLsbD i = decide (i < 4) := by
  interval_cases i <;> decide

/-- High nibble written by `set_flags` reads back as the low 4 bits of `value`. -/
theorem igmp_flags_bv (raw value : BitVec 8) :
    ((((raw &&& ~~~(240#8)) ||| ((value <<< 4) &&& (240#8))) &&& (240#8)) >>> 4)
      = value &&& (15#8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 4
  · have h4i : 4 + i < 8 := by omega
    have hnot : ¬ 4 + i < 4 := by omega
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, h4i, hnot, h,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.or_false, Bool.false_or, Nat.add_sub_cancel, getLsbD_bv240 (4 + i) h4i,
      getLsbD_bv15 i (by omega : i < 8), show 4 ≤ 4 + i by omega, show i < 4 by exact h]
    simp only [Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.false_or, Nat.add_sub_cancel_left]
  · simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, getLsbD_ge8 _ (4 + i) (by omega),
      getLsbD_bv15 i hi, h, Bool.and_false]
    simp only [show decide False = false by rfl, Bool.and_false]

/-- Bits outside `RAW_BYTE_8_MASK_FLAGS` are unchanged by `set_flags`. -/
theorem igmp_low_bv (raw value : BitVec 8) :
    (((raw &&& ~~~(240#8)) ||| ((value <<< 4) &&& (240#8))) &&& ~~~(240#8))
      = raw &&& ~~~(240#8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and, getLsbD_bv240 i hi]
  by_cases h : i < 4
  · have hd : decide (4 ≤ i) = false := by simp [show ¬ 4 ≤ i by omega]
    simp only [hd, decide_eq_true h, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.or_false]
  · have hd : decide (4 ≤ i) = true := by simp [show 4 ≤ i by omega]
    simp only [hd, Bool.not_true, Bool.false_and, Bool.and_false]

theorem igmp_flags_set (raw_byte_8 value : Std.U8) :
    igmp_flags_set_spec raw_byte_8 value := by
  unfold igmp_flags_set_spec
    transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_flags
    transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags
  simp only [
    transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_FLAGS,
    transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_OFFSET_FLAGS,
    HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
  have h4 : (4#u8).val < 8 := by scalar_tac
  simp only [h4, ↓reduceIte, bind_tc_ok, lift, spec_ok]
  have h4n : (4#u8).bv.toNat = 4 := by
    simp [UScalar.bv, UScalar.val, BitVec.toNat_ofNat]
  have h240 : (240#u8).bv = 240#8 := by rfl
  have h15 : (15#u8).bv = 15#8 := by rfl
  constructor
  · apply UScalar.val_eq_imp
    simp only [UScalar.val, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, h4n, h240, h15]
    exact congrArg BitVec.toNat (igmp_flags_bv raw_byte_8.bv value.bv)
  · apply UScalar.val_eq_imp
    simp only [UScalar.val, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, h4n, h240, h15]
    exact congrArg BitVec.toNat (igmp_low_bv raw_byte_8.bv value.bv)

end Benchmark.Cases.Etherparse.Transport
