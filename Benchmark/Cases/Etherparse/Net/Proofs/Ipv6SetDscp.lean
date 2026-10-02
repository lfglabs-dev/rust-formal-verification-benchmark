import Mathlib.Tactic.IntervalCases
import Benchmark.Cases.Etherparse.Net.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

set_option linter.unusedSimpArgs false

theorem getLsbD_ge8 (x : BitVec 8) (i : Nat) (hi : 8 ≤ i) : x.getLsbD i = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le x.toFin.isLt (Nat.pow_le_pow_right (by decide) hi))

theorem mask63_id (x : BitVec 8) : ((x >>> 2) &&& (63#8)) = x >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 6
  · have hbit : (63#8).getLsbD i = true := by interval_cases i <;> decide
    simp [hbit]
  · have hhi : i = 6 ∨ i = 7 := by omega
    rcases hhi with rfl | rfl
    · simp [getLsbD_ge8 x 8 (by decide)]
    · simp [getLsbD_ge8 x 9 (by decide)]

/-- `set_dscp` puts `dscp` (at most 63) into the top 6 bits of the traffic class. -/
theorem set_dscp_bv (tc dscp : BitVec 8) (hd : dscp.toNat ≤ 63) :
    (((tc &&& (3#8)) ||| ((dscp <<< 2) &&& (252#8))) >>> 2) = dscp := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  by_cases h : i < 6
  · have hj : 2 + i < 8 := by omega
    have hnot : ¬ 2 + i < 2 := by omega
    have h3 : (3#8).getLsbD (2 + i) = false := by interval_cases i <;> decide
    have h252 : (252#8).getLsbD (2 + i) = true := by interval_cases i <;> decide
    simp only [hj, hnot, h3, h252, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.and_false, Bool.false_or, Bool.and_true, Bool.not_false, Nat.add_sub_cancel_left]
  · have hge : 8 ≤ 2 + i := by omega
    have hbit : dscp.getLsbD i = false := by
      simp only [BitVec.getLsbD]
      exact Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (show dscp.toNat < 2 ^ 6 by omega)
          (Nat.pow_le_pow_right (by decide) (by omega : 6 ≤ i)))
    simp [getLsbD_ge8 _ (2 + i) hge, hbit]

theorem and63_le (x : Std.U8) : x &&& 63#u8 ≤ 63#u8 := by
  rw [UScalar.le_equiv, UScalar.val_and]
  have h63 : (63#u8).val = 63 := by rfl
  rw [h63]
  exact Nat.and_le_right

theorem shift2_le63 (x : Std.U8) : ∃ y, x >>> 2#i32 = ok y ∧ y.val = x.val >>> 2 ∧ y.bv = x.bv >>> 2 ∧ y ≤ 63#u8 := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  have hpos : 0 ≤ (2#i32).val := by scalar_tac
  have hto : (2#i32).toNat = 2 := by rfl
  have hlt : (2#i32).toNat < 8 := by simp [hto]
  simp only [hpos, hto, hlt, ↓reduceIte]
  refine ⟨⟨x.bv >>> 2⟩, rfl, ?_, rfl, ?_⟩
  · change (x.bv >>> 2).toNat = x.val >>> 2
    rw [BitVec.toNat_ushiftRight]
    rfl
  · rw [UScalar.le_equiv, UScalar.val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h63 : (63#u8).val = 63 := by rfl
    have hv : x.bv.toNat < 256 := x.bv.toFin.isLt
    rw [h63]
    omega

theorem shl2 (x : Std.U8) : ∃ y, x <<< 2#i32 = ok y ∧ y.bv = x.bv <<< 2 := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  have hpos : 0 ≤ (2#i32).val := by scalar_tac
  have hto : (2#i32).toNat = 2 := by rfl
  have hlt : (2#i32).toNat < 8 := by simp [hto]
  simp only [hpos, hto, hlt, ↓reduceIte]
  exact ⟨⟨x.bv <<< 2⟩, rfl, rfl⟩

theorem ipv6_set_dscp (header : net.ipv6_header.Ipv6Header) (dscp : net.ip_dscp.IpDscp)
    (h_dscp : dscp.val ≤ 63) (h_flow : header.flow_label.val ≤ 2^20 - 1) :
    ipv6_set_dscp_spec header dscp := by
  have _ := h_flow
  obtain ⟨sh0, hsh0, hsh0v, hsh0b, hsh0le⟩ := shift2_le63 header.traffic_class
  unfold ipv6_set_dscp_spec
    net.ipv6_header.Ipv6Header.dscp
    net.ipv6_header.Ipv6Header.set_dscp
    net.ip_dscp.IpDscp.value
    net.ip_dscp.IpDscp.try_new
    net.ip_dscp.IpDscp.new_unchecked
  simp only [net.ip_dscp.IpDscp.MAX_U8, hsh0, bind_tc_ok, lift, spec_ok, spec_massert,
    and63_le, hsh0le, massert_True, ↓reduceIte, and_true, true_and]
  obtain ⟨i2, hi2, hi2b⟩ := shl2 dscp
  simp only [hi2, bind_tc_ok]
  have htc : ((header.traffic_class &&& 3#u8) ||| (i2 &&& 252#u8)).bv =
      (header.traffic_class.bv &&& (3#8)) ||| ((dscp.bv <<< 2) &&& (252#8)) := by
    simp [UScalar.bv_and, UScalar.bv_or, hi2b, show (3#u8).bv = 3#8 by rfl,
      show (252#u8).bv = 252#8 by rfl]
  obtain ⟨sh1, hsh1, hsh1v, hsh1b, hsh1le⟩ :=
    shift2_le63 ((header.traffic_class &&& 3#u8) ||| (i2 &&& 252#u8))
  have hsh1_dscp : sh1.bv = dscp.bv := by
    have hd : dscp.bv.toNat ≤ 63 := h_dscp
    simp only [hsh1b, htc]
    exact set_dscp_bv header.traffic_class.bv dscp.bv hd
  have hsh1_le : sh1 ≤ 63#u8 := by
    rw [UScalar.le_equiv]
    have : sh1.val = dscp.val := congrArg BitVec.toNat hsh1_dscp
    rw [this]
    exact h_dscp
  have h63bv : (63#u8).bv = 63#8 := by rfl
  have hmask : sh0 &&& 63#u8 = sh0 := by
    apply UScalar.val_eq_imp
    have hm := congrArg BitVec.toNat (mask63_id header.traffic_class.bv)
    simp only [UScalar.val, UScalar.bv_and, h63bv, hsh0b]
    rw [hm, ← hsh0b]
  have hand63 (z : Std.U8) (hz : z.val ≤ 63) : z &&& 63#u8 = z := by
    apply UScalar.val_eq_imp
    have hbit : (U8.bv z) &&& 63#8 = U8.bv z := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_and]
      by_cases h : i < 6
      · have : (63#8).getLsbD i = true := by interval_cases i <;> decide
        simp only [this, Bool.and_true]
      · have hbit' : (U8.bv z).getLsbD i = false := by
          have hzn : (U8.bv z).toNat = z.val := U8.bv_toNat z
          simp only [BitVec.getLsbD]
          rw [hzn]
          exact Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (show z.val < 2 ^ 6 by omega)
              (Nat.pow_le_pow_right (by decide) (by omega : 6 ≤ i)))
        have hhi : i = 6 ∨ i = 7 := by omega
        rcases hhi with rfl | rfl
        · have hm : (63#8).getLsbD 6 = false := by decide
          have hg : (U8.bv z).getLsbD 6 = (U8.bv z)[6] :=
            BitVec.getLsbD_eq_getElem (by decide)
          simp only [← hg, hbit', hm, Bool.and_false, Bool.false_and]
        · have hm : (63#8).getLsbD 7 = false := by decide
          have hg : (U8.bv z).getLsbD 7 = (U8.bv z)[7] :=
            BitVec.getLsbD_eq_getElem (by decide)
          simp only [← hg, hbit', hm, Bool.and_false, Bool.false_and]
    simp only [UScalar.val, UScalar.bv_and, h63bv]
    exact congrArg BitVec.toNat hbit
  have hsh1_eq : sh1 = dscp := by
    apply UScalar.val_eq_imp
    exact congrArg BitVec.toNat hsh1_dscp
  have hsh1_val : sh1.val ≤ 63 := by
    rw [UScalar.le_equiv] at hsh1_le
    exact hsh1_le
  simp only [hsh1, hsh1_le, hmask, hand63 sh1 hsh1_val, ↓reduceIte, bind_tc_ok, spec_ok,
    massert_True]
  refine ⟨⟨sh0, rfl, rfl⟩, ⟨sh1, rfl, hsh1_eq⟩, ?_⟩
  · exact hsh1_eq

end Benchmark.Cases.Etherparse.Net
