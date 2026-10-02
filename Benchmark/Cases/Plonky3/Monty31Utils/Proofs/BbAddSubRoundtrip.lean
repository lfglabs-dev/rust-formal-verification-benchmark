import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u32_size : UScalar.size UScalarTy.U32 = 2^32 := by simp [U32.size, U32.numBits]

theorem c_p : (2013265921#u32).val = 2013265921 := rfl

theorem c_zero : (0#u32).val = 0 := rfl

theorem ovsub32_val (x y : Std.U32) :
    core.num.U32.overflowing_sub x y = ok (⟨x.bv - y.bv⟩, decide (x.val < y.val)) := rfl

theorem sub_bv32_val (x y : Std.U32) :
    (⟨x.bv - y.bv⟩ : Std.U32).val = (2^32 - y.val + x.val) % 2^32 := by
  show (x.bv - y.bv).toNat = _
  rw [BitVec.toNat_sub]; rfl

theorem wadd32 (x y : Std.U32) : core.num.U32.wrapping_add x y = ok (U32.wrapping_add x y) := rfl

theorem add_spec {MP : Type} (inst : data_traits.MontyParameters MP) (h : BBParams inst)
    (a b : Std.U32) (hab : a.val + b.val < 2 * 2013265921) :
    utils.add inst a b ⦃ r => r.val = (a.val + b.val) % 2013265921 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.add
  simp only [hp, bind_tc_ok]
  step as ⟨s, hs⟩
  rw [ovsub32_val, bind_tc_ok]
  show (if decide (s.val < (2013265921#u32).val) = true then ok s
    else ok (⟨s.bv - (2013265921#u32).bv⟩ : Std.U32)) ⦃ r => r.val = (a.val + b.val) % 2013265921 ⦄
  rw [c_p]
  by_cases hlt : s.val < 2013265921
  · simp only [hlt, decide_true, if_true, spec_ok]
    omega
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, spec_ok]
    rw [sub_bv32_val, c_p]
    omega

theorem sub_spec {MP : Type} (inst : data_traits.MontyParameters MP) (h : BBParams inst)
    (a b : Std.U32) (ha : a.val < 2013265921) (hb : b.val < 2013265921) :
    utils.sub inst a b ⦃ r => r.val = (a.val + 2013265921 - b.val) % 2013265921 ⦄ := by
  obtain ⟨hp, hbits, hmu, hmask⟩ := h
  unfold utils.sub
  simp only [hp]
  rw [ovsub32_val, bind_tc_ok]
  show (do
      let corr ← if decide (a.val < b.val) = true then ok 2013265921#u32 else ok 0#u32
      core.num.U32.wrapping_add (⟨a.bv - b.bv⟩ : Std.U32) corr) ⦃ r =>
    r.val = (a.val + 2013265921 - b.val) % 2013265921 ⦄
  by_cases hlt : a.val < b.val
  · simp only [hlt, decide_true, if_true, bind_tc_ok, wadd32, spec_ok]
    rw [U32.wrapping_add_val_eq, sub_bv32_val, u32_size, c_p]
    omega
  · simp only [hlt, decide_false, if_false, Bool.false_eq_true, bind_tc_ok, wadd32, spec_ok]
    rw [U32.wrapping_add_val_eq, sub_bv32_val, u32_size, c_zero]
    omega

/--
Modular subtraction undoes modular addition: `sub(add(a, b), b) = a` for canonical BabyBear
inputs, without panicking.
-/
theorem bb_add_sub_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (a b : Std.U32)
    (h_a : a.val < 2013265921) (h_b : b.val < 2013265921) :
    bb_add_sub_roundtrip_spec inst a b := by
  unfold bb_add_sub_roundtrip_spec
  apply spec_bind (add_spec inst h_params a b (by omega))
  intro s hs
  have hsP : s.val < 2013265921 := by rw [hs]; exact Nat.mod_lt _ (by norm_num)
  apply spec_mono (sub_spec inst h_params s b hsP h_b)
  intro r hr
  rw [hr, hs]
  omega

end Benchmark.Cases.Plonky3.Monty31Utils
