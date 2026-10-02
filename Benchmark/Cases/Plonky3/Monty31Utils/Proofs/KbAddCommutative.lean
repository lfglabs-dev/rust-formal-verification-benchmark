import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem c_p : (2130706433#u32).val = 2130706433 := rfl

theorem ovsub32_val (x y : Std.U32) :
    core.num.U32.overflowing_sub x y = ok (⟨x.bv - y.bv⟩, decide (x.val < y.val)) := rfl

theorem sub_bv32_val (x y : Std.U32) :
    (⟨x.bv - y.bv⟩ : Std.U32).val = (2^32 - y.val + x.val) % 2^32 := by
  show (x.bv - y.bv).toNat = _
  rw [BitVec.toNat_sub]; rfl

theorem add_spec {MP : Type} (inst : data_traits.MontyParameters MP) (h : KBParams inst)
    (a b : Std.U32) (hab : a.val + b.val < 2 * 2130706433) :
    utils.add inst a b ⦃ r => r.val = (a.val + b.val) % 2130706433 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.add
  simp only [hp, bind_tc_ok]
  step as ⟨s, hs⟩
  rw [ovsub32_val, bind_tc_ok]
  show (if decide (s.val < (2130706433#u32).val) = true then ok s
    else ok (⟨s.bv - (2130706433#u32).bv⟩ : Std.U32)) ⦃ r => r.val = (a.val + b.val) % 2130706433 ⦄
  rw [c_p]
  by_cases hlt : s.val < 2130706433
  · simp only [hlt, decide_true, if_true, spec_ok]
    omega
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, spec_ok]
    rw [sub_bv32_val, c_p]
    omega

/--
Modular addition `add` (checked `u32` sum followed by a conditional subtraction of `P` via
`overflowing_sub`) never panics on canonical KoalaBear inputs and is commutative.
-/
theorem kb_add_commutative {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_add_commutative_spec inst a b := by
  unfold kb_add_commutative_spec
  apply spec_bind (add_spec inst h_params a b (by omega))
  intro ab hab
  apply spec_bind (add_spec inst h_params b a (by omega))
  intro ba hba
  rw [spec_ok, hab, hba, Nat.add_comm]

end Benchmark.Cases.Plonky3.Monty31Utils
