import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u64_size : UScalar.size UScalarTy.U64 = 2^64 := by simp [U64.size, U64.numBits]

theorem u32_size : UScalar.size UScalarTy.U32 = 2^32 := by simp [U32.size, U32.numBits]

theorem u64_size' : U64.size = 2^64 := by simp [U64.size, U64.numBits]

theorem c_mu : (2164260865#u32).val = 2164260865 := rfl

theorem c_mask : (4294967295#u32).val = 4294967295 := rfl

theorem c_p : (2130706433#u32).val = 2130706433 := rfl

theorem c_zero : (0#u32).val = 0 := rfl

theorem c_p64 : (UScalar.cast UScalarTy.U64 2130706433#u32).val = 2130706433 := rfl

theorem ovsub_val (x y : Std.U64) :
    core.num.U64.overflowing_sub x y = ok (⟨x.bv - y.bv⟩, decide (x.val < y.val)) := rfl

theorem sub_bv_val (x y : Std.U64) :
    (⟨x.bv - y.bv⟩ : Std.U64).val = (2^64 - y.val + x.val) % 2^64 := by
  show (x.bv - y.bv).toNat = _
  rw [BitVec.toNat_sub]; rfl

theorem wadd32 (x y : Std.U32) : core.num.U32.wrapping_add x y = ok (U32.wrapping_add x y) := rfl

theorem mask_eq {MP : Type} (inst : data_traits.MontyParameters MP)
    (hb : inst.MONTY_BITS = ok 32#u32) :
    data_traits.MontyParameters.MONTY_MASK.default inst = ok 4294967295#u32 := by
  unfold data_traits.MontyParameters.MONTY_MASK.default
  rw [hb, bind_tc_ok]
  rfl

theorem kb_key (x : Nat) : x * 2164260865 % 2^32 * 2130706433 % 2^32 = x % 2^32 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_mod,
    show 2164260865 * 2130706433 % 2^32 = 1 by norm_num, Nat.mul_one, Nat.mod_mod]

theorem kb_cancel (r1 r2 : Nat) (h1 : r1 < 2130706433) (h2 : r2 < 2130706433)
    (h : r1 * 2^32 % 2130706433 = r2 * 2^32 % 2130706433) : r1 = r2 := by
  have e : ∀ r, r < 2130706433 → r = r * 2^32 % 2130706433 * 1057030144 % 2130706433 := by
    intro r hr
    rw [Nat.mul_mod (r * 2^32 % 2130706433), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc,
      Nat.mul_mod r, show 2^32 * 1057030144 % 2130706433 = 1 by norm_num, Nat.mul_one,
      Nat.mod_mod, Nat.mod_eq_of_lt hr]
  rw [e r1 h1, e r2 h2, h]

theorem reduce_arith (x t u : Nat) (hx : x < 2^32 * 2130706433) (ht : t < 2^32)
    (hu : u = t * 2130706433) (hkey : u % 2^32 = x % 2^32) :
    ((2^64 - u + x) % 2^64 / 2^32 % 2^32
        + (if x < u then 2130706433 else 0)) % 2^32 < 2130706433 ∧
    ((2^64 - u + x) % 2^64 / 2^32 % 2^32
        + (if x < u then 2130706433 else 0)) % 2^32 * 2^32 % 2130706433
      = x % 2130706433 := by
  have hub : u < 2^32 * 2130706433 := by omega
  by_cases hxu : x < u
  · simp only [hxu, if_true]
    obtain ⟨k, hk⟩ : ∃ k, u = x + 2^32 * k := ⟨(u - x) / 2^32, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hkP : k < 2130706433 := by omega
    have h1 : (2^64 - u + x) % 2^64 = 2^64 - 2^32 * k := by omega
    have h2 : (2^64 - 2^32 * k) / 2^32 = 2^32 - k := by omega
    have hres : ((2^64 - u + x) % 2^64 / 2^32 % 2^32 + 2130706433) % 2^32 = 2130706433 - k := by
      rw [h1, h2]; omega
    rw [hres]
    refine ⟨by omega, ?_⟩
    omega
  · simp only [hxu, if_false]
    obtain ⟨k, hk⟩ : ∃ k, x = u + 2^32 * k := ⟨(x - u) / 2^32, by omega⟩
    have hkP : k < 2130706433 := by omega
    have h1 : (2^64 - u + x) % 2^64 = 2^32 * k := by omega
    have h2 : (2^32 * k) / 2^32 = k := by omega
    have hres : ((2^64 - u + x) % 2^64 / 2^32 % 2^32 + 0) % 2^32 = k := by
      rw [h1, h2]; omega
    rw [hres]
    refine ⟨hkP, ?_⟩
    omega

/-- The common tail of `monty_reduce` / `large_monty_reduce`. -/
theorem tail_spec (xc u : Std.U64) (t : Nat) (hxc : xc.val < 2^32 * 2130706433) (ht : t < 2^32)
    (hu : u.val = t * 2130706433) (hkey : u.val % 2^32 = xc.val % 2^32) :
    (do
      let (x_sub_u, over) ← core.num.U64.overflowing_sub xc u
      let i ← x_sub_u >>> 32#u32
      let corr ← if over = true then ok 2130706433#u32 else ok 0#u32
      core.num.U32.wrapping_add (UScalar.cast UScalarTy.U32 i) corr) ⦃ r =>
      r.val < 2130706433 ∧ r.val * 2^32 % 2130706433 = xc.val % 2130706433 ⦄ := by
  rw [ovsub_val]
  simp only [bind_tc_ok]
  step as ⟨i8, hi8⟩
  have hA := reduce_arith xc.val t u.val hxc ht hu hkey
  rw [sub_bv_val] at hi8
  by_cases hxu : xc.val < u.val
  · simp only [hxu, decide_true, if_true, bind_tc_ok, wadd32, spec_ok] at hA ⊢
    rw [U32.wrapping_add_val_eq, UScalar.cast_val_eq, hi8, u32_size, Nat.shiftRight_eq_div_pow,
      UScalarTy.U32_numBits_eq, c_p]
    exact hA
  · simp only [hxu, decide_false, if_false, Bool.false_eq_true, bind_tc_ok, wadd32, spec_ok] at hA ⊢
    rw [U32.wrapping_add_val_eq, UScalar.cast_val_eq, hi8, u32_size, Nat.shiftRight_eq_div_pow,
      UScalarTy.U32_numBits_eq, c_zero]
    exact hA

theorem monty_reduce_spec {MP : Type} (inst : data_traits.MontyParameters MP) (h : KBParams inst)
    (x : Std.U64) (hx : x.val < 2^32 * 2130706433) :
    utils.monty_reduce inst x ⦃ r => r.val < 2130706433 ∧
      r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.monty_reduce
  simp only [hp, hb, hmu, hmask, mask_eq inst hb, bind_tc_ok, lift]
  unfold core.num.U64.wrapping_mul rust_primitives.arithmetic.wrapping_mul_u64
  simp only [bind_tc_ok]
  set t := (x.wrapping_mul (UScalar.cast UScalarTy.U64 2164260865#u32) &&&
    UScalar.cast UScalarTy.U64 4294967295#u32) with ht_def
  have htv : t.val = x.val * 2164260865 % 2^64 % 2^32 := by
    rw [ht_def, UScalar.val_and, U64.wrapping_mul_val_eq, U32.cast_U64_val_eq,
      U32.cast_U64_val_eq, u64_size, c_mu, c_mask]
    exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have htb : t.val < 2^32 := by rw [htv]; exact Nat.mod_lt _ (by norm_num)
  step as ⟨u, hu⟩
  have hkey : u.val % 2^32 = x.val % 2^32 := by
    rw [hu, c_p64, htv, Nat.mod_mod_of_dvd _ (by norm_num : 2^32 ∣ 2^64)]
    exact kb_key x.val
  exact tail_spec x u t.val hx htb (by rw [hu, c_p64]) hkey

theorem to_monty_val {MP : Type} (inst : data_traits.MontyParameters MP) (h : KBParams inst)
    (x : Std.U32) :
    utils.to_monty inst x ⦃ r => r.val = x.val * 2^32 % 2130706433 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.to_monty
  simp only [hp, hb, bind_tc_ok, lift]
  step as ⟨i2, hi2⟩
  step as ⟨i5, hi5⟩
  have hx : x.val < 2^32 := x.hBounds
  rw [UScalar.cast_val_eq, hi5, hi2, U32.cast_U64_val_eq, c_p64, u64_size', Nat.shiftLeft_eq,
    UScalarTy.U32_numBits_eq]
  have h1 : x.val * 2^32 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h1]
  have h2 : x.val * 2^32 % 2130706433 < 2130706433 := Nat.mod_lt _ (by norm_num)
  omega

theorem kb_mm (a b : Nat) : a * 2^32 % 2130706433 * (b * 2^32 % 2130706433) % 2130706433
    = a * b % 2130706433 * 2^32 % 2130706433 * 2^32 % 2130706433 := by
  have h1 : a * 2^32 % 2130706433 * (b * 2^32 % 2130706433) ≡ a * 2^32 * (b * 2^32)
      [MOD 2130706433] :=
    Nat.ModEq.mul (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
  have h2 : a * b % 2130706433 * 2^32 % 2130706433 * 2^32 ≡ a * b * 2^32 * 2^32
      [MOD 2130706433] :=
    Nat.ModEq.mul_right _ ((Nat.mod_modEq _ _).trans (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)))
  have h3 : a * 2^32 * (b * 2^32) = a * b * 2^32 * 2^32 := by ring
  rw [h3] at h1
  exact h1.trans h2.symm

/--
Montgomery multiplication is correct: reducing the product of the Montgomery forms of `a` and `b`
gives the Montgomery form of `a * b mod P` (KoalaBear), and nothing panics.
-/
theorem kb_monty_mul_correct {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_monty_mul_correct_spec inst a b := by
  unfold kb_monty_mul_correct_spec
  apply spec_bind (to_monty_val inst h_params a)
  intro ma hma
  apply spec_bind (to_monty_val inst h_params b)
  intro mb hmb
  have hmaP : ma.val < 2130706433 := by rw [hma]; exact Nat.mod_lt _ (by norm_num)
  have hmbP : mb.val < 2130706433 := by rw [hmb]; exact Nat.mod_lt _ (by norm_num)
  have hma64 : (UScalar.cast UScalarTy.U64 ma).val = ma.val := U32.cast_U64_val_eq ma
  have hmb64 : (UScalar.cast UScalarTy.U64 mb).val = mb.val := U32.cast_U64_val_eq mb
  have ha64 : (UScalar.cast UScalarTy.U64 a).val = a.val := U32.cast_U64_val_eq a
  have hb64 : (UScalar.cast UScalarTy.U64 b).val = b.val := U32.cast_U64_val_eq b
  have hprod_b : ma.val * mb.val < 2130706433 * 2130706433 := Nat.mul_lt_mul'' hmaP hmbP
  have hab_b : a.val * b.val < 2130706433 * 2130706433 := Nat.mul_lt_mul'' h_a h_b
  step as ⟨prod, hprod⟩
  step as ⟨ab, hab⟩
  step as ⟨abm, habm⟩
  have hc64 : (2130706433#u64).val = 2130706433 := rfl
  have habmv : abm.val = a.val * b.val % 2130706433 := by rw [habm, hab, ha64, hb64]
  have habm32 : (UScalar.cast UScalarTy.U32 abm).val = a.val * b.val % 2130706433 := by
    rw [UScalar.cast_val_eq, habmv]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (a.val * b.val) (show 0 < 2130706433 by norm_num)
    show _ < 2^32
    omega
  apply spec_bind (to_monty_val inst h_params (UScalar.cast UScalarTy.U32 abm))
  intro e he
  have hprodv : prod.val = ma.val * mb.val := by rw [hprod, hma64, hmb64]
  apply spec_bind (monty_reduce_spec inst h_params prod (by rw [hprodv]; omega))
  intro r ⟨hr1, hr2⟩
  rw [spec_ok]
  rw [habm32] at he
  have heP : e.val < 2130706433 := by rw [he]; exact Nat.mod_lt _ (by norm_num)
  apply kb_cancel _ _ hr1 heP
  rw [hr2, hprodv, hma, hmb, he, kb_mm]

end Benchmark.Cases.Plonky3.Monty31Utils
