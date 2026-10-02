import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u64_size : UScalar.size UScalarTy.U64 = 2^64 := by simp [U64.size, U64.numBits]

theorem u32_size : UScalar.size UScalarTy.U32 = 2^32 := by simp [U32.size, U32.numBits]

theorem u64_size' : U64.size = 2^64 := by simp [U64.size, U64.numBits]

theorem u128_size' : U128.size = 2^128 := by simp [U128.size, U128.numBits]

theorem c_mu : (2164260865#u32).val = 2164260865 := rfl

theorem c_mask : (4294967295#u32).val = 4294967295 := rfl

theorem c_p : (2130706433#u32).val = 2130706433 := rfl

theorem c_zero : (0#u32).val = 0 := rfl

theorem c_p64 : (UScalar.cast UScalarTy.U64 2130706433#u32).val = 2130706433 := rfl

theorem ovsub_val (x y : Std.U64) :
    core.num.U64.overflowing_sub x y = ok (⟨x.bv - y.bv⟩, decide (x.val < y.val)) := rfl

theorem ovsub32_val (x y : Std.U32) :
    core.num.U32.overflowing_sub x y = ok (⟨x.bv - y.bv⟩, decide (x.val < y.val)) := rfl

theorem sub_bv_val (x y : Std.U64) :
    (⟨x.bv - y.bv⟩ : Std.U64).val = (2^64 - y.val + x.val) % 2^64 := by
  show (x.bv - y.bv).toNat = _
  rw [BitVec.toNat_sub]; rfl

theorem sub_bv32_val (x y : Std.U32) :
    (⟨x.bv - y.bv⟩ : Std.U32).val = (2^32 - y.val + x.val) % 2^32 := by
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

theorem large_monty_reduce_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (h : KBParams inst) (x : Std.U64) (hx : x.val < 2 * (2^32 * 2130706433)) :
    utils.large_monty_reduce inst x ⦃ r => r.val < 2130706433 ∧
      r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.large_monty_reduce
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
  step as ⟨rp, hrp⟩
  rw [c_p64, Nat.shiftLeft_eq, u64_size'] at hrp
  have hrpv : rp.val = 2^32 * 2130706433 := by rw [hrp]; norm_num
  rw [ovsub_val]
  simp only [bind_tc_ok]
  by_cases hlt : x.val < rp.val
  · simp only [hlt, decide_true]
    exact tail_spec x u t.val (by omega) htb (by rw [hu, c_p64]) hkey
  · simp only [hlt, decide_false]
    have hxc : (⟨x.bv - rp.bv⟩ : Std.U64).val = x.val - 2^32 * 2130706433 := by
      rw [sub_bv_val]; omega
    have := tail_spec ⟨x.bv - rp.bv⟩ u t.val (by omega) htb (by rw [hu, c_p64]) (by omega)
    rw [hxc] at this
    refine spec_mono this ?_
    intro r hr
    refine ⟨hr.1, ?_⟩
    rw [hr.2]
    omega

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

theorem monty_reduce_u128_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (h : KBParams inst) (x : Std.U128) (hx : x.val < 2^96) :
    utils.monty_reduce_u128 inst x ⦃ r => r.val < 2130706433 ∧
      r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄ := by
  have h' := h
  obtain ⟨hp, hb, hmu, hmask⟩ := h'
  unfold utils.monty_reduce_u128
  simp only [hp, hb, bind_tc_ok, lift]
  step
  step as ⟨i1, hi1⟩
  step
  step as ⟨i2, hi2⟩
  step as ⟨i5, hi5⟩
  step as ⟨trp, htrp⟩
  have htrpv : trp.val = 2 * (2^32 * 2130706433) := by
    rw [htrp, hi5, c_p64, u64_size']; simp only [Nat.shiftLeft_eq]; norm_num
  have hlo : (UScalar.cast UScalarTy.U64 x).val = x.val % 2^64 := by
    rw [UScalar.cast_val_eq]; rfl
  have hhi : (UScalar.cast UScalarTy.U32 i2).val = x.val / 2^64 := by
    rw [UScalar.cast_val_eq, hi2, Nat.shiftRight_eq_div_pow]
    show x.val / 2^64 % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  set lo := UScalar.cast UScalarTy.U64 x with hlo_def
  have hlob : lo.val < 2^64 := lo.hBounds
  have hLR : (if lo ≥ trp then lo - trp else ok lo) ⦃ lr =>
      lr.val < 2 * (2^32 * 2130706433) ∧ lr.val % 2130706433 = lo.val % 2130706433 ⦄ := by
    by_cases hge : lo ≥ trp
    · rw [if_pos hge]
      have hge' : trp.val ≤ lo.val := (UScalar.le_equiv _ _).mp hge
      step as ⟨lr, hlr⟩
      constructor
      · omega
      · rw [hlr, htrpv]; omega
    · rw [if_neg hge, spec_ok]
      have hlt : lo.val < trp.val := by
        have := (UScalar.le_equiv trp lo).not.mp hge
        omega
      exact ⟨by omega, rfl⟩
  apply spec_bind hLR
  intro lr ⟨hlr1, hlr2⟩
  apply spec_bind (large_monty_reduce_spec inst h lr hlr1)
  intro r ⟨hr1, hr2⟩
  apply spec_bind (to_monty_val inst h _)
  intro hr hhr
  have hhrP : hr.val < 2130706433 := by rw [hhr]; exact Nat.mod_lt _ (by norm_num)
  apply spec_mono (add_spec inst h hr r (by omega))
  intro res hres
  constructor
  · rw [hres]; exact Nat.mod_lt _ (by norm_num)
  · rw [hres]
    have e1 : (hr.val + r.val) % 2130706433 * 2^32 ≡ hr.val * 2^32 + r.val * 2^32
        [MOD 2130706433] := by
      have := (Nat.mod_modEq (hr.val + r.val) 2130706433).mul_right (2^32)
      rw [Nat.add_mul] at this
      exact this
    have e2 : hr.val * 2^32 ≡ x.val / 2^64 * 2^64 [MOD 2130706433] := by
      rw [hhr, hhi]
      have := (Nat.mod_modEq (x.val / 2^64 * 2^32) 2130706433).mul_right (2^32)
      rw [Nat.mul_assoc, show (2:Nat)^32 * 2^32 = 2^64 by norm_num] at this
      exact this
    have e3 : r.val * 2^32 ≡ x.val % 2^64 [MOD 2130706433] := by
      unfold Nat.ModEq
      rw [hr2, hlr2, hlo]
    have e4 := e1.trans (e2.add e3)
    rw [Nat.div_add_mod'] at e4
    exact e4

/--
`monty_reduce_u128(x) * 2^32 ≡ x (mod P)` for every `x = hi * 2^64 + lo` (`hi: u32`, `lo: u64`),
KoalaBear parameters, without panicking.
-/
theorem kb_monty_reduce_u128_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (lo : Std.U64) (hi : Std.U32) :
    kb_monty_reduce_u128_identity_spec inst lo hi := by
  unfold kb_monty_reduce_u128_identity_spec
  step as ⟨hs, hhs⟩
  have hhi : hi.val < 2^32 := by have := hi.hBounds; rwa [UScalarTy.U32_numBits_eq] at this
  have hlo : lo.val < 2^64 := by have := lo.hBounds; rwa [UScalarTy.U64_numBits_eq] at this
  have hxv : (hs ||| UScalar.cast UScalarTy.U128 lo).val = 2^64 * hi.val + lo.val := by
    rw [UScalar.val_or, hhs, U64.cast_U128_val_eq, U32.cast_U128_val_eq, u128_size',
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm,
      Nat.two_pow_add_eq_or_of_lt hlo]
  have hxb : (hs ||| UScalar.cast UScalarTy.U128 lo).val < 2^96 := by
    rw [hxv]; omega
  apply spec_bind (monty_reduce_u128_spec inst h_params _ hxb)
  intro r hr
  rw [spec_ok]
  exact hr.2

end Benchmark.Cases.Plonky3.Monty31Utils
