import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u64_size : UScalar.size UScalarTy.U64 = 2^64 := by simp [U64.size, U64.numBits]

theorem u32_size : UScalar.size UScalarTy.U32 = 2^32 := by simp [U32.size, U32.numBits]

theorem c_mu : (2281701377#u32).val = 2281701377 := rfl

theorem c_mask : (4294967295#u32).val = 4294967295 := rfl

theorem c_p : (2013265921#u32).val = 2013265921 := rfl

theorem c_zero : (0#u32).val = 0 := rfl

theorem c_p64 : (UScalar.cast UScalarTy.U64 2013265921#u32).val = 2013265921 := rfl

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

theorem bb_key (x : Nat) : x * 2281701377 % 2^32 * 2013265921 % 2^32 = x % 2^32 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_mod,
    show 2281701377 * 2013265921 % 2^32 = 1 by norm_num, Nat.mul_one, Nat.mod_mod]

theorem reduce_arith (x t u : Nat) (hx : x < 2^32 * 2013265921) (ht : t < 2^32)
    (hu : u = t * 2013265921) (hkey : u % 2^32 = x % 2^32) :
    ((2^64 - u + x) % 2^64 / 2^32 % 2^32
        + (if x < u then 2013265921 else 0)) % 2^32 < 2013265921 ∧
    ((2^64 - u + x) % 2^64 / 2^32 % 2^32
        + (if x < u then 2013265921 else 0)) % 2^32 * 2^32 % 2013265921
      = x % 2013265921 := by
  have hub : u < 2^32 * 2013265921 := by omega
  by_cases hxu : x < u
  · simp only [hxu, if_true]
    obtain ⟨k, hk⟩ : ∃ k, u = x + 2^32 * k := ⟨(u - x) / 2^32, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hkP : k < 2013265921 := by omega
    have h1 : (2^64 - u + x) % 2^64 = 2^64 - 2^32 * k := by omega
    have h2 : (2^64 - 2^32 * k) / 2^32 = 2^32 - k := by omega
    have hres : ((2^64 - u + x) % 2^64 / 2^32 % 2^32 + 2013265921) % 2^32 = 2013265921 - k := by
      rw [h1, h2]; omega
    rw [hres]
    refine ⟨by omega, ?_⟩
    omega
  · simp only [hxu, if_false]
    obtain ⟨k, hk⟩ : ∃ k, x = u + 2^32 * k := ⟨(x - u) / 2^32, by omega⟩
    have hkP : k < 2013265921 := by omega
    have h1 : (2^64 - u + x) % 2^64 = 2^32 * k := by omega
    have h2 : (2^32 * k) / 2^32 = k := by omega
    have hres : ((2^64 - u + x) % 2^64 / 2^32 % 2^32 + 0) % 2^32 = k := by
      rw [h1, h2]; omega
    rw [hres]
    refine ⟨hkP, ?_⟩
    omega

/-- The common tail of `monty_reduce` / `large_monty_reduce`. -/
theorem tail_spec (xc u : Std.U64) (t : Nat) (hxc : xc.val < 2^32 * 2013265921) (ht : t < 2^32)
    (hu : u.val = t * 2013265921) (hkey : u.val % 2^32 = xc.val % 2^32) :
    (do
      let (x_sub_u, over) ← core.num.U64.overflowing_sub xc u
      let i ← x_sub_u >>> 32#u32
      let corr ← if over = true then ok 2013265921#u32 else ok 0#u32
      core.num.U32.wrapping_add (UScalar.cast UScalarTy.U32 i) corr) ⦃ r =>
      r.val < 2013265921 ∧ r.val * 2^32 % 2013265921 = xc.val % 2013265921 ⦄ := by
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

theorem monty_reduce_spec {MP : Type} (inst : data_traits.MontyParameters MP) (h : BBParams inst)
    (x : Std.U64) (hx : x.val < 2^32 * 2013265921) :
    utils.monty_reduce inst x ⦃ r => r.val < 2013265921 ∧
      r.val * 2^32 % 2013265921 = x.val % 2013265921 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.monty_reduce
  simp only [hp, hb, hmu, hmask, mask_eq inst hb, bind_tc_ok, lift]
  unfold core.num.U64.wrapping_mul rust_primitives.arithmetic.wrapping_mul_u64
  simp only [bind_tc_ok]
  set t := (x.wrapping_mul (UScalar.cast UScalarTy.U64 2281701377#u32) &&&
    UScalar.cast UScalarTy.U64 4294967295#u32) with ht_def
  have htv : t.val = x.val * 2281701377 % 2^64 % 2^32 := by
    rw [ht_def, UScalar.val_and, U64.wrapping_mul_val_eq, U32.cast_U64_val_eq,
      U32.cast_U64_val_eq, u64_size, c_mu, c_mask]
    exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have htb : t.val < 2^32 := by rw [htv]; exact Nat.mod_lt _ (by norm_num)
  step as ⟨u, hu⟩
  have hkey : u.val % 2^32 = x.val % 2^32 := by
    rw [hu, c_p64, htv, Nat.mod_mod_of_dvd _ (by norm_num : 2^32 ∣ 2^64)]
    exact bb_key x.val
  exact tail_spec x u t.val hx htb (by rw [hu, c_p64]) hkey

/--
Montgomery reduction `monty_reduce` never panics on inputs below `P * 2^32` and returns a
canonical BabyBear value (`< P`).
-/
theorem bb_monty_reduce_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32) :
    bb_monty_reduce_output_range_spec inst x := by
  unfold bb_monty_reduce_output_range_spec
  apply spec_mono (monty_reduce_spec inst h_params x (by omega))
  intro r hr
  exact hr.1

end Benchmark.Cases.Plonky3.Monty31Utils
