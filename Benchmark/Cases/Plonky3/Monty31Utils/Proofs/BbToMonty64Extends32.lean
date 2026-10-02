import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u64_size' : U64.size = 2^64 := by simp [U64.size, U64.numBits]

theorem u128_size' : U128.size = 2^128 := by simp [U128.size, U128.numBits]

theorem c_p64 : (UScalar.cast UScalarTy.U64 2013265921#u32).val = 2013265921 := rfl

theorem to_monty_val {MP : Type} (inst : data_traits.MontyParameters MP) (h : BBParams inst)
    (x : Std.U32) :
    utils.to_monty inst x ⦃ r => r.val = x.val * 2^32 % 2013265921 ⦄ := by
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
  have h2 : x.val * 2^32 % 2013265921 < 2013265921 := Nat.mod_lt _ (by norm_num)
  omega

theorem to_monty_64_val {MP : Type} (inst : data_traits.MontyParameters MP) (h : BBParams inst)
    (x : Std.U64) :
    utils.to_monty_64 inst x ⦃ r => r.val = x.val * 2^32 % 2013265921 ⦄ := by
  obtain ⟨hp, hb, hmu, hmask⟩ := h
  unfold utils.to_monty_64
  simp only [hp, hb, bind_tc_ok, lift]
  step as ⟨i2, hi2⟩
  step as ⟨i5, hi5⟩
  have hx : x.val < 2^64 := x.hBounds
  have hc : (UScalar.cast UScalarTy.U128 2013265921#u32).val = 2013265921 := rfl
  rw [UScalar.cast_val_eq, hi5, hi2, U64.cast_U128_val_eq, hc, u128_size', Nat.shiftLeft_eq,
    UScalarTy.U32_numBits_eq]
  have h1 : x.val * 2^32 < 2^128 := by omega
  rw [Nat.mod_eq_of_lt h1]
  have h2 : x.val * 2^32 % 2013265921 < 2013265921 := Nat.mod_lt _ (by norm_num)
  omega

/--
The 64-bit Montgomery conversion `to_monty_64` (computing in `u128`) agrees with the 32-bit
`to_monty` (computing in `u64`) on every `u32` input, for the BabyBear parameters.
-/
theorem bb_to_monty_64_extends_32 {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U32) :
    bb_to_monty_64_extends_32_spec inst x := by
  unfold bb_to_monty_64_extends_32_spec
  apply spec_bind (to_monty_64_val inst h_params _)
  intro w hw
  apply spec_bind (to_monty_val inst h_params x)
  intro n hn
  rw [spec_ok, hw, hn, U32.cast_U64_val_eq]

end Benchmark.Cases.Plonky3.Monty31Utils
