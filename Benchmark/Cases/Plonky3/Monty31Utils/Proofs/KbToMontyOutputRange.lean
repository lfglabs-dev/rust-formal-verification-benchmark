import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

theorem u64_size' : U64.size = 2^64 := by simp [U64.size, U64.numBits]

theorem c_p64 : (UScalar.cast UScalarTy.U64 2130706433#u32).val = 2130706433 := rfl

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

/--
For every `u32`, `to_monty` (computing `((x as u64) << 32) % P`) never panics and lands in
`[0, P)` for the KoalaBear prime.
-/
theorem kb_to_monty_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U32) :
    kb_to_monty_output_range_spec inst x := by
  unfold kb_to_monty_output_range_spec
  apply spec_mono (to_monty_val inst h_params x)
  intro r hr
  rw [hr]; exact Nat.mod_lt _ (by norm_num)

end Benchmark.Cases.Plonky3.Monty31Utils
