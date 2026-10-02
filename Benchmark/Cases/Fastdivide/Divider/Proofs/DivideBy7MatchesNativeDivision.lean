import Benchmark.Cases.Fastdivide.Divider.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

theorem d7_mul_div_lt (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : a * b / 2^64 < 2^64 := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  exact Nat.mul_lt_mul'' ha hb

theorem d7_mul_div_le (a b : Nat) (ha : a < 2^64) : a * b / 2^64 ≤ b := by
  apply Nat.div_le_of_le_mul
  exact Nat.mul_le_mul_right _ ha.le

/-- `libdivide_mullhi_u64 x y` never panics and returns the high 64 bits of `x * y`. -/
@[local step]
theorem d7_mullhi_spec (x y : Std.U64) :
    libdivide_mullhi_u64 x y ⦃ r => r.val = x.val * y.val / 2^64 ⦄ := by
  unfold libdivide_mullhi_u64
  step*
  rw [UScalar.cast_val_eq, i1_post1, Nat.shiftRight_eq_div_pow, i_post, xl_post, yl_post,
    U64.cast_U128_val_eq, U64.cast_U128_val_eq]
  apply Nat.mod_eq_of_lt
  exact d7_mul_div_lt _ _ x.hBounds y.hBounds

/-- Semantics of `divide` on the `General` variant (no panic, no wrap-around). -/
theorem d7_divide_general_spec (m : Std.U64) (s : Std.U8) (n : Std.U64) (hs : s.val < 64) :
    DividerU64.divide (DividerU64.General m s) n ⦃ r =>
      r.val = ((n.val - m.val * n.val / 2^64) / 2 + m.val * n.val / 2^64) / 2^s.val ⦄ := by
  unfold DividerU64.divide
  simp only [CoreModels.core.num.U64.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u64]
  have hq := d7_mul_div_le m.val n.val m.hBounds
  have hn := n.hBounds
  step*
  rw [r_post1, Nat.shiftRight_eq_div_pow, U64.wrapping_add_val_eq, i1_post1,
    Nat.shiftRight_eq_div_pow, i_post1, q_post]
  have hsz : UScalar.size .U64 = 2^64 := by simp [U64.size, U64.numBits]
  rw [hsz, Nat.mod_eq_of_lt (by simp at hn; omega)]

/-- `divide_by 7` evaluates (by kernel computation) to the `General` divider. -/
theorem d7_divide_by_eq :
    DividerU64.divide_by 7#u64 = ok (DividerU64.General 2635249153387078803#u64 2#u8) := by
  rfl

/--
Dividing by the precomputed `DividerU64::divide_by(7)` (the 65-bit-magic
`General` path) never panics and agrees with `n / 7`.
-/
theorem divide_by_7_matches_native_division (n : Std.U64)
    (h_n : n.val < 2^64 - 1) :
    divide_by_7_matches_native_division_spec n := by
  unfold divide_by_7_matches_native_division_spec
  rw [d7_divide_by_eq, bind_tc_ok]
  apply spec_mono (d7_divide_general_spec _ _ n (by simp))
  intro r hr
  rw [hr]
  simp
  omega

end Benchmark.Cases.Fastdivide.Divider
