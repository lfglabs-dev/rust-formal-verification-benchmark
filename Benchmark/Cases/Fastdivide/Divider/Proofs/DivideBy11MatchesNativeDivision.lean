import Benchmark.Cases.Fastdivide.Divider.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

theorem d11_mul_div_lt (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : a * b / 2^64 < 2^64 := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  exact Nat.mul_lt_mul'' ha hb

/-- `libdivide_mullhi_u64 x y` never panics and returns the high 64 bits of `x * y`. -/
@[local step]
theorem d11_mullhi_spec (x y : Std.U64) :
    libdivide_mullhi_u64 x y ⦃ r => r.val = x.val * y.val / 2^64 ⦄ := by
  unfold libdivide_mullhi_u64
  step*
  rw [UScalar.cast_val_eq, i1_post1, Nat.shiftRight_eq_div_pow, i_post, xl_post, yl_post,
    U64.cast_U128_val_eq, U64.cast_U128_val_eq]
  apply Nat.mod_eq_of_lt
  exact d11_mul_div_lt _ _ x.hBounds y.hBounds

/-- Semantics of `divide` on the `Fast` variant. -/
theorem d11_divide_fast_spec (m : Std.U64) (s : Std.U8) (n : Std.U64) (hs : s.val < 64) :
    DividerU64.divide (DividerU64.Fast m s) n ⦃ r => r.val = m.val * n.val / 2^64 / 2^s.val ⦄ := by
  unfold DividerU64.divide
  step*
  rw [r_post1, Nat.shiftRight_eq_div_pow, i_post]

/-- `divide_by 11` evaluates (by kernel computation) to the `Fast` divider. -/
theorem d11_divide_by_eq :
    DividerU64.divide_by 11#u64 = ok (DividerU64.Fast 13415813871788764812#u64 3#u8) := by
  rfl

/--
Dividing by the precomputed `DividerU64::divide_by(11)` (the 64-bit-magic
`Fast` path) never panics and agrees with `n / 11`.
-/
theorem divide_by_11_matches_native_division (n : Std.U64)
    (h_n : n.val < 2^64 - 1) :
    divide_by_11_matches_native_division_spec n := by
  unfold divide_by_11_matches_native_division_spec
  rw [d11_divide_by_eq, bind_tc_ok]
  apply spec_mono (d11_divide_fast_spec _ _ n (by simp))
  intro r hr
  rw [hr]
  simp
  omega

end Benchmark.Cases.Fastdivide.Divider
