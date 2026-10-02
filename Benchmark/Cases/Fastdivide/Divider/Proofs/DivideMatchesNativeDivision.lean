import Benchmark.Cases.Fastdivide.Divider.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

/-- The high half of a 64x64-bit product fits in 64 bits. -/
theorem mul_div_lt (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : a * b / 2^64 < 2^64 := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  exact Nat.mul_lt_mul'' ha hb

/-- `mulhi(a, b) ≤ b` when `a < 2^64`. -/
theorem mul_div_le (a b : Nat) (ha : a < 2^64) : a * b / 2^64 ≤ b := by
  apply Nat.div_le_of_le_mul
  exact Nat.mul_le_mul_right _ ha.le

/-- Round-up division lemma (the core of the libdivide correctness argument):
if `M * d = N + e` and `e * n < N`, then `M * n / N = n / d`. -/
theorem roundup (N M d e n : ℕ) (hd : 0 < d) (hM : M * d = N + e) (hen : e * n < N) :
    M * n / N = n / d := by
  have hN : 0 < N := by omega
  apply Nat.div_eq_of_lt_le
  · -- (n/d) * N ≤ M * n
    have h1 : n / d * N ≤ n / d * (M * d) := Nat.mul_le_mul_left _ (by omega)
    have h2 : d * (n / d) ≤ n := Nat.mul_div_le n d
    calc n / d * N ≤ n / d * (M * d) := h1
      _ = M * (d * (n / d)) := by ring
      _ ≤ M * n := Nat.mul_le_mul_left _ h2
  · -- M * n < (n/d + 1) * N
    have h3 : n < d * (n / d + 1) := by
      have := Nat.lt_mul_div_succ n hd
      simpa using this
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    calc d * (M * n) = n * N + e * n := by
          rw [show d * (M * n) = n * (M * d) by ring, hM]; ring
      _ < n * N + N := by omega
      _ = (n + 1) * N := by ring
      _ ≤ d * (n / d + 1) * N := Nat.mul_le_mul_right _ h3
      _ = (n / d + 1) * N * d := by ring
      _ = _ := by ring

/-- In the `Fast` path the magic number `2^(64+k)/d + 1` fits in a `u64` without overflow. -/
theorem fast_bound (K d : ℕ) (hKd : K < d) (hK : K ≤ 2^63) : 2^64 * K / d + 2 ≤ 2^64 := by
  have hd : 0 < d := by omega
  have : 2^64 * K / d < 2^64 - 1 := by
    rw [Nat.div_lt_iff_lt_mul hd]; omega
  omega

/-- Arithmetic correctness of the `Fast` path, with `K = 2^k < d` and
`e = d - 2^(64+k) mod d < K`. -/
theorem fast_arith (K d n : ℕ) (hKd : K < d) (hn : n < 2^64)
    (he : d - (2^64 * K) % d < K) :
    ((2^64 * K) / d + 1) * n / 2^64 / K = n / d := by
  have hd : 0 < d := by omega
  rw [Nat.div_div_eq_div_mul]
  apply roundup (2^64 * K) _ d (d - (2^64 * K) % d) n hd
  · have h1 := Nat.div_add_mod' (2^64 * K) d
    have h2 := Nat.mod_lt (2^64 * K) hd
    rw [Nat.add_mul, one_mul]
    generalize 2 ^ 64 * K / d * d = A at *
    omega
  · calc (d - (2^64 * K) % d) * n < K * 2^64 := Nat.mul_lt_mul'' he hn
      _ = 2^64 * K := by ring

/-- The 65-bit magic number of the `General` path lies in `[2^64, 2^65)`. -/
theorem general_m_bounds (K d : ℕ) (hKd : K < d) (hd2 : d < 2 * K) (hK63 : K ≤ 2^63) :
    2^64 ≤ 2 + (2^64 * K + (2^64 * K - d)) / d ∧ 2 + (2^64 * K + (2^64 * K - d)) / d < 2^65 := by
  have hd : 0 < d := by omega
  have hE : 2^64 * K + (2^64 * K - d) = 2^65 * K - d := by omega
  rw [hE]
  constructor
  · have : 2^64 - 2 ≤ (2^65 * K - d) / d := by
      rw [Nat.le_div_iff_mul_le hd]; omega
    omega
  · have : (2^65 * K - d) / d < 2^65 - 2 := by
      rw [Nat.div_lt_iff_lt_mul hd]; omega
    omega

/-- Arithmetic correctness of the `General` path (65-bit magic number `2^64 + magic_low`),
with `K = 2^k < d < 2K`. -/
theorem general_arith (K d n : ℕ) (hKd : K < d) (hd2 : d < 2 * K) (hK63 : K ≤ 2^63)
    (hn : n < 2^64) :
    ((n - (2 + (2^64 * K + (2^64 * K - d)) / d) % 2^64 * n / 2^64) / 2
      + (2 + (2^64 * K + (2^64 * K - d)) / d) % 2^64 * n / 2^64) / K = n / d := by
  have hd : 0 < d := by omega
  have hE : 2^64 * K + (2^64 * K - d) = 2^65 * K - d := by omega
  rw [hE]
  generalize hm : 2 + (2^65 * K - d) / d = m
  -- bounds on m
  have hm1 : 2^64 ≤ m := by
    have : 2^64 - 2 ≤ (2^65 * K - d) / d := by
      rw [Nat.le_div_iff_mul_le hd]; omega
    omega
  have hm2 : m < 2^65 := by
    have : (2^65 * K - d) / d < 2^65 - 2 := by
      rw [Nat.div_lt_iff_lt_mul hd]; omega
    omega
  have hmod : m % 2^64 = m - 2^64 := by omega
  rw [hmod]
  -- key identity: m * d = 2^65 * K + e'
  have hkey : m * n / (2^65 * K) = n / d := by
    apply roundup (2^65 * K) m d (d - (2^65 * K - d) % d) n hd
    · have h1 := Nat.div_add_mod' (2^65 * K - d) d
      have h2 := Nat.mod_lt (2^65 * K - d) hd
      rw [← hm, Nat.add_mul]
      generalize (2 ^ 65 * K - d) / d * d = A at *
      omega
    · calc (d - (2^65 * K - d) % d) * n < (2 * K) * 2^64 :=
            Nat.mul_lt_mul'' (by omega) hn
        _ = 2^65 * K := by ring
  -- q = m * n / 2^64 - n
  have hq : (m - 2^64) * n / 2^64 = m * n / 2^64 - n := by
    rw [Nat.sub_mul, Nat.sub_mul_div]
  have hq2 : n ≤ m * n / 2^64 := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc n * 2^64 = 2^64 * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right _ hm1
  have hq3 : m * n / 2^64 ≤ 2 * n := by
    apply Nat.div_le_of_le_mul
    calc m * n ≤ 2^65 * n := Nat.mul_le_mul_right _ hm2.le
      _ = 2^64 * (2 * n) := by ring
  rw [hq]
  have h5 : (n - (m * n / 2 ^ 64 - n)) / 2 + (m * n / 2 ^ 64 - n) = m * n / 2^64 / 2 := by
    omega
  rw [h5, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← hkey]
  congr 1
  ring

/-- A non-power of two never divides a power of two. -/
theorem rem_ne_zero (d j : ℕ) (hnp : ¬ d.isPowerOfTwo) : 2^j % d ≠ 0 := by
  intro h0
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.dvd_of_mod_eq_zero h0)
  exact hnp ⟨i, hi⟩

/-- `⌊log₂ d⌋ < 64` for any `u64`. -/
theorem log_lt (d : Std.U64) : Nat.log 2 d.val < 64 := by
  have := d.hBounds
  rcases Nat.eq_zero_or_pos d.val with h | h
  · simp [h]
  · exact Nat.log_lt_of_lt_pow (by omega) (by simpa using this)

/-- Value of the Aeneas `leading_zeros` model on a non-zero `u64`. -/
theorem lz_val (d : Std.U64) (h : d.val ≠ 0) :
    (Aeneas.Std.core.num.U64.leading_zeros d).val = 63 - Nat.log 2 d.val := by
  unfold Aeneas.Std.core.num.U64.leading_zeros Aeneas.Std.BitVec.leadingZeros
  have h1 : d.bv ≠ 0 := by
    intro h2; apply h; simp [UScalar.val, h2]
  have h2 := log_lt d
  simp only [h1, if_false]
  change (BitVec.ofNat 32 (64 - Nat.log 2 d.val - 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  omega

/-- `floor_log2 d` never panics for `d ≠ 0` and returns `⌊log₂ d⌋`. -/
@[local step]
theorem floor_log2_spec (d : Std.U64) (h : d.val ≠ 0) :
    floor_log2 d ⦃ r => r.val = Nat.log 2 d.val ⦄ := by
  unfold floor_log2 CoreModels.core.num.U64.leading_zeros
    CoreModels.rust_primitives.arithmetic.leading_zeros_u64
  have h1 := lz_val d h
  have h2 := log_lt d
  have h3 : (UScalar.cast UScalarTy.U8 (Aeneas.Std.core.num.U64.leading_zeros d)).val =
      63 - Nat.log 2 d.val := by
    rw [UScalar.cast_val_eq, h1]; simp; omega
  step*

/-- The core-models `is_power_of_two` agrees with `Nat.isPowerOfTwo`. -/
@[local step]
theorem is_pow2_spec (d : Std.U64) (h : d.val ≠ 0) :
    CoreModels.core.num.U64.is_power_of_two d ⦃ b => (b = true ↔ d.val.isPowerOfTwo) ⦄ := by
  unfold CoreModels.core.num.U64.is_power_of_two
  step*
  rw [← Nat.and_sub_one_eq_zero_iff_isPowerOfTwo h, ← i_post1, ← UScalar.val_and, ← i1_post1]
  simp only [decide_eq_true_eq]
  rw [UScalar.eq_equiv]
  simp

/-- `libdivide_mullhi_u64 x y` never panics and returns the high 64 bits of `x * y`. -/
@[local step]
theorem mullhi_spec (x y : Std.U64) :
    libdivide_mullhi_u64 x y ⦃ r => r.val = x.val * y.val / 2^64 ⦄ := by
  unfold libdivide_mullhi_u64
  step*
  rw [UScalar.cast_val_eq, i1_post1, Nat.shiftRight_eq_div_pow, i_post, xl_post, yl_post,
    U64.cast_U128_val_eq, U64.cast_U128_val_eq]
  apply Nat.mod_eq_of_lt
  exact mul_div_lt _ _ x.hBounds y.hBounds

/-- Semantics of `divide` on the `BitShift` variant. -/
theorem divide_bitshift_spec (s : Std.U8) (n : Std.U64) (hs : s.val < 64) :
    DividerU64.divide (DividerU64.BitShift s) n ⦃ r => r.val = n.val / 2^s.val ⦄ := by
  unfold DividerU64.divide
  step*
  rw [r_post1, Nat.shiftRight_eq_div_pow]

/-- Semantics of `divide` on the `Fast` variant. -/
theorem divide_fast_spec (m : Std.U64) (s : Std.U8) (n : Std.U64) (hs : s.val < 64) :
    DividerU64.divide (DividerU64.Fast m s) n ⦃ r => r.val = m.val * n.val / 2^64 / 2^s.val ⦄ := by
  unfold DividerU64.divide
  step*
  rw [r_post1, Nat.shiftRight_eq_div_pow, i_post]

/-- Semantics of `divide` on the `General` variant (no panic, no wrap-around). -/
theorem divide_general_spec (m : Std.U64) (s : Std.U8) (n : Std.U64) (hs : s.val < 64) :
    DividerU64.divide (DividerU64.General m s) n ⦃ r =>
      r.val = ((n.val - m.val * n.val / 2^64) / 2 + m.val * n.val / 2^64) / 2^s.val ⦄ := by
  unfold DividerU64.divide
  simp only [CoreModels.core.num.U64.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u64]
  have hq := mul_div_le m.val n.val m.hBounds
  have hn := n.hBounds
  step*
  rw [r_post1, Nat.shiftRight_eq_div_pow, U64.wrapping_add_val_eq, i1_post1,
    Nat.shiftRight_eq_div_pow, i_post1, q_post]
  have hsz : UScalar.size .U64 = 2^64 := by simp [U64.size, U64.numBits]
  rw [hsz, Nat.mod_eq_of_lt (by simp at hn; omega)]

/-- A divider is correct for `d` if dividing any `n` with it never panics and yields `n / d`. -/
def DividerCorrect (dv : DividerU64) (d : Nat) : Prop :=
  ∀ n : Std.U64, DividerU64.divide dv n ⦃ r => r.val = n.val / d ⦄

/-- `power_of_2_division` either returns a correct `BitShift` divider or `None` for
non-powers of two. -/
theorem power_of_2_division_spec (d : Std.U64) (h : d.val ≠ 0) :
    DividerU64.power_of_2_division d ⦃ o =>
      (o = core.option.Option.None ∧ ¬ d.val.isPowerOfTwo) ∨
      (∃ dv, o = core.option.Option.Some dv ∧ DividerCorrect dv d.val) ⦄ := by
  unfold DividerU64.power_of_2_division
  step*
  right
  refine ⟨_, rfl, fun n => ?_⟩
  obtain ⟨j, hj⟩ := b_post.mp ‹_›
  have hlog : Nat.log 2 d.val = j := by rw [hj, Nat.log_pow (by norm_num)]
  apply spec_mono (divide_bitshift_spec i n (by have := log_lt d; omega))
  intro r hr
  rw [hr, i_post, hlog, hj]

/-- For a non-power of two, `fast_path` never panics (all asserts hold, no overflow)
and, when it returns a divider, that divider is correct. -/
theorem fast_path_spec (d : Std.U64) (h : d.val ≠ 0) (hnp : ¬ d.val.isPowerOfTwo) :
    DividerU64.fast_path d ⦃ o =>
      o = core.option.Option.None ∨
      (∃ dv, o = core.option.Option.Some dv ∧ DividerCorrect dv d.val) ⦄ := by
  unfold DividerU64.fast_path
  have hlog := log_lt d
  have hK1 : 2^(Nat.log 2 d.val) ≤ d.val := Nat.pow_log_le_self 2 h
  have hK2 : d.val < 2^(Nat.log 2 d.val + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hK3 : 2^(Nat.log 2 d.val) ≠ d.val := fun e => hnp ⟨_, e.symm⟩
  have hd64 : d.val < 2^64 := by simpa using d.hBounds
  generalize hk : Nat.log 2 d.val = k at *
  have hKpos : 0 < 2^k := by positivity
  have hK63 : 2^k ≤ 2^63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : 2^(k+64) = 2^64 * 2^k := by rw [pow_add, mul_comm]
  have hN128 : 2^(k+64) < 2^128 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  step as ⟨b, hb⟩
  have hbf : ¬ (b = true) := fun e => hnp (hb.mp e)
  simp only [hbf, Bool.false_eq_true, ↓reduceIte]
  step as ⟨fl, hfl⟩
  step as ⟨i, hi⟩
  step as ⟨u, hu1, hu2, hu3⟩
  rw [hk] at hfl
  have hs128 : U128.size = 2^128 := by simp [U128.size, U128.numBits]
  have hu : u.val = 2^(k+64) := by
    rw [hu1, Nat.shiftLeft_eq, one_mul, hi, hfl, hs128, Nat.mod_eq_of_lt hN128]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = d.val := by rw [hi1]; simp
  step as ⟨pm, hpm⟩
  have hpmv : pm.val = 2^(k+64) / d.val := by rw [hpm, hu, hi1v]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = d.val := by rw [hi2]; simp
  have hmul : pm.val * d.val ≤ 2^(k+64) := by rw [hpmv]; exact Nat.div_mul_le_self _ _
  have hmul2 : pm.val * i2.val ≤ U128.max := by rw [hi2v, U128.max_eq]; omega
  step as ⟨i3, hi3⟩
  have hi3u : i3.val ≤ u.val := by rw [hi3, hi2v, hu]; exact hmul
  step as ⟨i4, hi4⟩
  have hdm := Nat.div_add_mod' (2^(k+64)) d.val
  have hmodlt := Nat.mod_lt (2^(k+64)) (Nat.pos_of_ne_zero h)
  have hi4v : i4.val = 2^(k+64) % d.val := by
    rw [hi4, hi3, hi2v, hu, hpmv]
    omega
  step as ⟨rem, hrem⟩
  have hremv : rem.val = 2^(k+64) % d.val := by
    rw [hrem, UScalar.cast_val_eq, hi4v]
    apply Nat.mod_eq_of_lt
    simp only [UScalarTy.U64_numBits_eq]
    omega
  have hrpos : 2^(k+64) % d.val ≠ 0 := rem_ne_zero _ _ hnp
  step
  step
  step as ⟨e, he⟩
  step as ⟨i5, hi5⟩
  have hs64 : U64.size = 2^64 := by simp [U64.size, U64.numBits]
  have hi5v : i5.val = 2^k := by
    rw [hi5, Nat.shiftLeft_eq, one_mul, hfl, hs64, Nat.mod_eq_of_lt (by omega)]
  split
  · left; rfl
  · rename_i hlt
    have hlt' : e.val < 2^k := by
      rw [← hi5v]; simpa using hlt
    have hb2 := fast_bound (2^k) d.val (by omega) (by omega)
    step as ⟨i6, hi6⟩
    have hi6v : i6.val = 2^(k+64) / d.val := by
      rw [hi6, UScalar.cast_val_eq, hpmv, hN]
      apply Nat.mod_eq_of_lt
      simp only [UScalarTy.U64_numBits_eq]
      omega
    have hi6b : i6.val + (1#u64).val ≤ U64.max := by
      have h1 : (1#u64).val = 1 := by simp
      rw [hi6v, hN, U64.max_eq, h1]; omega
    step as ⟨i7, hi7⟩
    right
    refine ⟨_, rfl, fun n => ?_⟩
    apply spec_mono (divide_fast_spec i7 fl n (by omega))
    intro r hr
    rw [hr, hi7, hi6v, hfl, hN]
    apply fast_arith (2^k) d.val n.val (by omega) (by simpa using n.hBounds)
    rw [← hN, ← hremv]
    omega

/-- For a non-power of two, `general_path` never panics and returns a correct divider. -/
theorem general_path_spec (d : Std.U64) (h : d.val ≠ 0) (hnp : ¬ d.val.isPowerOfTwo) :
    DividerU64.general_path d ⦃ dv => DividerCorrect dv d.val ⦄ := by
  unfold DividerU64.general_path CoreModels.core.num.U64.leading_zeros
    CoreModels.rust_primitives.arithmetic.leading_zeros_u64
  have hlz := lz_val d h
  have hlog := log_lt d
  have hK1 : 2^(Nat.log 2 d.val) ≤ d.val := Nat.pow_log_le_self 2 h
  have hK2 : d.val < 2^(Nat.log 2 d.val + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hK3 : 2^(Nat.log 2 d.val) ≠ d.val := fun e => hnp ⟨_, e.symm⟩
  have hd64 : d.val < 2^64 := by simpa using d.hBounds
  generalize hk : Nat.log 2 d.val = k at *
  have hKpos : 0 < 2^k := by positivity
  have hK63 : 2^k ≤ 2^63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : 2^(k+64) = 2^64 * 2^k := by rw [pow_add, mul_comm]
  have hN127 : 2^(k+64) ≤ 2^127 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2' : d.val < 2 * 2^k := by rw [pow_succ] at hK2; omega
  have hs128 : U128.size = 2^128 := by simp [U128.size, U128.numBits]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = 63 - k := by
    rw [hi1, UScalar.cast_val_eq, hlz]; simp; omega
  step as ⟨p, hp⟩
  step as ⟨i2, hi2⟩
  step as ⟨e, he1, he2, he3⟩
  have hev : e.val = 2^(k+64) := by
    have : i2.val = k + 64 := by rw [hi2, hp, hi1v]; omega
    rw [he1, Nat.shiftLeft_eq, one_mul, this, hs128,
      Nat.mod_eq_of_lt (lt_of_le_of_lt hN127 (by norm_num))]
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = d.val := by rw [hi3]; simp
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = 2^(k+64) - d.val := by rw [hi4, hev, hi3v]
  have hadd : e.val + i4.val ≤ U128.max := by rw [hev, hi4v, U128.max_eq]; omega
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = d.val := by rw [hi6]; simp
  step as ⟨i7, hi7⟩
  have hi7v : i7.val = (2^64 * 2^k + (2^64 * 2^k - d.val)) / d.val := by
    rw [hi7, hi5, hev, hi4v, hi6v, hN]
  have hmb := general_m_bounds (2^k) d.val (by omega) hK2' hK63
  have hadd2 : (2#u128).val + i7.val ≤ U128.max := by
    have h2 : (2#u128).val = 2 := by simp
    rw [hi7v, U128.max_eq, h2]; omega
  step as ⟨m, hm⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  have hi9v : i9.val = k := by rw [hi9, hp, hi1v]; omega
  have hi8v : i8.val = (2 + (2^64 * 2^k + (2^64 * 2^k - d.val)) / d.val) % 2^64 := by
    rw [hi8, UScalar.cast_val_eq, hm, hi7v]
    simp
  intro n
  apply spec_mono (divide_general_spec i8 i9 n (by omega))
  intro r hr
  rw [hr, hi8v, hi9v]
  exact general_arith (2^k) d.val n.val (by omega) hK2' hK63 (by simpa using n.hBounds)

/-- `divide_by d` never panics for `d ≠ 0` and returns a correct divider. -/
theorem divide_by_spec (d : Std.U64) (h : d.val ≠ 0) :
    DividerU64.divide_by d ⦃ dv => DividerCorrect dv d.val ⦄ := by
  unfold DividerU64.divide_by
  step
  have ho := power_of_2_division_spec d h
  step as ⟨o, ho⟩
  rcases ho with ⟨ho, hnp⟩ | ⟨dv, ho, hdv⟩
  · simp only [ho, CoreModels.core.option.Option.or_else,
      DividerU64.divide_by.closure.Insts.CoreOpsFunctionFnOnceTupleOptionDividerU64.call_once]
    have ho1 := fast_path_spec d h hnp
    step as ⟨o1, ho1⟩
    rcases ho1 with ho1 | ⟨dv, ho1, hdv⟩
    · simp only [ho1, CoreModels.core.option.Option.unwrap_or_else,
        DividerU64.divide_by.closure_1.Insts.CoreOpsFunctionFnOnceTupleDividerU64.call_once]
      exact general_path_spec d h hnp
    · simp only [ho1, CoreModels.core.option.Option.unwrap_or_else, spec_ok]
      exact hdv
  · simp only [ho, CoreModels.core.option.Option.or_else,
      CoreModels.core.option.Option.unwrap_or_else, bind_tc_ok, spec_ok]
    exact hdv

/--
For every divisor `d` and dividend `n` drawn from the property-test
strategies, precomputing `DividerU64::divide_by(d)` and dividing `n` with it
never panics and returns exactly `n / d`.
-/
theorem divide_matches_native_division (n d : Std.U64)
    (h_n : n.val < 2^64 - 1)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 2^64 - 1) :
    divide_matches_native_division_spec n d := by
  have _ := h_n
  have _ := h_d_hi
  unfold divide_matches_native_division_spec
  apply spec_bind (divide_by_spec d (by omega))
  intro dv hdv
  exact hdv n

end Benchmark.Cases.Fastdivide.Divider
