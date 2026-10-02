import Benchmark.Cases.Ruint.GcdMatrix.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.GcdMatrix

abbrev Mat := Std.U64 × Std.U64 × Std.U64 × Std.U64 × Bool

/-- What `apply_u128` needs: the matrix maps `(a, b)` to `(gcd a b, 0)`. -/
def MatPost (a b : Nat) (m : Mat) : Prop :=
  if m.2.2.2.2 then
    m.1.val * a = m.2.1.val * b + Nat.gcd a b ∧ m.2.2.2.1.val * b = m.2.2.1.val * a + 0
  else
    m.2.1.val * b = m.1.val * a + Nat.gcd a b ∧ m.2.2.1.val * a = m.2.2.2.1.val * b + 0

/-- Loop invariant of `from_u64`. -/
def Inv (a b : Nat) (s : Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64) : Prop :=
  0 < s.2.1.val ∧
  a = s.2.2.2.2.2.val * s.1.val + s.2.2.2.1.val * s.2.1.val ∧
  b = s.2.2.2.2.1.val * s.1.val + s.2.2.1.val * s.2.1.val ∧
  s.2.2.1.val * s.2.2.2.2.2.val = s.2.2.2.1.val * s.2.2.2.2.1.val + 1 ∧
  Nat.gcd s.1.val s.2.1.val = Nat.gcd a b

theorem body_spec (a b : Nat) (r0 r1 q00 q01 q10 q11 : Std.U64)
    (hA : a < 2^64) (hB : b < 2^64) (hinv : Inv a b (r0, r1, q00, q01, q10, q11)) :
    algorithms.gcd.matrix.Matrix.from_u64_loop.body r0 r1 q00 q01 q10 q11
    ⦃ r => match r with
      | .done m => MatPost a b m
      | .cont s' => Inv a b s' ∧ s'.2.1.val < r1.val ⦄ := by
  obtain ⟨hr1, ha, hb, hdet, hg⟩ := hinv
  simp only at ha hb hdet hg hr1 ⊢
  -- first half-step facts
  have hdiv : r0.val % r1.val + r0.val / r1.val * r1.val = r0.val := by
    have := Nat.mod_add_div r0.val r1.val; rw [Nat.mul_comm] at this; omega
  have hM : r0.val % r1.val < r1.val := Nat.mod_lt _ hr1
  have KB : b = q10.val * (r0.val % r1.val) + (q00.val + r0.val / r1.val * q10.val) * r1.val := by
    rw [hb]; conv_lhs => rw [← hdiv]
    ring
  have KA : a = q11.val * (r0.val % r1.val) + (q01.val + r0.val / r1.val * q11.val) * r1.val := by
    rw [ha]; conv_lhs => rw [← hdiv]
    ring
  have hB1 : q00.val + r0.val / r1.val * q10.val ≤ b := by
    have := Nat.le_mul_of_pos_right (q00.val + r0.val / r1.val * q10.val) hr1
    omega
  have hA1 : q01.val + r0.val / r1.val * q11.val ≤ a := by
    have := Nat.le_mul_of_pos_right (q01.val + r0.val / r1.val * q11.val) hr1
    omega
  have hr0 : r0.val < 2^64 := by have := r0.hBounds; simpa [UScalarTy.numBits] using this
  have hmax : U64.max = 2^64 - 1 := by simp [U64.max_eq]
  unfold algorithms.gcd.matrix.Matrix.from_u64_loop.body
  step as ⟨q, q_post⟩
  have : q.val * r1.val ≤ U64.max := by rw [q_post, hmax]; omega
  step as ⟨i, i_post⟩
  have : i.val ≤ r0.val := by rw [i_post, q_post]; omega
  step as ⟨r01, r01_post, r01_post'⟩
  have hr01 : r01.val = r0.val % r1.val := by rw [r01_post, i_post, q_post]; omega
  have : q.val * q10.val ≤ U64.max := by rw [q_post, hmax]; omega
  step as ⟨i1, i1_post⟩
  have : q00.val + i1.val ≤ U64.max := by rw [i1_post, q_post, hmax]; omega
  step as ⟨q001, q001_post⟩
  have : q.val * q11.val ≤ U64.max := by rw [q_post, hmax]; omega
  step as ⟨i2, i2_post⟩
  have : q01.val + i2.val ≤ U64.max := by rw [i2_post, q_post, hmax]; omega
  step as ⟨q011, q011_post⟩
  have e001 : q001.val = q00.val + r0.val / r1.val * q10.val := by rw [q001_post, i1_post, q_post]
  have e011 : q011.val = q01.val + r0.val / r1.val * q11.val := by rw [q011_post, i2_post, q_post]
  -- half-state invariant
  have hbH : b = q10.val * r01.val + q001.val * r1.val := by rw [KB, hr01, e001]
  have haH : a = q11.val * r01.val + q011.val * r1.val := by rw [KA, hr01, e011]
  have hdetH : q001.val * q11.val = q011.val * q10.val + 1 := by
    rw [e001, e011, Nat.add_mul, Nat.add_mul, hdet]; ring
  have hgH : Nat.gcd r01.val r1.val = Nat.gcd a b := by
    rw [hr01, ← Nat.gcd_rec, Nat.gcd_comm, hg]
  split
  · -- r0 % r1 = 0: return (q10, q11, q001, q011, false)
    rename_i h0
    have h0' : r01.val = 0 := by simp [h0]
    simp only [WP.spec_ok, MatPost]
    rw [h0'] at hbH haH hgH
    simp only [Nat.mul_zero, Nat.zero_add, Nat.gcd_zero_left] at hbH haH hgH
    refine ⟨?_, ?_⟩
    · rw [← hgH, hbH, haH]
      calc q11.val * (q001.val * r1.val) = (q001.val * q11.val) * r1.val := by ring
        _ = (q011.val * q10.val + 1) * r1.val := by rw [hdetH]
        _ = q10.val * (q011.val * r1.val) + r1.val := by ring
    · rw [hbH, haH]; ring
  · rename_i h0
    have h0' : r01.val ≠ 0 := by intro h; apply h0; scalar_tac
    have hr01pos : 0 < r01.val := Nat.pos_of_ne_zero h0'
    -- second half-step facts
    have hdiv2 : r1.val % r01.val + r1.val / r01.val * r01.val = r1.val := by
      have := Nat.mod_add_div r1.val r01.val; rw [Nat.mul_comm] at this; omega
    have hM2 : r1.val % r01.val < r01.val := Nat.mod_lt _ hr01pos
    have KB2 : b = (q10.val + r1.val / r01.val * q001.val) * r01.val + q001.val * (r1.val % r01.val) := by
      rw [hbH]; conv_lhs => rw [← hdiv2]
      ring
    have KA2 : a = (q11.val + r1.val / r01.val * q011.val) * r01.val + q011.val * (r1.val % r01.val) := by
      rw [haH]; conv_lhs => rw [← hdiv2]
      ring
    have hB2 : q10.val + r1.val / r01.val * q001.val ≤ b := by
      have := Nat.le_mul_of_pos_right (q10.val + r1.val / r01.val * q001.val) hr01pos
      omega
    have hA2 : q11.val + r1.val / r01.val * q011.val ≤ a := by
      have := Nat.le_mul_of_pos_right (q11.val + r1.val / r01.val * q011.val) hr01pos
      omega
    have hr1b : r1.val < 2^64 := by have := r1.hBounds; simpa [UScalarTy.numBits] using this
    step as ⟨q1, q1_post⟩
    have : q1.val * r01.val ≤ U64.max := by rw [q1_post, hmax]; omega
    step as ⟨i3, i3_post⟩
    have : i3.val ≤ r1.val := by rw [i3_post, q1_post]; omega
    step as ⟨r11, r11_post, r11_post'⟩
    have hr11 : r11.val = r1.val % r01.val := by rw [r11_post, i3_post, q1_post]; omega
    have : q1.val * q001.val ≤ U64.max := by rw [q1_post, hmax]; omega
    step as ⟨i4, i4_post⟩
    have : q10.val + i4.val ≤ U64.max := by rw [i4_post, q1_post, hmax]; omega
    step as ⟨q101, q101_post⟩
    have : q1.val * q011.val ≤ U64.max := by rw [q1_post, hmax]; omega
    step as ⟨i5, i5_post⟩
    have : q11.val + i5.val ≤ U64.max := by rw [i5_post, q1_post, hmax]; omega
    step as ⟨q111, q111_post⟩
    have e101 : q101.val = q10.val + r1.val / r01.val * q001.val := by rw [q101_post, i4_post, q1_post]
    have e111 : q111.val = q11.val + r1.val / r01.val * q011.val := by rw [q111_post, i5_post, q1_post]
    have hbF : b = q101.val * r01.val + q001.val * r11.val := by rw [KB2, hr11, e101]
    have haF : a = q111.val * r01.val + q011.val * r11.val := by rw [KA2, hr11, e111]
    have hdetF : q001.val * q111.val = q011.val * q101.val + 1 := by
      rw [e101, e111, Nat.mul_add, Nat.mul_add, hdetH]; ring
    have hgF : Nat.gcd r01.val r11.val = Nat.gcd a b := by
      rw [hr11, Nat.gcd_comm, ← Nat.gcd_rec, hgH]
    split
    · rename_i h1
      have h1' : r11.val = 0 := by simp [h1]
      simp only [WP.spec_ok, MatPost]
      rw [h1'] at hbF haF hgF
      simp only [Nat.mul_zero, Nat.add_zero, Nat.gcd_zero_right] at hbF haF hgF
      refine ⟨?_, ?_⟩
      · rw [← hgF, hbF, haF]
        calc q001.val * (q111.val * r01.val) = (q001.val * q111.val) * r01.val := by ring
          _ = (q011.val * q101.val + 1) * r01.val := by rw [hdetF]
          _ = q011.val * (q101.val * r01.val) + r01.val := by ring
      · rw [hbF, haF]; ring
    · rename_i h1
      have h1' : r11.val ≠ 0 := by intro h; apply h1; scalar_tac
      simp only [WP.spec_ok, Inv]
      refine ⟨⟨Nat.pos_of_ne_zero h1', ?_, ?_, ?_, hgF⟩, ?_⟩
      · exact haF
      · exact hbF
      · rw [hdetF]
      · rw [hr11, hr01]
        calc r1.val % (r0.val % r1.val) < r0.val % r1.val := Nat.mod_lt _ (by omega)
          _ < r1.val := hM

theorem u128_size : UScalar.size .U128 = 2^128 := by simp [U128.size, U128.numBits]

theorem mul_lt_128 (x y : Nat) (hx : x < 2^64) (hy : y < 2^64) : x * y < 2^128 := by
  have : x * y < 2^64 * 2^64 := Nat.mul_lt_mul'' hx hy
  simpa [← pow_add] using this

/-- `apply_u128` on the u128-casts of `a`, `b` computes `x*a - y*b` exactly
when the difference is non-negative. -/
theorem wmul_wsub (x a y b : Std.U64) (g : Nat) (h : x.val * a.val = y.val * b.val + g) :
    (Aeneas.Std.U128.wrapping_sub
      (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 x) (UScalar.cast .U128 a))
      (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 y) (UScalar.cast .U128 b))).val = g := by
  have hx := x.hBounds; have ha := a.hBounds; have hy := y.hBounds; have hb := b.hBounds
  simp only [U128.wrapping_sub_val_eq, U128.wrapping_mul_val_eq, U64.cast_U128_val_eq, u128_size]
  have h1 := mul_lt_128 x.val a.val (by simpa using hx) (by simpa using ha)
  have h2 := mul_lt_128 y.val b.val (by simpa using hy) (by simpa using hb)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  omega


theorem from_u64_post (a b : Std.U64) (hab : b.val ≤ a.val) :
    algorithms.gcd.matrix.Matrix.from_u64 a b ⦃ m => MatPost a.val b.val m ⦄ := by
  have hA : a.val < 2^64 := by have := a.hBounds; simpa [UScalarTy.numBits] using this
  have hB : b.val < 2^64 := by have := b.hBounds; simpa [UScalarTy.numBits] using this
  unfold algorithms.gcd.matrix.Matrix.from_u64
  step
  split
  · rename_i h0
    have h0' : b.val = 0 := by simp [h0]
    simp only [WP.spec_ok, MatPost, algorithms.gcd.matrix.Matrix.IDENTITY]
    simp [h0']
  · rename_i h0
    have h0' : b.val ≠ 0 := by intro h; apply h0; scalar_tac
    apply spec_bind (Pₘ := fun m => MatPost a.val b.val m)
    · unfold algorithms.gcd.matrix.Matrix.from_u64_loop
      apply loop.spec_decr_nat (fun s => s.2.1.val) (Inv a.val b.val)
      · intro s hs
        obtain ⟨r0, r1, q00, q01, q10, q11⟩ := s
        apply spec_mono (body_spec a.val b.val r0 r1 q00 q01 q10 q11 hA hB hs)
        intro r hr
        cases r <;> exact hr
      · simp only [Inv]
        refine ⟨Nat.pos_of_ne_zero h0', ?_, ?_, ?_, ?_⟩ <;> simp
    · intro m hm
      obtain ⟨m0, m1, m2, m3, sg⟩ := m
      simpa using hm


theorem apply_post (a b : Std.U64) (m : Mat) (h : MatPost a.val b.val m) :
    algorithms.gcd.matrix.Matrix.apply_u128 m (UScalar.cast .U128 a) (UScalar.cast .U128 b)
    ⦃ cd => cd.1.val = Nat.gcd a.val b.val ∧ cd.2.val = 0 ⦄ := by
  obtain ⟨m0, m1, m2, m3, sg⟩ := m
  unfold algorithms.gcd.matrix.Matrix.apply_u128
  cases sg
  · simp only [MatPost, Bool.false_eq_true, ↓reduceIte] at h
    simp only [core.num.U128.wrapping_mul,
      rust_primitives.arithmetic.wrapping_mul_u128, core.num.U128.wrapping_sub,
      rust_primitives.arithmetic.wrapping_sub_u128, bind_tc_ok, lift]
    exact ⟨wmul_wsub m1 b m0 a _ h.1, wmul_wsub m2 a m3 b 0 h.2⟩
  · simp only [MatPost, ↓reduceIte] at h
    simp only [core.num.U128.wrapping_mul,
      rust_primitives.arithmetic.wrapping_mul_u128, core.num.U128.wrapping_sub,
      rust_primitives.arithmetic.wrapping_sub_u128, bind_tc_ok, lift]
    exact ⟨wmul_wsub m0 a m1 b _ h.1, wmul_wsub m3 b m2 a 0 h.2⟩

/--
For all `a b : u64`, with `(a, b) := (max(a, b), min(a, b))`, the Lehmer
matrix `Matrix::from_u64(a, b)` (a full 64-bit extended Euclid run) never
panics, and applying it with `apply_u128` to `(a, b)` yields `(c, d)` with
`c >= d`, `c = gcd(a, b)` and `d = 0`.
-/
theorem from_u64_gcd (a b : Std.U64) :
    from_u64_gcd_spec a b := by
  unfold from_u64_gcd_spec
  generalize hhi : (if a.val ≤ b.val then b else a) = hi
  generalize hlo : (if a.val ≤ b.val then a else b) = lo
  have hle : lo.val ≤ hi.val := by
    rw [← hhi, ← hlo]; split <;> omega
  apply spec_bind (from_u64_post hi lo hle)
  intro m hm
  apply spec_mono (apply_post hi lo m hm)
  intro cd hcd
  refine ⟨?_, hcd.1, hcd.2⟩
  rw [hcd.2]; exact Nat.zero_le _

end Benchmark.Cases.Ruint.GcdMatrix
