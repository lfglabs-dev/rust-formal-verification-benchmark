import Benchmark.Cases.Ruint.GcdMatrix.Specs
import Mathlib.Tactic.LinearCombination

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.GcdMatrix

/-- High half of a packed cofactor word `k = u * 2^32 + v`. -/
def Uc (k : Nat) : Nat := k / 2^32
/-- Low half of a packed cofactor word. -/
def Vc (k : Nat) : Nat := k % 2^32

/-- Consecutive Euclid remainders `(X, Y) = (A_j, A_{j+1})` of the prefix `(a0, a1)`
with packed cofactor words `(Kj, Kj1)`, `j` even. -/
def EvenPair (a0 a1 X Y Kj Kj1 : Nat) : Prop :=
  a0 = Vc Kj1 * X + Vc Kj * Y ∧ a1 = Uc Kj1 * X + Uc Kj * Y ∧
  Uc Kj * Vc Kj1 = Uc Kj1 * Vc Kj + 1

/-- Same, `j` odd. -/
def OddPair (a0 a1 X Y Kj Kj1 : Nat) : Prop :=
  a0 = Vc Kj1 * X + Vc Kj * Y ∧ a1 = Uc Kj1 * X + Uc Kj * Y ∧
  Uc Kj1 * Vc Kj = Uc Kj * Vc Kj1 + 1

theorem pack_eq (u v : Nat) (hv : v < 2^32) : Uc (u * 2^32 + v) = u ∧ Vc (u * 2^32 + v) = v := by
  unfold Uc Vc
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt hv, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem unpack (k : Nat) : k = Uc k * 2^32 + Vc k := by
  unfold Uc Vc; have := Nat.div_add_mod k (2^32); rw [Nat.mul_comm] at this; omega

theorem Vc_lt (k : Nat) : Vc k < 2^32 := Nat.mod_lt _ (by norm_num)

/-- One Euclid step on an even pair gives an odd pair, and the packed update
`Kj + q * Kj1` does not carry. -/
theorem step_even (a0 a1 X Y Kj Kj1 q : Nat) (h : EvenPair a0 a1 X Y Kj Kj1) (hq : q * Y ≤ X)
    (hY : 2^32 ≤ Y) (ha0 : a0 < 2^64) (ha1 : a1 < 2^64) :
    Kj + q * Kj1 < 2^64 ∧ Uc (Kj + q * Kj1) = Uc Kj + q * Uc Kj1 ∧
    Vc (Kj + q * Kj1) = Vc Kj + q * Vc Kj1 ∧ OddPair a0 a1 Y (X - q * Y) Kj1 (Kj + q * Kj1) := by
  obtain ⟨h0, h1, hd⟩ := h
  have e0 : a0 = (Vc Kj + q * Vc Kj1) * Y + Vc Kj1 * (X - q * Y) := by
    rw [h0]; zify [hq]; ring
  have e1 : a1 = (Uc Kj + q * Uc Kj1) * Y + Uc Kj1 * (X - q * Y) := by
    rw [h1]; zify [hq]; ring
  have bV : Vc Kj + q * Vc Kj1 < 2^32 := by
    by_contra hc; push Not at hc
    have : 2^32 * 2^32 ≤ (Vc Kj + q * Vc Kj1) * Y := Nat.mul_le_mul hc hY
    have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
    omega
  have bU : Uc Kj + q * Uc Kj1 < 2^32 := by
    by_contra hc; push Not at hc
    have : 2^32 * 2^32 ≤ (Uc Kj + q * Uc Kj1) * Y := Nat.mul_le_mul hc hY
    have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
    omega
  have hK : Kj + q * Kj1 = (Uc Kj + q * Uc Kj1) * 2^32 + (Vc Kj + q * Vc Kj1) := by
    conv_lhs => rw [unpack Kj, unpack Kj1]
    ring
  obtain ⟨pu, pv⟩ := pack_eq _ _ bV
  rw [← hK] at pu pv
  refine ⟨?_, pu, pv, ?_, ?_, ?_⟩
  · rw [hK]; omega
  · rw [pv]; exact e0
  · rw [pu]; exact e1
  · rw [pu, pv]
    have : (Uc Kj + q * Uc Kj1) * Vc Kj1 = Uc Kj * Vc Kj1 + q * Uc Kj1 * Vc Kj1 := by ring
    rw [this, hd]; ring

theorem step_odd (a0 a1 X Y Kj Kj1 q : Nat) (h : OddPair a0 a1 X Y Kj Kj1) (hq : q * Y ≤ X)
    (hY : 2^32 ≤ Y) (ha0 : a0 < 2^64) (ha1 : a1 < 2^64) :
    Kj + q * Kj1 < 2^64 ∧ Uc (Kj + q * Kj1) = Uc Kj + q * Uc Kj1 ∧
    Vc (Kj + q * Kj1) = Vc Kj + q * Vc Kj1 ∧ EvenPair a0 a1 Y (X - q * Y) Kj1 (Kj + q * Kj1) := by
  obtain ⟨h0, h1, hd⟩ := h
  have e0 : a0 = (Vc Kj + q * Vc Kj1) * Y + Vc Kj1 * (X - q * Y) := by
    rw [h0]; zify [hq]; ring
  have e1 : a1 = (Uc Kj + q * Uc Kj1) * Y + Uc Kj1 * (X - q * Y) := by
    rw [h1]; zify [hq]; ring
  have bV : Vc Kj + q * Vc Kj1 < 2^32 := by
    by_contra hc; push Not at hc
    have : 2^32 * 2^32 ≤ (Vc Kj + q * Vc Kj1) * Y := Nat.mul_le_mul hc hY
    have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
    omega
  have bU : Uc Kj + q * Uc Kj1 < 2^32 := by
    by_contra hc; push Not at hc
    have : 2^32 * 2^32 ≤ (Uc Kj + q * Uc Kj1) * Y := Nat.mul_le_mul hc hY
    have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
    omega
  have hK : Kj + q * Kj1 = (Uc Kj + q * Uc Kj1) * 2^32 + (Vc Kj + q * Vc Kj1) := by
    conv_lhs => rw [unpack Kj, unpack Kj1]
    ring
  obtain ⟨pu, pv⟩ := pack_eq _ _ bV
  rw [← hK] at pu pv
  refine ⟨?_, pu, pv, ?_, ?_, ?_⟩
  · rw [hK]; omega
  · rw [pv]; exact e0
  · rw [pu]; exact e1
  · rw [pu, pv]
    have : Uc Kj1 * (Vc Kj + q * Vc Kj1) = Uc Kj1 * Vc Kj + q * Uc Kj1 * Vc Kj1 := by ring
    rw [this, hd]; ring


abbrev Mat := Std.U64 × Std.U64 × Std.U64 × Std.U64 × Bool

def One (k : Nat) : Prop := 1 ≤ Uc k ∧ 1 ≤ Vc k

abbrev St7 := Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64
abbrev Out8 := Std.U64 × Std.U64 × Std.U64 × Bool × Std.U64 × Std.U64 × Std.U64 × Std.U64

/-- Loop invariant of `from_u64_prefix`: the window `(x, y, z) = (A_i, A_{i+1}, A_{i+2})`
(`i` odd) of the prefix remainder sequence with packed cofactors `K_{i-1} .. K_{i+2}`. -/
def LInv (a0 a1 : Nat) (s : St7) : Prop :=
  ∃ W : Nat,
    EvenPair a0 a1 W s.1.val s.2.1.val s.2.2.1.val ∧
    OddPair a0 a1 s.1.val s.2.2.2.1.val s.2.2.1.val s.2.2.2.2.1.val ∧
    EvenPair a0 a1 s.2.2.2.1.val s.2.2.2.2.2.1.val s.2.2.2.2.1.val s.2.2.2.2.2.2.val ∧
    s.1.val + s.2.2.2.1.val ≤ W ∧ s.2.2.2.1.val + s.2.2.2.2.2.1.val ≤ s.1.val ∧
    s.2.2.2.2.2.1.val < s.2.2.2.1.val ∧ 2^32 ≤ s.2.2.2.1.val ∧
    One s.2.2.2.2.1.val ∧ One s.2.2.2.2.2.2.val ∧
    (One s.2.2.1.val ∨ (s.2.1.val = 2^32 ∧ s.2.2.1.val = 1))

/-- Loop postcondition. -/
def LPost (a0 a1 : Nat) (o : Out8) : Prop :=
  ∃ W : Nat,
    (if o.2.2.2.1 then
      EvenPair a0 a1 W o.1.val o.2.1.val o.2.2.1.val ∧
      OddPair a0 a1 o.1.val o.2.2.2.2.1.val o.2.2.1.val o.2.2.2.2.2.1.val ∧
      EvenPair a0 a1 o.2.2.2.2.1.val o.2.2.2.2.2.2.1.val o.2.2.2.2.2.1.val o.2.2.2.2.2.2.2.val
    else
      OddPair a0 a1 W o.1.val o.2.1.val o.2.2.1.val ∧
      EvenPair a0 a1 o.1.val o.2.2.2.2.1.val o.2.2.1.val o.2.2.2.2.2.1.val ∧
      OddPair a0 a1 o.2.2.2.2.1.val o.2.2.2.2.2.2.1.val o.2.2.2.2.2.1.val o.2.2.2.2.2.2.2.val) ∧
    o.1.val + o.2.2.2.2.1.val ≤ W ∧ o.2.2.2.2.1.val + o.2.2.2.2.2.2.1.val ≤ o.1.val ∧
    o.2.2.2.2.2.2.1.val < o.2.2.2.2.1.val ∧ 2^32 ≤ o.2.2.2.2.1.val ∧ o.2.2.2.2.2.2.1.val < 2^32 ∧
    One o.2.2.2.2.2.1.val ∧ One o.2.2.2.2.2.2.2.val ∧
    (if o.2.2.2.1 then (One o.2.2.1.val ∨ (o.2.1.val = 2^32 ∧ o.2.2.1.val = 1))
     else One o.2.2.1.val)

theorem prefix_body_spec (a0 a1 : Nat) (ha0 : a0 < 2^64) (ha1 : a1 < 2^64)
    (L x K0 K1 y K2 z K3 : Std.U64) (hL : L.val = 2^32)
    (hinv : LInv a0 a1 (x, K0, K1, y, K2, z, K3)) :
    algorithms.gcd.matrix.Matrix.from_u64_prefix_loop.body L x K0 K1 y K2 z K3
    ⦃ r => match r with
      | .done o => LPost a0 a1 o
      | .cont s' => LInv a0 a1 s' ∧ s'.2.2.2.2.2.1.val < z.val ⦄ := by
  obtain ⟨W, hp0, hp1, hp2, hW, hx, hzy, hy, hoK2, hoK3, hoK1⟩ := hinv
  simp only at hp0 hp1 hp2 hW hx hzy hy hoK2 hoK3 hoK1
  have hmax : U64.max = 2^64 - 1 := by simp [U64.max_eq]
  have hxb : x.val < 2^64 := by have := x.hBounds; simpa [UScalarTy.numBits] using this
  have hyb : y.val < 2^64 := by have := y.hBounds; simpa [UScalarTy.numBits] using this
  have hzb : z.val < 2^64 := by have := z.hBounds; simpa [UScalarTy.numBits] using this
  unfold algorithms.gcd.matrix.Matrix.from_u64_prefix_loop.body
  have hm1 : (¬ (z >= L)) || (z < y) := by simp; scalar_tac
  step
  split
  · rename_i hzL
    have hzL' : 2^32 ≤ z.val := by scalar_tac
    have hq : y.val / z.val * z.val ≤ y.val := Nat.div_mul_le_self _ _
    obtain ⟨hK31, hU31, hV31, hp3⟩ :=
      step_even a0 a1 y.val z.val K2.val K3.val (y.val / z.val) hp2 hq hzL' ha0 ha1
    have hz0 : z > 0#u64 := by scalar_tac
    step
    step as ⟨q, q_post⟩
    have : q.val * z.val ≤ U64.max := by rw [q_post, hmax]; omega
    step as ⟨i1, i1_post⟩
    have : i1.val ≤ y.val := by rw [i1_post, q_post]; omega
    step as ⟨a31, a31_post, a31_post'⟩
    have ha31 : a31.val = y.val % z.val := by rw [a31_post, i1_post, q_post, Nat.mod_eq_sub_div_mul]
    have : q.val * K3.val ≤ U64.max := by rw [q_post, hmax]; omega
    step as ⟨i2, i2_post⟩
    have : K2.val + i2.val ≤ U64.max := by rw [i2_post, q_post, hmax]; omega
    step as ⟨k31, k31_post⟩
    have hk31 : k31.val = K2.val + y.val / z.val * K3.val := by rw [k31_post, i2_post, q_post]
    have hp3' : OddPair a0 a1 z.val a31.val K3.val k31.val := by
      rw [ha31, hk31, Nat.mod_eq_sub_div_mul]; exact hp3
    have hzpos : 0 < z.val := by omega
    have ha31z : a31.val < z.val := by rw [ha31]; exact Nat.mod_lt _ hzpos
    have hq1 : 1 ≤ y.val / z.val := (Nat.one_le_div_iff hzpos).mpr (by omega)
    have hza31 : z.val + a31.val ≤ y.val := by
      rw [ha31]
      have := Nat.div_add_mod y.val z.val
      have : z.val * 1 ≤ z.val * (y.val / z.val) := Nat.mul_le_mul_left _ hq1
      omega
    have hoK31 : One k31.val := by
      unfold One; rw [hk31, hU31, hV31]; unfold One at hoK2; omega
    have hm2 : (decide (a31 < L) || decide (a31 < z)) = true := by simp; scalar_tac
    step
    split
    · rename_i ha31L
      simp only [WP.spec_ok]
      refine ⟨x.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hp1, hp2, hp3'⟩
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); scalar_tac
      · exact hoK3
      · exact hoK31
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hoK2
    · rename_i ha31L
      have ha31L' : 2^32 ≤ a31.val := by scalar_tac
      have hq' : z.val / a31.val * a31.val ≤ z.val := Nat.div_mul_le_self _ _
      obtain ⟨hK32, hU32, hV32, hp4⟩ :=
        step_odd a0 a1 z.val a31.val K3.val k31.val (z.val / a31.val) hp3' hq' ha31L' ha0 ha1
      have ha0' : a31 > 0#u64 := by scalar_tac
      step
      step as ⟨q1, q1_post⟩
      have : q1.val * a31.val ≤ U64.max := by rw [q1_post, hmax]; omega
      step as ⟨i3, i3_post⟩
      have : i3.val ≤ z.val := by rw [i3_post, q1_post]; omega
      step as ⟨a32, a32_post, a32_post'⟩
      have ha32 : a32.val = z.val % a31.val := by rw [a32_post, i3_post, q1_post, Nat.mod_eq_sub_div_mul]
      have : q1.val * k31.val ≤ U64.max := by rw [q1_post, hmax]; omega
      step as ⟨i4, i4_post⟩
      have : K3.val + i4.val ≤ U64.max := by rw [i4_post, q1_post, hmax]; omega
      step as ⟨k32, k32_post⟩
      have hk32 : k32.val = K3.val + z.val / a31.val * k31.val := by rw [k32_post, i4_post, q1_post]
      have hp4' : EvenPair a0 a1 a31.val a32.val k31.val k32.val := by
        rw [ha32, hk32, Nat.mod_eq_sub_div_mul]; exact hp4
      have ha31pos : 0 < a31.val := by omega
      have ha32a31 : a32.val < a31.val := by rw [ha32]; exact Nat.mod_lt _ ha31pos
      have hq2 : 1 ≤ z.val / a31.val := (Nat.one_le_div_iff ha31pos).mpr (by omega)
      have ha31a32 : a31.val + a32.val ≤ z.val := by
        rw [ha32]
        have := Nat.div_add_mod z.val a31.val
        have : a31.val * 1 ≤ a31.val * (z.val / a31.val) := Nat.mul_le_mul_left _ hq2
        omega
      have hoK32 : One k32.val := by
        unfold One; rw [hk32, hU32, hV32]; unfold One at hoK3; omega
      refine ⟨⟨y.val, hp2, hp3', hp4', ?_, ?_, ?_, ?_, hoK31, hoK32, Or.inl hoK3⟩, ?_⟩
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); omega
      · (try simp only); omega
  · rename_i hzL
    simp only [WP.spec_ok]
    refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [↓reduceIte]
      exact ⟨hp0, hp1, hp2⟩
    · (try simp only); omega
    · (try simp only); omega
    · (try simp only); omega
    · (try simp only); omega
    · (try simp only); scalar_tac
    · exact hoK2
    · exact hoK3
    · simp only [↓reduceIte]; exact hoK1


theorem prefix_loop_spec (a0 a1 : Nat) (ha0 : a0 < 2^64) (ha1 : a1 < 2^64)
    (L x K0 K1 y K2 z K3 : Std.U64) (hL : L.val = 2^32)
    (hinv : LInv a0 a1 (x, K0, K1, y, K2, z, K3)) :
    algorithms.gcd.matrix.Matrix.from_u64_prefix_loop L x K0 K1 y K2 z K3
    ⦃ o => LPost a0 a1 o ⦄ := by
  unfold algorithms.gcd.matrix.Matrix.from_u64_prefix_loop
  apply loop.spec_decr_nat (fun s : St7 => s.2.2.2.2.2.1.val) (LInv a0 a1)
  · intro s hs
    obtain ⟨x', K0', K1', y', K2', z', K3'⟩ := s
    apply spec_mono (prefix_body_spec a0 a1 ha0 ha1 L x' K0' K1' y' K2' z' K3' hL hs)
    intro r hr
    cases r <;> exact hr
  · exact hinv

/-- What the final assertions need from the returned matrix `m = (m0, m1, m2, m3, sg)`:
it is the identity, or it maps the prefix `(a0, a1)` to a pair `(X, Y)` of
consecutive remainders satisfying Jebelean's condition. -/
def GoodM (a0 a1 : Nat) (m : Mat) : Prop :=
  m = (1#u64, 0#u64, 0#u64, 1#u64, true) ∨
  ∃ X Y : Nat,
    a0 = m.2.2.2.1.val * X + m.2.1.val * Y ∧ a1 = m.2.2.1.val * X + m.1.val * Y ∧
    1 ≤ m.2.2.1.val ∧ 1 ≤ m.2.2.2.1.val ∧
    (if m.2.2.2.2 then
       m.1.val * m.2.2.2.1.val = m.2.1.val * m.2.2.1.val + 1 ∧ m.2.2.1.val ≤ Y ∧
         Y + m.2.1.val + m.2.2.2.1.val ≤ X
     else
       m.2.1.val * m.2.2.1.val = m.1.val * m.2.2.2.1.val + 1 ∧ m.2.2.2.1.val ≤ Y ∧
         Y + m.1.val + m.2.2.1.val ≤ X)

theorem coef_lt (a V1 V0 X Y : Nat) (h : a = V1 * X + V0 * Y) (ha : a < 2^64) (hX : 2^32 ≤ X) :
    V1 < 2^32 := by
  by_contra hc; push Not at hc
  have : 2^32 * 2^32 ≤ V1 * X := Nat.mul_le_mul hc hX
  have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
  omega

theorem coef_sum_lt (a V1 V0 X Y : Nat) (h : a = V1 * X + V0 * Y) (ha : a < 2^64) (hXY : Y ≤ X)
    (hY : 2^32 ≤ Y) : V1 + V0 < 2^32 := by
  by_contra hc; push Not at hc
  have : 2^32 * 2^32 ≤ (V1 + V0) * Y := Nat.mul_le_mul hc hY
  have : V1 * Y ≤ V1 * X := Nat.mul_le_mul_left _ hXY
  have : (2:Nat)^64 = 2^32 * 2^32 := by norm_num
  nlinarith



theorem LIMIT_eq : algorithms.gcd.matrix.Matrix.from_u64_prefix.LIMIT = ok 4294967296#u64 := by
  unfold algorithms.gcd.matrix.Matrix.from_u64_prefix.LIMIT; rfl

theorem IDENTITY_eq : algorithms.gcd.matrix.Matrix.IDENTITY = (1#u64, 0#u64, 0#u64, 1#u64, true) := by
  unfold algorithms.gcd.matrix.Matrix.IDENTITY; rfl

theorem shr32_val (k : Std.U64) (x : Std.U64) (h : x.val = k.val >>> 32) : x.val = Uc k.val := by
  rw [h, Nat.shiftRight_eq_div_pow]; rfl

theorem init_pair (a0 a1 : Nat) : EvenPair a0 a1 a0 a1 (2^32) 1 := by
  unfold EvenPair Uc Vc; norm_num

theorem Uc_lt (k : Std.U64) : Uc k.val < 2^32 := by
  have := k.hBounds; simp [UScalarTy.numBits] at this
  unfold Uc; omega

theorem good_of_even (a0 a1 X Y : Nat) (Kj Kj1 m0 m1 m2 m3 : Std.U64)
    (h : EvenPair a0 a1 X Y Kj.val Kj1.val)
    (hm0 : m0.val = Uc Kj.val) (hm1 : m1.val = Vc Kj.val) (hm2 : m2.val = Uc Kj1.val)
    (hm3 : m3.val = Vc Kj1.val) (ho : One Kj1.val) (hY : Uc Kj1.val ≤ Y)
    (hX : Y + Vc Kj.val + Vc Kj1.val ≤ X) : GoodM a0 a1 (m0, m1, m2, m3, true) := by
  right
  obtain ⟨e0, e1, ed⟩ := h
  refine ⟨X, Y, ?_, ?_, ?_, ?_, ?_⟩
  · show a0 = m3.val * X + m1.val * Y
    rw [hm3, hm1]; exact e0
  · show a1 = m2.val * X + m0.val * Y
    rw [hm2, hm0]; exact e1
  · show 1 ≤ m2.val
    rw [hm2]; exact ho.1
  · show 1 ≤ m3.val
    rw [hm3]; exact ho.2
  · simp only [↓reduceIte]
    rw [hm0, hm1, hm2, hm3]
    refine ⟨?_, hY, hX⟩
    rw [ed]; ring

theorem good_of_odd (a0 a1 X Y : Nat) (Kj Kj1 m0 m1 m2 m3 : Std.U64)
    (h : OddPair a0 a1 X Y Kj.val Kj1.val)
    (hm0 : m0.val = Uc Kj.val) (hm1 : m1.val = Vc Kj.val) (hm2 : m2.val = Uc Kj1.val)
    (hm3 : m3.val = Vc Kj1.val) (ho : One Kj1.val) (hY : Vc Kj1.val ≤ Y)
    (hX : Y + Uc Kj.val + Uc Kj1.val ≤ X) : GoodM a0 a1 (m0, m1, m2, m3, false) := by
  right
  obtain ⟨e0, e1, ed⟩ := h
  refine ⟨X, Y, ?_, ?_, ?_, ?_, ?_⟩
  · show a0 = m3.val * X + m1.val * Y
    rw [hm3, hm1]; exact e0
  · show a1 = m2.val * X + m0.val * Y
    rw [hm2, hm0]; exact e1
  · show 1 ≤ m2.val
    rw [hm2]; exact ho.1
  · show 1 ≤ m3.val
    rw [hm3]; exact ho.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hm0, hm1, hm2, hm3]
    refine ⟨?_, hY, hX⟩
    rw [Nat.mul_comm (Vc Kj.val), ed]

theorem from_u64_prefix_good (a0 a1 : Std.U64) (h0 : 2^63 ≤ a0.val) (h01 : a1.val ≤ a0.val) :
    algorithms.gcd.matrix.Matrix.from_u64_prefix a0 a1 ⦃ m => GoodM a0.val a1.val m ⦄ := by
  have hA0 : a0.val < 2^64 := by have := a0.hBounds; simpa [UScalarTy.numBits] using this
  have hA1 : a1.val < 2^64 := by have := a1.hBounds; simpa [UScalarTy.numBits] using this
  have hmax : U64.max = 2^64 - 1 := by simp [U64.max_eq]
  have hsz : U64.size = 2^64 := by simp [U64.size, U64.numBits]
  unfold algorithms.gcd.matrix.Matrix.from_u64_prefix
  rw [LIMIT_eq, IDENTITY_eq]
  step as ⟨i, i_post1, i_post2, i_post3⟩
  have hi : i.val = 2^63 := by rw [i_post1, hsz]; decide
  have : a0 ≥ i := by scalar_tac
  step
  have : a0 ≥ a1 := by scalar_tac
  step
  step as ⟨k0, k0_post1, k0_post2, k0_post3⟩
  have hk0 : k0.val = 2^32 := by rw [k0_post1, hsz]; decide
  split
  · simp only [WP.spec_ok]; left; rfl
  · rename_i ha1L
    have ha1L' : 2^32 ≤ a1.val := by scalar_tac
    obtain ⟨hK2b, hU2, hV2, hp1⟩ := step_even a0.val a1.val a0.val a1.val (2^32) 1 (a0.val / a1.val)
      (init_pair _ _) (Nat.div_mul_le_self _ _) ha1L' hA0 hA1
    step as ⟨q, q_post⟩
    have : q.val * a1.val ≤ U64.max := by rw [q_post, hmax]; have := Nat.div_mul_le_self a0.val a1.val; omega
    step as ⟨i2, i2_post⟩
    have : i2.val ≤ a0.val := by rw [i2_post, q_post]; exact Nat.div_mul_le_self _ _
    step as ⟨a2, a2_post, a2_post'⟩
    have ha2 : a2.val = a0.val % a1.val := by rw [a2_post, i2_post, q_post, Nat.mod_eq_sub_div_mul]
    step as ⟨i3, i3_post⟩
    have : k0.val + i3.val ≤ U64.max := by rw [i3_post, q_post, hk0, hmax]; omega
    step as ⟨k2, k2_post⟩
    have hk2 : k2.val = 2^32 + a0.val / a1.val * 1 := by rw [k2_post, i3_post, q_post, hk0]
    have hp1' : OddPair a0.val a1.val a1.val a2.val 1 k2.val := by
      rw [ha2, hk2, Nat.mod_eq_sub_div_mul]; exact hp1
    have ha1pos : 0 < a1.val := by omega
    have hqge : 1 ≤ a0.val / a1.val := (Nat.one_le_div_iff ha1pos).mpr h01
    have hUk2 : Uc k2.val = 1 := by rw [hk2, hU2]; simp [Uc, Vc]
    have hVk2 : Vc k2.val = a0.val / a1.val := by rw [hk2, hV2]; simp [Uc, Vc]
    have ha2a1 : a2.val < a1.val := by rw [ha2]; exact Nat.mod_lt _ ha1pos
    have ha1a2 : a1.val + a2.val ≤ a0.val := by
      rw [ha2]
      have := Nat.div_add_mod a0.val a1.val
      have : a1.val * 1 ≤ a1.val * (a0.val / a1.val) := Nat.mul_le_mul_left _ hqge
      omega
    split
    · rename_i ha2L
      step as ⟨u2, u2_post1, u2_post2, u2_post3⟩
      have hu2 : u2.val = Uc k2.val := shr32_val k2 u2 u2_post1
      step as ⟨v2, v2_post⟩
      have hv2 : v2.val = Vc k2.val := by rw [v2_post]; rfl
      split
      · rename_i hav
        have : a2.val ≤ a1.val := by omega
        step as ⟨i4, i4_post, i4_post'⟩
        split
        · rename_i hiu
          simp only [WP.spec_ok]
          right
          obtain ⟨e0, e1, ed⟩ := hp1'
          have hU1 : Uc 1 = 0 := by decide
          have hV1 : Vc 1 = 1 := by decide
          have hav' : v2.val ≤ a2.val := hav
          have hiu' : u2.val ≤ i4.val := hiu
          refine ⟨a1.val, a2.val, ?_, ?_, ?_, ?_, ?_⟩
          · show a0.val = v2.val * a1.val + (1#u64 : Std.U64).val * a2.val
            rw [hv2, e0, hV1]; simp
          · show a1.val = u2.val * a1.val + (0#u64 : Std.U64).val * a2.val
            rw [hu2, hUk2]; simp
          · show 1 ≤ u2.val
            rw [hu2, hUk2]
          · show 1 ≤ v2.val
            rw [hv2, hVk2]; exact hqge
          · simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, hav', ?_⟩
            · rw [hu2, hUk2]; simp
            · have : (0#u64 : Std.U64).val = 0 := rfl
              rw [this]; omega
        · simp only [WP.spec_ok]; left; rfl
      · simp only [WP.spec_ok]; left; rfl
    · rename_i ha2L
      have ha2L' : 2^32 ≤ a2.val := by scalar_tac
      have hq1' : a1.val / a2.val * a2.val ≤ a1.val := Nat.div_mul_le_self _ _
      obtain ⟨hK3b, hU3, hV3, hp2⟩ :=
        step_odd a0.val a1.val a1.val a2.val 1 k2.val (a1.val / a2.val) hp1' hq1' ha2L' hA0 hA1
      step as ⟨q1, q1_post⟩
      have : q1.val * a2.val ≤ U64.max := by rw [q1_post, hmax]; omega
      step as ⟨i4, i4_post⟩
      have : i4.val ≤ a1.val := by rw [i4_post, q1_post]; omega
      step as ⟨a3, a3_post, a3_post'⟩
      have ha3 : a3.val = a1.val % a2.val := by rw [a3_post, i4_post, q1_post, Nat.mod_eq_sub_div_mul]
      have : q1.val * k2.val ≤ U64.max := by rw [q1_post, hmax]; omega
      step as ⟨i5, i5_post⟩
      have : (1#u64 : Std.U64).val + i5.val ≤ U64.max := by
        have h1 : (1#u64 : Std.U64).val = 1 := rfl
        rw [i5_post, q1_post, hmax, h1]; omega
      step as ⟨k3, k3_post⟩
      have hk3 : k3.val = 1 + a1.val / a2.val * k2.val := by rw [k3_post, i5_post, q1_post]
      have hp2' : EvenPair a0.val a1.val a2.val a3.val k2.val k3.val := by
        rw [ha3, hk3, Nat.mod_eq_sub_div_mul]; exact hp2
      have ha2pos : 0 < a2.val := by omega
      have hq1ge : 1 ≤ a1.val / a2.val := (Nat.one_le_div_iff ha2pos).mpr (by omega)
      have ha3a2 : a3.val < a2.val := by rw [ha3]; exact Nat.mod_lt _ ha2pos
      have ha2a3 : a2.val + a3.val ≤ a1.val := by
        rw [ha3]
        have := Nat.div_add_mod a1.val a2.val
        have : a2.val * 1 ≤ a2.val * (a1.val / a2.val) := Nat.mul_le_mul_left _ hq1ge
        omega
      have hoK2 : One k2.val := by unfold One; rw [hUk2, hVk2]; omega
      have hoK3 : One k3.val := by
        unfold One; rw [hk3, hU3, hV3, hUk2, hVk2]
        have hU1 : Uc 1 = 0 := by decide
        have hV1 : Vc 1 = 1 := by decide
        rw [hU1, hV1]; constructor
        · omega
        · have : 1 ≤ a1.val / a2.val * (a0.val / a1.val) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          omega
      have hinv : LInv a0.val a1.val (a1, k0, 1#u64, a2, k2, a3, k3) := by
        refine ⟨a0.val, ?_, hp1', hp2', ha1a2, ha2a3, ha3a2, ha2L', hoK2, hoK3, Or.inr ⟨hk0, rfl⟩⟩
        show EvenPair a0.val a1.val a0.val a1.val k0.val 1
        rw [hk0]; exact init_pair _ _
      apply spec_bind (prefix_loop_spec a0.val a1.val hA0 hA1 4294967296#u64 a1 k0 1#u64 a2 k2 a3 k3 rfl hinv)
      intro o ho
      obtain ⟨P, K', K'', e, Q, K''', R, K''''⟩ := o
      obtain ⟨W, hpairs, hWP, hPQ, hRQ, hQL, hRL, hoK3', hoK4', hoK2'⟩ := ho
      simp only at hpairs hWP hPQ hRQ hQL hRL hoK3' hoK4' hoK2'
      step as ⟨u0, u0_post1, u0_post2, u0_post3⟩
      have hu0 : u0.val = Uc K'.val := shr32_val _ _ u0_post1
      step as ⟨u1, u1_post1, u1_post2, u1_post3⟩
      have hu1 : u1.val = Uc K''.val := shr32_val _ _ u1_post1
      step as ⟨u2, u2_post1, u2_post2, u2_post3⟩
      have hu2 : u2.val = Uc K'''.val := shr32_val _ _ u2_post1
      step as ⟨u3, u3_post1, u3_post2, u3_post3⟩
      have hu3 : u3.val = Uc K''''.val := shr32_val _ _ u3_post1
      step as ⟨v0, v0_post⟩
      have hv0 : v0.val = Vc K'.val := by rw [v0_post]; rfl
      step as ⟨v1, v1_post⟩
      have hv1 : v1.val = Vc K''.val := by rw [v1_post]; rfl
      step as ⟨v2, v2_post⟩
      have hv2 : v2.val = Vc K'''.val := by rw [v2_post]; rfl
      step as ⟨v3, v3_post⟩
      have hv3 : v3.val = Vc K''''.val := by rw [v3_post]; rfl
      have : Q ≥ 4294967296#u64 := by scalar_tac
      step
      have : R < 4294967296#u64 := by scalar_tac
      step
      have hPL : 2^32 ≤ P.val := by omega
      have hWL : P.val ≤ W := by omega
      have bU1 := Uc_lt K''; have bU2 := Uc_lt K'''; have bU3 := Uc_lt K''''
      have bV1 := Vc_lt K''.val; have bV2 := Vc_lt K'''.val; have bV3 := Vc_lt K''''.val
      cases e
      · -- mid-loop exit: window starts at an even index
        simp only [Bool.false_eq_true, ↓reduceIte] at hpairs hoK2'
        obtain ⟨hpa, hpb, hpc⟩ := hpairs
        have : (decide ¬false = true || decide (Q ≥ v2)) = true := by simp
        step
        have bQ : Uc K'''.val < 2^32 := coef_lt _ _ _ _ _ hpb.2.1 hA1 hPL
        have : Q ≥ u2 := by show u2.val ≤ Q.val; rw [hu2]; omega
        split
        · contradiction
        step
        have hQP : Q.val ≤ P.val := by omega
        step as ⟨i6, i6_post, i6_post'⟩
        have : v2.val + v1.val ≤ U64.max := by rw [hv2, hv1, hmax]; omega
        step as ⟨i7, i7_post⟩
        split
        · rename_i h67
          have h67' : Vc K'''.val + Vc K''.val ≤ P.val - Q.val := by
            have : i7.val ≤ i6.val := h67
            rw [i7_post, i6_post, hv2, hv1] at this; exact this
          have gE : GoodM a0.val a1.val (u1, v1, u2, v2, true) :=
            good_of_even _ _ P.val Q.val K'' K''' u1 v1 u2 v2 hpb hu1 hv1 hu2 hv2 hoK3' (by omega) (by omega)
          split
          · rename_i hRv
            have hRv' : Vc K''''.val ≤ R.val := by
              have : v3.val ≤ R.val := hRv
              rwa [hv3] at this
            have hRQ' : R.val ≤ Q.val := by omega
            step as ⟨i8, i8_post, i8_post'⟩
            have : u3.val + u2.val ≤ U64.max := by rw [hu3, hu2, hmax]; omega
            step as ⟨i9, i9_post⟩
            split
            · rename_i h89
              have h89' : Uc K''''.val + Uc K'''.val ≤ Q.val - R.val := by
                have : i9.val ≤ i8.val := h89
                rw [i9_post, i8_post, hu3, hu2] at this; exact this
              simp only [WP.spec_ok]
              exact good_of_odd _ _ Q.val R.val K''' K'''' u2 v2 u3 v3 hpc hu2 hv2 hu3 hv3 hoK4' hRv'
                (by omega)
            · simp only [WP.spec_ok]; exact gE
          · simp only [WP.spec_ok]; exact gE
        · simp only [WP.spec_ok]
          have b1 : Vc K''.val < 2^32 := coef_lt _ _ _ _ _ hpa.1 hA0 (by omega)
          have b2 : Uc K''.val + Uc K'.val < 2^32 := coef_sum_lt _ _ _ _ _ hpa.2.1 hA1 hWL hPL
          exact good_of_odd _ _ W P.val K' K'' u0 v0 u1 v1 hpa hu0 hv0 hu1 hv1 hoK2' (by omega)
            (by omega)
      · -- exit at the loop head: window starts at an odd index
        simp only [↓reduceIte] at hpairs hoK2'
        obtain ⟨hpa, hpb, hpc⟩ := hpairs
        have bQ : Vc K'''.val < 2^32 := coef_lt _ _ _ _ _ hpb.1 hA0 hPL
        have : (decide ¬true = true || decide (Q ≥ v2)) = true := by
          simp only [decide_not, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
          show v2.val ≤ Q.val; rw [hv2]; omega
        step
        split
        swap
        · contradiction
        have hQP : Q.val ≤ P.val := by omega
        step as ⟨i6, i6_post, i6_post'⟩
        have : u2.val + u1.val ≤ U64.max := by rw [hu2, hu1, hmax]; omega
        step as ⟨i7, i7_post⟩
        split
        · rename_i h67
          have h67' : Uc K'''.val + Uc K''.val ≤ P.val - Q.val := by
            have : i7.val ≤ i6.val := h67
            rw [i7_post, i6_post, hu2, hu1] at this; exact this
          have gO : GoodM a0.val a1.val (u1, v1, u2, v2, false) :=
            good_of_odd _ _ P.val Q.val K'' K''' u1 v1 u2 v2 hpb hu1 hv1 hu2 hv2 hoK3' (by omega) (by omega)
          split
          · rename_i hRu
            have hRu' : Uc K''''.val ≤ R.val := by
              have : u3.val ≤ R.val := hRu
              rwa [hu3] at this
            have hRQ' : R.val ≤ Q.val := by omega
            step as ⟨i8, i8_post, i8_post'⟩
            have : v3.val + v2.val ≤ U64.max := by rw [hv3, hv2, hmax]; omega
            step as ⟨i9, i9_post⟩
            split
            · rename_i h89
              have h89' : Vc K''''.val + Vc K'''.val ≤ Q.val - R.val := by
                have : i9.val ≤ i8.val := h89
                rw [i9_post, i8_post, hv3, hv2] at this; exact this
              simp only [WP.spec_ok]
              exact good_of_even _ _ Q.val R.val K''' K'''' u2 v2 u3 v3 hpc hu2 hv2 hu3 hv3 hoK4' hRu'
                (by omega)
            · simp only [WP.spec_ok]; exact gO
          · simp only [WP.spec_ok]; exact gO
        · simp only [WP.spec_ok]
          rcases hoK2' with ho | ⟨hK1, hK2⟩
          · have b1 : Uc K''.val < 2^32 := coef_lt _ _ _ _ _ hpa.2.1 hA1 (by omega)
            have b2 : Vc K''.val + Vc K'.val < 2^32 := coef_sum_lt _ _ _ _ _ hpa.1 hA0 hWL hPL
            exact good_of_even _ _ W P.val K' K'' u0 v0 u1 v1 hpa hu0 hv0 hu1 hv1 ho (by omega)
              (by omega)
          · left
            have e0 : u0 = 1#u64 := by
              apply UScalar.eq_of_val_eq; rw [hu0, hK1]; decide
            have e1 : v0 = 0#u64 := by
              apply UScalar.eq_of_val_eq; rw [hv0, hK1]; decide
            have e2 : u1 = 0#u64 := by
              apply UScalar.eq_of_val_eq; rw [hu1, hK2]; decide
            have e3 : v1 = 1#u64 := by
              apply UScalar.eq_of_val_eq; rw [hv1, hK2]; decide
            rw [e0, e1, e2, e3]


theorem u128_size : UScalar.size .U128 = 2^128 := by simp [U128.size, U128.numBits]

theorem u128_lt (x : Std.U128) : x.val < 2^128 := by
  have := x.hBounds; simpa [UScalarTy.numBits] using this

/-- `(x as u128).wrapping_mul(A).wrapping_sub((y as u128).wrapping_mul(B))` is the exact
difference when it lies in `[0, 2^128)`. -/
theorem wsub_wmul (x y : Std.U64) (A B : Std.U128) (c : Nat)
    (h : x.val * A.val = y.val * B.val + c) (hc : c < 2^128) :
    (Aeneas.Std.U128.wrapping_sub
      (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 x) A)
      (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 y) B)).val = c := by
  simp only [U128.wrapping_sub_val_eq, U128.wrapping_mul_val_eq, U64.cast_U128_val_eq, u128_size]
  set M : Nat := 2^128 with hM
  have hMpos : 0 < M := by positivity
  set p := y.val * B.val % M with hp
  set t := x.val * A.val % M with ht
  have hpM : p < M := Nat.mod_lt _ hMpos
  have htM : t < M := Nat.mod_lt _ hMpos
  have h1 : (t + (M - p)) % M + p ≡ c + p [MOD M] := by
    have e1 : (t + (M - p)) % M + p ≡ t + (M - p) + p [MOD M] := Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
    have e2 : t + (M - p) + p = t + M := by omega
    rw [e2] at e1
    have e3 : t + M ≡ t [MOD M] := by simp [Nat.ModEq]
    have e4 : t ≡ x.val * A.val [MOD M] := Nat.mod_modEq _ _
    have e5 : c + p ≡ c + y.val * B.val [MOD M] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
    rw [h] at e4
    have e6 : y.val * B.val + c = c + y.val * B.val := by ring
    rw [e6] at e4
    exact e1.trans (e3.trans (e4.trans e5.symm))
  have h2 := Nat.ModEq.add_right_cancel' p h1
  unfold Nat.ModEq at h2
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hc] at h2
  exact h2


theorem gcd_dvd_of_eq (A B c u v : Nat) (h : u * A = v * B + c) : Nat.gcd A B ∣ c := by
  have h1 : Nat.gcd A B ∣ u * A := Dvd.dvd.mul_left (Nat.gcd_dvd_left A B) u
  have h2 : Nat.gcd A B ∣ v * B := Dvd.dvd.mul_left (Nat.gcd_dvd_right A B) v
  have : c = u * A - v * B := by omega
  rw [this]; exact Nat.dvd_sub h1 h2

theorem gcd_dvd_of_eq' (A B c u v : Nat) (h : u * B = v * A + c) : Nat.gcd A B ∣ c := by
  rw [Nat.gcd_comm]; exact gcd_dvd_of_eq B A c u v h

theorem gcd_of_unimod (A B c d p q r t : Nat) (hA : A = p * c + q * d) (hB : B = r * c + t * d)
    (hc : Nat.gcd A B ∣ c) (hd : Nat.gcd A B ∣ d) :
    Nat.gcd A B = Nat.gcd c d := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd hc hd
  · apply Nat.dvd_gcd
    · rw [hA]
      exact Nat.dvd_add (Dvd.dvd.mul_left (Nat.gcd_dvd_left c d) p) (Dvd.dvd.mul_left (Nat.gcd_dvd_right c d) q)
    · rw [hB]
      exact Nat.dvd_add (Dvd.dvd.mul_left (Nat.gcd_dvd_left c d) r) (Dvd.dvd.mul_left (Nat.gcd_dvd_right c d) t)

/-- Jebelean's condition, sign pattern `true` (`c = m0 A - m1 B`, `d = m3 B - m2 A`). -/
theorem jebelean_true (a0 a1 X Y m0 m1 m2 m3 A B α β s : Nat)
    (e0 : a0 = m3 * X + m1 * Y) (e1 : a1 = m2 * X + m0 * Y) (hm2 : 1 ≤ m2) (hm3 : 1 ≤ m3)
    (hdet : m0 * m3 = m1 * m2 + 1) (hY : m2 ≤ Y) (hX : Y + m1 + m3 ≤ X)
    (hα : α < 2^64) (hβ : β < 2^64) (hA : A * 2^s = 2^64 * a0 + α) (hB : B * 2^s = 2^64 * a1 + β) :
    ∃ c d : Nat, m0 * A = m1 * B + c ∧ m3 * B = m2 * A + d ∧ d < c ∧ c ≤ A ∧ d < B ∧
      Nat.gcd A B = Nat.gcd c d := by
  have hs : (0:ℤ) < 2^s := by positivity
  have z0 := congrArg (Nat.cast (R := ℤ)) e0
  have z1 := congrArg (Nat.cast (R := ℤ)) e1
  have zA := congrArg (Nat.cast (R := ℤ)) hA
  have zB := congrArg (Nat.cast (R := ℤ)) hB
  have zdet := congrArg (Nat.cast (R := ℤ)) hdet
  push_cast at z0 z1 zA zB zdet
  have zX : (m0:ℤ) * a0 - m1 * a1 = X := by
    linear_combination (m0:ℤ) * z0 - (m1:ℤ) * z1 + (X:ℤ) * zdet
  have zY : (m3:ℤ) * a1 - m2 * a0 = Y := by
    linear_combination (m3:ℤ) * z1 - (m2:ℤ) * z0 + (Y:ℤ) * zdet
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = (m0:ℤ) * A - m1 * B := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = (m3:ℤ) * B - m2 * A := ⟨_, rfl⟩
  have eC : C * 2^s = 18446744073709551616 * X + m0 * α - m1 * β := by
    rw [hC]; linear_combination (m0:ℤ) * zA - (m1:ℤ) * zB + 18446744073709551616 * zX
  have eD : D * 2^s = 18446744073709551616 * Y + m3 * β - m2 * α := by
    rw [hD]; linear_combination (m3:ℤ) * zB - (m2:ℤ) * zA + 18446744073709551616 * zY
  have hαz : (α:ℤ) ≤ 18446744073709551615 := by exact_mod_cast (by omega : α ≤ 18446744073709551615)
  have hβz : (β:ℤ) ≤ 18446744073709551615 := by exact_mod_cast (by omega : β ≤ 18446744073709551615)
  have hα' : (m2:ℤ) * α ≤ m2 * 18446744073709551615 := mul_le_mul_of_nonneg_left hαz (by positivity)
  have hβ' : ((m1:ℤ) + m3) * β ≤ (m1 + m3) * 18446744073709551615 :=
    mul_le_mul_of_nonneg_left hβz (by positivity)
  have hYz : (m2:ℤ) ≤ Y := by exact_mod_cast hY
  have hXz : (Y:ℤ) + m1 + m3 ≤ X := by exact_mod_cast hX
  have hm2z : (1:ℤ) ≤ m2 := by exact_mod_cast hm2
  have hm3z : (1:ℤ) ≤ m3 := by exact_mod_cast hm3
  have p1 : (0:ℤ) ≤ m3 * β := by positivity
  have p2 : (0:ℤ) ≤ (m0 + m2) * α := by positivity
  have hDpos : 0 < D * 2^s := by
    rw [eD]; nlinarith
  have hCD : 0 < (C - D) * 2^s := by
    rw [sub_mul, eC, eD]; nlinarith
  have hD0 : 0 < D := pos_of_mul_pos_left hDpos hs.le
  have hCD0 : 0 < C - D := pos_of_mul_pos_left hCD hs.le
  have eA : (A:ℤ) = m3 * C + m1 * D := by rw [hC, hD]; linear_combination (-(A:ℤ)) * zdet
  have eB : (B:ℤ) = m2 * C + m0 * D := by rw [hC, hD]; linear_combination (-(B:ℤ)) * zdet
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c:ℤ) = C := ⟨C.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d:ℤ) = D := ⟨D.toNat, Int.toNat_of_nonneg (by omega)⟩
  have n1 : m0 * A = m1 * B + c := by
    have : ((m0 * A : ℕ) : ℤ) = ((m1 * B + c : ℕ) : ℤ) := by push_cast; rw [hc, hC]; ring
    exact_mod_cast this
  have n2 : m3 * B = m2 * A + d := by
    have : ((m3 * B : ℕ) : ℤ) = ((m2 * A + d : ℕ) : ℤ) := by push_cast; rw [hd, hD]; ring
    exact_mod_cast this
  have n3 : A = m3 * c + m1 * d := by
    have : ((A : ℕ) : ℤ) = ((m3 * c + m1 * d : ℕ) : ℤ) := by push_cast; rw [hc, hd]; exact eA
    exact_mod_cast this
  have n4 : B = m2 * c + m0 * d := by
    have : ((B : ℕ) : ℤ) = ((m2 * c + m0 * d : ℕ) : ℤ) := by push_cast; rw [hc, hd]; exact eB
    exact_mod_cast this
  have hdc : d < c := by omega
  refine ⟨c, d, n1, n2, hdc, ?_, ?_, gcd_of_unimod A B c d m3 m1 m2 m0 n3 n4
    (gcd_dvd_of_eq A B c m0 m1 n1) (gcd_dvd_of_eq' A B d m3 m2 n2)⟩
  · have h1 : c ≤ m3 * c := Nat.le_mul_of_pos_left c hm3
    omega
  · have h1 : c ≤ m2 * c := Nat.le_mul_of_pos_left c hm2
    omega

/-- Jebelean's condition, sign pattern `false` (`c = m1 B - m0 A`, `d = m2 A - m3 B`). -/
theorem jebelean_false (a0 a1 X Y m0 m1 m2 m3 A B α β s : Nat)
    (e0 : a0 = m3 * X + m1 * Y) (e1 : a1 = m2 * X + m0 * Y) (hm2 : 1 ≤ m2) (hm3 : 1 ≤ m3)
    (hdet : m1 * m2 = m0 * m3 + 1) (hY : m3 ≤ Y) (hX : Y + m0 + m2 ≤ X)
    (hα : α < 2^64) (hβ : β < 2^64) (hA : A * 2^s = 2^64 * a0 + α) (hB : B * 2^s = 2^64 * a1 + β) :
    ∃ c d : Nat, m1 * B = m0 * A + c ∧ m2 * A = m3 * B + d ∧ d < c ∧ c ≤ A ∧ d < B ∧
      Nat.gcd A B = Nat.gcd c d := by
  have hs : (0:ℤ) < 2^s := by positivity
  have z0 := congrArg (Nat.cast (R := ℤ)) e0
  have z1 := congrArg (Nat.cast (R := ℤ)) e1
  have zA := congrArg (Nat.cast (R := ℤ)) hA
  have zB := congrArg (Nat.cast (R := ℤ)) hB
  have zdet := congrArg (Nat.cast (R := ℤ)) hdet
  push_cast at z0 z1 zA zB zdet
  have zX : (m1:ℤ) * a1 - m0 * a0 = X := by
    linear_combination (m1:ℤ) * z1 - (m0:ℤ) * z0 + (X:ℤ) * zdet
  have zY : (m2:ℤ) * a0 - m3 * a1 = Y := by
    linear_combination (m2:ℤ) * z0 - (m3:ℤ) * z1 + (Y:ℤ) * zdet
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = (m1:ℤ) * B - m0 * A := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = (m2:ℤ) * A - m3 * B := ⟨_, rfl⟩
  have eC : C * 2^s = 18446744073709551616 * X + m1 * β - m0 * α := by
    rw [hC]; linear_combination (m1:ℤ) * zB - (m0:ℤ) * zA + 18446744073709551616 * zX
  have eD : D * 2^s = 18446744073709551616 * Y + m2 * α - m3 * β := by
    rw [hD]; linear_combination (m2:ℤ) * zA - (m3:ℤ) * zB + 18446744073709551616 * zY
  have hαz : (α:ℤ) ≤ 18446744073709551615 := by exact_mod_cast (by omega : α ≤ 18446744073709551615)
  have hβz : (β:ℤ) ≤ 18446744073709551615 := by exact_mod_cast (by omega : β ≤ 18446744073709551615)
  have hα' : ((m0:ℤ) + m2) * α ≤ (m0 + m2) * 18446744073709551615 :=
    mul_le_mul_of_nonneg_left hαz (by positivity)
  have hβ' : (m3:ℤ) * β ≤ m3 * 18446744073709551615 := mul_le_mul_of_nonneg_left hβz (by positivity)
  have hYz : (m3:ℤ) ≤ Y := by exact_mod_cast hY
  have hXz : (Y:ℤ) + m0 + m2 ≤ X := by exact_mod_cast hX
  have hm2z : (1:ℤ) ≤ m2 := by exact_mod_cast hm2
  have hm3z : (1:ℤ) ≤ m3 := by exact_mod_cast hm3
  have p1 : (0:ℤ) ≤ m2 * α := by positivity
  have p2 : (0:ℤ) ≤ (m1 + m3) * β := by positivity
  have hDpos : 0 < D * 2^s := by
    rw [eD]; nlinarith
  have hCD : 0 < (C - D) * 2^s := by
    rw [sub_mul, eC, eD]; nlinarith
  have hD0 : 0 < D := pos_of_mul_pos_left hDpos hs.le
  have hCD0 : 0 < C - D := pos_of_mul_pos_left hCD hs.le
  have eA : (A:ℤ) = m3 * C + m1 * D := by rw [hC, hD]; linear_combination (-(A:ℤ)) * zdet
  have eB : (B:ℤ) = m2 * C + m0 * D := by rw [hC, hD]; linear_combination (-(B:ℤ)) * zdet
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c:ℤ) = C := ⟨C.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d:ℤ) = D := ⟨D.toNat, Int.toNat_of_nonneg (by omega)⟩
  have n1 : m1 * B = m0 * A + c := by
    have : ((m1 * B : ℕ) : ℤ) = ((m0 * A + c : ℕ) : ℤ) := by push_cast; rw [hc, hC]; ring
    exact_mod_cast this
  have n2 : m2 * A = m3 * B + d := by
    have : ((m2 * A : ℕ) : ℤ) = ((m3 * B + d : ℕ) : ℤ) := by push_cast; rw [hd, hD]; ring
    exact_mod_cast this
  have n3 : A = m3 * c + m1 * d := by
    have : ((A : ℕ) : ℤ) = ((m3 * c + m1 * d : ℕ) : ℤ) := by push_cast; rw [hc, hd]; exact eA
    exact_mod_cast this
  have n4 : B = m2 * c + m0 * d := by
    have : ((B : ℕ) : ℤ) = ((m2 * c + m0 * d : ℕ) : ℤ) := by push_cast; rw [hc, hd]; exact eB
    exact_mod_cast this
  have hdc : d < c := by omega
  refine ⟨c, d, n1, n2, hdc, ?_, ?_, gcd_of_unimod A B c d m3 m1 m2 m0 n3 n4
    (gcd_dvd_of_eq' A B c m1 m0 n1) (gcd_dvd_of_eq A B d m2 m3 n2)⟩
  · have h1 : c ≤ m3 * c := Nat.le_mul_of_pos_left c hm3
    omega
  · have h1 : c ≤ m2 * c := Nat.le_mul_of_pos_left c hm2
    omega


theorem apply_eq (m0 m1 m2 m3 : Std.U64) (sg : Bool) (A B : Std.U128) :
    algorithms.gcd.matrix.Matrix.apply_u128 (m0, m1, m2, m3, sg) A B =
      ok (if sg then
            (Aeneas.Std.U128.wrapping_sub (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m0) A)
               (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m1) B),
             Aeneas.Std.U128.wrapping_sub (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m3) B)
               (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m2) A))
          else
            (Aeneas.Std.U128.wrapping_sub (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m1) B)
               (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m0) A),
             Aeneas.Std.U128.wrapping_sub (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m2) A)
               (Aeneas.Std.U128.wrapping_mul (UScalar.cast .U128 m3) B))) := by
  cases sg <;> rfl

theorem apply_good (a0 a1 : Nat) (m : Mat) (hg : GoodM a0 a1 m) (A B : Std.U128) (s α β : Nat)
    (hα : α < 2^64) (hβ : β < 2^64) (hA : A.val * 2^s = 2^64 * a0 + α)
    (hB : B.val * 2^s = 2^64 * a1 + β) (hBA : B.val ≤ A.val) :
    algorithms.gcd.matrix.Matrix.apply_u128 m A B
    ⦃ cd => cd.1.val ≥ cd.2.val ∧
      (if m = algorithms.gcd.matrix.Matrix.IDENTITY then cd.1 = A ∧ cd.2 = B
       else cd.1.val ≤ A.val ∧ cd.2.val < B.val ∧ Nat.gcd A.val B.val = Nat.gcd cd.1.val cd.2.val) ⦄ := by
  have hAlt := u128_lt A
  have hBlt := u128_lt B
  obtain ⟨m0, m1, m2, m3, sg⟩ := m
  rw [apply_eq, WP.spec_ok]
  by_cases hid : (m0, m1, m2, m3, sg) = algorithms.gcd.matrix.Matrix.IDENTITY
  · rw [if_pos hid]
    rw [IDENTITY_eq] at hid
    simp only [Prod.mk.injEq] at hid
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hid
    have c1 := wsub_wmul 1#u64 0#u64 A B A.val (by simp) hAlt
    have c2 := wsub_wmul 1#u64 0#u64 B A B.val (by simp) hBlt
    rw [if_pos rfl]
    refine ⟨?_, UScalar.eq_of_val_eq c1, UScalar.eq_of_val_eq c2⟩
    rw [c1, c2]; exact hBA
  · rw [if_neg hid]
    rcases hg with h | ⟨X, Y, e0, e1, hm2, hm3, hrest⟩
    · rw [IDENTITY_eq] at hid; exact absurd h hid
    simp only at e0 e1 hm2 hm3 hrest
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrest ⊢
      obtain ⟨hdet, hY, hX⟩ := hrest
      obtain ⟨c, d, n1, n2, hdc, hcA, hdB, hg⟩ :=
        jebelean_false a0 a1 X Y m0.val m1.val m2.val m3.val A.val B.val α β s e0 e1 hm2 hm3 hdet hY hX
          hα hβ hA hB
      have c1 := wsub_wmul m1 m0 B A c n1 (by omega)
      have c2 := wsub_wmul m2 m3 A B d n2 (by omega)
      rw [c1, c2]
      exact ⟨hdc.le, hcA, hdB, hg⟩
    · simp only [↓reduceIte] at hrest ⊢
      obtain ⟨hdet, hY, hX⟩ := hrest
      obtain ⟨c, d, n1, n2, hdc, hcA, hdB, hg⟩ :=
        jebelean_true a0 a1 X Y m0.val m1.val m2.val m3.val A.val B.val α β s e0 e1 hm2 hm3 hdet hY hX
          hα hβ hA hB
      have c1 := wsub_wmul m0 m1 A B c n1 (by omega)
      have c2 := wsub_wmul m3 m2 B A d n2 (by omega)
      rw [c1, c2]
      exact ⟨hdc.le, hcA, hdB, hg⟩


theorem lz128 (x : Std.U128) (h : x.val ≠ 0) :
    (Aeneas.Std.core.num.U128.leading_zeros x).val = 127 - Nat.log 2 x.val := by
  unfold Aeneas.Std.core.num.U128.leading_zeros Aeneas.Std.BitVec.leadingZeros
  have h1 : x.bv ≠ 0 := by
    intro h2; apply h; simp [UScalar.val, h2]
  have h2 : Nat.log 2 x.val < 128 := Nat.log_lt_of_lt_pow h (u128_lt x)
  simp only [h1, if_false]
  change (BitVec.ofNat 32 (128 - Nat.log 2 x.val - 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  omega

theorem eq_ident (m : Mat) :
    algorithms.gcd.matrix.Matrix.Insts.CoreCmpPartialEqMatrix.eq m algorithms.gcd.matrix.Matrix.IDENTITY
    ⦃ r => (r = true ↔ m = algorithms.gcd.matrix.Matrix.IDENTITY) ⦄ := by
  obtain ⟨m0, m1, m2, m3, b⟩ := m
  rw [IDENTITY_eq]
  unfold algorithms.gcd.matrix.Matrix.Insts.CoreCmpPartialEqMatrix.eq
  show (if m0 = 1#u64 then if m1 = 0#u64 then if m2 = 0#u64 then if m3 = 1#u64 then
      ok (decide (b = true)) else ok false else ok false else ok false else ok false) ⦃ r =>
      r = true ↔ (m0, m1, m2, m3, b) = (1#u64, 0#u64, 0#u64, 1#u64, true) ⦄
  split_ifs with h0 h1 h2 h3 <;> rw [WP.spec_ok] <;> simp only [Prod.mk.injEq]
  · subst h0 h1 h2 h3; simp
  all_goals simp_all

/-- The original postcondition on every input except `a = b = 0`. -/
theorem from_u64_prefix_ok (a b : Std.U128)
    (hnot : ¬ (a.val = 0 ∧ b.val = 0)) :
    let hi := if a.val ≤ b.val then b else a
    let lo := if a.val ≤ b.val then a else b
    (do
      let s ← core.num.U128.leading_zeros hi
      let sa ← hi <<< s
      let sb ← lo <<< s
      let sa64 ← sa >>> 64#i32
      let sb64 ← sb >>> 64#i32
      let m ← algorithms.gcd.matrix.Matrix.from_u64_prefix (UScalar.cast .U64 sa64) (UScalar.cast .U64 sb64)
      let cd ← algorithms.gcd.matrix.Matrix.apply_u128 m hi lo
      let isId ← algorithms.gcd.matrix.Matrix.Insts.CoreCmpPartialEqMatrix.eq m
        algorithms.gcd.matrix.Matrix.IDENTITY
      ok (cd, isId))
    ⦃ r => r.1.1.val ≥ r.1.2.val ∧
      (if r.2 then r.1.1 = hi ∧ r.1.2 = lo
       else r.1.1.val ≤ hi.val ∧ r.1.2.val < lo.val ∧
         Nat.gcd hi.val lo.val = Nat.gcd r.1.1.val r.1.2.val) ⦄ := by
  have h_nonzero : a.val ≠ 0 ∨ b.val ≠ 0 := by
    by_cases ha : a.val = 0
    · by_cases hb : b.val = 0
      · exact absurd (And.intro ha hb) hnot
      · exact Or.inr hb
    · exact Or.inl ha
  dsimp only
  generalize hhi : (if a.val ≤ b.val then b else a) = hi
  generalize hlo : (if a.val ≤ b.val then a else b) = lo
  have hle : lo.val ≤ hi.val := by rw [← hhi, ← hlo]; split <;> omega
  have hhi0 : hi.val ≠ 0 := by rw [← hhi]; split <;> omega
  have hhib := u128_lt hi
  have hlog : Nat.log 2 hi.val < 128 := Nat.log_lt_of_lt_pow hhi0 hhib
  have hpow1 : 2^(Nat.log 2 hi.val) ≤ hi.val := Nat.pow_log_le_self 2 hhi0
  have hpow2 : hi.val < 2^(Nat.log 2 hi.val + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  unfold core.num.U128.leading_zeros rust_primitives.arithmetic.leading_zeros_u128
  have hs := lz128 hi hhi0
  step*
  have hsz : U128.size = 2^128 := by simp [U128.size, U128.numBits]
  generalize hk : (Aeneas.Std.core.num.U128.leading_zeros hi).val = k at *
  have hkL : k + Nat.log 2 hi.val = 127 := by omega
  have hhik : hi.val * 2^k < 2^128 := by
    have : hi.val * 2^k < 2^(Nat.log 2 hi.val + 1) * 2^k := Nat.mul_lt_mul_of_pos_right hpow2 (by positivity)
    rw [← pow_add] at this
    have e : Nat.log 2 hi.val + 1 + k = 128 := by omega
    rw [e] at this; exact this
  have hlok : lo.val * 2^k ≤ hi.val * 2^k := Nat.mul_le_mul_right _ hle
  have hsa : sa.val = hi.val * 2^k := by
    rw [sa_post1, Nat.shiftLeft_eq, hsz, Nat.mod_eq_of_lt hhik]
  have hsb : sb.val = lo.val * 2^k := by
    rw [sb_post1, Nat.shiftLeft_eq, hsz, Nat.mod_eq_of_lt (by omega)]
  have hsa127 : 2^127 ≤ hi.val * 2^k := by
    have : 2^(Nat.log 2 hi.val) * 2^k ≤ hi.val * 2^k := Nat.mul_le_mul_right _ hpow1
    rw [← pow_add, show Nat.log 2 hi.val + k = 127 by omega] at this; exact this
  have hsa64 : sa64.val = hi.val * 2^k / 2^64 := by rw [sa64_post1, Nat.shiftRight_eq_div_pow, hsa]
  have hsb64 : sb64.val = lo.val * 2^k / 2^64 := by rw [sb64_post1, Nat.shiftRight_eq_div_pow, hsb]
  have hlt64 : hi.val * 2^k / 2^64 < 2^64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [← pow_add]; exact hhik
  have hc0 : (UScalar.cast .U64 sa64).val = hi.val * 2^k / 2^64 := by
    rw [UScalar.cast_val_eq, hsa64]; exact Nat.mod_eq_of_lt hlt64
  have hc1 : (UScalar.cast .U64 sb64).val = lo.val * 2^k / 2^64 := by
    rw [UScalar.cast_val_eq, hsb64]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_div_right hlok) hlt64)
  have h0 : 2^63 ≤ (UScalar.cast .U64 sa64).val := by
    rw [hc0, Nat.le_div_iff_mul_le (by positivity), ← pow_add]; exact hsa127
  have h01 : (UScalar.cast .U64 sb64).val ≤ (UScalar.cast .U64 sa64).val := by
    rw [hc0, hc1]; exact Nat.div_le_div_right hlok
  apply spec_bind (from_u64_prefix_good _ _ h0 h01)
  intro m hm
  have hA : hi.val * 2^k = 2^64 * (UScalar.cast .U64 sa64).val + hi.val * 2^k % 2^64 := by
    rw [hc0]; exact (Nat.div_add_mod _ _).symm
  have hB : lo.val * 2^k = 2^64 * (UScalar.cast .U64 sb64).val + lo.val * 2^k % 2^64 := by
    rw [hc1]; exact (Nat.div_add_mod _ _).symm
  apply spec_bind (apply_good _ _ m hm hi lo k _ _ (Nat.mod_lt _ (by positivity))
    (Nat.mod_lt _ (by positivity)) hA hB hle)
  intro cd hcd
  apply spec_bind (eq_ident m)
  intro isId hid
  rw [WP.spec_ok]
  refine ⟨hcd.1, ?_⟩
  by_cases hmI : m = algorithms.gcd.matrix.Matrix.IDENTITY
  · have hcd2 := hcd.2
    split at hcd2
    · rw [if_pos (hid.mpr hmI)]; exact hcd2
    · contradiction
  · have hcd2 := hcd.2
    split at hcd2
    · contradiction
    · have : ¬ isId = true := fun h => hmI (hid.mp h)
      rw [if_neg this]
      exact hcd2

/-- `0u128.leading_zeros()` is 128. Adapted from `review/NonVacuity.lean`. -/
theorem leading_zeros_zero :
    core.num.U128.leading_zeros (0#u128) = ok (⟨128#32⟩ : Std.U32) := by
  simp [core.num.U128.leading_zeros, rust_primitives.arithmetic.leading_zeros_u128,
    Aeneas.Std.core.num.U128.leading_zeros, BitVec.leadingZeros]

/-- `0u128 << 128` panics in the debug profile. Adapted from `review/NonVacuity.lean`. -/
theorem shift_128_panics :
    ((0#u128 : Std.U128) <<< (⟨128#32⟩ : Std.U32) : RustM Std.U128) = fail .panic := by
  show UScalar.shiftLeft_UScalar _ _ = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
  rw [if_neg (by decide)]

/-- At `a = b = 0` the test body panics on the first shift. -/
theorem from_u64_prefix_zero_panics (a b : Std.U128) (hzero : a.val = 0 ∧ b.val = 0) :
    let hi := if a.val ≤ b.val then b else a
    let lo := if a.val ≤ b.val then a else b
    (do
      let s ← core.num.U128.leading_zeros hi
      let sa ← hi <<< s
      let sb ← lo <<< s
      let sa64 ← sa >>> 64#i32
      let sb64 ← sb >>> 64#i32
      let m ← algorithms.gcd.matrix.Matrix.from_u64_prefix (UScalar.cast .U64 sa64) (UScalar.cast .U64 sb64)
      let cd ← algorithms.gcd.matrix.Matrix.apply_u128 m hi lo
      let isId ← algorithms.gcd.matrix.Matrix.Insts.CoreCmpPartialEqMatrix.eq m
        algorithms.gcd.matrix.Matrix.IDENTITY
      ok (cd, isId)) = fail .panic := by
  dsimp only
  have ha : a = 0#u128 := by
    apply UScalar.eq_of_val_eq
    rw [hzero.1]
    decide
  have hb : b = 0#u128 := by
    apply UScalar.eq_of_val_eq
    rw [hzero.2]
    decide
  subst ha hb
  have hif : (if (0#u128).val ≤ (0#u128).val then (0#u128) else (0#u128)) = (0#u128) := by
    split <;> rfl
  simp only [hif]
  rw [leading_zeros_zero, bind_tc_ok, shift_128_panics, bind_tc_fail]

/--
For all `a b : u128`, with `(a, b) := (max(a, b), min(a, b))` normalised so
that the top bit of `a` is set, the Lehmer matrix computed by
`Matrix::from_u64_prefix` from the 64-bit prefixes (Jebelean's double-digit
condition, packed 32-bit cofactors) panics exactly when `a = b = 0`
(`leading_zeros` is 128 and `a << 128` overflows: an upstream bug) and
otherwise never panics, and applying it to the full `(a, b)` with
`apply_u128` yields `(c, d)` with `c >= d`; either the matrix is the
identity and `(c, d) = (a, b)`, or `c <= a`, `d < b` and
`gcd(a, b) = gcd(c, d)`.
-/
theorem from_u64_prefix_gcd (a b : Std.U128) :
    from_u64_prefix_spec a b := by
  unfold from_u64_prefix_spec
  refine ⟨fun hzero => ?_, fun hnot => from_u64_prefix_ok a b hnot⟩
  exact from_u64_prefix_zero_panics a b hzero

end Benchmark.Cases.Ruint.GcdMatrix
