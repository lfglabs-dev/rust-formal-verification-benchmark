import Benchmark.Cases.Succinct.Broadword.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open succinct

namespace Benchmark.Cases.Succinct.Broadword

/-- Byte `i` of a natural number. -/
def bt (x i : Nat) : Nat := x / 2 ^ (8 * i) % 256

theorem bt_eq (x i : Nat) : bt x i = (x >>> (8 * i)) % 2 ^ 8 := by
  simp [bt, Nat.shiftRight_eq_div_pow]

theorem bt_and (x y i : Nat) : bt (x &&& y) i = bt x i &&& bt y i := by
  simp only [bt_eq, Nat.shiftRight_and_distrib, Nat.and_mod_two_pow]

theorem bt_or (x y i : Nat) : bt (x ||| y) i = bt x i ||| bt y i := by
  simp only [bt_eq, Nat.shiftRight_or_distrib, Nat.or_mod_two_pow]

theorem bt_xor (x y i : Nat) : bt (x ^^^ y) i = bt x i ^^^ bt y i := by
  simp only [bt_eq, Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem bt_zero (x : Nat) : bt x 0 = x % 256 := by simp [bt]

theorem bt_succ (x i : Nat) : bt x (i + 1) = bt (x / 256) i := by
  simp only [bt, Nat.div_div_eq_div_mul]
  congr 2
  rw [show 8 * (i + 1) = 8 + 8 * i by ring, Nat.pow_add]

theorem bt_lt (x i : Nat) : bt x i < 256 := Nat.mod_lt _ (by norm_num)

/-- Subtraction without borrows is byte-wise. -/
theorem bt_sub : ∀ (i a b : Nat), b ≤ a → (∀ j ≤ i, bt b j ≤ bt a j) →
    bt (a - b) i = bt a i - bt b i := by
  intro i
  induction i with
  | zero =>
    intro a b hab h
    have h0 := h 0 (le_refl 0)
    simp only [bt_zero] at h0 ⊢
    omega
  | succ i ih =>
    intro a b hab h
    have h0 := h 0 (Nat.zero_le _)
    simp only [bt_zero] at h0
    have hdiv : (a - b) / 256 = a / 256 - b / 256 := by omega
    rw [bt_succ, bt_succ, bt_succ, hdiv]
    apply ih
    · exact Nat.div_le_div_right hab
    · intro j hj
      have := h (j + 1) (by omega)
      rwa [bt_succ, bt_succ] at this

theorem H8_val : broadword.H8.val = 0x8080808080808080 := by
  unfold broadword.H8; rfl

theorem L8_val : broadword.L8.val = 0x0101010101010101 := by
  unfold broadword.L8; rfl

theorem bt_H8 : ∀ i < 8, bt 0x8080808080808080 i = 128 := by decide
theorem bt_L8 : ∀ i < 8, bt 0x0101010101010101 i = 1 := by decide

theorem val_not64 (x : Std.U64) : (~~~x).val = 2 ^ 64 - 1 - x.val := by
  have h : (~~~x).bv = ~~~x.bv := rfl
  show (~~~x).bv.toNat = _
  rw [h, BitVec.toNat_not]
  rfl

theorem bt_ones : ∀ i < 8, bt (2 ^ 64 - 1) i = 255 := by decide

theorem bt_not (y i : Nat) (hy : y < 2 ^ 64) (hi : i < 8) : bt (2 ^ 64 - 1 - y) i = 255 - bt y i := by
  rw [bt_sub i _ _ (by omega), bt_ones i hi]
  intro j hj
  rw [bt_ones j (by omega)]
  have := bt_lt y j
  omega

theorem and128 (R : Nat) : R &&& 128 = 128 ↔ R.testBit 7 = true := by
  constructor
  · intro h
    have := congrArg (fun n => n.testBit 7) h
    have h128 : (128 : Nat).testBit 7 = true := by decide
    simpa [Nat.testBit_and, h128] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and]
    by_cases hj : j = 7
    · subst hj; simp [h]
    · have : (128 : Nat).testBit j = false := by
        rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.testBit_two_pow]
        simp only [decide_eq_false_iff_not]; omega
      simp [this]

theorem tb7 (x : Nat) (hx : x < 256) : x.testBit 7 = decide (128 ≤ x) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_decide]
  show x / 128 % 2 = 1 ↔ 128 ≤ x
  omega

theorem or128 : ∀ b < 256, b ||| 128 = 128 + b % 128 := by decide +kernel

theorem not255 : ∀ b < 256, 255 - b = b ^^^ 255 := by decide +kernel

theorem le8_byte (a b : Nat) (ha : a < 256) (hb : b < 256) :
    ((((b ||| 128) - (a &&& 127)) ||| (a ^^^ b)) ^^^ (a &&& (255 - b))) &&& 128 = 128 ↔ a ≤ b := by
  have hand : a &&& 127 = a % 128 := Nat.and_two_pow_sub_one_eq_mod a 7
  rw [and128, or128 b hb, hand, not255 b hb]
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and]
  have hT : 128 + b % 128 - a % 128 < 256 := by omega
  rw [tb7 _ hT, tb7 a ha, tb7 b hb, show (255 : Nat).testBit 7 = true from by decide]
  by_cases h1 : 128 ≤ a <;> by_cases h2 : 128 ≤ b <;> by_cases h3 : 128 ≤ 128 + b % 128 - a % 128 <;>
    simp [h1, h2, h3] <;> omega

/--
The broadword "parallel unsigned ≤" on the eight bytes of two words,
`u_le8(x, y) = ((((y | H8) - (x & !H8)) | (x ^ y)) ^ (x & !y)) & H8`, never
panics and sets byte `i` of the result to `0x80` exactly when byte `i` of `x`
is at most byte `i` of `y`.
-/
theorem u_le8_bytewise (n m : Std.U64) :
    u_le8_bytewise_spec n m := by
  unfold u_le8_bytewise_spec broadword.u_le8
  have hH := H8_val
  have hn := n.hBounds
  have hm := m.hBounds
  have hnH : (~~~broadword.H8).val = 0x7F7F7F7F7F7F7F7F := by rw [val_not64, hH]; norm_num
  step*
  · rw [i2_post1, i_post1, UScalar.val_and, UScalar.val_or, i1_post, hnH, hH]
    have := Nat.right_le_or (n := m.val) (m := 0x8080808080808080)
    have := Nat.and_le_right (n := n.val) (m := 0x7F7F7F7F7F7F7F7F)
    omega
  · intro k hk
    have hsub1 : n.val &&& 0x7F7F7F7F7F7F7F7F ≤ m.val ||| 0x8080808080808080 := by
      have := Nat.right_le_or (n := m.val) (m := 0x8080808080808080)
      have := Nat.and_le_right (n := n.val) (m := 0x7F7F7F7F7F7F7F7F)
      omega
    have hbt7F : ∀ j < 8, bt 0x7F7F7F7F7F7F7F7F j = 127 := by decide
    have hbytes : ∀ j ≤ k, bt (n.val &&& 0x7F7F7F7F7F7F7F7F) j ≤ bt (m.val ||| 0x8080808080808080) j := by
      intro j hj
      rw [bt_and, bt_or, bt_H8 j (by omega), hbt7F j (by omega)]
      have := Nat.right_le_or (n := bt m.val j) (m := 128)
      have := Nat.and_le_right (n := bt n.val j) (m := 127)
      omega
    show bt n.val k ≤ bt m.val k ↔ bt (i8 &&& broadword.H8).val k = 128
    rw [UScalar.val_and, i8_post1, UScalar.val_xor, i5_post1, UScalar.val_or, i3_post1, i_post1,
      i2_post1, UScalar.val_and, UScalar.val_or, i1_post, hnH, i4_post1, UScalar.val_xor,
      i7_post1, UScalar.val_and, i6_post, val_not64, hH,
      bt_and, bt_xor, bt_or, bt_sub k _ _ hsub1 hbytes, bt_or, bt_and, bt_xor, bt_and,
      bt_not _ _ m.hBounds hk, bt_H8 k hk, hbt7F k hk]
    exact (le8_byte _ _ (bt_lt _ _) (bt_lt _ _)).symm

end Benchmark.Cases.Succinct.Broadword
