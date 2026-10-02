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

theorem nz8_byte : ∀ b < 256, ((((b ||| 128) - 1) ||| b) &&& 128 = 128 ↔ b ≠ 0) := by
  decide +kernel

/--
The broadword "parallel > 0" `u_nz8(n) = (((n | H8) - L8) | n) & H8` never
panics and, for each of the eight bytes, sets byte `i` of the result to
`0x80` exactly when byte `i` of `n` is non-zero.
-/
theorem u_nz8_bytewise (n : Std.U64) :
    u_nz8_bytewise_spec n := by
  unfold u_nz8_bytewise_spec broadword.u_nz8
  have hH := H8_val
  have hL := L8_val
  have hn := n.hBounds
  step*
  · rw [i_post1, UScalar.val_or, hL, hH]
    have := Nat.right_le_or (n := n.val) (m := 0x8080808080808080)
    omega
  · intro k hk
    have hsubL : 0x0101010101010101 ≤ n.val ||| 0x8080808080808080 := by
      have := Nat.right_le_or (n := n.val) (m := 0x8080808080808080)
      omega
    have hbytes : ∀ j ≤ k, bt 0x0101010101010101 j ≤ bt (n.val ||| 0x8080808080808080) j := by
      intro j hj
      rw [bt_L8 j (by omega), bt_or, bt_H8 j (by omega)]
      have := Nat.right_le_or (n := bt n.val j) (m := 128)
      omega
    show bt n.val k ≠ 0 ↔ bt (i2 &&& broadword.H8).val k = 128
    rw [UScalar.val_and, i2_post1, UScalar.val_or, i1_post1, i_post1, UScalar.val_or, hH, hL,
      bt_and, bt_or, bt_sub k _ _ hsubL hbytes, bt_or, bt_H8 k hk, bt_L8 k hk]
    exact (nz8_byte _ (bt_lt _ _)).symm

end Benchmark.Cases.Succinct.Broadword
