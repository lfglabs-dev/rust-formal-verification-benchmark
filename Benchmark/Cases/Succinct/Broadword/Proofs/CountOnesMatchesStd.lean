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

/-- Number of set bits among the `n` lowest bits of `x`. -/
def pc (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pc x n + (x.testBit n).toNat

theorem pc_add (x a : Nat) : ∀ b, pc x (a + b) = pc x a + pc (x >>> a) b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc, pc, ih, pc, Nat.testBit_shiftRight, Nat.add_assoc]

theorem pc_mod (x : Nat) : ∀ n, n ≤ 8 → pc (x % 256) n = pc x n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [pc, pc, ih (by omega)]
    congr 2
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
    simp; omega

theorem pc_bytes (x : Nat) : ∀ n, pc x (8 * n) = ∑ j ∈ Finset.range n, pc (bt x j) 8 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, show 8 * (n + 1) = 8 * n + 8 by ring, pc_add, bt_eq,
      show (2 : Nat) ^ 8 = 256 by norm_num, pc_mod _ 8 (le_refl _)]

theorem bt_decomp (x : Nat) : ∀ n, x % 256 ^ n = ∑ j ∈ Finset.range n, bt x j * 256 ^ j := by
  intro n
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Nat.mod_pow_succ, ih, Finset.sum_range_succ, bt, pow_mul]
    norm_num; ring

theorem hP (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) : (c0 + c1 * 256 + c2 * 256 ^ 2 + c3 * 256 ^ 3 + c4 * 256 ^ 4 + c5 * 256 ^ 5 + c6 * 256 ^ 6 + c7 * 256 ^ 7) * 0x0101010101010101 =
      (c0 + (c0 + c1) * 256 + (c0 + c1 + c2) * 256 ^ 2 + (c0 + c1 + c2 + c3) * 256 ^ 3 + (c0 + c1 + c2 + c3 + c4) * 256 ^ 4 + (c0 + c1 + c2 + c3 + c4 + c5) * 256 ^ 5 + (c0 + c1 + c2 + c3 + c4 + c5 + c6) * 256 ^ 6 + (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7) * 256 ^ 7) + 2 ^ 64 * ((c1 + c2 + c3 + c4 + c5 + c6 + c7) + (c2 + c3 + c4 + c5 + c6 + c7) * 256 + (c3 + c4 + c5 + c6 + c7) * 256 ^ 2 + (c4 + c5 + c6 + c7) * 256 ^ 3 + (c5 + c6 + c7) * 256 ^ 4 + (c6 + c7) * 256 ^ 5 + c7 * 256 ^ 6) := by
  ring

theorem hT (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8)
    (h3 : c3 ≤ 8) (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    (c0 + (c0 + c1) * 256 + (c0 + c1 + c2) * 256 ^ 2 + (c0 + c1 + c2 + c3) * 256 ^ 3 + (c0 + c1 + c2 + c3 + c4) * 256 ^ 4 + (c0 + c1 + c2 + c3 + c4 + c5) * 256 ^ 5 + (c0 + c1 + c2 + c3 + c4 + c5 + c6) * 256 ^ 6 + (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7) * 256 ^ 7) / 2 ^ 56 = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
  apply Nat.div_eq_of_lt_le <;> norm_num <;> omega

theorem hTlt (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8)
    (h3 : c3 ≤ 8) (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    (c0 + (c0 + c1) * 256 + (c0 + c1 + c2) * 256 ^ 2 + (c0 + c1 + c2 + c3) * 256 ^ 3 + (c0 + c1 + c2 + c3 + c4) * 256 ^ 4 + (c0 + c1 + c2 + c3 + c4 + c5) * 256 ^ 5 + (c0 + c1 + c2 + c3 + c4 + c5 + c6) * 256 ^ 6 + (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7) * 256 ^ 7) < 2 ^ 64 := by
  norm_num; omega

theorem mul_L8_top (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8)
    (h3 : c3 ≤ 8) (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    (c0 + c1 * 256 + c2 * 256 ^ 2 + c3 * 256 ^ 3 + c4 * 256 ^ 4 + c5 * 256 ^ 5 + c6 * 256 ^ 6 + c7 * 256 ^ 7) * 0x0101010101010101 % 2 ^ 64 / 2 ^ 56 = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
  rw [hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hTlt c0 c1 c2 c3 c4 c5 c6 c7 h0 h1 h2 h3 h4 h5 h6 h7),
    hT c0 c1 c2 c3 c4 c5 c6 c7 h0 h1 h2 h3 h4 h5 h6 h7]

theorem div_swap (y a b : Nat) : y / a / b = y / b / a := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bt_shr1 (y i : Nat) : bt (y / 2) i = bt y i / 2 + 128 * (bt y (i + 1) % 2) := by
  rw [bt_succ]; unfold bt
  rw [div_swap y 2, div_swap y 256]
  generalize y / 2 ^ (8 * i) = Y
  omega

theorem bt_shr2 (y i : Nat) : bt (y / 4) i = bt y i / 4 + 64 * (bt y (i + 1) % 4) := by
  rw [bt_succ]; unfold bt
  rw [div_swap y 4, div_swap y 256]
  generalize y / 2 ^ (8 * i) = Y
  omega

theorem bt_shr4 (y i : Nat) : bt (y / 16) i = bt y i / 16 + 16 * (bt y (i + 1) % 16) := by
  rw [bt_succ]; unfold bt
  rw [div_swap y 16, div_swap y 256]
  generalize y / 2 ^ (8 * i) = Y
  omega

/-- Addition without carries is byte-wise. -/
theorem bt_add : ∀ (i a b : Nat), (∀ j ≤ i, bt a j + bt b j < 256) →
    bt (a + b) i = bt a i + bt b i := by
  intro i
  induction i with
  | zero =>
    intro a b h
    have h0 := h 0 (le_refl 0)
    simp only [bt_zero] at h0 ⊢
    omega
  | succ i ih =>
    intro a b h
    have h0 := h 0 (Nat.zero_le _)
    simp only [bt_zero] at h0
    have hdiv : (a + b) / 256 = a / 256 + b / 256 := by omega
    rw [bt_succ, bt_succ, bt_succ, hdiv]
    apply ih
    intro j hj
    have := h (j + 1) (by omega)
    rwa [bt_succ, bt_succ] at this

theorem bt_big (x j : Nat) (hx : x < 2 ^ 64) (hj : 8 ≤ j) : bt x j = 0 := by
  unfold bt
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem pc_le (x : Nat) : ∀ n, pc x n ≤ n := by
  intro n
  induction n with
  | zero => exact le_refl 0
  | succ n ih => rw [pc]; cases x.testBit n <;> simp <;> omega

def s1 (b : Nat) : Nat := b - (b &&& 170) / 2
def s2 (b : Nat) : Nat := (s1 b &&& 51) + (s1 b / 4 &&& 51)
def s3 (b : Nat) : Nat := (s2 b + s2 b / 16) % 16

theorem s_facts : ∀ b < 256, s3 b = pc b 8 ∧ s2 b % 16 ≤ 4 ∧ s2 b / 16 ≤ 4 ∧ s2 b ≤ 68 := by
  decide +kernel

theorem mask51 : ∀ u < 64, ∀ t < 4, (u + 64 * t) &&& 51 = u &&& 51 := by
  decide +kernel

theorem bt_A : ∀ j < 8, bt 0xAAAAAAAAAAAAAAAA j = 170 := by decide
theorem bt_M2 : ∀ j < 8, bt 0x3333333333333333 j = 51 := by decide
theorem bt_M4 : ∀ j < 8, bt 0x0F0F0F0F0F0F0F0F j = 15 := by decide

theorem bt_A_even (j : Nat) : bt 0xAAAAAAAAAAAAAAAA j % 2 = 0 := by
  by_cases hj : j < 8
  · rw [bt_A j hj]
  · rw [bt_big _ _ (by norm_num) (by omega)]

theorem try_from_one :
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize =
      ok (core.result.Result.Ok 1#u32) := by
  unfold core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  simp [lift, core.num.U32.MAX, core.num.U32.MIN, U32.rMax]
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast]
  rfl

theorem range_next_lt (i e : Std.U32) (h : i.val < e.val) :
    ∃ i' : Std.U32, i'.val = i.val + 1 ∧
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.Some i, { start := i', «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, core.U32.Insts.CoreCloneClone.clone,
    core.U32.Insts.CoreIterRangeStep.forward_checked, try_from_one,
    core.num.U32.checked_add, core.num.U32.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u32]
  have hmax : i.val + (1#u32).val ≤ UScalar.max UScalarTy.U32 := by
    have := e.hmax; simp only [UScalar.max] at *; scalar_tac
  have := UScalar.overflowing_add_eq i 1#u32
  simp only [gt_iff_lt, Nat.not_lt.mpr hmax, if_false] at this
  obtain ⟨h1, h2⟩ := this
  generalize UScalar.overflowing_add i 1#u32 = z at *
  obtain ⟨r, b⟩ := z
  simp only at h1 h2
  subst h2
  exact ⟨r, by simpa using h1, rfl⟩

theorem range_next_ge (i e : Std.U32) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

theorem shr_bit (x : Std.U64) (i : Std.U32) (hi : i.val < 64) :
    ∃ z : Std.U64, z.val = x.val / 2 ^ i.val ∧ x >>> i = ok z := by
  have hs := U64.ShiftRight_spec x i
  cases h : x >>> i with
  | ok z =>
    rw [h] at hs
    simp only [partialSpec_ok] at hs
    exact ⟨z, by rw [hs.1, Nat.shiftRight_eq_div_pow], rfl⟩
  | fail e =>
    rw [h] at hs
    cases e <;> simp [partialSpec] at hs
    omega
  | div =>
    rw [h] at hs
    simp [partialSpec] at hs

theorem body_ge (x : Std.U64) (i n : Std.U32) (h : ¬ i.val < 64) :
    core.num.U64.count_ones_loop.body x { start := i, «end» := 64#u32 } n = ok (.done n) := by
  unfold core.num.U64.count_ones_loop.body
  rw [range_next_ge i _ (by simpa using h)]
  rfl

theorem body_lt (x : Std.U64) (i n : Std.U32) (h : i.val < 64) (hn : n.val ≤ 64) :
    ∃ i' n' : Std.U32, i'.val = i.val + 1 ∧ n'.val = n.val + (x.val.testBit i.val).toNat ∧
      core.num.U64.count_ones_loop.body x { start := i, «end» := 64#u32 } n =
        ok (.cont ({ start := i', «end» := 64#u32 }, n')) := by
  obtain ⟨i', hi', hnext⟩ := range_next_lt i 64#u32 (by simpa using h)
  obtain ⟨z, hz, hsh⟩ := shr_bit x i h
  unfold core.num.U64.count_ones_loop.body
  rw [hnext]
  simp only [bind_tc_ok, hsh, lift]
  have hand : (z &&& 1#u64).val = x.val / 2 ^ i.val % 2 := by
    rw [UScalar.val_and, hz]; simp [Nat.and_one_is_mod]
  by_cases hb : x.val / 2 ^ i.val % 2 = 1
  · have heq : (z &&& 1#u64) = 1#u64 := by
      apply UScalar.eq_of_val_eq; rw [hand, hb]; rfl
    have htb : x.val.testBit i.val = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp [hb]
    obtain ⟨n1, hn1, hadd⟩ : ∃ n1 : Std.U32, n1.val = n.val + 1 ∧ n + 1#u32 = ok n1 := by
      have hs := U32.add_spec (x := n) (y := 1#u32)
      cases hh : n + 1#u32 with
      | ok y =>
        rw [hh] at hs
        simp only [partialSpec_ok] at hs
        exact ⟨y, by simpa using hs, rfl⟩
      | fail e =>
        rw [hh] at hs
        cases e <;> simp [partialSpec] at hs
        scalar_tac
      | div =>
        rw [hh] at hs
        simp [partialSpec] at hs
    refine ⟨i', n1, hi', by rw [hn1, htb]; rfl, ?_⟩
    simp [hsh, heq, hadd]
  · have heq : (z &&& 1#u64) ≠ 1#u64 := by
      intro hc; have := congrArg UScalar.val hc; rw [hand] at this; simp at this; omega
    have htb : x.val.testBit i.val = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp [hb]
    refine ⟨i', n, hi', by rw [htb]; rfl, ?_⟩
    simp [hsh, heq]

theorem count_loop_spec (x : Std.U64) : ∀ (k : Nat) (i : Std.U32) (n : Std.U32),
    64 - i.val = k → i.val ≤ 64 → n.val = pc x.val i.val →
    core.num.U64.count_ones_loop { start := i, «end» := 64#u32 } x n ⦃ r => r.val = pc x.val 64 ⦄ := by
  intro k
  induction k with
  | zero =>
    intro i n hk hi hn
    unfold core.num.U64.count_ones_loop
    rw [loop.eq_1]
    simp only [body_ge x i n (by omega), WP.spec_ok]
    rw [hn, show i.val = 64 by omega]
  | succ k ih =>
    intro i n hk hi hn
    have hnle : n.val ≤ 64 := by rw [hn]; have := pc_le x.val i.val; omega
    obtain ⟨i', n', hi', hn', hb⟩ := body_lt x i n (by omega) hnle
    unfold core.num.U64.count_ones_loop
    rw [loop.eq_1]
    simp only [hb]
    apply ih i' n' (by omega) (by omega)
    rw [hn', hn, hi', pc]

theorem L8_val : broadword.L8.val = 0x0101010101010101 := by
  unfold broadword.L8; rfl

theorem and_mod2 (a b : Nat) (hb : b % 2 = 0) : (a &&& b) % 2 = 0 := by
  have := Nat.and_mod_two_pow (a := a) (b := b) (n := 1)
  rw [show (2 : Nat) ^ 1 = 2 by norm_num] at this
  rw [this, hb, Nat.and_zero]

theorem core_bytes (X X1 X2 X3 : Nat) (hX : X < 2 ^ 64)
    (h1 : X1 = X - (X &&& 0xAAAAAAAAAAAAAAAA) / 2)
    (h2 : X2 = (X1 &&& 0x3333333333333333) + (X1 / 4 &&& 0x3333333333333333))
    (h3 : X3 = (X2 + X2 / 16) &&& 0x0F0F0F0F0F0F0F0F) :
    ∀ i < 8, bt X3 i = pc (bt X i) 8 := by
  have hY1 : ∀ j, bt ((X &&& 0xAAAAAAAAAAAAAAAA) / 2) j = (bt X j &&& bt 0xAAAAAAAAAAAAAAAA j) / 2 := by
    intro j
    rw [bt_shr1, bt_and, bt_and, and_mod2 _ _ (bt_A_even _)]
    simp
  have hX1 : ∀ i < 8, bt X1 i = s1 (bt X i) := by
    intro i hi
    rw [h1, bt_sub, hY1, bt_A i hi]
    · rfl
    · exact le_trans (Nat.div_le_self _ _) Nat.and_le_left
    · intro j _
      rw [hY1]
      exact le_trans (Nat.div_le_self _ _) Nat.and_le_left
  have hX2 : ∀ i < 8, bt X2 i = s2 (bt X i) := by
    intro i hi
    rw [h2, bt_add, bt_and, bt_and, bt_M2 i hi, bt_shr2, hX1 i hi,
      mask51 _ (by have := bt_lt X i; unfold s1; omega) _ (Nat.mod_lt _ (by norm_num))]
    · rfl
    · intro j hj
      rw [bt_and, bt_and, bt_M2 j (by omega)]
      have := Nat.and_le_right (n := bt X1 j) (m := 51)
      have := Nat.and_le_right (n := bt (X1 / 4) j) (m := 51)
      omega
  have hX2lt : X2 < 2 ^ 64 := by
    rw [h2]
    have := Nat.and_le_right (n := X1) (m := 0x3333333333333333)
    have := Nat.and_le_right (n := X1 / 4) (m := 0x3333333333333333)
    omega
  have hX2b : ∀ j, bt X2 j % 16 ≤ 4 ∧ bt X2 j ≤ 68 := by
    intro j
    by_cases hj : j < 8
    · rw [hX2 j hj]
      have := s_facts (bt X j) (bt_lt _ _)
      omega
    · rw [bt_big _ _ hX2lt (by omega)]; omega
  intro i hi
  have hb := s_facts (bt X i) (bt_lt _ _)
  rw [h3, bt_and, bt_M4 i hi, bt_add, bt_shr4, hX2 i hi,
    show (15 : Nat) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, ← hb.1]
  · unfold s3; omega
  · intro j hj
    rw [bt_shr4]
    have := hX2b j
    have := hX2b (j + 1)
    omega

theorem fast_spec (x : Std.U64) :
    broadword.count_ones x ⦃ r => r.val = ∑ j ∈ Finset.range 8, pc (bt x.val j) 8 ⦄ := by
  unfold broadword.count_ones
  have hL := L8_val
  have hx := x.hBounds
  simp only [core.num.U64.wrapping_mul, rust_primitives.arithmetic.wrapping_mul_u64]
  step*
  · rw [i1_post1, i_post1, UScalar.val_and, Nat.shiftRight_eq_div_pow]
    exact le_trans (Nat.div_le_self _ _) Nat.and_le_left
  · rw [i2_post1, i4_post1, UScalar.val_and, UScalar.val_and]
    have := Nat.and_le_right (n := x1.val) (m := 3689348814741910323)
    have := Nat.and_le_right (n := i3.val) (m := 3689348814741910323)
    simp only [U64.max_def] at *
    scalar_tac
  · rw [x2_post, i5_post1, i2_post1, i4_post1, UScalar.val_and, UScalar.val_and, Nat.shiftRight_eq_div_pow]
    have := Nat.and_le_right (n := x1.val) (m := 3689348814741910323)
    have := Nat.and_le_right (n := i3.val) (m := 3689348814741910323)
    simp only [U64.max_def] at *
    scalar_tac
  · have hX : x.val < 2 ^ 64 := hx
    have h1 : x1.val = x.val - (x.val &&& 0xAAAAAAAAAAAAAAAA) / 2 := by
      rw [x1_post1, i1_post1, i_post1, UScalar.val_and, Nat.shiftRight_eq_div_pow]; rfl
    have h2 : x2.val = (x1.val &&& 0x3333333333333333) + (x1.val / 4 &&& 0x3333333333333333) := by
      rw [x2_post, i2_post1, i4_post1, UScalar.val_and, UScalar.val_and, i3_post1,
        Nat.shiftRight_eq_div_pow]; rfl
    have h3 : x3.val = (x2.val + x2.val / 16) &&& 0x0F0F0F0F0F0F0F0F := by
      rw [x3_post1, UScalar.val_and, i6_post, i5_post1, Nat.shiftRight_eq_div_pow]; rfl
    have hbytes := core_bytes x.val x1.val x2.val x3.val hX h1 h2 h3
    have hx3 : x3.val = ∑ j ∈ Finset.range 8, bt x3.val j * 256 ^ j := by
      rw [← bt_decomp, Nat.mod_eq_of_lt]
      have := x3.hBounds
      exact lt_of_lt_of_le this (by norm_num)
    have hres : i8.val = (x3.val * 0x0101010101010101 % 2 ^ 64) / 2 ^ 56 := by
      rw [i8_post1, U64.wrapping_mul_val_eq, hL, Nat.shiftRight_eq_div_pow, UScalar.size_def]; rfl
    have hsmall : i8.val < 2 ^ UScalarTy.Usize.numBits := by
      have h8 : i8.val < 2 ^ 8 := by
        rw [hres]
        apply Nat.div_lt_of_lt_mul
        have := Nat.mod_lt (x3.val * 0x0101010101010101) (show 2 ^ 64 > 0 by norm_num)
        omega
      have hnb : 8 ≤ UScalarTy.Usize.numBits := by
        rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with h | h <;> omega
      exact lt_of_lt_of_le h8 (Nat.pow_le_pow_right (by norm_num) hnb)
    rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt hsmall, hres, hx3]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
    rw [hbytes 0 (by norm_num), hbytes 1 (by norm_num), hbytes 2 (by norm_num), hbytes 3 (by norm_num),
      hbytes 4 (by norm_num), hbytes 5 (by norm_num), hbytes 6 (by norm_num), hbytes 7 (by norm_num)]
    apply mul_L8_top <;> exact pc_le _ 8

/--
For every 64-bit word, Vigna's broadword population count `count_ones`
(SWAR: 2-bit, 4-bit and byte partial sums, then a wrapping multiplication by
`L8 = 0x0101_0101_0101_0101` and a shift by 56) never panics and returns the
same number as the standard `u64::count_ones`.
-/
theorem count_ones_matches_std (word : Std.U64) :
    count_ones_matches_std_spec word := by
  unfold count_ones_matches_std_spec
  apply spec_bind (fast_spec word)
  intro a ha
  apply spec_bind (count_loop_spec word 64 0#u32 0#u32 (by simp) (by simp) (by simp [pc]))
  intro b hb
  rw [WP.spec_ok]
  show a.val = b.val
  rw [ha, hb, show (64 : Nat) = 8 * 8 by norm_num, pc_bytes]

end Benchmark.Cases.Succinct.Broadword
