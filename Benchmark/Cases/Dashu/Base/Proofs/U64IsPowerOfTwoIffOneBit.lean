import Benchmark.Cases.Dashu.Base.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

theorem pot_numBits_ge : 32 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all

theorem pot_try_from_one :
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize =
      ok (core.result.Result.Ok 1#u32) := by
  unfold core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  simp only [lift, bind_tc_ok]
  have hpow : (2:Nat)^32 ≤ 2^System.Platform.numBits :=
    Nat.pow_le_pow_right (by norm_num) pot_numBits_ge
  have hmaxv : (UScalar.cast .Usize core.num.U32.MAX).val = 4294967295 := by
    rw [UScalar.cast_val_eq]
    have hv : (core.num.U32.MAX).val = 4294967295 := by rfl
    rw [hv, UScalarTy.Usize_numBits_eq]
    apply Nat.mod_eq_of_lt
    omega
  have hminv : (UScalar.cast .Usize core.num.U32.MIN).val = 0 := by
    rw [UScalar.cast_val_eq]
    have hv : (core.num.U32.MIN).val = 0 := by rfl
    rw [hv]; simp
  have h1v : (1#usize).val = 1 := by simp
  have h1 : ¬ (1#usize > UScalar.cast .Usize core.num.U32.MAX) := by
    rw [gt_iff_lt, UScalar.lt_equiv, hmaxv, h1v]; omega
  have h2 : ¬ (1#usize < UScalar.cast .Usize core.num.U32.MIN) := by
    rw [UScalar.lt_equiv, hminv, h1v]; omega
  simp only [h1, h2, if_false]
  congr
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq, h1v]
  simp

theorem pot_range_next_lt (i e : Std.U32) (h : i.val < e.val) :
    ∃ i' : Std.U32, i'.val = i.val + 1 ∧
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.Some i, { start := i', «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next, core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, core.U32.Insts.CoreCloneClone.clone,
    core.U32.Insts.CoreIterRangeStep.forward_checked, pot_try_from_one,
    core.num.U32.checked_add, core.num.U32.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u32, if_true, ite_true]
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

theorem pot_range_next_ge (i e : Std.U32) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next, core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

/-- Number of set bits of `x` at positions `< i`. -/
def pot_popc (x : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => pot_popc x i + (if x.testBit i then 1 else 0)

theorem pot_body_lt (x : Std.U64) (i n : Std.U32) (hi : i.val < 64) (hn : n.val ≤ i.val) :
    core.num.U64.count_ones_loop.body x { start := i, «end» := 64#u32 } n ⦃ cf =>
      ∃ i' n' : Std.U32, cf = ControlFlow.cont ({ start := i', «end» := 64#u32 }, n') ∧
        i'.val = i.val + 1 ∧ n'.val = n.val + (if x.val.testBit i.val then 1 else 0) ⦄ := by
  obtain ⟨i', hi', hnext⟩ := pot_range_next_lt i 64#u32 (by simpa using hi)
  unfold core.num.U64.count_ones_loop.body
  rw [hnext]
  simp only [bind_tc_ok]
  step as ⟨s, hs⟩
  simp only [lift, bind_tc_ok]
  have hand : (s &&& 1#u64).val = x.val / 2 ^ i.val % 2 := by
    rw [UScalar.val_and, hs, Nat.shiftRight_eq_div_pow]
    simp [Nat.and_one_is_mod]
  have htb : x.val.testBit i.val = decide (x.val / 2 ^ i.val % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  split
  · rename_i heq
    have h1 : x.val / 2 ^ i.val % 2 = 1 := by
      have := congrArg UScalar.val heq; rw [hand] at this; simpa using this
    step as ⟨n1, hn1⟩
    exact ⟨i', n1, rfl, hi', by rw [hn1, htb]; simp [h1]⟩
  · rename_i hne
    have h0 : x.val / 2 ^ i.val % 2 ≠ 1 := by
      intro hc; apply hne; apply UScalar.eq_of_val_eq; rw [hand, hc]; rfl
    exact ⟨i', n, rfl, hi', by rw [htb]; simp [h0]⟩

theorem pot_body_ge (x : Std.U64) (i n : Std.U32) (hi : ¬ i.val < 64) :
    core.num.U64.count_ones_loop.body x { start := i, «end» := 64#u32 } n =
      ok (ControlFlow.done n) := by
  unfold core.num.U64.count_ones_loop.body
  rw [pot_range_next_ge i 64#u32 (by simpa using hi)]
  rfl

theorem pot_loop (x : Std.U64) : ∀ (k : Nat) (i n : Std.U32),
    64 - i.val = k → i.val ≤ 64 → n.val = pot_popc x.val i.val →
    core.num.U64.count_ones_loop { start := i, «end» := 64#u32 } x n ⦃ c =>
      c.val = pot_popc x.val 64 ⦄ := by
  intro k
  induction k with
  | zero =>
    intro i n hk hi hn
    have hge : ¬ i.val < 64 := by omega
    have hi64 : i.val = 64 := by omega
    unfold core.num.U64.count_ones_loop
    rw [loop.eq_1]
    simp only [pot_body_ge x i n hge, bind_tc_ok, WP.spec_ok]
    rw [hn, hi64]
  | succ k ih =>
    intro i n hk hi hn
    have hlt : i.val < 64 := by omega
    have hpc : pot_popc x.val i.val ≤ i.val := by
      clear hk hi hn hlt ih
      generalize i.val = m
      induction m with
      | zero => simp [pot_popc]
      | succ m ihm => simp only [pot_popc]; split <;> omega
    obtain ⟨cf, hbody, i', n', rfl, hi', hn'⟩ := spec_imp_exists (pot_body_lt x i n hlt (by omega))
    unfold core.num.U64.count_ones_loop
    rw [loop.eq_1]
    simp only [hbody]
    have := ih i' n' (by omega) (by omega) (by rw [hn', hi', hn]; rfl)
    unfold core.num.U64.count_ones_loop at this
    exact this

theorem pot_popc_zero_iff (x : Nat) : ∀ i, pot_popc x i = 0 ↔ ∀ j < i, x.testBit j = false := by
  intro i
  induction i with
  | zero => simp [pot_popc]
  | succ i ih =>
    simp only [pot_popc]
    constructor
    · intro h j hj
      by_cases hb : x.testBit i = true
      · simp [hb] at h
      · simp only [hb, ↓reduceIte, Nat.add_zero] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact ih.mp h j hj
        · subst hj; simpa using hb
    · intro h
      have hb : x.testBit i = false := h i (by omega)
      have := ih.mpr (fun j hj => h j (by omega))
      simp [hb, this]

theorem pot_popc_one_iff (x : Nat) : ∀ i, pot_popc x i = 1 ↔
    ∃ k < i, x.testBit k = true ∧ ∀ j < i, j ≠ k → x.testBit j = false := by
  intro i
  induction i with
  | zero => simp [pot_popc]
  | succ i ih =>
    simp only [pot_popc]
    by_cases hb : x.testBit i = true
    · simp only [hb, ↓reduceIte]
      rw [show pot_popc x i + 1 = 1 ↔ pot_popc x i = 0 by omega, pot_popc_zero_iff]
      constructor
      · intro h
        exact ⟨i, by omega, hb, fun j hj hji => h j (by omega)⟩
      · rintro ⟨k, hk, hkb, hall⟩ j hj
        by_cases hki : k = i
        · subst hki; exact hall j (by omega) (by omega)
        · have := hall i (by omega) (fun h => hki h.symm)
          simp [hb] at this
    · rw [if_neg hb, Nat.add_zero, ih]
      constructor
      · rintro ⟨k, hk, hkb, hall⟩
        refine ⟨k, by omega, hkb, fun j hj hjk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hall j hj hjk
        · subst hj; simpa using hb
      · rintro ⟨k, hk, hkb, hall⟩
        have hki : k ≠ i := by intro h; subst h; exact hb hkb
        exact ⟨k, by omega, hkb, fun j hj hjk => hall j (by omega) hjk⟩

theorem pot_one_bit_iff_pow (x : Nat) (hx : x < 2^64) :
    (∃ k < 64, x.testBit k = true ∧ ∀ j < 64, j ≠ k → x.testBit j = false) ↔
      ∃ k, x = 2^k := by
  constructor
  · rintro ⟨k, hk, hkb, hall⟩
    refine ⟨k, Nat.eq_of_testBit_eq fun j => ?_⟩
    rw [Nat.testBit_two_pow]
    by_cases hjk : j = k
    · subst hjk; simp [hkb]
    · have : x.testBit j = false := by
        by_cases hj : j < 64
        · exact hall j hj hjk
        · exact Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [this]
      simp [Ne.symm hjk]
  · rintro ⟨k, rfl⟩
    have hk : k < 64 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hx
    exact ⟨k, hk, by simp [Nat.testBit_two_pow],
      fun j _ hjk => by simp [Nat.testBit_two_pow, Ne.symm hjk]⟩

/--
For every `u64`, dashu's `PowerOfTwo::is_power_of_two` never panics and
returns `true` exactly when the population count `x.count_ones()` is 1.
-/
theorem u64_is_power_of_two_iff_one_bit (x : Std.U64) :
    u64_is_power_of_two_iff_one_bit_spec x := by
  unfold u64_is_power_of_two_iff_one_bit_spec U64.Insts.Dashu_baseBitPowerOfTwo.is_power_of_two
    core.num.U64.is_power_of_two core.num.U64.count_ones
  have hloop := pot_loop x 64 0#u32 0#u32 (by simp) (by simp) (by simp [pot_popc])
  have hx64 : x.val < 2^64 := by scalar_tac
  have key : pot_popc x.val 64 = 1 ↔ ∃ k, x.val = 2^k := by
    rw [pot_popc_one_iff, pot_one_bit_iff_pow x.val hx64]
  split
  · rename_i hne
    have hx0 : x.val ≠ 0 := by
      intro h0
      have : x = 0#u64 := UScalar.eq_of_val_eq (by simp [h0])
      simp [this] at hne
    have hx1 : 1 ≤ x.val := by omega
    step as ⟨i, hi⟩
    simp only [lift, bind_tc_ok]
    apply spec_bind hloop
    intro c hc
    rw [WP.spec_ok]
    have hand : (x &&& i = 0#u64) ↔ x.val &&& (x.val - 1) = 0 := by
      constructor
      · intro h
        have := congrArg UScalar.val h
        rw [UScalar.val_and, hi] at this
        simpa using this
      · intro h
        apply UScalar.eq_of_val_eq
        rw [UScalar.val_and, hi, h]
        rfl
    simp only
    rw [decide_eq_true_iff, hand, hc, key, Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hx0]
    exact Iff.rfl
  · rename_i hz
    have hx0 : x.val = 0 := by simpa using hz
    simp only [bind_tc_ok]
    apply spec_bind hloop
    intro c hc
    rw [WP.spec_ok]
    simp only [Bool.false_eq_true, false_iff]
    rw [hc, key, hx0]
    rintro ⟨k, hk⟩
    exact (Nat.two_pow_pos k).ne hk

end Benchmark.Cases.Dashu.Base
