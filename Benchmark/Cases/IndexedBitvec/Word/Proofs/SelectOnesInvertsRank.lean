import Benchmark.Cases.IndexedBitvec.Word.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

/-- number of set bits of a natural number -/
def pc (n : Nat) : Nat := if n = 0 then 0 else n % 2 + pc (n / 2)
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem pc_zero : pc 0 = 0 := by rw [pc]; simp

theorem pc_two_mul_add (a b : Nat) (hb : b < 2) : pc (2 * a + b) = pc a + b := by
  rw [pc]
  split
  · have : a = 0 := by omega
    have : b = 0 := by omega
    subst_vars; simp [pc_zero]
  · have h1 : (2 * a + b) % 2 = b := by omega
    have h2 : (2 * a + b) / 2 = a := by omega
    rw [h1, h2]; omega

theorem pc_mul_pow_add (k : Nat) : ∀ a b : Nat, b < 2 ^ k → pc (a * 2 ^ k + b) = pc a + pc b := by
  induction k with
  | zero => intro a b hb; simp at hb; subst hb; simp [pc_zero]
  | succ k ih =>
    intro a b hb
    have e : a * 2 ^ (k + 1) + b = 2 * (a * 2 ^ k + b / 2) + b % 2 := by
      have : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by ring
      omega
    have eb : b = 2 * (b / 2) + b % 2 := by omega
    rw [e, pc_two_mul_add _ _ (Nat.mod_lt _ (by norm_num)), ih a (b / 2) (by rw [pow_succ] at hb; omega)]
    conv_rhs => rw [eb, pc_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))]
    omega

theorem pc_mul_pow (a k : Nat) : pc (a * 2 ^ k) = pc a := by
  have := pc_mul_pow_add k a 0 (by positivity)
  simpa [pc_zero] using this

theorem pc_le (k : Nat) : ∀ a : Nat, a < 2 ^ k → pc a ≤ k := by
  induction k with
  | zero => intro a ha; simp at ha; subst ha; simp [pc_zero]
  | succ k ih =>
    intro a ha
    have e : a = 2 * (a / 2) + a % 2 := by omega
    rw [e, pc_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))]
    have := ih (a / 2) (by rw [pow_succ] at ha; omega)
    omega

theorem pc_pos (a : Nat) (ha : 0 < a) : 0 < pc a := by
  rw [pc]; rw [if_neg (by omega)]
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have : 0 < a / 2 := by omega
    have := pc_pos (a / 2) this
    omega
  · omega
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem countBits_succ (bit : Nat → Bool) (b : Bool) (n : Nat) :
    countBits bit b (n + 1) = countBits bit b n + (if bit n = b then 1 else 0) := by
  unfold countBits
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : bit n = b <;> simp [h]

/-- LSB-first count of the low `w` bits is the popcount. -/
theorem countBits_testBit (w : Nat) : ∀ n : Nat, n < 2 ^ w → countBits n.testBit true w = pc n := by
  induction w with
  | zero => intro n hn; simp at hn; subst hn; simp [countBits, pc_zero]
  | succ w ih =>
    intro n hn
    have hP : 0 < 2 ^ w := by positivity
    have hq : n / 2 ^ w < 2 := by
      rw [Nat.div_lt_iff_lt_mul hP]; rw [pow_succ] at hn; linarith
    have hlow : countBits n.testBit true w = countBits (n % 2 ^ w).testBit true w := by
      unfold countBits; congr 1; apply List.filter_congr; intro i hi
      rw [List.mem_range] at hi; rw [Nat.testBit_mod_two_pow]; simp [hi]
    have htop : n.testBit w = decide (n / 2 ^ w = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_eq_of_lt hq]
    rw [countBits_succ, hlow, ih _ (Nat.mod_lt _ hP), htop]
    conv_rhs => rw [← Nat.div_add_mod' n (2 ^ w), pc_mul_pow_add _ _ _ (Nat.mod_lt _ hP)]
    generalize n / 2 ^ w = q at hq ⊢
    rcases (show q = 0 ∨ q = 1 by omega) with h | h
    · rw [h, pc_zero]; simp
    · rw [h]
      have : pc 1 = 1 := by rw [pc]; simp [pc_zero]
      rw [this]; simp; omega

theorem try_from_one :
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize = ok (core.result.Result.Ok 1#u32) := by
  unfold core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  simp only [lift, bind_tc_ok]
  unfold core.num.U32.MAX core.num.U32.MIN
  split_ifs with h1 h2
  · exfalso
    have hv : (UScalar.cast UScalarTy.Usize (UScalar.ofNat U32.rMax Std.core.num.U32.MAX._proof_1)).val = 4294967295 := by
      rw [UScalar.cast_val_eq]
      rcases System.Platform.numBits_eq with h | h <;> simp [h, U32.rMax, UScalar.size, UScalarTy.numBits]
    scalar_tac
  · exfalso
    have := UScalar.cast_val_eq UScalarTy.Usize (0#u32)
    scalar_tac
  · have : UScalar.cast UScalarTy.U32 1#usize = 1#u32 := by
      apply UScalar.eq_of_val_eq; rw [UScalar.cast_val_eq]; simp
    rw [this]

theorem forward_checked_one (k : Std.U32) (h : k.val < 4294967295) :
    core.U32.Insts.CoreIterRangeStep.forward_checked k 1#usize =
      ok (core.option.Option.Some (UScalar.overflowing_add k 1#u32).1) := by
  unfold core.U32.Insts.CoreIterRangeStep.forward_checked
  rw [try_from_one]
  simp only [bind_tc_ok, core.num.U32.checked_add, core.num.U32.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_u32]
  have := UScalar.overflowing_add_eq k 1#u32
  have hmax : k.val + (1#u32).val ≤ UScalar.max .U32 := by
    have : UScalar.max .U32 = 4294967295 := by
      simp [U32.max_def, U32.numBits]
    simp only [this]; simp; omega
  simp only [gt_iff_lt, not_lt.mpr hmax, ↓reduceIte] at this
  obtain ⟨_, h2⟩ := this
  generalize UScalar.overflowing_add k 1#u32 = z at *
  obtain ⟨a, b⟩ := z
  simp only at h2
  subst h2
  rfl

theorem range_next_lt (k e : Std.U32) (h : k.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.U32.Insts.CoreIterRangeStep
      ({ start := k, «end» := e } : core.ops.range.Range Std.U32) ⦃ r =>
      r.1 = core.option.Option.Some k ∧ r.2.«end» = e ∧ r.2.start.val = k.val + 1 ⦄ := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, core.IteratorRange.next,
    core.U32.Insts.CoreIterRangeStep, core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd,
    core.U32.Insts.CoreCloneClone, core.U32.Insts.CoreCloneClone.clone, bind_tc_ok]
  have hlt : compare k.val e.val = .lt := Nat.compare_eq_lt.mpr h
  have he : e.val ≤ 4294967295 := by scalar_tac
  rw [forward_checked_one k (by omega)]
  simp only [hlt, bind_tc_ok, ↓reduceIte, WP.spec_ok]
  refine ⟨by simp, by simp, ?_⟩
  have := UScalar.overflowing_add_eq k 1#u32
  have hmax : k.val + (1#u32).val ≤ UScalar.max .U32 := by
    have : UScalar.max .U32 = 4294967295 := by
      simp [U32.max_def, U32.numBits]
    simp only [this]; simp; omega
  simp only [gt_iff_lt, not_lt.mpr hmax, ↓reduceIte] at this
  rw [this.1]; simp

theorem range_next_eq (k e : Std.U32) (h : e.val ≤ k.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.U32.Insts.CoreIterRangeStep
      ({ start := k, «end» := e } : core.ops.range.Range Std.U32) =
      ok (core.option.Option.None, { start := k, «end» := e }) := by
  have hc : compare k.val e.val ≠ .lt := by rw [Ne, Nat.compare_eq_lt]; omega
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, core.IteratorRange.next,
    core.U32.Insts.CoreIterRangeStep, core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd, bind_tc_ok]
  split <;> simp_all


theorem countBits_le (bit : Nat → Bool) (b : Bool) (n : Nat) : countBits bit b n ≤ n := by
  induction n with
  | zero => simp [countBits]
  | succ n ih => rw [countBits_succ]; split <;> omega

theorem shr_and_one_u32 (x : Std.U32) (i : Std.U32) (hi : i.val < 32) :
    x >>> i ⦃ y => (y &&& 1#u32).val = if x.val.testBit i.val then 1 else 0 ⦄ := by
  step*
  rw [UScalar.val_and]
  have h1 : (1#u32).val = 1 := by simp
  rw [h1, y_post1, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (x.val / 2 ^ i.val)
  split <;> simp_all

theorem count_ones_spec_u32 (x : Std.U32) :
    core.num.U32.count_ones x ⦃ r => r.val = countBits (x.val.testBit) true 32 ⦄ := by
  unfold core.num.U32.count_ones core.num.U32.count_ones_loop
  apply loop.spec_decr_nat (fun p => 32 - p.1.start.val)
    (fun p => p.1.«end».val = 32 ∧ p.1.start.val ≤ 32 ∧
      p.2.val = countBits (x.val.testBit) true p.1.start.val)
  · rintro ⟨⟨k, e⟩, n⟩ ⟨he, hk, hn⟩
    simp only at he hk hn ⊢
    have heW : e.val = 32 := he
    unfold core.num.U32.count_ones_loop.body
    by_cases hlt : k.val < 32
    · apply WP.spec_bind (range_next_lt k e (by omega))
      rintro ⟨o, it'⟩ ⟨ho, he', hs'⟩
      simp only at ho he' hs'
      simp only [ho]
      apply WP.spec_bind (shr_and_one_u32 x k hlt)
      intro y hy
      simp only [lift, bind_tc_ok]
      by_cases hb : x.val.testBit k.val
      · have : (y &&& 1#u32) = 1#u32 := UScalar.eq_of_val_eq (by rw [hy, if_pos hb]; simp)
        simp only [this, ↓reduceIte]
        have hnb : n.val + 1 ≤ 32 := by have := countBits_le (x.val.testBit) true k.val; omega
        step*
        refine ⟨by rw [he', heW], by omega, ?_, by omega⟩
        rw [n1_post, hs', countBits_succ, if_pos hb, hn]
      · have : (y &&& 1#u32) ≠ 1#u32 := by
          intro h; have := congrArg UScalar.val h; rw [hy, if_neg hb] at this; simp at this
        simp only [this, ↓reduceIte, WP.spec_ok]
        refine ⟨⟨by rw [he', heW], by omega, ?_⟩, by omega⟩
        rw [hs', countBits_succ, if_neg hb, hn]; rfl
    · have hkW : k.val = 32 := by omega
      rw [range_next_eq k e (by omega)]
      apply (WP.spec_ok (ControlFlow.done n)).mpr
      show n.val = countBits _ true 32
      rw [hn, hkW]
  · simp [countBits]

theorem shr_and_one_u16 (x : Std.U16) (i : Std.U32) (hi : i.val < 16) :
    x >>> i ⦃ y => (y &&& 1#u16).val = if x.val.testBit i.val then 1 else 0 ⦄ := by
  step*
  rw [UScalar.val_and]
  have h1 : (1#u16).val = 1 := by simp
  rw [h1, y_post1, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (x.val / 2 ^ i.val)
  split <;> simp_all

theorem count_ones_spec_u16 (x : Std.U16) :
    core.num.U16.count_ones x ⦃ r => r.val = countBits (x.val.testBit) true 16 ⦄ := by
  unfold core.num.U16.count_ones core.num.U16.count_ones_loop
  apply loop.spec_decr_nat (fun p => 16 - p.1.start.val)
    (fun p => p.1.«end».val = 16 ∧ p.1.start.val ≤ 16 ∧
      p.2.val = countBits (x.val.testBit) true p.1.start.val)
  · rintro ⟨⟨k, e⟩, n⟩ ⟨he, hk, hn⟩
    simp only at he hk hn ⊢
    have heW : e.val = 16 := he
    unfold core.num.U16.count_ones_loop.body
    by_cases hlt : k.val < 16
    · apply WP.spec_bind (range_next_lt k e (by omega))
      rintro ⟨o, it'⟩ ⟨ho, he', hs'⟩
      simp only at ho he' hs'
      simp only [ho]
      apply WP.spec_bind (shr_and_one_u16 x k hlt)
      intro y hy
      simp only [lift, bind_tc_ok]
      by_cases hb : x.val.testBit k.val
      · have : (y &&& 1#u16) = 1#u16 := UScalar.eq_of_val_eq (by rw [hy, if_pos hb]; simp)
        simp only [this, ↓reduceIte]
        have hnb : n.val + 1 ≤ 16 := by have := countBits_le (x.val.testBit) true k.val; omega
        step*
        refine ⟨by rw [he', heW], by omega, ?_, by omega⟩
        rw [n1_post, hs', countBits_succ, if_pos hb, hn]
      · have : (y &&& 1#u16) ≠ 1#u16 := by
          intro h; have := congrArg UScalar.val h; rw [hy, if_neg hb] at this; simp at this
        simp only [this, ↓reduceIte, WP.spec_ok]
        refine ⟨⟨by rw [he', heW], by omega, ?_⟩, by omega⟩
        rw [hs', countBits_succ, if_neg hb, hn]; rfl
    · have hkW : k.val = 16 := by omega
      rw [range_next_eq k e (by omega)]
      apply (WP.spec_ok (ControlFlow.done n)).mpr
      show n.val = countBits _ true 16
      rw [hn, hkW]
  · simp [countBits]

theorem lz_val (f : Std.U32) :
    (Aeneas.Std.core.num.U32.leading_zeros f).val = if f.val = 0 then 32 else 31 - Nat.log 2 f.val := by
  have hf : f.val = f.bv.toNat := rfl
  have hl : Nat.log 2 f.val < 32 := by
    rcases Nat.eq_zero_or_pos f.val with h | h
    · rw [h]; simp
    · exact Nat.log_lt_of_lt_pow (by omega) (by scalar_tac)
  simp only [Aeneas.Std.core.num.U32.leading_zeros, Aeneas.Std.BitVec.leadingZeros, UScalar.val]
  split_ifs with h1 h2 h2
  · simp
  · exfalso; apply h2; simp [h1]
  · exfalso; apply h1; apply BitVec.eq_of_toNat_eq; rw [h2]; rfl
  · rw [← hf]; simp; omega

theorem mask_hi (a : Nat) (ha : a < 2^32) : a &&& 4294901760 = (a / 2^16) * 2^16 := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hc : (4294901760 : Nat) = (2^16 - 1) * 2^16 := by norm_num
  rw [Nat.testBit_and, hc, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : 16 ≤ k
  · by_cases h2 : k < 32
    · have : k - 16 + 16 = k := by omega
      simp [h1, this, show k - 16 < 16 by omega]
    · have : a.testBit k = false := Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have : k - 16 + 16 = k := by omega
      simp [h1, *]
  · simp [h1]

theorem mask_lo (a : Nat) : a &&& 65535 = a % 2^16 := by
  have : (65535 : Nat) = 2^16 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem pc_split (v o : Nat) : pc v = pc ((v * 2^o) / 2^16) + pc ((v * 2^o) % 2^16) := by
  rw [← pc_mul_pow_add 16 _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod', pc_mul_pow]

theorem shift_div (v o s : Nat) :
    (v * 2^(o + s)) / 2^16 = ((v * 2^o) / 2^16) * 2^s + ((v * 2^o) % 2^16 * 2^s) / 2^16 := by
  have e : v * 2^(o + s) = ((v * 2^o) % 2^16 * 2^s) + (((v * 2^o) / 2^16) * 2^s) * 2^16 := by
    have := Nat.div_add_mod' (v * 2^o) (2^16)
    rw [pow_add]
    calc v * (2^o * 2^s) = (v * 2^o) * 2^s := by ring
      _ = ((v * 2 ^ o / 2 ^ 16) * 2 ^ 16 + v * 2 ^ o % 2 ^ 16) * 2^s := by rw [this]
      _ = _ := by ring
  rw [e, Nat.add_mul_div_right _ _ (by norm_num)]
  ring

theorem shift_mod (v o s : Nat) :
    (v * 2^(o + s)) % 2^16 = ((v * 2^o) % 2^16 * 2^s) % 2^16 := by
  rw [pow_add, ← mul_assoc, Nat.mod_mul_mod]

theorem pc_shift (v o s : Nat) :
    pc ((v * 2^(o + s)) / 2^16) = pc ((v * 2^o) / 2^16) + pc (((v * 2^o) % 2^16 * 2^s) / 2^16) := by
  rw [shift_div, pc_mul_pow_add]
  rw [Nat.div_lt_iff_lt_mul (by norm_num), mul_comm (2^s)]
  exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by norm_num)) (by positivity)

theorem testBit_window (v o k : Nat) :
    ((v * 2^o) % 2^16).testBit k = (decide (k < 16) && decide (o ≤ k) && v.testBit (k - o)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  cases decide (k < 16) <;> simp

theorem select_loop_spec (v : Nat) (hv : v < 2^16) (N0 : Nat) (hN0 : N0 ≤ 16) :
    ∀ (nth offset fr : Std.U32), fr.val = (v * 2^offset.val) % 2^16 →
      pc ((v * 2^offset.val) / 2^16) + nth.val = N0 → offset.val < 48 →
      word.select_ones_u16_loop nth offset fr ⦃ r =>
        (N0 < pc v → r.val < 16 ∧ v.testBit (15 - r.val) = true ∧ pc ((v * 2^r.val) / 2^16) = N0) ∧
        (pc v ≤ N0 → r.val = 16) ⦄ := by
  intro nth offset fr hfr hcnt hoff
  unfold word.select_ones_u16_loop
  apply loop.spec_decr_nat (fun p => p.1.val)
    (fun p => p.2.2.val = (v * 2^p.2.1.val) % 2^16 ∧
      pc ((v * 2^p.2.1.val) / 2^16) + p.1.val = N0 ∧ p.2.1.val < 48)
  · rintro ⟨nth, offset, fr⟩ ⟨hfr, hcnt, hoff⟩
    simp only at hfr hcnt hoff ⊢
    unfold word.select_ones_u16_loop.body
    simp only [CoreModels.core.num.U32.leading_zeros, CoreModels.rust_primitives.arithmetic.leading_zeros_u32, bind_tc_ok]
    have hW : fr.val < 2^16 := by rw [hfr]; exact Nat.mod_lt _ (by norm_num)
    have hsplit := pc_split v offset.val
    rw [← hfr] at hsplit
    have hlz := lz_val fr
    by_cases hz : fr.val = 0
    · rw [if_pos hz] at hlz
      step*
      rw [hz, pc_zero] at hsplit
      refine ⟨fun h => by omega, fun _ => by simp⟩
    · rw [if_neg hz] at hlz
      have hlogW : Nat.log 2 fr.val < 16 := Nat.log_lt_of_lt_pow hz hW
      have hpow : 2 ^ Nat.log 2 fr.val ≤ fr.val := Nat.pow_log_le_self 2 hz
      have hpow2 : fr.val < 2 ^ (Nat.log 2 fr.val + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hoff16 : offset.val < 16 := by
        by_contra hc
        apply hz; rw [hfr]
        apply Nat.eq_of_testBit_eq
        intro k; rw [testBit_window, Nat.zero_testBit]
        by_cases hk : k < 16
        · have : ¬ (offset.val ≤ k) := by omega
          simp [this]
        · simp [hk]
      have hbitW : fr.val.testBit (Nat.log 2 fr.val) = true := by
        have hd : fr.val / 2 ^ Nat.log 2 fr.val = 1 :=
          Nat.div_eq_of_lt_le (by rw [one_mul]; exact hpow) (by rw [pow_succ] at hpow2; omega)
        rw [Nat.testBit_eq_decide_div_mod_eq, hd]; rfl
      step as ⟨nlz, hnlz1, hnlz2⟩
      have hn : nlz.val = 15 - Nat.log 2 fr.val := by omega
      have : ¬ (nlz ≥ 16#u32) := by scalar_tac
      simp only [this, ↓reduceIte]
      split
      · rename_i h0
        have h0' : nth.val = 0 := by rw [h0]; rfl
        step as ⟨i1, hi1⟩
        apply (WP.spec_ok _).mpr
        have hwin := testBit_window v offset.val (Nat.log 2 fr.val)
        rw [← hfr, hbitW] at hwin
        simp only [Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at hwin
        obtain ⟨⟨_, hLo⟩, hvb⟩ := hwin
        have hpcW : 0 < pc fr.val := pc_pos _ (by omega)
        refine ⟨fun _ => ⟨by omega, ?_, ?_⟩, fun h => by omega⟩
        · have : 15 - i1.val = Nat.log 2 fr.val - offset.val := by omega
          rw [this]; exact hvb
        · have e : i1.val = offset.val + nlz.val := by omega
          rw [e, pc_shift, ← hfr]
          have : fr.val * 2 ^ nlz.val / 2 ^ 16 = 0 := by
            apply Nat.div_eq_of_lt
            calc fr.val * 2 ^ nlz.val < 2 ^ (Nat.log 2 fr.val + 1) * 2 ^ nlz.val :=
                  Nat.mul_lt_mul_of_pos_right hpow2 (by positivity)
              _ = 2 ^ 16 := by rw [← pow_add]; congr 1; omega
          rw [this, pc_zero]; omega
      · rename_i h0
        have h0' : nth.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
        have hnth : nth.val ≤ 16 := by omega
        step*
        have hs : shift.val = 15 - Nat.log 2 fr.val + nth.val := by omega
        have hlt32 : fr.val * 2 ^ shift.val < 2 ^ (16 + nth.val) := by
          calc fr.val * 2 ^ shift.val < 2 ^ (Nat.log 2 fr.val + 1) * 2 ^ shift.val :=
                Nat.mul_lt_mul_of_pos_right hpow2 (by positivity)
            _ = 2 ^ (16 + nth.val) := by rw [← pow_add]; congr 1; omega
        have hge : 2 ^ 16 ≤ fr.val * 2 ^ shift.val := by
          calc 2 ^ 16 ≤ 2 ^ (Nat.log 2 fr.val + shift.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 ^ Nat.log 2 fr.val * 2 ^ shift.val := by rw [pow_add]
            _ ≤ fr.val * 2 ^ shift.val := Nat.mul_le_mul_right _ hpow
        have h32 : 2 ^ (16 + nth.val) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hf1 : from1.val = fr.val * 2 ^ shift.val := by
          rw [from1_post1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
          simp [U32.size, U32.numBits]; omega
        have hi1v : i1.val = (fr.val * 2 ^ shift.val / 2 ^ 16) * 2 ^ 16 := by
          rw [i1_post1, UScalar.val_and, hf1]
          have : (4294901760#u32).val = 4294901760 := by simp
          rw [this, mask_hi _ (by omega)]
        have hc_hi : fr.val * 2 ^ shift.val / 2 ^ 16 < 2 ^ nth.val := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_add, Nat.add_comm]; exact hlt32
        have hc_lo : 1 ≤ fr.val * 2 ^ shift.val / 2 ^ 16 := by
          rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
        apply WP.spec_bind (count_ones_spec_u32 i1)
        intro c hc
        rw [countBits_testBit 32 _ (by scalar_tac), hi1v, pc_mul_pow] at hc
        have hcle : c.val ≤ nth.val := by rw [hc]; exact pc_le _ _ hc_hi
        have hcpos : 1 ≤ c.val := by rw [hc]; exact pc_pos _ (by omega)
        step*
        have hf2 : from2.val = fr.val * 2 ^ shift.val % 2 ^ 16 := by
          rw [from2_post1, UScalar.val_and, hf1]
          have : (65535#u32).val = 65535 := by simp
          rw [this, mask_lo]
        refine ⟨?_, ?_, by omega, by omega⟩
        · rw [hf2, offset1_post, hfr, shift_mod]
        · rw [offset1_post, pc_shift, ← hfr, ← hc]; omega
  · exact ⟨hfr, hcnt, hoff⟩

theorem get_spec (x : word.Word) (j : Std.Usize) (hj : j.val < 64) :
    word.Word.get x j ⦃ r => r = core.option.Option.Some (x.val.testBit (63 - j.val)) ⦄ := by
  unfold word.Word.get word.Word.index_check word.Word.len
  have : ¬ (j ≥ 64#usize) := by scalar_tac
  simp only [this, ↓reduceIte, bind_tc_ok]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok, U64.Insts.CoreConvertFromWord.from]
  step*
  have hi2 : i2.val = 63 - j.val := by
    rw [i2_post, UScalar.cast_val_eq, i1_post1]; apply Nat.mod_eq_of_lt; simp; omega
  have hi3 : i3.val = 2 ^ (63 - j.val) := by
    have : 2^(63 - j.val) < 2^64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [i3_post1, hi2, Nat.shiftLeft_eq, one_mul]; apply Nat.mod_eq_of_lt
    simpa [U64.size, U64.numBits] using this
  have hi4 : i4.val = x.val &&& 2 ^ (63 - j.val) := by
    rw [i4_post1, UScalar.val_and, hi3]
  congr 1
  have h0 : (i4 > 0#u64) ↔ 0 < i4.val := by constructor <;> intro h <;> scalar_tac
  rw [Bool.eq_iff_iff, decide_eq_true_iff, h0, hi4, Nat.and_two_pow]
  cases (x.val.testBit (63 - j.val)) <;> simp


theorem countBits_window (v : Nat) (hv : v < 2^16) (r : Nat) (hr : r ≤ 16) :
    countBits (fun j => (v * 2^48).testBit (63 - j)) true r = pc (v * 2^r / 2^16) := by
  induction r with
  | zero => simp only [pow_zero, mul_one, Nat.div_eq_of_lt hv, pc_zero]; simp [countBits]
  | succ r ih =>
    rw [countBits_succ, ih (by omega), shift_div v r 1, pow_one]
    have hW : v * 2^r % 2^16 < 2^16 := Nat.mod_lt _ (by norm_num)
    have hb : v * 2^r % 2^16 * 2 / 2^16 < 2 := by omega
    have hpm := pc_mul_pow_add 1 (v * 2 ^ r / 2 ^ 16) (v * 2^r % 2^16 * 2 / 2^16) (by rw [pow_one]; exact hb)
    rw [pow_one] at hpm
    rw [hpm]
    have htb : (v * 2^48).testBit (63 - r) = decide (v * 2^r % 2^16 * 2 / 2^16 = 1) := by
      rw [Nat.testBit_mul_two_pow]
      have h1 : 63 - r - 48 = 15 - r := by omega
      have := testBit_window v r 15
      simp only [show (15 : Nat) < 16 by norm_num, show r ≤ 15 by omega, decide_true, Bool.true_and,
        show 15 - r = 15 - r from rfl] at this
      rw [h1, ← this, Nat.testBit_eq_decide_div_mod_eq]
      have e : v * 2 ^ r % 2 ^ 16 * 2 / 2 ^ 16 = v * 2 ^ r % 2 ^ 16 / 2 ^ 15 := by
        generalize v * 2 ^ r % 2 ^ 16 = W
        simp only [show (2:ℕ)^16 = 65536 by norm_num, show (2:ℕ)^15 = 32768 by norm_num]; omega
      rw [e]
      have : v * 2 ^ r % 2 ^ 16 / 2 ^ 15 < 2 := by omega
      simp [show 48 ≤ 63 - r by omega]
      omega
    rw [htb]
    rcases (show v * 2^r % 2^16 * 2 / 2^16 = 0 ∨ v * 2^r % 2^16 * 2 / 2^16 = 1 by omega) with h | h
    · rw [h, pc_zero]; simp
    · rw [h]; have : pc 1 = 1 := by rw [pc]; simp [pc_zero]
      rw [this]; simp

theorem select_u16_spec (x : Std.U16) (i : Std.U32) (hi : i.val ≤ 16) :
    word.select_ones_u16 x i ⦃ r =>
      (i.val < pc x.val → r.val < 16 ∧ x.val.testBit (15 - r.val) = true ∧ pc (x.val * 2^r.val / 2^16) = i.val) ∧
      (pc x.val ≤ i.val → r.val = 16) ⦄ := by
  have hx : x.val < 2^16 := by scalar_tac
  unfold word.select_ones_u16
  simp only [lift, bind_tc_ok]
  have hc : (UScalar.cast UScalarTy.U32 x).val = x.val := by
    rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; simp; omega
  apply select_loop_spec x.val hx i.val hi
  · rw [hc]; simp [Nat.mod_eq_of_lt hx]
  · have h0 : x.val / 65536 = 0 := Nat.div_eq_of_lt (by omega)
    simp [h0, pc_zero]
  · simp

theorem countBits_eq_sum (f : Nat → Bool) (b : Bool) (n : Nat) :
    countBits f b n = ∑ i ∈ Finset.range n, (if f i = b then 1 else 0) := by
  induction n with
  | zero => simp [countBits]
  | succ n ih => rw [countBits_succ, Finset.sum_range_succ, ih]

theorem shift_count (x : Nat) (hx : x < 2^64) (m : Nat) (hm : m ≤ 64) :
    countBits (fun k => (x >>> (64 - m)).testBit k) true 64 =
      countBits (fun j => x.testBit (63 - j)) true m := by
  rw [countBits_eq_sum, countBits_eq_sum]
  simp only [Nat.testBit_shiftRight]
  rw [← Finset.sum_range_add_sum_Ico _ hm]
  have h0 : ∑ k ∈ Finset.Ico m 64, (if x.testBit (64 - m + k) = true then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have : x.testBit (64 - m + k) = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [this]
  rw [h0, Nat.add_zero, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have : 64 - m + (m - 1 - j) = 63 - j := by omega
  rw [this]

theorem shr_and_one (x : Std.U64) (i : Std.U32) (hi : i.val < 64) :
    x >>> i ⦃ y => (y &&& 1#u64).val = if x.val.testBit i.val then 1 else 0 ⦄ := by
  step*
  rw [UScalar.val_and]
  have h1 : (1#u64).val = 1 := by simp
  rw [h1, y_post1, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (x.val / 2 ^ i.val)
  split <;> simp_all

theorem count_ones_spec (x : Std.U64) :
    core.num.U64.count_ones x ⦃ r => r.val = countBits (x.val.testBit) true 64 ⦄ := by
  unfold core.num.U64.count_ones core.num.U64.count_ones_loop
  apply loop.spec_decr_nat (fun p => 64 - p.1.start.val)
    (fun p => p.1.«end».val = 64 ∧ p.1.start.val ≤ 64 ∧
      p.2.val = countBits (x.val.testBit) true p.1.start.val)
  · rintro ⟨⟨k, e⟩, n⟩ ⟨he, hk, hn⟩
    simp only at he hk hn ⊢
    have he64 : e.val = 64 := he
    unfold core.num.U64.count_ones_loop.body
    by_cases hlt : k.val < 64
    · apply WP.spec_bind (range_next_lt k e (by omega))
      rintro ⟨o, it'⟩ ⟨ho, he', hs'⟩
      simp only at ho he' hs'
      simp only [ho]
      apply WP.spec_bind (shr_and_one x k hlt)
      intro y hy
      simp only [lift, bind_tc_ok]
      by_cases hb : x.val.testBit k.val
      · have : (y &&& 1#u64) = 1#u64 := UScalar.eq_of_val_eq (by rw [hy, if_pos hb]; simp)
        simp only [this, ↓reduceIte]
        have hnb : n.val + 1 ≤ 64 := by have := countBits_le (x.val.testBit) true k.val; omega
        step*
        refine ⟨by rw [he', he64], by omega, ?_, by omega⟩
        rw [n1_post, hs', countBits_succ, if_pos hb, hn]
      · have : (y &&& 1#u64) ≠ 1#u64 := by
          intro h; have := congrArg UScalar.val h; rw [hy, if_neg hb] at this; simp at this
        simp only [this, ↓reduceIte, WP.spec_ok]
        refine ⟨⟨by rw [he', he64], by omega, ?_⟩, by omega⟩
        rw [hs', countBits_succ, if_neg hb, hn]; rfl
    · have hk64 : k.val = 64 := by omega
      rw [range_next_eq k e (by omega)]
      apply (WP.spec_ok (ControlFlow.done n)).mpr
      show n.val = countBits _ true 64
      rw [hn, hk64]
  · simp [countBits]

theorem testBit_not64 (m : Std.U64) (k : Nat) :
    (~~~m).val.testBit k = (decide (k < 64) && !m.val.testBit k) := by
  have h1 : (~~~m).val = (~~~m.bv).toNat := rfl
  have h2 : m.val = m.bv.toNat := rfl
  rw [h1, h2, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]

theorem complement_eq (x : word.Word) : word.Word.complement x = ok (~~~x) := by
  simp [word.Word.complement, U64.Insts.CoreConvertFromWord.from, word.Word.Insts.CoreConvertFromU64.from, lift]

theorem rank_ones_spec (x : word.Word) (idx : Std.Usize) (h : idx.val < 64) :
    word.Word.rank_ones x idx ⦃ r => ∃ e : Std.U32, r = core.option.Option.Some e ∧
      e.val = countBits (fun j => x.val.testBit (63 - j)) true idx.val ⦄ := by
  unfold word.Word.rank_ones
  by_cases h0 : idx = 0#usize
  · simp only [h0, ↓reduceIte, WP.spec_ok]
    refine ⟨0#u32, rfl, ?_⟩
    simp [countBits]
  · simp only [h0, ↓reduceIte]
    unfold word.Word.index_check word.Word.len
    have : ¬ (idx ≥ 64#usize) := by scalar_tac
    simp only [this, ↓reduceIte, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      U64.Insts.CoreConvertFromWord.from]
    step*
    have hi2 : i2.val = 64 - idx.val := by
      rw [i2_post, UScalar.cast_val_eq, i1_post1]; apply Nat.mod_eq_of_lt; simp; omega
    apply WP.spec_bind (count_ones_spec to_count)
    intro c hc
    apply (WP.spec_ok _).mpr
    refine ⟨c, rfl, ?_⟩
    rw [hc, to_count_post1, hi2]
    exact shift_count x.val (by scalar_tac) idx.val (by omega)

theorem rank_ones_64 (x : word.Word) : word.Word.rank_ones x 64#usize = ok core.option.Option.None := by
  unfold word.Word.rank_ones word.Word.index_check word.Word.len
  simp [core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]


theorem countBits_not (x : word.Word) (n : Nat) (hn : n ≤ 64) :
    countBits (fun j => (~~~x).val.testBit (63 - j)) true n =
      countBits (fun j => x.val.testBit (63 - j)) false n := by
  rw [countBits_eq_sum, countBits_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [testBit_not64]
  have : 63 - j < 64 := by omega
  cases x.val.testBit (63 - j) <;> simp [this]

def C (x : Std.U64) (p : Nat) : Nat := countBits (fun j => x.val.testBit (63 - j)) true p

theorem C_eq_pc (x : Std.U64) (p : Nat) (hp : p ≤ 64) : C x p = pc (x.val / 2^(64 - p)) := by
  have hx : x.val < 2^64 := by scalar_tac
  induction p with
  | zero => simp only [C, Nat.sub_zero, Nat.div_eq_of_lt hx, pc_zero]; simp [countBits]
  | succ p ih =>
    unfold C at ih ⊢
    rw [countBits_succ, ih (by omega), show 64 - (p+1) = 63 - p by omega]
    have e1 : x.val / 2^(64 - p) = x.val / 2^(63 - p) / 2 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]; congr 2; omega
    generalize hX : x.val / 2^(63 - p) = X
    have e2 : X = 2 * (X / 2) + X % 2 := by omega
    have htb : x.val.testBit (63 - p) = decide (X % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hX]
    rw [e1, hX, htb]
    conv_rhs => rw [e2, pc_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))]
    rcases Nat.mod_two_eq_zero_or_one X with h | h <;> simp [h]

theorem C_chunk (x : Std.U64) (c q : Nat) (hc : c ≤ 3) (hq : q ≤ 16) :
    C x (16*c + q) = C x (16*c) + pc ((x.val / 2^(48 - 16*c) % 2^16) * 2^q / 2^16) := by
  rw [C_eq_pc x _ (by omega), C_eq_pc x _ (by omega)]
  set v := x.val / 2^(48 - 16*c) % 2^16 with hv
  set A := x.val / 2^(64 - 16*c) with hA
  have h1 : x.val / 2^(48 - 16*c) = A * 2^16 + v := by
    rw [hA, hv]
    have : x.val / 2^(64 - 16*c) = x.val / 2^(48 - 16*c) / 2^16 := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
    rw [this, Nat.div_add_mod']
  have h2 : x.val / 2^(64 - (16*c + q)) = x.val / 2^(48 - 16*c) / 2^(16 - q) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  have h3 : v * 2^q / 2^16 = v / 2^(16 - q) := by
    have : (2:Nat)^16 = 2^(16 - q) * 2^q := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_div_mul_right _ _ (by positivity)]
  have h4 : (A * 2^16 + v) / 2^(16 - q) = A * 2^q + v / 2^(16 - q) := by
    have : (2:Nat)^16 = 2^q * 2^(16 - q) := by rw [← pow_add]; congr 1; omega
    rw [this, ← mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
  rw [h2, h1, h4, h3, pc_mul_pow_add]
  have hv16 : v < 2^16 := Nat.mod_lt _ (by norm_num)
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  calc v < 2^16 := hv16
    _ = 2^(q + (16 - q)) := by congr 1; omega

theorem chunk_select (x : Std.U64) (c : Nat) (hc : c ≤ 3) (v : Std.U16)
    (hv : v.val = x.val / 2^(48 - 16*c) % 2^16) (k : Std.U32) (hk : k.val < pc v.val) :
    word.select_ones_u16 v k ⦃ r => r.val < 16 ∧ x.val.testBit (63 - (r.val + 16*c)) = true ∧
      C x (r.val + 16*c) = C x (16*c) + k.val ⦄ := by
  have hv16 : v.val < 2^16 := by scalar_tac
  have hk16 : k.val ≤ 16 := by have := pc_le 16 _ hv16; omega
  apply WP.spec_mono (select_u16_spec v k hk16)
  rintro r ⟨h1, _⟩
  obtain ⟨hr, hb, hp⟩ := h1 hk
  refine ⟨hr, ?_, ?_⟩
  · rw [hv, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have : 15 - r.val + (48 - 16*c) = 63 - (r.val + 16*c) := by omega
    rw [← this]; exact hb.2
  · rw [Nat.add_comm, C_chunk x c r.val hc (by omega), ← hv, hp]

theorem chunk_pc (x : Std.U64) (c : Nat) (hc : c ≤ 3) :
    pc (x.val / 2^(48 - 16*c) % 2^16) = C x (16*c + 16) - C x (16*c) := by
  rw [C_chunk x c 16 hc (by norm_num), Nat.mul_div_cancel _ (by positivity)]; omega

theorem select_ones_spec (x : Std.U64) (nth : Std.U32) :
    word.Word.select_ones x nth ⦃ o =>
      (nth.val < pc x.val → ∃ r : Std.U32, o = core.option.Option.Some r ∧ r.val < 64 ∧
        x.val.testBit (63 - r.val) = true ∧ C x r.val = nth.val) ∧
      (pc x.val ≤ nth.val → o = core.option.Option.None) ⦄ := by
  have hx : x.val < 2^64 := by scalar_tac
  have hpcx : pc x.val = C x 64 := by rw [C_eq_pc x 64 (by norm_num)]; simp
  unfold word.Word.select_ones
  apply WP.spec_bind (rank_ones_spec x 32#usize (by simp))
  rintro o32 ⟨r32, ho32, hr32⟩
  simp only [ho32, core.option.Option.Some, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok]
  apply WP.spec_bind (rank_ones_spec x 16#usize (by simp))
  rintro o16 ⟨r16, ho16, hr16⟩
  simp only [ho16, core.option.Option.Some, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok]
  apply WP.spec_bind (rank_ones_spec x 48#usize (by simp))
  rintro o48 ⟨r48, ho48, hr48⟩
  simp only [ho48, core.option.Option.Some, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok,
    core.convert.Into.Blanket.into, U64.Insts.CoreConvertFromWord, U64.Insts.CoreConvertFromWord.from]
  have e16 : r16.val = C x 16 := by rw [hr16]; rfl
  have e32 : r32.val = C x 32 := by rw [hr32]; rfl
  have e48 : r48.val = C x 48 := by rw [hr48]; rfl
  have m1 := chunk_pc x 0 (by norm_num)
  have m2 := chunk_pc x 1 (by norm_num)
  have m3 := chunk_pc x 2 (by norm_num)
  have m4 := chunk_pc x 3 (by norm_num)
  have n1 := C_chunk x 0 16 (by norm_num) (by norm_num)
  have n2 := C_chunk x 1 16 (by norm_num) (by norm_num)
  have n3 := C_chunk x 2 16 (by norm_num) (by norm_num)
  have n4 := C_chunk x 3 16 (by norm_num) (by norm_num)
  have c0 : C x 0 = 0 := by simp [C, countBits]
  have h65 : (65535#u64).val = 65535 := by simp
  have hcast : ∀ a : Std.U64, (UScalar.cast UScalarTy.U16 a).val = a.val % 2^16 := by
    intro a; rw [UScalar.cast_val_eq]; rfl
  simp only [show 16*0 = 0 by rfl, show 16*1 = 16 by rfl, show 16*2 = 32 by rfl, show 16*3 = 48 by rfl,
    show 0 + 16 = 16 by rfl, show 16 + 16 = 32 by rfl, show 32 + 16 = 48 by rfl, show 48 + 16 = 64 by rfl] at m1 m2 m3 m4 n1 n2 n3 n4
  split
  · split
    · step*
      have hv : i2.val = x.val / 2^(48 - 16*0) % 2^16 := by
        rw [i2_post, hcast, i1_post1, UScalar.val_and, i_post1, Nat.shiftRight_eq_div_pow, h65, mask_lo]
        simp
      apply WP.spec_bind (chunk_select x 0 (by norm_num) i2 hv nth (by rw [hv]; have := m1; norm_num at this ⊢; rw [this]; scalar_tac))
      rintro r ⟨hr, hb, hc⟩
      apply (WP.spec_ok _).mpr
      simp only [show 16 * 0 = 0 by rfl, Nat.add_zero] at hb hc
      refine ⟨fun _ => ⟨r, rfl, by omega, hb, by omega⟩, fun h => by scalar_tac⟩
    · step*
      have hv : i2.val = x.val / 2^(48 - 16*1) % 2^16 := by
        rw [i2_post, hcast, i1_post1, UScalar.val_and, i_post1, Nat.shiftRight_eq_div_pow, h65, mask_lo]
        simp
      apply WP.spec_bind (chunk_select x 1 (by norm_num) i2 hv i3
        (by rw [hv]; have := m2; norm_num at this ⊢; rw [this]; scalar_tac))
      rintro r ⟨hr, hb, hc⟩
      step as ⟨res, hres⟩
      apply (WP.spec_ok _).mpr
      simp only [show 16 * 1 = 16 by rfl] at hb hc
      have hres' : res.val = r.val + 16 := by scalar_tac
      refine ⟨fun _ => ⟨res, rfl, by omega, by rw [hres']; exact hb, by rw [hres', hc]; scalar_tac⟩,
        fun h => by scalar_tac⟩
  · split
    · step*
      have hv : i2.val = x.val / 2^(48 - 16*2) % 2^16 := by
        rw [i2_post, hcast, i1_post1, UScalar.val_and, i_post1, Nat.shiftRight_eq_div_pow, h65, mask_lo]
        simp
      apply WP.spec_bind (chunk_select x 2 (by norm_num) i2 hv i3
        (by rw [hv]; have := m3; norm_num at this ⊢; rw [this]; scalar_tac))
      rintro r ⟨hr, hb, hc⟩
      step as ⟨res, hres⟩
      apply (WP.spec_ok _).mpr
      simp only [show 16 * 2 = 32 by rfl] at hb hc
      have hres' : res.val = r.val + 32 := by scalar_tac
      refine ⟨fun _ => ⟨res, rfl, by omega, by rw [hres']; exact hb, by rw [hres', hc]; scalar_tac⟩,
        fun h => by scalar_tac⟩
    · apply WP.spec_bind (count_ones_spec x)
      intro tot htot
      rw [countBits_testBit 64 _ hx] at htot
      split
      · apply (WP.spec_ok _).mpr
        exact ⟨fun h => by scalar_tac, fun _ => rfl⟩
      · step*
        have hv : i2.val = x.val / 2^(48 - 16*3) % 2^16 := by
          rw [i2_post, hcast, i1_post1, UScalar.val_and, h65, mask_lo]
          simp
        apply WP.spec_bind (chunk_select x 3 (by norm_num) i2 hv i3
          (by rw [hv]; have := m4; norm_num at this ⊢; rw [this]; scalar_tac))
        rintro r ⟨hr, hb, hc⟩
        step as ⟨res, hres⟩
        apply (WP.spec_ok _).mpr
        simp only [show 16 * 3 = 48 by rfl] at hb hc
        have hres' : res.val = r.val + 48 := by scalar_tac
        refine ⟨fun _ => ⟨res, rfl, by omega, by rw [hres']; exact hb, by rw [hres', hc]; scalar_tac⟩,
          fun h => by scalar_tac⟩

/--
For every word `x` and every `i` below `x.count_ones()`, `x.select_ones(i)`
returns `Some(r)` with `x.rank_ones(r) == Some(i)` and `x.get(r) == Some(true)`;
`x.select_ones(x.count_ones())` returns `None`.
-/
theorem select_ones_inverts_rank (x : word.Word) :
    select_ones_inverts_rank_spec x := by
  unfold select_ones_inverts_rank_spec
  have hx : x.val < 2^64 := by scalar_tac
  unfold word.Word.count_ones
  simp only [U64.Insts.CoreConvertFromWord.from, bind_tc_ok]
  apply WP.spec_mono (count_ones_spec x)
  intro total htot
  rw [countBits_testBit 64 _ hx] at htot
  refine ⟨?_, ?_⟩
  · intro i hi
    apply WP.spec_bind (select_ones_spec x i)
    rintro o ⟨h1, _⟩
    obtain ⟨r, ho, hr64, hb, hc⟩ := h1 (by omega)
    simp only [ho, core.option.Option.unwrap, bind_tc_ok, lift]
    have hcv : (UScalar.cast UScalarTy.Usize r).val = r.val := by
      rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
    apply WP.spec_bind (rank_ones_spec x (UScalar.cast UScalarTy.Usize r) (by omega))
    rintro o1 ⟨e, he, hev⟩
    apply WP.spec_bind (get_spec x (UScalar.cast UScalarTy.Usize r) (by omega))
    intro g hg
    apply (WP.spec_ok _).mpr
    refine ⟨?_, ?_⟩
    · rw [he]; congr 1; apply UScalar.eq_of_val_eq; rw [hev, hcv]; exact hc
    · rw [hg, hcv, hb]
  · apply WP.spec_mono (select_ones_spec x total)
    rintro o ⟨_, h2⟩
    exact h2 (by omega)

end Benchmark.Cases.IndexedBitvec.Word
