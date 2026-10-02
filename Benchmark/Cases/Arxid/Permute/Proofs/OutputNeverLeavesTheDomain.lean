import Benchmark.Cases.Arxid.Permute.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid

namespace Benchmark.Cases.Arxid.Permute

/-! Reference proof. Both Feistel loops keep the two halves below `2^20`
(`od_fl_spec`, `od_il_bound`, by induction over the rounds with `loop.eq_1`,
using that `round_fn` masks its result to 20 bits and
`Nat.xor_lt_two_pow`); the packed result `(l << 20) | r` is then
`l * 2^20 + r < 2^40`. -/

@[local step]
theorem od_rotl64_spec (x : Std.U64) (n : Std.U32) : core.num.U64.rotate_left x n ⦃ _ => True ⦄ := by
  unfold core.num.U64.rotate_left
  step*

@[local step]
theorem od_rotl32_spec (x : Std.U32) (n : Std.U32) : core.num.U32.rotate_left x n ⦃ _ => True ⦄ := by
  unfold core.num.U32.rotate_left
  step*

@[local step]
theorem od_subkey_spec (key : Std.U64) (round : Std.Usize) (h : round.val < 6) :
    permute.subkey key round ⦃ _ => True ⦄ := by
  unfold permute.subkey
  simp only [core.num.U64.wrapping_mul, core.num.U32.wrapping_add,
    rust_primitives.arithmetic.wrapping_mul_u64, rust_primitives.arithmetic.wrapping_add_u32]
  step*

theorem od_round_fn_spec (r : Std.U32) (key : Std.U64) (round : Std.Usize) (h : round.val < 6) :
    permute.round_fn r key round 20#u32 ⦃ f => f.val < 2^20 ⦄ := by
  unfold permute.round_fn
  simp only [core.num.U32.wrapping_add, rust_primitives.arithmetic.wrapping_add_u32]
  step*
  have hi : i.val = 2^20 := by rw [i_post1]; simp [U32.size, U32.numBits, Nat.shiftLeft_eq]
  have hm : mask.val = 2^20 - 1 := by omega
  rw [UScalar.val_and]
  have := Nat.and_le_right (n := x3.val) (m := mask.val)
  omega
theorem od_range_next_lt (i e : Std.Usize) (h : i.val < e.val) :
    ∃ i' : Std.Usize, i'.val = i.val + 1 ∧
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.Some i, { start := i', «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare i.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, core.Usize.Insts.CoreCloneClone.clone,
    core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize]
  have hmax : i.val + (1#usize).val ≤ UScalar.max UScalarTy.Usize := by
    have := e.hmax; simp only [UScalar.max] at *; scalar_tac
  have := UScalar.overflowing_add_eq i 1#usize
  simp only [gt_iff_lt, Nat.not_lt.mpr hmax, if_false] at this
  obtain ⟨h1, h2⟩ := this
  generalize UScalar.overflowing_add i 1#usize = z at *
  obtain ⟨r, b⟩ := z
  simp only at h1 h2
  subst h2
  exact ⟨r, by simpa using h1, rfl⟩

theorem od_range_next_ge (i e : Std.Usize) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

theorem od_rev_next_pos (s e : Std.Usize) (h : s.val < e.val) :
    ∃ e' : Std.Usize, e'.val = e.val - 1 ∧
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
        core.Usize.Insts.CoreIterRangeStep)
      { iter := { start := s, «end» := e } } =
      ok (core.option.Option.Some e', { iter := { start := s, «end» := e' } }) := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
    core.IteratorRange.next_back,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare s.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, 
    core.Usize.Insts.CoreIterRangeStep.backward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_sub, core.num.Usize.overflowing_sub,
    rust_primitives.arithmetic.overflowing_sub_usize, uoverflowing_sub, if_true]
  have h1 : ¬ e.val < (1#usize).val := by simp; omega
  simp only [h1, decide_false, Bool.false_eq_true, if_false, bind_tc_ok]
  refine ⟨⟨e.bv - (1#usize).bv⟩, ?_, rfl⟩
  have hle : (1#usize).bv ≤ e.bv := by
    rw [BitVec.le_def]; simp at h1 ⊢; omega
  show (e.bv - (1#usize).bv).toNat = _
  rw [BitVec.toNat_sub_of_le hle]
  simp

theorem od_rev_next_zero (s e : Std.Usize) (h : ¬ s.val < e.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
        core.Usize.Insts.CoreIterRangeStep)
      { iter := { start := s, «end» := e } } =
      ok (core.option.Option.None, { iter := { start := s, «end» := e } }) := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
    core.IteratorRange.next_back,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare s.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

theorem od_round_fn_ok (r : Std.U32) (key : Std.U64) (round : Std.Usize) (h : round.val < 6) :
    ∃ f : Std.U32, permute.round_fn r key round 20#u32 = ok f ∧ f.val < 2^20 :=
  spec_imp_exists (od_round_fn_spec r key round h)

theorem od_fl_body_lt (key : Std.U64) (i e : Std.Usize) (l r : Std.U32) (h : i.val < e.val) :
    ∃ i' : Std.Usize, i'.val = i.val + 1 ∧
    permute.feistel_n_loop.body key 20#u32 { start := i, «end» := e } l r =
      (do let f ← permute.round_fn r key i 20#u32
          ok (ControlFlow.cont ({ start := i', «end» := e }, r, l ^^^ f))) := by
  obtain ⟨i', hi', hn⟩ := od_range_next_lt i e h
  refine ⟨i', hi', ?_⟩
  unfold permute.feistel_n_loop.body
  simp only [hn, bind_tc_ok, lift]
  rfl

theorem od_fl_body_ge (key : Std.U64) (i e : Std.Usize) (l r : Std.U32) (h : ¬ i.val < e.val) :
    permute.feistel_n_loop.body key 20#u32 { start := i, «end» := e } l r =
      ok (ControlFlow.done (l, r)) := by
  unfold permute.feistel_n_loop.body
  simp only [od_range_next_ge i e h, bind_tc_ok]
  rfl

theorem od_il_body_pos (key : Std.U64) (j : Std.Usize) (l r : Std.U32) (h : 0 < j.val) :
    ∃ j' : Std.Usize, j'.val = j.val - 1 ∧
    permute.feistel_n_inv_loop.body key 20#u32 { iter := { start := 0#usize, «end» := j } } l r =
      (do let f ← permute.round_fn l key j' 20#u32
          ok (ControlFlow.cont ({ iter := { start := 0#usize, «end» := j' } }, r ^^^ f, l))) := by
  obtain ⟨j', hj', hn⟩ := od_rev_next_pos 0#usize j (by simpa using h)
  refine ⟨j', hj', ?_⟩
  unfold permute.feistel_n_inv_loop.body
  simp only [hn, bind_tc_ok, lift]
  rfl

theorem od_il_body_zero (key : Std.U64) (j : Std.Usize) (l r : Std.U32) (h : j.val = 0) :
    permute.feistel_n_inv_loop.body key 20#u32 { iter := { start := 0#usize, «end» := j } } l r =
      ok (ControlFlow.done (l, r)) := by
  unfold permute.feistel_n_inv_loop.body
  simp only [od_rev_next_zero 0#usize j (by simp [h]), bind_tc_ok]
  rfl

theorem od_xor_lt (a b : Std.U32) (ha : a.val < 2^20) (hb : b.val < 2^20) : (a ^^^ b).val < 2^20 := by
  rw [UScalar.val_xor]
  exact Nat.xor_lt_two_pow ha hb

theorem od_xor_xor_cancel (a b : Std.U32) : (a ^^^ b) ^^^ b = a := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_xor, UScalar.val_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem od_fl_unfold_ge (key : Std.U64) (i : Std.Usize) (l r : Std.U32) (h : ¬ i.val < 6) :
    permute.feistel_n_loop { start := i, «end» := 6#usize } key 20#u32 l r = ok (l, r) := by
  unfold permute.feistel_n_loop
  rw [loop.eq_1]
  simp only [od_fl_body_ge key i 6#usize l r (by simpa using h)]

theorem od_fl_unfold_lt (key : Std.U64) (i : Std.Usize) (l r : Std.U32) (h : i.val < 6) :
    ∃ i' : Std.Usize, i'.val = i.val + 1 ∧ ∃ f : Std.U32, f.val < 2^20 ∧
      permute.round_fn r key i 20#u32 = ok f ∧
      permute.feistel_n_loop { start := i, «end» := 6#usize } key 20#u32 l r =
      permute.feistel_n_loop { start := i', «end» := 6#usize } key 20#u32 r (l ^^^ f) := by
  obtain ⟨i', hi', hb⟩ := od_fl_body_lt key i 6#usize l r (by simpa using h)
  obtain ⟨f, hf, hfb⟩ := od_round_fn_ok r key i h
  refine ⟨i', hi', f, hfb, hf, ?_⟩
  conv_lhs => unfold permute.feistel_n_loop
  rw [loop.eq_1]
  simp only [hb, hf, bind_tc_ok]
  rfl

theorem od_il_unfold_zero (key : Std.U64) (j : Std.Usize) (l r : Std.U32) (h : j.val = 0) :
    permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := j } } key 20#u32 l r
      = ok (l, r) := by
  unfold permute.feistel_n_inv_loop
  rw [loop.eq_1]
  simp only [od_il_body_zero key j l r h]

theorem od_il_unfold_pos (key : Std.U64) (j : Std.Usize) (l r : Std.U32) (h : 0 < j.val) (h6 : j.val ≤ 6) :
    ∃ j' : Std.Usize, j'.val = j.val - 1 ∧ ∃ f : Std.U32, f.val < 2^20 ∧
      permute.round_fn l key j' 20#u32 = ok f ∧
      permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := j } } key 20#u32 l r =
      permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := j' } } key 20#u32 (r ^^^ f) l := by
  obtain ⟨j', hj', hb⟩ := od_il_body_pos key j l r h
  obtain ⟨f, hf, hfb⟩ := od_round_fn_ok l key j' (by omega)
  refine ⟨j', hj', f, hfb, hf, ?_⟩
  conv_lhs => unfold permute.feistel_n_inv_loop
  rw [loop.eq_1]
  simp only [hb, hf, bind_tc_ok]
  rfl

/-- Forward loop from round `i`: stays in the 20-bit halves, and the inverse loop
over all six rounds undoes it down to the inverse loop over rounds `0..i`. -/
theorem od_fl_spec (key : Std.U64) : ∀ (n : Nat) (i : Std.Usize) (l r : Std.U32),
    i.val + n = 6 → l.val < 2^20 → r.val < 2^20 →
    ∃ l' r' : Std.U32,
      permute.feistel_n_loop { start := i, «end» := 6#usize } key 20#u32 l r = ok (l', r') ∧
      l'.val < 2^20 ∧ r'.val < 2^20 ∧
      permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := 6#usize } } key 20#u32 l' r' =
      permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := i } } key 20#u32 l r := by
  intro n
  induction n with
  | zero =>
    intro i l r hn hl hr
    refine ⟨l, r, od_fl_unfold_ge key i l r (by omega), hl, hr, ?_⟩
    have : i = 6#usize := UScalar.eq_of_val_eq (by simp; omega)
    rw [this]
  | succ n ih =>
    intro i l r hn hl hr
    obtain ⟨i', hi', f, hf, hfb, heq⟩ := od_fl_unfold_lt key i l r (by omega)
    obtain ⟨l', r', h1, h2, h3, h4⟩ := ih i' r (l ^^^ f) (by omega) hr (od_xor_lt l f hl hf)
    refine ⟨l', r', by rw [heq, h1], h2, h3, ?_⟩
    rw [h4]
    obtain ⟨j', hj', g, _, hgb, heq2⟩ := od_il_unfold_pos key i' r (l ^^^ f) (by omega) (by omega)
    have hj : j' = i := UScalar.eq_of_val_eq (by omega)
    subst hj
    rw [heq2]
    rw [hfb] at hgb
    cases hgb
    rw [od_xor_xor_cancel]

/-- Inverse loop from `j ≤ 6`: stays in the 20-bit halves. -/
theorem od_il_bound (key : Std.U64) : ∀ (n : Nat) (j : Std.Usize) (l r : Std.U32),
    j.val = n → n ≤ 6 → l.val < 2^20 → r.val < 2^20 →
    ∃ l' r' : Std.U32,
      permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := j } } key 20#u32 l r = ok (l', r') ∧
      l'.val < 2^20 ∧ r'.val < 2^20 := by
  intro n
  induction n with
  | zero =>
    intro j l r hj _ hl hr
    exact ⟨l, r, od_il_unfold_zero key j l r hj, hl, hr⟩
  | succ n ih =>
    intro j l r hj hn hl hr
    obtain ⟨j', hj', f, hf, _, heq⟩ := od_il_unfold_pos key j l r (by omega) (by omega)
    rw [heq]
    exact ih j' (r ^^^ f) l (by omega) (by omega) (od_xor_lt r f hr hf) hl

theorem od_max_id_eq : permute.MAX_ID = ok 1099511627775#u64 := by
  unfold permute.MAX_ID permute.WIDTH_BITS
  rfl

theorem od_feistel_n_spec (input key : Std.U64) :
    permute.feistel_n input key 6#usize 40#u32 ⦃ c =>
      ∃ l1 r1 : Std.U32, l1.val < 2^20 ∧ r1.val < 2^20 ∧ c.val = l1.val * 2^20 + r1.val ∧
      ∃ l0 r0 : Std.U32, l0.val = input.val / 2^20 % 2^20 ∧ r0.val = input.val % 2^20 ∧
        permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := 6#usize } } key 20#u32 l1 r1
          = ok (l0, r0) ⦄ := by
  unfold permute.feistel_n
  step*
  have hh : half = 20#u32 := UScalar.eq_of_val_eq (by simp [half_post])
  subst hh
  have hi : i.val = 2^20 := by rw [i_post1]; simp [U64.size, U64.numBits, Nat.shiftLeft_eq]
  have hm : mask.val = 2^20 - 1 := by omega
  have hl : l.val = input.val / 2^20 % 2^20 := by
    rw [l_post, UScalar.cast_val_eq, i2_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod,
      i1_post1, Nat.shiftRight_eq_div_pow]
    simp only [UScalarTy.numBits]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (input.val / 2^20) (show 0 < 2^20 by norm_num)
    omega
  have hr : r.val = input.val % 2^20 := by
    rw [r_post, UScalar.cast_val_eq, i3_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    simp only [UScalarTy.numBits]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (input.val) (show 0 < 2^20 by norm_num)
    omega
  have hlb : l.val < 2^20 := by rw [hl]; exact Nat.mod_lt _ (by norm_num)
  have hrb : r.val < 2^20 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨l1, r1, h1, h2, h3, h4⟩ := od_fl_spec key 6 0#usize l r (by simp) hlb hrb
  rw [h1]
  simp only [bind_tc_ok]
  step*
  refine ⟨l1, r1, h2, h3, ?_, l, r, hl, hr, ?_⟩
  · have h4' : i4.val = l1.val := by
      rw [i4_post, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    have h6' : i6.val = r1.val := by
      rw [i6_post, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    have h5' : i5.val = l1.val * 2^20 := by
      have hs : U64.size = 2^64 := by simp [U64.size, U64.numBits]
      rw [i5_post1, h4', Nat.shiftLeft_eq, hs, Nat.mod_eq_of_lt (by omega)]
    rw [UScalar.val_or, h5', h6', ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h3]
  · rw [h4, od_il_unfold_zero key 0#usize l r (by simp)]

theorem od_feistel_n_inv_spec (c key : Std.U64) :
    permute.feistel_n_inv c key 6#usize 40#u32 ⦃ d =>
      ∃ l r a b : Std.U32, l.val = c.val / 2^20 % 2^20 ∧ r.val = c.val % 2^20 ∧
        permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := 6#usize } } key 20#u32 l r
          = ok (a, b) ∧ a.val < 2^20 ∧ b.val < 2^20 ∧ d.val = a.val * 2^20 + b.val ⦄ := by
  unfold permute.feistel_n_inv
  step*
  have hh : half = 20#u32 := UScalar.eq_of_val_eq (by simp [half_post])
  subst hh
  have hi : i.val = 2^20 := by rw [i_post1]; simp [U64.size, U64.numBits, Nat.shiftLeft_eq]
  have hm : mask.val = 2^20 - 1 := by omega
  have hl : l.val = c.val / 2^20 % 2^20 := by
    rw [l_post, UScalar.cast_val_eq, i2_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod,
      i1_post1, Nat.shiftRight_eq_div_pow]
    simp only [UScalarTy.numBits]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (c.val / 2^20) (show 0 < 2^20 by norm_num)
    omega
  have hr : r.val = c.val % 2^20 := by
    rw [r_post, UScalar.cast_val_eq, i3_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    simp only [UScalarTy.numBits]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (c.val) (show 0 < 2^20 by norm_num)
    omega
  have hlb : l.val < 2^20 := by rw [hl]; exact Nat.mod_lt _ (by norm_num)
  have hrb : r.val < 2^20 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨a, b, h1, h2, h3⟩ := od_il_bound key 6 6#usize l r (by simp) (by omega) hlb hrb
  simp only [core.iter.traits.iterator.Iterator.rev.default, core.iter.adapters.rev.Rev.new,
    bind_tc_ok, h1]
  step*
  refine ⟨l, r, a, b, hl, hr, h1, h2, h3, ?_⟩
  have h4' : i4.val = a.val := by
    rw [i4_post, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
  have h6' : i6.val = b.val := by
    rw [i6_post, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
  have h5' : i5.val = a.val * 2^20 := by
    have hs : U64.size = 2^64 := by simp [U64.size, U64.numBits]
    rw [i5_post1, h4', Nat.shiftLeft_eq, hs, Nat.mod_eq_of_lt (by omega)]
  rw [UScalar.val_or, h5', h6', ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h3]

theorem od_mask_id (id : Std.U64) (h : id.val ≤ 2^40 - 1) : id &&& 1099511627775#u64 = id := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  have : (1099511627775#u64).val = 2^40 - 1 := by simp
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

theorem od_obfuscate_spec (id key : Std.U64) :
    permute.obfuscate id key ⦃ c =>
      ∃ l1 r1 : Std.U32, l1.val < 2^20 ∧ r1.val < 2^20 ∧ c.val = l1.val * 2^20 + r1.val ∧
      ∃ l0 r0 : Std.U32, l0.val = (id.val % 2^40) / 2^20 % 2^20 ∧ r0.val = (id.val % 2^40) % 2^20 ∧
        permute.feistel_n_inv_loop { iter := { start := 0#usize, «end» := 6#usize } } key 20#u32 l1 r1
          = ok (l0, r0) ⦄ := by
  unfold permute.obfuscate
  rw [od_max_id_eq]
  simp only [bind_tc_ok, lift, permute.ROUNDS, permute.WIDTH_BITS]
  have h := od_feistel_n_spec (id &&& 1099511627775#u64) key
  have hv : (id &&& 1099511627775#u64).val = id.val % 2^40 := by
    rw [UScalar.val_and]
    have : (1099511627775#u64).val = 2^40 - 1 := by simp
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [hv] at h
  exact h

/--
For every 64-bit key and every 64-bit input, both `obfuscate(id, key)` and
`deobfuscate(id, key)` never panic and return a value in the 40-bit domain,
i.e. at most `MAX_ID = 2^40 - 1` (inputs above the domain are reduced, and
every Feistel round keeps both halves below `2^20`).
-/
theorem output_never_leaves_the_domain (key id : Std.U64) :
    output_never_leaves_the_domain_spec key id := by
  unfold output_never_leaves_the_domain_spec
  obtain ⟨c, hc, l1, r1, hl1, hr1, hcv, _⟩ := spec_imp_exists (od_obfuscate_spec id key)
  rw [hc]
  simp only [bind_tc_ok]
  unfold permute.deobfuscate
  rw [od_max_id_eq]
  simp only [bind_tc_ok, lift, permute.ROUNDS, permute.WIDTH_BITS]
  obtain ⟨d, hd, l, r, a, b, _, _, _, ha, hb, hdv⟩ :=
    spec_imp_exists (od_feistel_n_inv_spec (id &&& 1099511627775#u64) key)
  rw [hd]
  simp only [bind_tc_ok, WP.spec_ok]
  constructor <;> omega

end Benchmark.Cases.Arxid.Permute
