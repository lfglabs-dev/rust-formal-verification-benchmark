import Benchmark.Cases.OpenpqlPrelude.Card.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Card

theorem cr_try_from_one :
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize =
      ok (core.result.Result.Ok 1#u32) := by
  unfold core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  have hmax : (UScalar.cast .Usize core.num.U32.MAX).val = 2^32 - 1 := by
    rw [UScalar.cast_val_eq]
    have : core.num.U32.MAX.val = 2^32 - 1 := by first | rfl | simp [core.num.U32.MAX]
    rw [this]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
  have hmin : (UScalar.cast .Usize core.num.U32.MIN).val = 0 := by
    rw [UScalar.cast_val_eq]
    have : core.num.U32.MIN.val = 0 := by first | rfl | simp [core.num.U32.MIN]
    rw [this]; simp
  have h1 : ¬ (1#usize > UScalar.cast .Usize core.num.U32.MAX) := by
    intro h; have : (1#usize).val > (UScalar.cast .Usize core.num.U32.MAX).val := h
    rw [hmax] at this; simp at this
  have h2 : ¬ (1#usize < UScalar.cast .Usize core.num.U32.MIN) := by
    intro h; have : (1#usize).val < (UScalar.cast .Usize core.num.U32.MIN).val := h
    rw [hmin] at this; simp at this
  simp only [lift, bind_tc_ok, h1, h2, if_false]
  congr 2
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]; simp

theorem cr_range_next_lt (i e : Std.U32) (h : i.val < e.val) :
    ∃ i' : Std.U32, i'.val = i.val + 1 ∧
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.Some i, { start := i', «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, core.U32.Insts.CoreCloneClone.clone,
    core.U32.Insts.CoreIterRangeStep.forward_checked,
    core.num.U32.checked_add, core.num.U32.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u32, cr_try_from_one, if_true]
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

theorem cr_range_next_ge (i e : Std.U32) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.U32.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.U32.Insts.CoreCmpPartialOrdU32, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

/-- Number of set bits of `v` at positions `[s, 64)`. -/
def cnt (v : Nat) (s : Nat) : Nat := ((List.range' s (64 - s)).filter (fun k => v.testBit k)).length

theorem cr_cnt_succ (v s : Nat) (hs : s < 64) :
    cnt v s = (if v.testBit s then 1 else 0) + cnt v (s + 1) := by
  unfold cnt
  have : 64 - s = (64 - (s + 1)) + 1 := by omega
  rw [this, List.range'_succ, List.filter_cons]
  split
  · simp_all; omega
  · simp_all

theorem cr_count_ones_loop (x : Std.U64) :
    core.num.U64.count_ones_loop { start := 0#u32, «end» := 64#u32 } x 0#u32 ⦃ r =>
      r.val = cnt x.val 0 ⦄ := by
  unfold core.num.U64.count_ones_loop
  apply loop.spec_decr_nat (fun p : core.ops.range.Range Std.U32 × Std.U32 => 64 - p.1.start.val)
    (fun p => p.1.«end» = 64#u32 ∧ p.1.start.val ≤ 64 ∧ p.2.val ≤ p.1.start.val ∧
      p.2.val + cnt x.val p.1.start.val = cnt x.val 0)
  · rintro ⟨⟨s, e⟩, n⟩ ⟨he, hs, hn, hinv⟩
    simp only at he hs hn hinv ⊢
    have he64 : e.val = 64 := by rw [he]; rfl
    unfold core.num.U64.count_ones_loop.body
    by_cases hlt : s.val < 64
    · obtain ⟨s', hs', hnext⟩ := cr_range_next_lt s e (by rw [he64]; exact hlt)
      rw [hnext]
      simp only [bind_tc_ok]
      step as ⟨y, hy⟩
      have hand : (y &&& 1#u64).val = x.val / 2 ^ s.val % 2 := by
        simp [UScalar.val_and, Nat.and_one_is_mod, hy, Nat.shiftRight_eq_div_pow]
      have hsucc := cr_cnt_succ x.val s.val hlt
      have htb : x.val.testBit s.val = decide (x.val / 2 ^ s.val % 2 = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
      by_cases hb : x.val / 2 ^ s.val % 2 = 1
      · have heq : (y &&& 1#u64) = 1#u64 := by
          apply UScalar.eq_of_val_eq; rw [hand, hb]; rfl
        simp only [lift, bind_tc_ok, heq, if_true]
        step as ⟨n1, hn1⟩
        refine ⟨he, by omega, by omega, ?_, by omega⟩
        rw [hn1, hs', ← hinv, hsucc, htb]; simp [hb]; omega
      · have heq : (y &&& 1#u64) ≠ 1#u64 := by
          intro hc; have := congrArg UScalar.val hc; rw [hand] at this; simp at this; omega
        simp only [lift, bind_tc_ok, heq, if_false, WP.spec_ok]
        refine ⟨he, by omega, by omega, ?_, by omega⟩
        rw [hs', ← hinv, hsucc, htb]; simp [hb]
    · rw [cr_range_next_ge s e (by rw [he64]; exact hlt)]
      simp only [bind_tc_ok, WP.spec_ok]
      have hs64 : s.val = 64 := by omega
      rw [← hinv, hs64]; simp [cnt]
  · simp [cnt]

/-- Rank index (`rank as i8`). -/
def ridx : card.rank.Rank → Nat
  | .R2 => 0 | .R3 => 1 | .R4 => 2 | .R5 => 3 | .R6 => 4 | .R7 => 5 | .R8 => 6
  | .R9 => 7 | .RT => 8 | .RJ => 9 | .RQ => 10 | .RK => 11 | .RA => 12

/-- Suit index (`suit as i8`). -/
def sidx : card.suit.Suit → Nat
  | .S => 0 | .H => 1 | .D => 2 | .C => 3

theorem cr_disc_rank (r : card.rank.Rank) : (read_discriminant r : Std.Isize).val = ridx r := by
  cases r <;> simp [read_discriminant, card.rank.Rank.read_discriminant, ridx]

theorem cr_disc_suit (s : card.suit.Suit) : (read_discriminant s : Std.Isize).val = sidx s := by
  cases s <;> simp [read_discriminant, card.suit.Suit.read_discriminant, sidx]

theorem cr_from_card (r : card.rank.Rank) (s : card.suit.Suit) :
    card.card64.Card64.from_card { rank := r, suit := s } ⦃ c =>
      c.val = 2 ^ (16 * sidx s + ridx r) ⦄ := by
  unfold card.card64.Card64.from_card card.card64.Card64.from_indices
  rw [card.card64.Card64.OFFSET_SUIT.eq_1]
  have hr := cr_disc_rank r
  have hs := cr_disc_suit s
  have hr12 : ridx r ≤ 12 := by cases r <;> simp [ridx]
  have hs3 : sidx s ≤ 3 := by cases s <;> simp [sidx]
  have hmin : Min.min IScalarTy.I8.numBits IScalarTy.Isize.numBits = 8 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [IScalarTy.numBits, h]
  have hi1 : (IScalar.cast .I8 (read_discriminant r : Std.Isize)).val = ridx r := by
    rw [IScalar.cast_val_eq, hr, hmin]; simp only [Int.bmod]; split <;> omega
  have hi3 : (IScalar.cast .I8 (read_discriminant s : Std.Isize)).val = sidx s := by
    rw [IScalar.cast_val_eq, hs, hmin]; simp only [Int.bmod]; split <;> omega
  have ht1 : IScalar.toNat (IScalar.cast .I8 (read_discriminant r : Std.Isize)) = ridx r := by
    simp only [IScalar.toNat, hi1]; simp
  step as ⟨a1, ha1⟩
  step as ⟨a3, ha3⟩
  step as ⟨sh1, hsh1, hsh1', hsh1''⟩
  have hsh1v : sh1.val = 2 ^ ridx r := by
    rw [hsh1, ha1]
    have : (↑(IScalar.cast IScalarTy.I8 (read_discriminant r : Std.Isize)) : Int).toNat = ridx r := by
      rw [hi1]; simp
    rw [this, Nat.shiftLeft_eq, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    have : 2 ^ ridx r ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hr12
    simp [U64.size, U64.numBits]; omega
  step as ⟨m, hm⟩
  all_goals try (rw [ha3, hi3]; simp [I8.min, I8.max, I8.numBits]; omega)
  step as ⟨sh2, hsh2, hsh2', hsh2''⟩
  all_goals try (simp only [IScalar.toNat, hm, ha3, hi3]; omega)
  have hmv : (↑m : Int).toNat = 16 * sidx s := by rw [hm, ha3, hi3]; omega
  rw [hsh2, hsh1v, hmv, Nat.shiftLeft_eq, ← Nat.pow_add, Nat.add_comm (ridx r)]
  apply Nat.mod_eq_of_lt
  have : 2 ^ (16 * sidx s + ridx r) ≤ 2 ^ 60 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp [U64.size, U64.numBits]; omega

theorem cr_contains_card (x : card.card64.Card64) (r : card.rank.Rank) (s : card.suit.Suit) :
    card.card64.Card64.contains_card x { rank := r, suit := s } ⦃ b =>
      b = x.val.testBit (16 * sidx s + ridx r) ⦄ := by
  unfold card.card64.Card64.contains_card
  apply spec_bind (cr_from_card r s)
  intro c hc
  simp only [lift, bind_tc_ok, WP.spec_ok]
  have hv : (c &&& x).val = (x.val.testBit (16 * sidx s + ridx r)).toNat * 2 ^ (16 * sidx s + ridx r) := by
    rw [UScalar.val_and, hc, Nat.land_comm, Nat.and_two_pow]
  by_cases hb : x.val.testBit (16 * sidx s + ridx r)
  · have : (c &&& x) = c := by
      apply UScalar.eq_of_val_eq; rw [hv, hc, hb]; simp
    simp [this, hb]
  · have : (c &&& x) ≠ c := by
      intro h; have := congrArg UScalar.val h; rw [hv, hc] at this; simp [hb] at this
    simp [this, hb]

theorem cr_filterAuxM {α : Type} (p : α → RustM Bool) (q : α → Bool) (h : ∀ a, p a = ok (q a)) :
    ∀ (l acc : List α), List.filterAuxM p l acc = ok ((l.filter q).reverse ++ acc) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a t ih =>
    intro acc
    simp only [List.filterAuxM, h, bind_tc_ok, ih]
    cases hq : q a <;> simp [hq, List.filter_cons]

theorem cr_filterM {α : Type} (l : List α) (p : α → RustM Bool) (q : α → Bool) (h : ∀ a, p a = ok (q a)) :
    l.filterM p = ok (l.filter q) := by
  simp only [List.filterM, cr_filterAuxM p q h l [], bind_tc_ok]
  simp
  rfl

theorem cr_eq_of_spec {α : Type} (e : RustM α) (v : α) (h : e ⦃ b => b = v ⦄) : e = ok v := by
  cases e with
  | ok a => rw [WP.spec_ok] at h; rw [h]
  | fail _ => exact absurd h (by simp [WP.spec, WP.theta, WP.wp_return])
  | div => exact absurd h (by simp [WP.spec, WP.theta, WP.wp_return])

theorem cr_card_contains_eq (x : card.card64.Card64) (c : card.card.Card) :
    card.card64.Card64.contains_card x c = ok (x.val.testBit (16 * sidx c.suit + ridx c.rank)) := by
  obtain ⟨r, s⟩ := c
  exact cr_eq_of_spec _ _ (cr_contains_card x r s)

theorem cr_count_eq (v : Nat) (hv : v &&& 0x1FFF1FFF1FFF1FFF = v) :
    cnt v 0 = (allCards.filter (fun c => v.testBit (16 * sidx c.suit + ridx c.rank))).length := by
  have hz : ∀ k, k ∈ [13, 14, 15, 29, 30, 31, 45, 46, 47, 61, 62, 63] → v.testBit k = false := by
    intro k hk
    have hm : Nat.testBit 0x1FFF1FFF1FFF1FFF k = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← hv, Nat.testBit_and, hm, Bool.and_false]
  have h13 := hz 13 (by simp); have h14 := hz 14 (by simp); have h15 := hz 15 (by simp)
  have h29 := hz 29 (by simp); have h30 := hz 30 (by simp); have h31 := hz 31 (by simp)
  have h45 := hz 45 (by simp); have h46 := hz 46 (by simp); have h47 := hz 47 (by simp)
  have h61 := hz 61 (by simp); have h62 := hz 62 (by simp); have h63 := hz 63 (by simp)
  unfold cnt
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  simp [List.countP_cons, List.range'_succ, allCards, allRanks, allSuits, sidx, ridx,
    h13, h14, h15, h29, h30, h31, h45, h46, h47, h61, h62, h63]
  omega

/--
For every `Card64` produced by the property-test generator (a `u64` masked with
`Card64::ALL`), `count()` (a popcount) never panics and equals the number of the 52 cards
for which `contains_card` holds.
-/
theorem card64_count_matches_contains_card (c64 : card.card64.Card64)
    (h_c64 : c64.val &&& 0x1FFF1FFF1FFF1FFF = c64.val) :
    card64_count_spec c64 := by
  unfold card64_count_spec card.card64.Card64.count core.num.U64.count_ones
  have hle : cnt c64.val 0 ≤ 64 := by
    unfold cnt
    have := List.length_filter_le (fun k => c64.val.testBit k) (List.range' 0 (64 - 0))
    simp at this ⊢; omega
  have hcount : (do
      let i ← core.num.U64.count_ones_loop { start := 0#u32, «end» := 64#u32 } c64 0#u32
      ok (UScalar.cast UScalarTy.U8 i)) ⦃ n => n.val = cnt c64.val 0 ⦄ := by
    apply spec_bind (cr_count_ones_loop c64)
    intro i hi
    simp only [WP.spec_ok]
    rw [UScalar.cast_val_eq, hi]
    simp; omega
  apply spec_bind hcount
  intro n hn
  rw [cr_filterM allCards _ (fun c => c64.val.testBit (16 * sidx c.suit + ridx c.rank))
    (cr_card_contains_eq c64)]
  simp only [bind_tc_ok, WP.spec_ok]
  rw [hn, cr_count_eq c64.val h_c64]

end Benchmark.Cases.OpenpqlPrelude.Card
