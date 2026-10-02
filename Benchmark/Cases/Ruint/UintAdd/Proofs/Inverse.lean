import Benchmark.Cases.Ruint.UintAdd.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.UintAdd

/-- Little-endian value of a list of 64-bit limbs. -/
def lval : List Std.U64 → Nat
  | [] => 0
  | x :: xs => x.val + 2^64 * lval xs

theorem u64_lt (x : Std.U64) : x.val < 2^64 := by
  have := x.hBounds; simpa [UScalarTy.numBits] using this

theorem lval_lt (l : List Std.U64) : lval l < 2^(64 * l.length) := by
  induction l with
  | nil => simp [lval]
  | cons x xs ih =>
    simp only [lval, List.length_cons]
    have hx := u64_lt x
    rw [Nat.mul_succ, pow_add, Nat.mul_comm (2^(64*xs.length))]
    have : lval xs + 1 ≤ 2^(64*xs.length) := ih
    nlinarith

theorem lval_append (l1 l2 : List Std.U64) :
    lval (l1 ++ l2) = lval l1 + 2^(64 * l1.length) * lval l2 := by
  induction l1 with
  | nil => simp [lval]
  | cons x xs ih =>
    simp only [List.cons_append, lval, ih, List.length_cons, Nat.mul_succ, pow_add]
    ring

theorem lval_inj (l1 l2 : List Std.U64) (hl : l1.length = l2.length) (hv : lval l1 = lval l2) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hl
    | cons y ys =>
      simp only [lval, List.length_cons, Nat.add_right_cancel_iff] at hv hl
      have hx := u64_lt x; have hy := u64_lt y
      have h1 : x.val = y.val := by omega
      have h2 : lval xs = lval ys := by omega
      have : x = y := by scalar_tac
      rw [this, ih ys hl h2]

theorem lval_take_succ (l : List Std.U64) (i : Nat) (hi : i < l.length) :
    lval (l.take (i+1)) = lval (l.take i) + 2^(64*i) * (l[i]).val := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, lval_append]
  have : (l.take i).length = i := by simp; omega
  rw [this]; simp [lval]


theorem ovf_add (x y : Std.U64) :
    (UScalar.overflowing_add x y).1.val + 2^64 * (UScalar.overflowing_add x y).2.toNat
      = x.val + y.val := by
  have h := UScalar.overflowing_add_eq x y
  have hx := u64_lt x; have hy := u64_lt y
  have hmax : UScalar.max .U64 = 2^64 - 1 := by simp [U64.max_eq]
  have hsize : UScalar.size .U64 = 2^64 := by simp [U64.size, U64.numBits]
  simp only [hmax, hsize] at h
  split at h <;> simp_all

theorem carrying_add_eq (l r : Std.U64) (c : Bool) :
    algorithms.add.carrying_add l r c =
      ok ((UScalar.overflowing_add (UScalar.overflowing_add l r).1 (UScalar.cast_fromBool .U64 c)).1,
          (UScalar.overflowing_add l r).2 ||
            (UScalar.overflowing_add (UScalar.overflowing_add l r).1 (UScalar.cast_fromBool .U64 c)).2) := by
  rfl

@[step]
theorem carrying_add_spec (l r : Std.U64) (c : Bool) :
    algorithms.add.carrying_add l r c ⦃ res => res.1.val + 2^64 * res.2.toNat = l.val + r.val + c.toNat ⦄ := by
  rw [carrying_add_eq, WP.spec_ok]
  have h1 := ovf_add l r
  have h2 := ovf_add (UScalar.overflowing_add l r).1 (UScalar.cast_fromBool .U64 c)
  rw [UScalar.cast_fromBool_val_eq] at h2
  generalize (UScalar.overflowing_add l r) = A at *
  obtain ⟨r1, c1⟩ := A
  generalize UScalar.overflowing_add r1 (UScalar.cast_fromBool .U64 c) = B at *
  obtain ⟨r2, c2⟩ := B
  simp only at h1 h2 ⊢
  have hr1 := u64_lt r1; have hr2 := u64_lt r2; have hl := u64_lt l; have hr := u64_lt r
  have hc : c.toNat ≤ 1 := Bool.toNat_le c
  cases c1 <;> cases c2 <;> simp only [Bool.or_true, Bool.or_false, Bool.toNat_true, Bool.toNat_false] at h1 h2 ⊢ <;> omega


theorem take_succ_set {α} (l : List α) (i : Nat) (x : α) (hi : i < l.length) :
    (l.set i x).take (i+1) = l.take i ++ [x] := by
  rw [List.take_add_one]
  have h1 : (l.set i x)[i]? = some x := by simp [hi]
  rw [h1, List.take_set_of_le (Nat.le_refl i)]
  rfl

theorem drop_succ_set {α} (l : List α) (i : Nat) (x : α) :
    (l.set i x).drop (i+1) = l.drop (i+1) := by
  rw [List.drop_set_of_lt]; omega

theorem getElem_of_drop_eq {α} (l m : List α) (i : Nat) (h : l.drop i = m.drop i)
    (hl : i < l.length) (hm : i < m.length) : l[i] = m[i] := by
  have h1 : (l.drop i)[0]? = (m.drop i)[0]? := by rw [h]
  simp [hl, hm] at h1
  exact h1

theorem drop_succ_of_drop_eq {α} (l m : List α) (i : Nat) (h : l.drop i = m.drop i) :
    l.drop (i+1) = m.drop (i+1) := by
  rw [← List.drop_drop, h, List.drop_drop]

/-- Loop invariant of `overflowing_add` after `i` limbs. -/
def AddInv {BITS LIMBS : Std.Usize} (x0 rhs : Uint BITS LIMBS)
    (st : Uint BITS LIMBS × Bool × Std.Usize) : Prop :=
  st.2.2.val ≤ LIMBS.val ∧
  st.1.limbs.val.drop st.2.2.val = x0.limbs.val.drop st.2.2.val ∧
  lval (st.1.limbs.val.take st.2.2.val) + 2^(64*st.2.2.val) * st.2.1.toNat
    = lval (x0.limbs.val.take st.2.2.val) + lval (rhs.limbs.val.take st.2.2.val)

theorem add_loop_spec {BITS LIMBS : Std.Usize} (x0 rhs self : Uint BITS LIMBS) (carry : Bool)
    (iter : Std.Usize) (h : AddInv x0 rhs (self, carry, iter)) :
    add.Uint.overflowing_add_loop self rhs carry iter
    ⦃ res => lval res.1.limbs.val + 2^(64*LIMBS.val) * res.2.toNat
        = lval x0.limbs.val + lval rhs.limbs.val ⦄ := by
  unfold add.Uint.overflowing_add_loop
  apply loop.spec_decr_nat (fun st => LIMBS.val - st.2.2.val) (AddInv x0 rhs)
  · intro st hst
    obtain ⟨s, c, k⟩ := st
    obtain ⟨hi, hdrop, hv⟩ := hst
    simp only at hi hdrop hv
    dsimp only
    unfold add.Uint.overflowing_add_loop.body
    split
    · rename_i hlt
      unfold core.num.Usize.unchecked_add
      step*
      have hls : s.limbs.val.length = LIMBS.val := s.limbs.property
      have hla : x0.limbs.val.length = LIMBS.val := x0.limbs.property
      have hlb : rhs.limbs.val.length = LIMBS.val := rhs.limbs.property
      have hiN : k.val < LIMBS.val := by scalar_tac
      have hxa : (s.limbs.val)[k.val] = (x0.limbs.val)[k.val] :=
        getElem_of_drop_eq _ _ _ hdrop (by omega) (by omega)
      subst a_post
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show iter1.val ≤ LIMBS.val
        omega
      · simp only [iter1_post, Array.set_val_eq]
        rw [drop_succ_set]; exact drop_succ_of_drop_eq _ _ _ hdrop
      · simp only [iter1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), lval_append, lval_take_succ _ _ (by omega),
          lval_take_succ _ _ (by omega)]
        have hlen : (List.take (↑k) s.limbs.val).length = k.val := by simp; omega
        rw [hlen]
        simp only [lval, Nat.mul_zero, Nat.add_zero]
        rw [i_post2, hxa] at i2_post
        rw [i1_post2] at i2_post
        have e := congrArg (fun t => t * 2^(64*k.val)) i2_post
        beta_reduce at e
        have hp : 2^(64*(k.val+1)) = 2^(64*k.val) * 2^64 := by rw [Nat.mul_succ, pow_add]
        rw [hp]
        nlinarith [hv, e]
      · show LIMBS.val - iter1.val < LIMBS.val - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hiN : k.val = LIMBS.val := by scalar_tac
      have hls : s.limbs.val.length = LIMBS.val := s.limbs.property
      have hla : x0.limbs.val.length = LIMBS.val := x0.limbs.property
      have hlb : rhs.limbs.val.length = LIMBS.val := rhs.limbs.property
      rw [hiN] at hv
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact hv
  · exact h

theorem ovf_sub (x y : Std.U64) :
    (uoverflowing_sub x y).1.val + y.val = x.val + 2^64 * (uoverflowing_sub x y).2.toNat := by
  have hx := u64_lt x; have hy := u64_lt y
  simp only [uoverflowing_sub]
  have hv : (⟨x.bv - y.bv⟩ : Std.U64).val = (2^64 - y.val + x.val) % 2^64 := by
    simp only [UScalar.val, BitVec.toNat_sub]
    simp [UScalarTy.numBits]
  rw [hv]
  by_cases h : x.val < y.val
  · simp only [h, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false, Bool.toNat_false]
    rw [show 2^64 - y.val + x.val = (x.val - y.val) + 2^64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem borrowing_sub_eq (l r : Std.U64) (c : Bool) :
    algorithms.add.borrowing_sub l r c =
      ok ((uoverflowing_sub (uoverflowing_sub l r).1 (UScalar.cast_fromBool .U64 c)).1,
          (uoverflowing_sub l r).2 ||
            (uoverflowing_sub (uoverflowing_sub l r).1 (UScalar.cast_fromBool .U64 c)).2) := by
  rfl

@[step]
theorem borrowing_sub_spec (l r : Std.U64) (c : Bool) :
    algorithms.add.borrowing_sub l r c ⦃ res => res.1.val + r.val + c.toNat = l.val + 2^64 * res.2.toNat ⦄ := by
  rw [borrowing_sub_eq, WP.spec_ok]
  have h1 := ovf_sub l r
  have h2 := ovf_sub (uoverflowing_sub l r).1 (UScalar.cast_fromBool .U64 c)
  rw [UScalar.cast_fromBool_val_eq] at h2
  generalize (uoverflowing_sub l r) = A at *
  obtain ⟨r1, c1⟩ := A
  generalize uoverflowing_sub r1 (UScalar.cast_fromBool .U64 c) = B at *
  obtain ⟨r2, c2⟩ := B
  simp only at h1 h2 ⊢
  have hr1 := u64_lt r1; have hr2 := u64_lt r2; have hl := u64_lt l; have hr := u64_lt r
  have hc : c.toNat ≤ 1 := Bool.toNat_le c
  cases c1 <;> cases c2 <;> simp only [Bool.or_true, Bool.or_false, Bool.toNat_true, Bool.toNat_false] at h1 h2 ⊢ <;> omega

/-- Loop invariant of `overflowing_sub` after `i` limbs. -/
def SubInv {BITS LIMBS : Std.Usize} (x0 rhs : Uint BITS LIMBS)
    (st : Uint BITS LIMBS × Bool × Std.Usize) : Prop :=
  st.2.2.val ≤ LIMBS.val ∧
  st.1.limbs.val.drop st.2.2.val = x0.limbs.val.drop st.2.2.val ∧
  lval (st.1.limbs.val.take st.2.2.val) + lval (rhs.limbs.val.take st.2.2.val)
    = lval (x0.limbs.val.take st.2.2.val) + 2^(64*st.2.2.val) * st.2.1.toNat

theorem sub_loop_spec {BITS LIMBS : Std.Usize} (x0 rhs self : Uint BITS LIMBS) (carry : Bool)
    (iter : Std.Usize) (h : SubInv x0 rhs (self, carry, iter)) :
    add.Uint.overflowing_sub_loop self rhs carry iter
    ⦃ res => lval res.1.limbs.val + lval rhs.limbs.val
        = lval x0.limbs.val + 2^(64*LIMBS.val) * res.2.toNat ⦄ := by
  unfold add.Uint.overflowing_sub_loop
  apply loop.spec_decr_nat (fun st => LIMBS.val - st.2.2.val) (SubInv x0 rhs)
  · intro st hst
    obtain ⟨s, c, k⟩ := st
    obtain ⟨hi, hdrop, hv⟩ := hst
    simp only at hi hdrop hv
    dsimp only
    unfold add.Uint.overflowing_sub_loop.body
    split
    · rename_i hlt
      unfold core.num.Usize.unchecked_add
      step*
      have hls : s.limbs.val.length = LIMBS.val := s.limbs.property
      have hla : x0.limbs.val.length = LIMBS.val := x0.limbs.property
      have hlb : rhs.limbs.val.length = LIMBS.val := rhs.limbs.property
      have hiN : k.val < LIMBS.val := by scalar_tac
      have hxa : (s.limbs.val)[k.val] = (x0.limbs.val)[k.val] :=
        getElem_of_drop_eq _ _ _ hdrop (by omega) (by omega)
      subst a_post
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show iter1.val ≤ LIMBS.val
        omega
      · simp only [iter1_post, Array.set_val_eq]
        rw [drop_succ_set]; exact drop_succ_of_drop_eq _ _ _ hdrop
      · simp only [iter1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), lval_append, lval_take_succ _ _ (by omega),
          lval_take_succ _ _ (by omega)]
        have hlen : (List.take (↑k) s.limbs.val).length = k.val := by simp; omega
        rw [hlen]
        simp only [lval, Nat.mul_zero, Nat.add_zero]
        rw [i_post2, hxa] at i2_post
        rw [i1_post2] at i2_post
        have e := congrArg (fun t => t * 2^(64*k.val)) i2_post
        beta_reduce at e
        have hp : 2^(64*(k.val+1)) = 2^(64*k.val) * 2^64 := by rw [Nat.mul_succ, pow_add]
        rw [hp]
        nlinarith [hv, e]
      · show LIMBS.val - iter1.val < LIMBS.val - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hiN : k.val = LIMBS.val := by scalar_tac
      have hls : s.limbs.val.length = LIMBS.val := s.limbs.property
      have hla : x0.limbs.val.length = LIMBS.val := x0.limbs.property
      have hlb : rhs.limbs.val.length = LIMBS.val := rhs.limbs.property
      rw [hiN] at hv
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact hv
  · exact h


theorem nlimbs_spec (B : Std.Usize) : nlimbs B ⦃ n => n.val = (B.val + 63) / 64 ⦄ := by
  unfold nlimbs core.num.Usize.div_ceil
  step*

/-- Value of `ruint::mask(bits)`. -/
def maskVal (B : Nat) : Nat := if B = 0 then 0 else if B % 64 = 0 then 2^64 - 1 else 2^(B % 64) - 1

theorem mask_spec (B : Std.Usize) : mask B ⦃ m => m.val = maskVal B.val ⦄ := by
  unfold mask maskVal
  split
  · rename_i h; simp only [WP.spec_ok]; simp [h]
  · rename_i h
    have h' : B.val ≠ 0 := by intro h2; apply h; scalar_tac
    step*
    · simp only [h', ↓reduceIte]
      have : B.val % 64 = 0 := by rename_i h2; rw [← bits1_post]; scalar_tac
      simp only [this, ↓reduceIte]
      rfl
    all_goals
      have hsz : U64.size = 2^64 := by simp [U64.size, U64.numBits]
      have hi : i.val = 2^bits1.val := by
        rw [i_post1, Nat.shiftLeft_eq, Nat.one_mul, hsz]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) i_post3)
      have hb0 : bits1.val ≠ 0 := fun h3 => ‹¬bits1 = 0#usize› (by scalar_tac)
      have hb0' : B.val % 64 ≠ 0 := by omega
      have hpos : 1 ≤ 2^bits1.val := Nat.one_le_two_pow
    · rw [hi]; simp [hpos]
    · rw [m_post1, hi, bits1_post]
      simp [h', hb0']


theorem LIMBS_1_eq (BITS LIMBS : Std.Usize) (h : nlimbs BITS = ok LIMBS) :
    Uint.LIMBS_1 BITS LIMBS = ok LIMBS := by
  unfold Uint.LIMBS_1
  rw [h]; simp

theorem MASK_eq (BITS LIMBS : Std.Usize) : Uint.MASK BITS LIMBS = mask BITS := by
  unfold Uint.MASK; rfl

theorem limbs_of_nlimbs {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) :
    LIMBS.val = (BITS.val + 63) / 64 := by
  have := nlimbs_spec BITS
  rw [h, WP.spec_ok] at this
  exact this

theorem should_mask_spec (BITS LIMBS : Std.Usize) :
    Uint.SHOULD_MASK BITS LIMBS ⦃ b => (b = true ↔ (BITS.val ≠ 0 ∧ BITS.val % 64 ≠ 0)) ⦄ := by
  unfold Uint.SHOULD_MASK
  split
  · rename_i h
    have h' : BITS.val ≠ 0 := by scalar_tac
    rw [MASK_eq]
    apply spec_bind (mask_spec BITS)
    intro m hm
    simp only [WP.spec_ok]
    have hmax : (core.num.U64.MAX).val = 2^64 - 1 := rfl
    constructor
    · intro hne
      refine ⟨h', fun h0 => ?_⟩
      have : m = core.num.U64.MAX := by
        apply UScalar.eq_of_val_eq
        rw [hm, hmax]; simp [maskVal, h', h0]
      simp [this] at hne
    · rintro ⟨_, h1⟩
      have hlt : 2^(BITS.val % 64) - 1 < 2^64 - 1 := by
        have : 2^(BITS.val % 64) < 2^64 := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ (by norm_num))
        have : 1 ≤ 2^(BITS.val % 64) := Nat.one_le_two_pow
        omega
      have : m ≠ core.num.U64.MAX := by
        intro he
        have := congrArg UScalar.val he
        rw [hm, hmax] at this
        simp [maskVal, h', h1] at this
        omega
      simpa using this
  · rename_i h
    simp only [WP.spec_ok]
    have : BITS.val = 0 := by scalar_tac
    simp [this]

theorem mod_split (L P x r : Nat) (hL : L < P) :
    (L + P * x) % (P * 2^r) = L + P * (x % 2^r) := by
  have hx : x = x % 2^r + 2^r * (x / 2^r) := (Nat.mod_add_div x (2^r)).symm
  have e : L + P * x = (L + P * (x % 2^r)) + (P * 2^r) * (x / 2^r) := by
    conv_lhs => rw [hx]
    ring
  rw [e, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h1 : x % 2^r < 2^r := Nat.mod_lt _ (Nat.two_pow_pos r)
  have h2 : x % 2^r + 1 ≤ 2^r := h1
  nlinarith

theorem masked_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) (x : Uint BITS LIMBS) :
    Uint.masked x ⦃ y => lval y.limbs.val = lval x.limbs.val % 2^BITS.val ⦄ := by
  have hN := limbs_of_nlimbs h
  have hlen : x.limbs.val.length = LIMBS.val := x.limbs.property
  unfold Uint.masked Uint.apply_mask
  apply spec_bind (should_mask_spec BITS LIMBS)
  intro b hb
  split
  · rename_i hbt
    obtain ⟨hB0, hB64⟩ := hb.mp hbt
    have hN1 : 1 ≤ LIMBS.val := by omega
    have hBN : BITS.val = 64 * (LIMBS.val - 1) + BITS.val % 64 := by omega
    rw [MASK_eq]
    step*
    apply spec_bind (mask_spec BITS)
    intro m hm
    step*
    subst a_post i1_post2
    rw [Array.set_val_eq]
    have hi : i.val + 1 = LIMBS.val := by omega
    have hset : (x.limbs.val.set i.val i3) = x.limbs.val.take i.val ++ [i3] := by
      rw [← take_succ_set _ _ _ (by omega), List.take_of_length_le (by simp; omega)]
    have hx : lval x.limbs.val = lval (x.limbs.val.take i.val) + 2^(64*i.val) * (x.limbs.val[i.val]).val := by
      rw [← lval_take_succ _ _ (by omega), List.take_of_length_le (by omega)]
    have hlenT : (x.limbs.val.take i.val).length = i.val := by simp; omega
    rw [hset, lval_append, hlenT, hx]
    simp only [lval, Nat.mul_zero, Nat.add_zero]
    rw [i3_post1, UScalar.val_and, hm]
    simp only [maskVal, hB0, hB64, ↓reduceIte, Nat.and_two_pow_sub_one_eq_mod]
    have hL := lval_lt (x.limbs.val.take i.val)
    rw [hlenT] at hL
    have hP : 2^BITS.val = 2^(64*i.val) * 2^(BITS.val % 64) := by rw [← pow_add]; congr 1; omega
    rw [hP, mod_split _ _ _ _ hL]
  · rename_i hbf
    simp only [WP.spec_ok]
    have hnot : ¬ (BITS.val ≠ 0 ∧ BITS.val % 64 ≠ 0) := fun hc => by simp_all
    have hlt := lval_lt x.limbs.val
    rw [hlen] at hlt
    by_cases hB0 : BITS.val = 0
    · have : LIMBS.val = 0 := by omega
      have hl0 : x.limbs.val = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hl0, lval]
    · have hB64 : BITS.val = 64 * LIMBS.val := by omega
      rw [hB64, Nat.mod_eq_of_lt hlt]


theorem lval_replicate_zero (n : Nat) : lval (List.replicate n (0#u64)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, lval, ih]

theorem zero_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) :
    Uint.ZERO BITS LIMBS ⦃ z => lval z.limbs.val = 0 ⦄ := by
  have hN := limbs_of_nlimbs h
  unfold Uint.ZERO Uint.from_limbs
  apply spec_bind (should_mask_spec BITS LIMBS)
  intro b hb
  split
  · rename_i hbt
    obtain ⟨hB0, hB64⟩ := hb.mp hbt
    rw [MASK_eq, LIMBS_1_eq _ _ h]
    step*
    apply spec_bind (mask_spec BITS)
    intro m hm
    step*
    case h_fail =>
      rw [i1_post2]; unfold Array.repeat; simp
    rw [Array.repeat_val, lval_replicate_zero]
  · rw [LIMBS_1_eq _ _ h, bind_tc_ok, WP.spec_ok]
    rw [Array.repeat_val, lval_replicate_zero]

theorem from_limbs_unmasked_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS)
    (l : Std.Array Std.U64 LIMBS) :
    Uint.from_limbs_unmasked BITS l ⦃ x => lval x.limbs.val = lval l.val % 2^BITS.val ⦄ := by
  unfold Uint.from_limbs_unmasked
  rw [LIMBS_1_eq _ _ h]
  simp only [bind_tc_ok]
  exact masked_spec h _

theorem uint_ext {BITS LIMBS : Std.Usize} (x y : Uint BITS LIMBS)
    (h : lval x.limbs.val = lval y.limbs.val) : x = y := by
  obtain ⟨⟨lx, hx⟩⟩ := x
  obtain ⟨⟨ly, hy⟩⟩ := y
  simp only at h
  have : lx = ly := lval_inj lx ly (by rw [hx, hy]) h
  subst this
  rfl


theorem pow_dvd_limbs {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) :
    2^(64*LIMBS.val) = 2^BITS.val * 2^(64*LIMBS.val - BITS.val) := by
  have hN := limbs_of_nlimbs h
  rw [← pow_add]; congr 1; omega

theorem overflowing_add_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS)
    (x y : Uint BITS LIMBS) :
    add.Uint.overflowing_add x y
    ⦃ r => lval r.1.limbs.val = (lval x.limbs.val + lval y.limbs.val) % 2^BITS.val ⦄ := by
  have hN := limbs_of_nlimbs h
  unfold add.Uint.overflowing_add
  split
  · rename_i hB
    have hB' : BITS.val = 0 := by scalar_tac
    apply spec_bind (zero_spec h)
    intro z hz
    simp only [WP.spec_ok]
    rw [hz, hB']; simp [Nat.mod_one]
  · rename_i hB
    have hB' : BITS.val ≠ 0 := by intro h0; apply hB; scalar_tac
    apply spec_bind (add_loop_spec x y x false 0#usize (by
      refine ⟨by simp, by simp, by simp [lval]⟩))
    intro st hst
    obtain ⟨s, c⟩ := st
    simp only at hst
    rw [MASK_eq]
    step*
    apply spec_bind (mask_spec BITS)
    intro m hm
    apply spec_bind (masked_spec h s)
    intro u hu
    simp only [WP.spec_ok]
    rw [hu, ← hst, pow_dvd_limbs h, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem overflowing_sub_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS)
    (x y : Uint BITS LIMBS) :
    add.Uint.overflowing_sub x y
    ⦃ r => (lval r.1.limbs.val + lval y.limbs.val) % 2^BITS.val = lval x.limbs.val % 2^BITS.val
        ∧ lval r.1.limbs.val < 2^BITS.val ⦄ := by
  have hN := limbs_of_nlimbs h
  unfold add.Uint.overflowing_sub
  split
  · rename_i hB
    have hB' : BITS.val = 0 := by scalar_tac
    apply spec_bind (zero_spec h)
    intro z hz
    simp only [WP.spec_ok]
    rw [hz, hB']; simp [Nat.mod_one]
  · rename_i hB
    have hB' : BITS.val ≠ 0 := by intro h0; apply hB; scalar_tac
    apply spec_bind (sub_loop_spec x y x false 0#usize (by
      refine ⟨by simp, by simp, by simp [lval]⟩))
    intro st hst
    obtain ⟨s, c⟩ := st
    simp only at hst
    rw [MASK_eq]
    step*
    apply spec_bind (mask_spec BITS)
    intro m hm
    apply spec_bind (masked_spec h s)
    intro u hu
    simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [hu, Nat.mod_add_mod, hst, pow_dvd_limbs h, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · rw [hu]; exact Nat.mod_lt _ (Nat.two_pow_pos _)


theorem add_op_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) (x y : Uint BITS LIMBS) :
    Uint.Insts.CoreOpsArithAddUintUint.add x y
    ⦃ z => lval z.limbs.val = (lval x.limbs.val + lval y.limbs.val) % 2^BITS.val ⦄ := by
  unfold Uint.Insts.CoreOpsArithAddUintUint.add add.Uint.wrapping_add
  apply spec_bind (overflowing_add_spec h x y)
  intro r hr
  obtain ⟨u, c⟩ := r
  simpa using hr

theorem sub_op_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) (x y : Uint BITS LIMBS) :
    Uint.Insts.CoreOpsArithSubUintUint.sub x y
    ⦃ z => (lval z.limbs.val + lval y.limbs.val) % 2^BITS.val = lval x.limbs.val % 2^BITS.val
        ∧ lval z.limbs.val < 2^BITS.val ⦄ := by
  unfold Uint.Insts.CoreOpsArithSubUintUint.sub add.Uint.wrapping_sub
  apply spec_bind (overflowing_sub_spec h x y)
  intro r hr
  obtain ⟨u, c⟩ := r
  simpa using hr

theorem neg_op_spec {BITS LIMBS : Std.Usize} (h : nlimbs BITS = ok LIMBS) (x : Uint BITS LIMBS) :
    Uint.Insts.CoreOpsArithNegUint.neg x
    ⦃ z => (lval z.limbs.val + lval x.limbs.val) % 2^BITS.val = 0
        ∧ lval z.limbs.val < 2^BITS.val ⦄ := by
  have hneg : add.Uint.overflowing_neg x
      ⦃ r => (lval r.1.limbs.val + lval x.limbs.val) % 2^BITS.val = 0
          ∧ lval r.1.limbs.val < 2^BITS.val ⦄ := by
    unfold add.Uint.overflowing_neg
    apply spec_bind (zero_spec h)
    intro zr hzr
    apply spec_mono (overflowing_sub_spec h zr x)
    intro r hr
    rw [hzr, Nat.zero_mod] at hr
    exact hr
  unfold Uint.Insts.CoreOpsArithNegUint.neg add.Uint.wrapping_neg
  apply spec_bind hneg
  intro r hr
  obtain ⟨u, c⟩ := r
  simpa using hr

theorem mod_cancel {M a b c : Nat} (h : (a + c) % M = (b + c) % M) (ha : a < M) (hb : b < M) :
    a = b := by
  have : a ≡ b [MOD M] := Nat.ModEq.add_right_cancel' c h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/--
For every supported width `BITS` (with `LIMBS = nlimbs(BITS)`) and every
`a : Uint<BITS, LIMBS>` produced by the proptest strategy, wrapping negation is
an additive inverse and an involution: `a + (-a) == U::ZERO`,
`a - a == U::ZERO` and `-(-a) == a`.
-/
theorem inverse (BITS LIMBS : Std.Usize) (la : Std.Array Std.U64 LIMBS)
    (h_bits : BITS.val ∈ [0, 1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096])
    (h_limbs : nlimbs BITS = ok LIMBS) :
    inverse_spec BITS LIMBS la := by
  unfold inverse_spec
  apply spec_bind (from_limbs_unmasked_spec h_limbs la); intro a ha
  apply spec_bind (neg_op_spec h_limbs a); intro na h1
  apply spec_bind (add_op_spec h_limbs a na); intro s h2
  apply spec_bind (zero_spec h_limbs); intro z hz
  apply spec_bind (sub_op_spec h_limbs a a); intro d h3
  apply spec_bind (zero_spec h_limbs); intro z' hz'
  apply spec_bind (neg_op_spec h_limbs a); intro na' h4
  apply spec_bind (neg_op_spec h_limbs na'); intro nna h5
  simp only [WP.spec_ok]
  have haM : lval a.limbs.val < 2^BITS.val := by rw [ha]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨uint_ext _ _ ?_, uint_ext _ _ ?_, uint_ext _ _ ?_⟩
  · rw [h2, hz, Nat.add_comm, h1.1]
  · rw [hz']
    apply mod_cancel (c := lval a.limbs.val) _ h3.2 (Nat.two_pow_pos _)
    rw [h3.1, Nat.zero_add]
  · apply mod_cancel (c := lval na'.limbs.val) _ h5.2 haM
    rw [h5.1, Nat.add_comm, h4.1]

end Benchmark.Cases.Ruint.UintAdd
