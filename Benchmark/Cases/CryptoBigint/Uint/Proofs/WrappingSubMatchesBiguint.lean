import Benchmark.Cases.CryptoBigint.Uint.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

theorem u64_lt (x : Std.U64) : x.val < 2^64 := by
  have := x.hBounds; simpa [UScalarTy.numBits] using this

theorem limbsVal_lt (l : List Std.U64) : limbsVal l < 2^(64 * l.length) := by
  induction l with
  | nil => simp [limbsVal]
  | cons x xs ih =>
    simp only [limbsVal, List.length_cons]
    have hx := u64_lt x
    rw [Nat.mul_succ, pow_add, Nat.mul_comm (2^(64*xs.length))]
    have : limbsVal xs + 1 ≤ 2^(64*xs.length) := ih
    nlinarith

theorem limbsVal_append (l1 l2 : List Std.U64) :
    limbsVal (l1 ++ l2) = limbsVal l1 + 2^(64 * l1.length) * limbsVal l2 := by
  induction l1 with
  | nil => simp [limbsVal]
  | cons x xs ih =>
    simp only [List.cons_append, limbsVal, ih, List.length_cons, Nat.mul_succ, pow_add]
    ring

theorem limbsVal_take_succ (l : List Std.U64) (i : Nat) (hi : i < l.length) :
    limbsVal (l.take (i+1)) = limbsVal (l.take i) + 2^(64*i) * (l[i]).val := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, limbsVal_append]
  have : (l.take i).length = i := by simp; omega
  rw [this]; simp [limbsVal]

theorem take_succ_set {α} (l : List α) (i : Nat) (x : α) (hi : i < l.length) :
    (l.set i x).take (i+1) = l.take i ++ [x] := by
  rw [List.take_add_one]
  have h1 : (l.set i x)[i]? = some x := by simp [hi]
  rw [h1, List.take_set_of_le (Nat.le_refl i)]
  rfl

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

theorem prim_borrowing_sub_eq (l r b : Std.U64) :
    primitives.borrowing_sub l r b =
      ok ((uoverflowing_sub (uoverflowing_sub l ⟨b.bv >>> 63⟩).1 r).1,
          Aeneas.Std.U64.wrapping_sub core.num.U64.MIN
            (UScalar.cast_fromBool .U64 ((uoverflowing_sub (uoverflowing_sub l ⟨b.bv >>> 63⟩).1 r).2 ||
              (uoverflowing_sub l ⟨b.bv >>> 63⟩).2))) := by
  rfl

theorem prim_borrowing_sub_spec (l r b : Std.U64) :
    primitives.borrowing_sub l r b ⦃ res =>
      res.1.val + r.val + b.val / 2^63 = l.val + 2^64 * (res.2.val / 2^63) ∧
      (res.2.val = 0 ∨ res.2.val = 2^64 - 1) ⦄ := by
  rw [prim_borrowing_sub_eq, WP.spec_ok]
  have hX : (⟨b.bv >>> 63⟩ : Std.U64).val = b.val / 2^63 := by
    simp only [UScalar.val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb := u64_lt b
  have h1 := ovf_sub l ⟨b.bv >>> 63⟩
  generalize (uoverflowing_sub l ⟨b.bv >>> 63⟩) = A at *
  obtain ⟨r1, c1⟩ := A
  have h2 := ovf_sub r1 r
  generalize uoverflowing_sub r1 r = B at *
  obtain ⟨r2, c2⟩ := B
  simp only at h1 h2 ⊢
  rw [hX] at h1
  have hsz : UScalar.size .U64 = 2^64 := by simp [U64.size, U64.numBits]
  have hmin : (core.num.U64.MIN : Std.U64).val = 0 := rfl
  rw [U64.wrapping_sub_val_eq, UScalar.cast_fromBool_val_eq, hmin, hsz]
  have hr1 := u64_lt r1; have hr2 := u64_lt r2; have hl := u64_lt l; have hr := u64_lt r
  have hbb : b.val / 2^63 ≤ 1 := by omega
  cases c1 <;> cases c2 <;> simp only [Bool.or_true, Bool.or_false, Bool.toNat_true, Bool.toNat_false] at h1 h2 ⊢ <;> omega

theorem limb_borrowing_sub_spec (l r b : limb.Limb) :
    limb.sub.Limb.borrowing_sub l r b ⦃ res =>
      res.1.val + r.val + b.val / 2^63 = l.val + 2^64 * (res.2.val / 2^63) ∧
      (res.2.val = 0 ∨ res.2.val = 2^64 - 1) ⦄ := by
  unfold limb.sub.Limb.borrowing_sub
  apply spec_bind (prim_borrowing_sub_spec l r b)
  rintro ⟨x, y⟩ h
  simpa using h

/-- Loop invariant of `Uint::borrowing_sub` after `i` limbs. -/
def SubInv {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) (b0 : Nat)
    (st : limb.Limb × Array limb.Limb LIMBS × Std.Usize) : Prop :=
  st.2.2.val ≤ LIMBS.val ∧ (st.1.val = 0 ∨ st.1.val = 2^64 - 1) ∧
  limbsVal (st.2.1.val.take st.2.2.val) + limbsVal (y.limbs.val.take st.2.2.val) + b0
    = limbsVal (x.limbs.val.take st.2.2.val) + 2^(64*st.2.2.val) * (st.1.val / 2^63)

theorem borrowing_sub_loop_spec {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) (b0 : Nat)
    (borrow : limb.Limb) (limbs : Array limb.Limb LIMBS) (i : Std.Usize)
    (h : SubInv x y b0 (borrow, limbs, i)) :
    uint.sub.Uint.borrowing_sub_loop x y borrow limbs i
    ⦃ res => (res.1.val = 0 ∨ res.1.val = 2^64 - 1) ∧
        limbsVal res.2.val + limbsVal y.limbs.val + b0
          = limbsVal x.limbs.val + 2^(64*LIMBS.val) * (res.1.val / 2^63) ⦄ := by
  unfold uint.sub.Uint.borrowing_sub_loop
  apply loop.spec_decr_nat (fun st => LIMBS.val - st.2.2.val) (SubInv x y b0)
  · intro st hst
    obtain ⟨c, s, k⟩ := st
    obtain ⟨hi, hc, hv⟩ := hst
    simp only at hi hc hv
    dsimp only
    unfold uint.sub.Uint.borrowing_sub_loop.body
    split
    · rename_i hlt
      have hls : s.val.length = LIMBS.val := s.property
      have hla : x.limbs.val.length = LIMBS.val := x.limbs.property
      have hlb : y.limbs.val.length = LIMBS.val := y.limbs.property
      have hkN : k.val < LIMBS.val := by scalar_tac
      step*
      apply spec_bind (limb_borrowing_sub_spec _ _ _)
      rintro ⟨w, b⟩ ⟨hw, hb⟩
      step*
      subst a_post
      refine ⟨⟨?_, hb, ?_⟩, ?_⟩
      · show i1.val ≤ LIMBS.val
        omega
      · show limbsVal ((s.set k w).val.take i1.val) + limbsVal (y.limbs.val.take i1.val) + b0
          = limbsVal (x.limbs.val.take i1.val) + 2^(64*i1.val) * (b.val / 2^63)
        simp only [i1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), limbsVal_append, limbsVal_take_succ _ _ (by omega),
          limbsVal_take_succ _ _ (by omega)]
        have hlen : (List.take (↑k) s.val).length = k.val := by simp; omega
        rw [hlen]
        simp only [limbsVal, Nat.mul_zero, Nat.add_zero]
        rw [← l_post2, ← l1_post2]
        have e := congrArg (fun t => t * 2^(64*k.val)) hw
        beta_reduce at e
        have hp : 2^(64*(k.val+1)) = 2^(64*k.val) * 2^64 := by rw [Nat.mul_succ, pow_add]
        rw [hp]
        nlinarith [hv, e]
      · show LIMBS.val - i1.val < LIMBS.val - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hiN : k.val = LIMBS.val := by scalar_tac
      have hls : s.val.length = LIMBS.val := s.property
      have hla : x.limbs.val.length = LIMBS.val := x.limbs.property
      have hlb : y.limbs.val.length = LIMBS.val := y.limbs.property
      rw [hiN] at hv
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hc, hv⟩
  · exact h

theorem borrowing_sub_zero_spec {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) :
    uint.sub.Uint.borrowing_sub x y limb.Limb.ZERO
    ⦃ res => (res.2.val = 0 ∨ res.2.val = 2^64 - 1) ∧
        uintVal res.1 + uintVal y = uintVal x + 2^(64*LIMBS.val) * (res.2.val / 2^63) ⦄ := by
  unfold uint.sub.Uint.borrowing_sub
  have h0 : SubInv x y 0 (limb.Limb.ZERO, Array.repeat LIMBS limb.Limb.ZERO, 0#usize) := by
    simp [SubInv, limbsVal, limb.Limb.ZERO]
  apply spec_bind (borrowing_sub_loop_spec x y 0 _ _ _ h0)
  rintro ⟨c1, l1⟩ ⟨hc, h⟩
  step*
  unfold uintVal
  simp only at h hc ⊢
  exact ⟨hc, h⟩

theorem wrapping_sub_general {LIMBS : Std.Usize} (x y : uint.Uint LIMBS)
    (hxy : uintVal y ≤ uintVal x) :
    uint.sub.Uint.wrapping_sub x y ⦃ r => uintVal r = uintVal x - uintVal y ⦄ := by
  unfold uint.sub.Uint.wrapping_sub
  apply spec_bind (borrowing_sub_zero_spec x y)
  rintro ⟨u, c⟩ ⟨hc, h⟩
  simp only at h hc ⊢
  have hlen : u.limbs.val.length = LIMBS.val := u.limbs.property
  have hlt := limbsVal_lt u.limbs.val
  rw [hlen] at hlt
  have hlt' : uintVal u < 2^(64*LIMBS.val) := hlt
  have hbit : c.val / 2^63 = 0 := by
    rcases hc with hc | hc
    · rw [hc, Nat.zero_div]
    · exfalso
      rw [hc] at h
      have : (2^64 - 1) / 2^63 = 1 := by norm_num
      rw [this] at h
      omega
  rw [hbit] at h
  step*

theorem uintVal_lt {LIMBS : Std.Usize} (x : uint.Uint LIMBS) : uintVal x < 2^(64*LIMBS.val) := by
  have hlen : x.limbs.val.length = LIMBS.val := x.limbs.property
  have := limbsVal_lt x.limbs.val
  rw [hlen] at this
  exact this

/--
For all `U256` values `a`, `b`, after swapping them so that `a >= b`, `a.wrapping_sub(&b)` never panics and its value is `a - b`, the value of `to_uint(a_bi - b_bi)`.
-/
theorem wrapping_sub_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_sub_matches_biguint_spec a b := by
  unfold wrapping_sub_matches_biguint_spec
  intro hi lo
  have ha : uintVal a < 2^256 := uintVal_lt a
  have hb : uintVal b < 2^256 := uintVal_lt b
  by_cases h : uintVal b > uintVal a
  · have hhi : hi = b := if_pos h
    have hlo : lo = a := if_pos h
    rw [hhi, hlo]
    apply spec_mono (wrapping_sub_general b a (le_of_lt h))
    intro r hr
    rw [hr, Nat.mod_eq_of_lt (by omega)]
  · have hhi : hi = a := if_neg h
    have hlo : lo = b := if_neg h
    rw [hhi, hlo]
    apply spec_mono (wrapping_sub_general a b (by omega))
    intro r hr
    rw [hr, Nat.mod_eq_of_lt (by omega)]

end Benchmark.Cases.CryptoBigint.Uint
