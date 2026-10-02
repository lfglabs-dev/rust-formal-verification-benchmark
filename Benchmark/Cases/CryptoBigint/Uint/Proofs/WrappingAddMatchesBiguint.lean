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

theorem prim_carrying_add_spec (l r c : Std.U64) :
    primitives.carrying_add l r c ⦃ res => res.1.val + 2^64 * res.2.val = l.val + r.val + c.val ⦄ := by
  unfold primitives.carrying_add
  step*
  have hl := u64_lt l; have hr := u64_lt r; have hc := u64_lt c
  rw [i1_post, i3_post, UScalar.cast_val_eq, UScalar.cast_val_eq, i2_post1, ret_post, i_post,
    a_post, b_post, carry1_post, U64.cast_U128_val_eq, U64.cast_U128_val_eq, U64.cast_U128_val_eq,
    Nat.shiftRight_eq_div_pow]
  simp only [UScalarTy.U64_numBits_eq]
  omega

theorem limb_carrying_add_spec (l r c : limb.Limb) :
    limb.add.Limb.carrying_add l r c ⦃ res => res.1.val + 2^64 * res.2.val = l.val + r.val + c.val ⦄ := by
  unfold limb.add.Limb.carrying_add
  apply spec_bind (prim_carrying_add_spec l r c)
  rintro ⟨x, y⟩ h
  simpa using h

/-- Loop invariant of `Uint::carrying_add` after `i` limbs. -/
def AddInv {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) (c0 : Nat)
    (st : limb.Limb × Array limb.Limb LIMBS × Std.Usize) : Prop :=
  st.2.2.val ≤ LIMBS.val ∧
  limbsVal (st.2.1.val.take st.2.2.val) + 2^(64*st.2.2.val) * st.1.val
    = limbsVal (x.limbs.val.take st.2.2.val) + limbsVal (y.limbs.val.take st.2.2.val) + c0

theorem carrying_add_loop_spec {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) (c0 : Nat)
    (carry : limb.Limb) (limbs : Array limb.Limb LIMBS) (i : Std.Usize)
    (h : AddInv x y c0 (carry, limbs, i)) :
    uint.add.Uint.carrying_add_loop x y carry limbs i
    ⦃ res => limbsVal res.2.val + 2^(64*LIMBS.val) * res.1.val
        = limbsVal x.limbs.val + limbsVal y.limbs.val + c0 ⦄ := by
  unfold uint.add.Uint.carrying_add_loop
  apply loop.spec_decr_nat (fun st => LIMBS.val - st.2.2.val) (AddInv x y c0)
  · intro st hst
    obtain ⟨c, s, k⟩ := st
    obtain ⟨hi, hv⟩ := hst
    simp only at hi hv
    dsimp only
    unfold uint.add.Uint.carrying_add_loop.body
    split
    · rename_i hlt
      have hls : s.val.length = LIMBS.val := s.property
      have hla : x.limbs.val.length = LIMBS.val := x.limbs.property
      have hlb : y.limbs.val.length = LIMBS.val := y.limbs.property
      have hkN : k.val < LIMBS.val := by scalar_tac
      step*
      apply spec_bind (limb_carrying_add_spec _ _ _)
      rintro ⟨w, c⟩ w_post
      step*
      subst a_post
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show i1.val ≤ LIMBS.val
        omega
      · show limbsVal ((s.set k w).val.take i1.val) + 2^(64*i1.val) * c.val
          = limbsVal (x.limbs.val.take i1.val) + limbsVal (y.limbs.val.take i1.val) + c0
        simp only [i1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), limbsVal_append, limbsVal_take_succ _ _ (by omega),
          limbsVal_take_succ _ _ (by omega)]
        have hlen : (List.take (↑k) s.val).length = k.val := by simp; omega
        rw [hlen]
        simp only [limbsVal, Nat.mul_zero, Nat.add_zero]
        rw [← l_post2, ← l1_post2]
        have e := congrArg (fun t => t * 2^(64*k.val)) w_post
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
      exact hv
  · exact h

theorem wrapping_add_general {LIMBS : Std.Usize} (x y : uint.Uint LIMBS) :
    uint.add.Uint.wrapping_add x y
    ⦃ r => uintVal r = (uintVal x + uintVal y) % 2^(64*LIMBS.val) ⦄ := by
  unfold uint.add.Uint.wrapping_add uint.add.Uint.carrying_add
  have h0 : AddInv x y 0 (limb.Limb.ZERO, Array.repeat LIMBS limb.Limb.ZERO, 0#usize) := by
    simp [AddInv, limbsVal, limb.Limb.ZERO]
  simp only [bind_assoc_eq]
  apply spec_bind (carrying_add_loop_spec x y 0 _ _ _ h0)
  rintro ⟨c1, l1⟩ h
  rw [Nat.add_zero] at h
  step*
  unfold uintVal
  have hlen : l1.val.length = LIMBS.val := l1.property
  have hlt := limbsVal_lt l1.val
  rw [hlen] at hlt
  simp only at h ⊢
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem uintVal_lt {LIMBS : Std.Usize} (x : uint.Uint LIMBS) : uintVal x < 2^(64*LIMBS.val) := by
  have hlen : x.limbs.val.length = LIMBS.val := x.limbs.property
  have := limbsVal_lt x.limbs.val
  rw [hlen] at this
  exact this

/--
For all `U256` values `a`, `b`, `a.wrapping_add(&b)` never panics and its value is `(a + b) mod 2^256`, the value of `to_uint(a_bi + b_bi)`.
-/
theorem wrapping_add_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_add_matches_biguint_spec a b := by
  unfold wrapping_add_matches_biguint_spec
  exact wrapping_add_general a b

end Benchmark.Cases.CryptoBigint.Uint
