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

theorem and_decomp (x1 x2 y1 y2 : Nat) (hx : x1 < 2^64) (hy : y1 < 2^64) :
    (x1 + 2^64 * x2) &&& (y1 + 2^64 * y2) = (x1 &&& y1) + 2^64 * (x2 &&& y2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hxy : x1 &&& y1 < 2^64 := Nat.and_lt_two_pow _ hy
  rw [Nat.add_comm x1, Nat.add_comm y1, Nat.add_comm (x1 &&& y1), Nat.testBit_and,
    Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ hxy]
  split <;> simp [Nat.testBit_and]

theorem limbsVal_zipWith_and (l1 l2 : List Std.U64) (h : l1.length = l2.length) :
    limbsVal (List.zipWith (· &&& ·) l1 l2) = limbsVal l1 &&& limbsVal l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zipWith_cons_cons, limbsVal, UScalar.val_and]
      rw [ih ys (by simpa using h), and_decomp _ _ _ _ (u64_lt x) (u64_lt y)]

/-- Loop invariant of `Uint::bitand` after `i` limbs. -/
def AndInv {LIMBS : Std.Usize} (u v : uint.Uint LIMBS)
    (st : Array limb.Limb LIMBS × Std.Usize) : Prop :=
  st.2.val ≤ LIMBS.val ∧
  st.1.val.take st.2.val = List.zipWith (· &&& ·) (u.limbs.val.take st.2.val) (v.limbs.val.take st.2.val)

theorem bitand_loop_spec {LIMBS : Std.Usize} (u v : uint.Uint LIMBS)
    (limbs : Array limb.Limb LIMBS) (i : Std.Usize) (h : AndInv u v (limbs, i)) :
    uint.bit_and.Uint.bitand_loop u v limbs i
    ⦃ res => res.val = List.zipWith (· &&& ·) u.limbs.val v.limbs.val ⦄ := by
  unfold uint.bit_and.Uint.bitand_loop
  apply loop.spec_decr_nat (fun st => LIMBS.val - st.2.val) (AndInv u v)
  · intro st hst
    obtain ⟨s, k⟩ := st
    obtain ⟨hi, hv⟩ := hst
    simp only at hi hv
    dsimp only
    unfold uint.bit_and.Uint.bitand_loop.body
    split
    · rename_i hlt
      have hls : s.val.length = LIMBS.val := s.property
      have hla : u.limbs.val.length = LIMBS.val := u.limbs.property
      have hlb : v.limbs.val.length = LIMBS.val := v.limbs.property
      have hkN : k.val < LIMBS.val := by scalar_tac
      unfold limb.bit_and.Limb.bitand
      step*
      subst a_post
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show i1.val ≤ LIMBS.val
        omega
      · show ((s.set k _).val.take i1.val)
          = List.zipWith (· &&& ·) (u.limbs.val.take i1.val) (v.limbs.val.take i1.val)
        simp only [i1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), hv, List.take_add_one, List.take_add_one,
          List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
          Option.toList_some, Option.toList_some, List.zipWith_append (by simp)]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_left]
        rw [← l_post2, ← l1_post2, UScalar.eq_of_val_eq x_post1]
      · show LIMBS.val - i1.val < LIMBS.val - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hiN : k.val = LIMBS.val := by scalar_tac
      have hls : s.val.length = LIMBS.val := s.property
      have hla : u.limbs.val.length = LIMBS.val := u.limbs.property
      have hlb : v.limbs.val.length = LIMBS.val := v.limbs.property
      rw [hiN] at hv
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact hv
  · exact h

theorem wrapping_and_general {LIMBS : Std.Usize} (u v : uint.Uint LIMBS) :
    uint.bit_and.Uint.wrapping_and u v ⦃ r => uintVal r = uintVal u &&& uintVal v ⦄ := by
  unfold uint.bit_and.Uint.wrapping_and uint.bit_and.Uint.bitand
  have h0 : AndInv u v (Array.repeat LIMBS limb.Limb.ZERO, 0#usize) := by
    simp [AndInv]
  apply spec_bind (bitand_loop_spec u v _ _ h0)
  intro l hl
  simp only [WP.spec_ok]
  have hla : u.limbs.val.length = LIMBS.val := u.limbs.property
  have hlb : v.limbs.val.length = LIMBS.val := v.limbs.property
  show limbsVal l.val = _
  rw [hl, limbsVal_zipWith_and _ _ (by omega)]
  rfl

theorem uintVal_lt {LIMBS : Std.Usize} (x : uint.Uint LIMBS) : uintVal x < 2^(64*LIMBS.val) := by
  have hlen : x.limbs.val.length = LIMBS.val := x.limbs.property
  have := limbsVal_lt x.limbs.val
  rw [hlen] at this
  exact this

/--
For all `U256` values `a`, `b`, `a.wrapping_and(&b)` never panics and its value is the bitwise AND of the values, the value of `to_uint(a_bi & b_bi)`.
-/
theorem wrapping_and_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_and_matches_biguint_spec a b := by
  unfold wrapping_and_matches_biguint_spec
  apply spec_mono (wrapping_and_general a b)
  intro r hr
  have ha : uintVal a < 2^256 := uintVal_lt a
  have hb : uintVal b < 2^256 := uintVal_lt b
  rw [hr, Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ hb)]

end Benchmark.Cases.CryptoBigint.Uint
