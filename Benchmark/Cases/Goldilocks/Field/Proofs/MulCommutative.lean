import Benchmark.Cases.Goldilocks.Field.Specs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

private theorem modulus_val : field.algo.MODULUS.val = 18446744069414584321 := by
  unfold field.algo.MODULUS; rfl

private theorem shr128_64 (x : Std.U128) : x >>> 64#i32 = ok ⟨x.bv.ushiftRight 64⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  rfl

private theorem shl128_64 (x : Std.U128) : x <<< 64#i32 = ok ⟨x.bv.shiftLeft 64⟩ := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rfl

private theorem shr64_32 (x : Std.U64) : x >>> 32#i32 = ok ⟨x.bv.ushiftRight 32⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  rfl

private theorem shl64_32 (x : Std.U64) : x <<< 32#i32 = ok ⟨x.bv.shiftLeft 32⟩ := by
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rfl

private theorem ushr_val {ty} (x : UScalar ty) (k : Nat) :
    (⟨x.bv.ushiftRight k⟩ : UScalar ty).val = x.val / 2^k := by
  show (x.bv >>> k).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl

private theorem shl_val {ty} (x : UScalar ty) (k : Nat) :
    (⟨x.bv.shiftLeft k⟩ : UScalar ty).val = x.val * 2^k % 2^ty.numBits := by
  show (x.bv <<< k).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl

private theorem bvsub_val (x y : Std.U64) :
    ((x.bv - y.bv)#uscalar : Std.U64).val = (x.val + (2^64 - y.val)) % 2^64 := by
  have h1 : ((x.bv - y.bv)#uscalar : Std.U64).val = (x.bv - y.bv).toNat := rfl
  rw [h1, BitVec.toNat_sub, Nat.add_comm]
  rfl

private theorem adj_val (c : Bool) :
    (UScalar.cast UScalarTy.U64 (U32.wrapping_sub 0#u32 (UScalar.cast_fromBool UScalarTy.U32 c))).val =
      if c then 2^32 - 1 else 0 := by
  cases c <;> rfl

private theorem wsub_val (x y : Std.U64) : (x.wrapping_sub y).val = (x.val + (2^64 - y.val)) % 2^64 := by
  rw [U64.wrapping_sub_val_eq]; simp only [UScalar.size, UScalarTy.numBits]

private theorem oadd_val (x y : Std.U64) :
    (UScalar.overflowing_add x y).1.val = (x.val + y.val) % 2^64 ∧
    (UScalar.overflowing_add x y).2 = decide (2^64 ≤ x.val + y.val) := by
  have h := UScalar.overflowing_add_eq x y
  have hx := x.hBounds
  have hy := y.hBounds
  simp only [UScalar.max, UScalar.size, UScalarTy.numBits] at h hx hy
  split_ifs at h with hc
  · obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, by rw [h2]; simp; omega⟩
  · obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, by rw [h2]; simp; omega⟩

private theorem mont_core (x0 x1 e a b r : Nat) (hx0 : x0 < 2^64) (hx1 : x1 < 2^64 - 2^32 + 1)
    (he : e = if 2^64 ≤ x0 + x0 * 2^32 % 2^64 then 1 else 0)
    (ha : a = (x0 + x0 * 2^32 % 2^64) % 2^64)
    (hb : b = ((a + (2^64 - a / 2^32)) % 2^64 + (2^64 - e)) % 2^64)
    (hr : r = ((x1 + (2^64 - b)) % 2^64 + (2^64 - if x1 < b then 2^32 - 1 else 0)) % 2^64) :
    r < 2^64 - 2^32 + 1 ∧ r * 2^64 % (2^64 - 2^32 + 1) = (x1 * 2^64 + x0) % (2^64 - 2^32 + 1) := by
  obtain ⟨hh, l, hl, rfl⟩ : ∃ hh l, l < 2^32 ∧ x0 = hh * 2^32 + l := ⟨x0 / 2^32, x0 % 2^32, by omega, by omega⟩
  have hhh : hh < 2^32 := by omega
  have hs : (hh * 2^32 + l) * 2^32 % 2^64 = l * 2^32 := by omega
  rw [hs] at he ha
  have hsum : hh * 2^32 + l + l * 2^32 = a + e * 2^64 := by
    split_ifs at he <;> subst he <;> omega
  obtain ⟨ah, al, hal, rfl⟩ : ∃ ah al, al < 2^32 ∧ a = ah * 2^32 + al := ⟨a / 2^32, a % 2^32, by omega, by omega⟩
  have hahb : ah < 2^32 := by omega
  have hal_eq : al = l := by omega
  subst hal_eq
  have he1 : e ≤ 1 := by split_ifs at he <;> omega
  have hdiv : (ah * 2^32 + al) / 2^32 = ah := by omega
  rw [hdiv] at hb
  have hbsum : b + ah + e = ah * 2^32 + al := by omega
  have hkey : b * 2^64 + (hh * 2^32 + al) = (ah * 2^32 + al) * 18446744069414584321 := by
    zify at hbsum hsum ⊢
    linear_combination (2^64 : ℤ) * hbsum + hsum
  have hbM : b < 2^64 - 2^32 + 1 := by omega
  have hM : (2^64 - 2^32 + 1 : Nat) = 18446744069414584321 := by norm_num
  rw [hM] at hx1 hbM ⊢
  by_cases hc : x1 < b
  · rw [if_pos hc] at hr
    have hrsum : r + b = x1 + 18446744069414584321 := by omega
    have hsum2 : x1 * 2^64 + (hh * 2^32 + al) + 2^64 * 18446744069414584321 =
        r * 2^64 + (ah * 2^32 + al) * 18446744069414584321 := by
      zify at hrsum hkey ⊢
      linear_combination (-2^64 : ℤ) * hrsum + hkey
    refine ⟨by omega, ?_⟩
    rw [← Nat.add_mul_mod_self_right (x1 * 2^64 + (hh * 2^32 + al)) (2^64) 18446744069414584321, hsum2,
      Nat.add_mul_mod_self_right]
  · rw [if_neg hc] at hr
    have hrsum : r + b = x1 := by omega
    have hsum2 : x1 * 2^64 + (hh * 2^32 + al) = r * 2^64 + (ah * 2^32 + al) * 18446744069414584321 := by
      zify at hrsum hkey ⊢
      linear_combination (-2^64 : ℤ) * hrsum + hkey
    refine ⟨by omega, ?_⟩
    rw [hsum2, Nat.add_mul_mod_self_right]

private theorem mont_reduce_eq (x : Std.U128) (hx : x.val < (2^64 - 2^32 + 1) * 2^64) :
    ∃ v, field.algo.generic.mont_reduce_128 x = ok v ∧
      v.val < 2^64 - 2^32 + 1 ∧ (v.val * 2^64) % (2^64 - 2^32 + 1) = x.val % (2^64 - 2^32 + 1) := by
  have hM := modulus_val
  have hlt : x < (⟨(UScalar.cast UScalarTy.U128 field.algo.MODULUS).bv.shiftLeft 64⟩ : Std.U128) := by
    change x.val < (⟨(UScalar.cast UScalarTy.U128 field.algo.MODULUS).bv.shiftLeft 64⟩ : Std.U128).val
    rw [shl_val, UScalar.cast_val_eq, hM]
    simp only [UScalarTy.numBits]
    omega
  unfold field.algo.generic.mont_reduce_128
  simp only [lift, bind_tc_ok, shl128_64, shr128_64, shl64_32, shr64_32, massert, hlt, if_true,
    CoreModels.core.num.U64.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u64,
    CoreModels.core.num.U64.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u64,
    CoreModels.core.num.U64.overflowing_add, CoreModels.rust_primitives.arithmetic.overflowing_add_u64,
    CoreModels.core.num.U32.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    uoverflowing_sub]
  generalize hp : (UScalar.cast UScalarTy.U64 x).overflowing_add
      (⟨(U64.bv (UScalar.cast UScalarTy.U64 x)).shiftLeft 32⟩ : Std.U64) = p
  obtain ⟨a, e⟩ := p
  have ho := oadd_val (UScalar.cast UScalarTy.U64 x) (⟨(U64.bv (UScalar.cast UScalarTy.U64 x)).shiftLeft 32⟩ : Std.U64)
  rw [hp] at ho
  obtain ⟨ha, he⟩ := ho
  dsimp only at ha he ⊢
  refine ⟨_, rfl, ?_⟩
  have hx0 : (UScalar.cast UScalarTy.U64 x).val = x.val % 2^64 := by
    rw [UScalar.cast_val_eq]; rfl
  have hx1 : (UScalar.cast UScalarTy.U64 (⟨x.bv.ushiftRight 64⟩ : Std.U128)).val = x.val / 2^64 := by
    rw [UScalar.cast_val_eq, ushr_val]; simp only [UScalarTy.numBits]; omega
  have hs : (⟨(U64.bv (UScalar.cast UScalarTy.U64 x)).shiftLeft 32⟩ : Std.U64).val = x.val % 2^64 * 2^32 % 2^64 := by
    rw [shl_val, hx0]; rfl
  have hb : (U64.wrapping_sub (U64.wrapping_sub a ⟨a.bv.ushiftRight 32⟩) (UScalar.cast_fromBool UScalarTy.U64 e)).val =
      (((a.val + (2^64 - a.val / 2^32)) % 2^64) + (2^64 - e.toNat)) % 2^64 := by
    rw [wsub_val, wsub_val, ushr_val, UScalar.cast_fromBool_val_eq]
  rw [hx0, hs] at ha he
  rw [wsub_val, adj_val, bvsub_val, hx1, hb]
  simp only [decide_eq_true_eq]
  have hxs : x.val = x.val / 2^64 * 2^64 + x.val % 2^64 := by omega
  have het : e.toNat = if 2^64 ≤ x.val % 2^64 + x.val % 2^64 * 2^32 % 2^64 then 1 else 0 := by
    rw [he]
    split_ifs with h
    · simp only [h, decide_true, Bool.toNat_true]
    · simp only [h, decide_false, Bool.toNat_false]
  obtain ⟨h1, h2⟩ := mont_core (x.val % 2^64) (x.val / 2^64) e.toNat a.val _ _ (by omega) (by omega)
    het ha rfl rfl
  refine ⟨h1, ?_⟩
  rw [h2, ← hxs]

private theorem mont_mul_eq (a b : Std.U64) (h : a.val * b.val < (2^64 - 2^32 + 1) * 2^64) :
    ∃ v, field.algo.generic.mont_mul a b = ok v ∧
      v.val < 2^64 - 2^32 + 1 ∧ (v.val * 2^64) % (2^64 - 2^32 + 1) = (a.val * b.val) % (2^64 - 2^32 + 1) := by
  unfold field.algo.generic.mont_mul
  simp only [lift, bind_tc_ok]
  have hmax : (UScalar.cast UScalarTy.U128 a).val * (UScalar.cast UScalarTy.U128 b).val ≤ UScalar.max UScalarTy.U128 := by
    rw [U64.cast_U128_val_eq, U64.cast_U128_val_eq]
    simp only [UScalar.max, UScalarTy.numBits]
    omega
  obtain ⟨p, hp, hpv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [U64.cast_U128_val_eq, U64.cast_U128_val_eq] at hpv
  rw [hp, bind_tc_ok]
  obtain ⟨v, hv, h1, h2⟩ := mont_reduce_eq p (by rw [hpv]; exact h)
  exact ⟨v, hv, h1, by rw [h2, hpv]⟩

private theorem to_zmod (r x : ℕ) (h : r * 2^64 % (2^64 - 2^32 + 1) = x % (2^64 - 2^32 + 1)) :
    (r : ZMod 18446744069414584321) * 2^64 = (x : ZMod 18446744069414584321) := by
  have h' : (r * 2^64) % 18446744069414584321 = x % 18446744069414584321 := by
    simpa using h
  have := (ZMod.natCast_eq_natCast_iff' (r * 2^64) x 18446744069414584321).mpr h'
  push_cast at this
  exact this

private theorem eq_of_zmod (r s k : ℕ) (hr : r < 2^64 - 2^32 + 1) (hs : s < 2^64 - 2^32 + 1)
    (h : (r : ZMod 18446744069414584321) * 2^k = (s : ZMod 18446744069414584321) * 2^k) : r = s := by
  have hcop : Nat.Coprime 2 18446744069414584321 := by
    rw [Nat.coprime_two_left]; decide
  have hu : IsUnit ((2 : ZMod 18446744069414584321) ^ k) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    simpa using this.pow k
  have h2 := hu.mul_left_inj.mp h
  have h3 := (ZMod.natCast_eq_natCast_iff' r s 18446744069414584321).mp h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
  exact h3

/--
Montgomery multiplication of reduced elements never panics and is commutative.
-/
theorem mul_commutative (a b : field.Field)
    (h_a : a.val < 2^64 - 2^32 + 1)
    (h_b : b.val < 2^64 - 2^32 + 1) :
    mul_commutative_spec a b := by

  unfold mul_commutative_spec field.Field.Insts.CoreOpsArithMulFieldField.mul
  have hb64 : b.val < 2^64 := by omega
  have ha64 : a.val < 2^64 := by omega
  obtain ⟨v1, hv1, h1, h1'⟩ := mont_mul_eq a b (Nat.mul_lt_mul'' h_a hb64)
  obtain ⟨v2, hv2, h2, h2'⟩ := mont_mul_eq b a (Nat.mul_lt_mul'' h_b ha64)
  simp only [hv1, hv2, bind_tc_ok, WP.spec_ok]
  rw [UScalar.eq_equiv]
  apply eq_of_zmod _ _ 64 h1 h2
  rw [to_zmod _ _ h1', to_zmod _ _ h2']
  push_cast
  ring

end Benchmark.Cases.Goldilocks.Field
