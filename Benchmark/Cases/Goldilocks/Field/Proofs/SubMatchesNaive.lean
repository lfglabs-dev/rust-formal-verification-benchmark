import Benchmark.Cases.Goldilocks.Field.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt

namespace Benchmark.Cases.Goldilocks.Field

private theorem modulus_val : field.algo.MODULUS.val = 18446744069414584321 := by
  unfold field.algo.MODULUS; rfl

private theorem lt_modulus (a : Std.U64) (ha : a.val < 2^64 - 2^32 + 1) : a < field.algo.MODULUS := by
  change a.val < field.algo.MODULUS.val
  rw [modulus_val]; omega

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

private theorem sub_eq (a b : Std.U64) (ha : a.val < 2^64 - 2^32 + 1) (hb : b.val < 2^64 - 2^32 + 1) :
    ∃ v, field.algo.generic.sub a b = ok v ∧
      v.val = (a.val + (2^64 - 2^32 + 1 - b.val)) % (2^64 - 2^32 + 1) := by
  have ha' := lt_modulus a ha
  have hb' := lt_modulus b hb
  unfold field.algo.generic.sub
  simp only [CoreModels.core.num.U64.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u64,
    CoreModels.core.num.U64.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u64,
    CoreModels.core.num.U32.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    massert, ha', hb', if_true, lift, bind_tc_ok, uoverflowing_sub]
  refine ⟨_, rfl, ?_⟩
  rw [wsub_val, adj_val, bvsub_val]
  by_cases hc : a.val < b.val
  · simp only [hc, decide_true, if_true]
    omega
  · simp only [hc, decide_false, if_false, Bool.false_eq_true]
    omega

/--
The branch-free Goldilocks subtraction `algo::sub` equals `(a - b).rem_euclid(MODULUS)` on reduced inputs.
-/
theorem sub_matches_naive (a b : Std.U64)
    (h_assume_a : a.val < 2^64 - 2^32 + 1)
    (h_assume_b : b.val < 2^64 - 2^32 + 1) :
    sub_matches_naive_spec a b := by

  unfold sub_matches_naive_spec
  obtain ⟨v, hv, hval⟩ := sub_eq a b h_assume_a h_assume_b
  rw [hv, WP.spec_ok, hval]
  push_cast
  omega

end Benchmark.Cases.Goldilocks.Field
