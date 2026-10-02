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

private theorem add_eq (a b : Std.U64) (ha : a.val < 2^64 - 2^32 + 1) (hb : b.val < 2^64 - 2^32 + 1) :
    ∃ v, field.algo.generic.add a b = ok v ∧ v.val = (a.val + b.val) % (2^64 - 2^32 + 1) := by
  have hM := modulus_val
  have ha' := lt_modulus a ha
  have hb' := lt_modulus b hb
  unfold field.algo.generic.add
  simp only [CoreModels.core.num.U64.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u64,
    CoreModels.core.num.U64.overflowing_sub, CoreModels.rust_primitives.arithmetic.overflowing_sub_u64,
    CoreModels.core.num.U32.wrapping_sub, CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    massert, ha', hb', if_true, lift, bind_tc_ok, uoverflowing_sub]
  refine ⟨_, rfl, ?_⟩
  have hw : (field.algo.MODULUS.wrapping_sub b).val = 18446744069414584321 - b.val := by
    rw [wsub_val, hM]; omega
  rw [wsub_val, adj_val, bvsub_val, hw]
  by_cases hc : a.val < 18446744069414584321 - b.val
  · simp only [hc, decide_true, if_true]
    omega
  · simp only [hc, decide_false, if_false, Bool.false_eq_true]
    omega

/--
The branch-free Goldilocks addition `algo::add` equals `(a + b) mod MODULUS` on reduced inputs.
-/
theorem add_matches_naive (a b : Std.U64)
    (h_assume_a : a.val < 2^64 - 2^32 + 1)
    (h_assume_b : b.val < 2^64 - 2^32 + 1) :
    add_matches_naive_spec a b := by

  unfold add_matches_naive_spec
  obtain ⟨v, hv, hval⟩ := add_eq a b h_assume_a h_assume_b
  rw [hv, WP.spec_ok]
  exact hval

end Benchmark.Cases.Goldilocks.Field
