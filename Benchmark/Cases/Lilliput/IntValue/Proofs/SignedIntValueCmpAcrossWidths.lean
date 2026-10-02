import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

def sicmp_val : value.int.signed.SignedIntValue → Int
  | .I8 v => v.val
  | .I16 v => v.val
  | .I32 v => v.val
  | .I64 v => v.val

theorem sicmp_val_of_mem {x : Std.I8} {v : value.int.signed.SignedIntValue}
    (h : v ∈ signedValues x) : sicmp_val v = x.val := by
  simp only [signedValues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  · exact IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  · exact IScalar.val_mod_pow_greater_numBits _ _ (by decide)

theorem sicmp_cast64 {ty : IScalarTy} (v : IScalar ty) (h : ty.numBits ≤ IScalarTy.I64.numBits) :
    (IScalar.cast .I64 v).val = v.val := IScalar.val_mod_pow_greater_numBits _ _ h

def sicmp_ordOfInt (x y : Int) : core.cmp.Ordering :=
  match compare x y with
  | .lt => .Less
  | .eq => .Equal
  | .gt => .Greater

theorem sicmp_i8_cmp (x y : Std.I8) :
    core.I8.Insts.CoreCmpOrd.cmp x y = ok (sicmp_ordOfInt x.val y.val) := rfl

theorem sicmp_i64_cmp (x y : Std.I64) :
    core.I64.Insts.CoreCmpOrd.cmp x y = ok (sicmp_ordOfInt x.val y.val) := rfl

theorem sicmp_cmp_eq (a b : value.int.signed.SignedIntValue) :
    value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp a b =
      ok (sicmp_ordOfInt (sicmp_val a) (sicmp_val b)) := by
  cases a <;> cases b <;>
    simp [value.int.signed.SignedIntValue.Insts.CoreCmpOrd.cmp,
      value.int.signed.SignedIntValue.canonicalized, sicmp_val, sicmp_i64_cmp,
      sicmp_cast64 _ (by decide : IScalarTy.I8.numBits ≤ IScalarTy.I64.numBits),
      sicmp_cast64 _ (by decide : IScalarTy.I16.numBits ≤ IScalarTy.I64.numBits),
      sicmp_cast64 _ (by decide : IScalarTy.I32.numBits ≤ IScalarTy.I64.numBits)]

theorem sicmp_ordOfInt_reverse (x y : Int) :
    core.cmp.Ordering.reverse (sicmp_ordOfInt x y) = ok (sicmp_ordOfInt y x) := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 : compare x y = .lt := Int.compare_eq_lt.mpr h
    have h2 : compare y x = .gt := Int.compare_eq_gt.mpr h
    simp [sicmp_ordOfInt, h1, h2, core.cmp.Ordering.reverse]
  · subst h
    simp [sicmp_ordOfInt, core.cmp.Ordering.reverse]
  · have h1 : compare x y = .gt := Int.compare_eq_gt.mpr h
    have h2 : compare y x = .lt := Int.compare_eq_lt.mpr h
    simp [sicmp_ordOfInt, h1, h2, core.cmp.Ordering.reverse]

/--
`SignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `i8` values `lhs`, `rhs` and every pair of width
variants (`I8`, `I16`, `I32`, `I64` holding the sign-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`.
-/
theorem signed_int_value_cmp_across_widths (lhs rhs : Std.I8) :
    signed_int_value_cmp_across_widths_spec lhs rhs := by
  intro lv hlv rv hrv
  rw [sicmp_i8_cmp, sicmp_cmp_eq, sicmp_cmp_eq, sicmp_val_of_mem hlv, sicmp_val_of_mem hrv]
  simp [sicmp_ordOfInt_reverse]

end Benchmark.Cases.Lilliput.IntValue
