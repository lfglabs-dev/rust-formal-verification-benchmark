import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

def uicmp_val : value.int.unsigned.UnsignedIntValue → Nat
  | .U8 v => v.val
  | .U16 v => v.val
  | .U32 v => v.val
  | .U64 v => v.val

theorem uicmp_val_of_mem {x : Std.U8} {v : value.int.unsigned.UnsignedIntValue}
    (h : v ∈ unsignedValues x) : uicmp_val v = x.val := by
  simp only [unsignedValues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact U8.cast_U16_val_eq x
  · exact U8.cast_U32_val_eq x
  · exact U8.cast_U64_val_eq x

def uicmp_ordOfNat (x y : Nat) : core.cmp.Ordering :=
  match compare x y with
  | .lt => .Less
  | .eq => .Equal
  | .gt => .Greater

theorem uicmp_u8_cmp (x y : Std.U8) :
    core.U8.Insts.CoreCmpOrd.cmp x y = ok (uicmp_ordOfNat x.val y.val) := rfl

theorem uicmp_u64_cmp (x y : Std.U64) :
    core.U64.Insts.CoreCmpOrd.cmp x y = ok (uicmp_ordOfNat x.val y.val) := rfl

theorem uicmp_cmp_eq (a b : value.int.unsigned.UnsignedIntValue) :
    value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp a b =
      ok (uicmp_ordOfNat (uicmp_val a) (uicmp_val b)) := by
  cases a <;> cases b <;>
    simp [value.int.unsigned.UnsignedIntValue.Insts.CoreCmpOrd.cmp,
      value.int.unsigned.UnsignedIntValue.canonicalized, uicmp_val, uicmp_u64_cmp]

theorem uicmp_ordOfNat_reverse (x y : Nat) :
    core.cmp.Ordering.reverse (uicmp_ordOfNat x y) = ok (uicmp_ordOfNat y x) := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 : compare x y = .lt := Nat.compare_eq_lt.mpr h
    have h2 : compare y x = .gt := Nat.compare_eq_gt.mpr h
    simp [uicmp_ordOfNat, h1, h2, core.cmp.Ordering.reverse]
  · subst h
    simp [uicmp_ordOfNat, core.cmp.Ordering.reverse]
  · have h1 : compare x y = .gt := Nat.compare_eq_gt.mpr h
    have h2 : compare y x = .lt := Nat.compare_eq_lt.mpr h
    simp [uicmp_ordOfNat, h1, h2, core.cmp.Ordering.reverse]

/--
`UnsignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `u8` values `lhs`, `rhs` and every pair of width
variants (`U8`, `U16`, `U32`, `U64` holding the zero-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`.
-/
theorem unsigned_int_value_cmp_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_cmp_across_widths_spec lhs rhs := by
  intro lv hlv rv hrv
  rw [uicmp_u8_cmp, uicmp_cmp_eq, uicmp_cmp_eq, uicmp_val_of_mem hlv, uicmp_val_of_mem hrv]
  simp [uicmp_ordOfNat_reverse]

end Benchmark.Cases.Lilliput.IntValue
