import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

def uieq_val : value.int.unsigned.UnsignedIntValue → Nat
  | .U8 v => v.val
  | .U16 v => v.val
  | .U32 v => v.val
  | .U64 v => v.val

theorem uieq_val_of_mem {x : Std.U8} {v : value.int.unsigned.UnsignedIntValue}
    (h : v ∈ unsignedValues x) : uieq_val v = x.val := by
  simp only [unsignedValues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact U8.cast_U16_val_eq x
  · exact U8.cast_U32_val_eq x
  · exact U8.cast_U64_val_eq x

theorem uieq_eq_eq (a b : value.int.unsigned.UnsignedIntValue) :
    value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq a b =
      ok (decide (uieq_val a = uieq_val b)) := by
  cases a <;> cases b <;>
    simp [value.int.unsigned.UnsignedIntValue.Insts.CoreCmpPartialEqUnsignedIntValue.eq, uieq_val,
      UScalar.eq_equiv]

theorem uieq_u8_eq (x y : Std.U8) :
    core.U8.Insts.CoreCmpPartialEqU8.eq x y = ok (decide (x.val = y.val)) := by
  show ok (x == y) = _
  congr 1
  by_cases h : x = y
  · subst h; simp
  · have h' : x.val ≠ y.val := fun e => h (UScalar.eq_imp _ _ e)
    simp [h, h']

/--
`UnsignedIntValue`'s `PartialEq` ignores the storage width: for all `u8`
values `lhs`, `rhs` and every pair of width variants (`U8`, `U16`, `U32`, `U64`
holding the zero-extended values), `lhs_value.eq(rhs_value)` and
`rhs_value.eq(lhs_value)` never panic and both equal `lhs == rhs`.
-/
theorem unsigned_int_value_eq_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_eq_across_widths_spec lhs rhs := by
  intro lv hlv rv hrv
  rw [uieq_u8_eq, uieq_eq_eq, uieq_eq_eq, uieq_val_of_mem hlv, uieq_val_of_mem hrv]
  rcases em (lhs.val = rhs.val) with h | h
  · simp [h]
  · simp [h, Ne.symm h]

end Benchmark.Cases.Lilliput.IntValue
