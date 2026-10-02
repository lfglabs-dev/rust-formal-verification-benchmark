import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/--
`UnsignedIntValue`'s `PartialEq` ignores the storage width: for all `u8`
values `lhs`, `rhs` and every pair of width variants (`U8`, `U16`, `U32`, `U64`
holding the zero-extended values), `lhs_value.eq(rhs_value)` and
`rhs_value.eq(lhs_value)` never panic and both equal `lhs == rhs`.
-/
theorem unsigned_int_value_eq_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_eq_across_widths_spec lhs rhs := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Lilliput.IntValue
