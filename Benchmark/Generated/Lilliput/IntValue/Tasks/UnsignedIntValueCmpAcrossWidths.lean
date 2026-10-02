import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/--
`UnsignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `u8` values `lhs`, `rhs` and every pair of width
variants (`U8`, `U16`, `U32`, `U64` holding the zero-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`.
-/
theorem unsigned_int_value_cmp_across_widths (lhs rhs : Std.U8) :
    unsigned_int_value_cmp_across_widths_spec lhs rhs := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Lilliput.IntValue
