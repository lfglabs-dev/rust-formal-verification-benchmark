import Benchmark.Cases.Lilliput.IntValue.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open lilliput_core

namespace Benchmark.Cases.Lilliput.IntValue

/--
`SignedIntValue`'s `Ord` agrees with the integer order regardless of the
storage width: for all `i8` values `lhs`, `rhs` and every pair of width
variants (`I8`, `I16`, `I32`, `I64` holding the sign-extended values),
`lhs_value.cmp(rhs_value)` equals `lhs.cmp(&rhs)` and
`rhs_value.cmp(lhs_value)` equals `lhs.cmp(&rhs).reverse()`.
-/
theorem signed_int_value_cmp_across_widths (lhs rhs : Std.I8) :
    signed_int_value_cmp_across_widths_spec lhs rhs := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Lilliput.IntValue
