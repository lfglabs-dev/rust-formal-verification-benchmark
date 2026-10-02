import Benchmark.Cases.RevBits.U32.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open rev_bits

namespace Benchmark.Cases.RevBits.U32

/--
For every `u32` value `x`, expanding it into a `[bool; 32]` bit array with
the reference implementation's `to_array` (bit `i` at index `i`) and
packing the array back with `to_u32` (which folds the bits from the last
index down with `out = out << 1 | bit`) never panics and returns `x`.
-/
theorem to_array_to_u32 (x : Std.U32) :
    to_array_to_u32_spec x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.RevBits.U32
