import Benchmark.Cases.Ruint.GcdMatrix.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.GcdMatrix

/--
For all `a b : u64`, with `(a, b) := (max(a, b), min(a, b))`, the Lehmer
matrix `Matrix::from_u64(a, b)` (a full 64-bit extended Euclid run) never
panics, and applying it with `apply_u128` to `(a, b)` yields `(c, d)` with
`c >= d`, `c = gcd(a, b)` and `d = 0`.
-/
theorem from_u64_gcd (a b : Std.U64) :
    from_u64_gcd_spec a b := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Ruint.GcdMatrix
