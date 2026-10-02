import Benchmark.Cases.Fastdivide.Divider.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open fastdivide

namespace Benchmark.Cases.Fastdivide.Divider

/--
For every divisor `d` and dividend `n` drawn from the property-test
strategies, precomputing `DividerU64::divide_by(d)` and dividing `n` with it
never panics and returns exactly `n / d`.
-/
theorem divide_matches_native_division (n d : Std.U64)
    (h_n : n.val < 2^64 - 1)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 2^64 - 1) :
    divide_matches_native_division_spec n d := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Fastdivide.Divider
