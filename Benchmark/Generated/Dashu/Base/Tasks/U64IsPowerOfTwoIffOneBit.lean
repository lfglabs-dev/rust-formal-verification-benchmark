import Benchmark.Cases.Dashu.Base.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dashu_base

namespace Benchmark.Cases.Dashu.Base

/--
For every `u64`, dashu's `PowerOfTwo::is_power_of_two` never panics and
returns `true` exactly when the population count `x.count_ones()` is 1.
-/
theorem u64_is_power_of_two_iff_one_bit (x : Std.U64) :
    u64_is_power_of_two_iff_one_bit_spec x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Dashu.Base
