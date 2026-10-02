import Benchmark.Cases.Crc32fast.Baseline.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crc32fast

namespace Benchmark.Cases.Crc32fast.Baseline

/--
For every initial CRC value `crc` and every byte vector `bytes`, the
slicing-by-16 implementation `update_fast_16(crc, &bytes)` and the
byte-at-a-time implementation `update_slow(crc, &bytes)` both run without
panicking and return the same CRC-32.
-/
theorem fast_16_is_the_same_as_slow (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) :
    fast_16_is_the_same_as_slow_spec crc bytes := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Crc32fast.Baseline
