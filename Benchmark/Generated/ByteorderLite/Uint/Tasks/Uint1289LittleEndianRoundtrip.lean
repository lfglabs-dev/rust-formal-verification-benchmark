import Benchmark.Cases.ByteorderLite.Uint.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/--
Writing any `n < 2^72` with `LittleEndian::write_uint128(&mut buf, n, 9)` into a zeroed 16-byte buffer and reading the first 9 bytes back with `LittleEndian::read_uint128(&buf[..9], 9)` never panics and returns the same value.
-/
theorem uint128_9_little_endian_roundtrip (n : Std.U128) (h_n : n.val < 2^72) :
    uint128_9_little_endian_roundtrip_spec n := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ByteorderLite.Uint
