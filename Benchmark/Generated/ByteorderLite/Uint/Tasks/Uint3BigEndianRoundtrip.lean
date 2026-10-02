import Benchmark.Cases.ByteorderLite.Uint.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/--
Writing any `n < 2^24` with `BigEndian::write_uint(&mut buf, n, 3)` into a zeroed 16-byte buffer and reading the first 3 bytes back with `BigEndian::read_uint(&buf[..3], 3)` never panics and returns the same value.
-/
theorem uint_3_big_endian_roundtrip (n : Std.U64) (h_n : n.val < 2^24) :
    uint_3_big_endian_roundtrip_spec n := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ByteorderLite.Uint
