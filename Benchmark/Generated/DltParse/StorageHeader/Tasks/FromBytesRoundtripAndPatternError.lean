import Benchmark.Cases.DltParse.StorageHeader.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dlt_parse

namespace Benchmark.Cases.DltParse.StorageHeader

/--
For every storage header `header` and 4-byte pattern `bad_pattern` different
from `StorageHeader::PATTERN_AT_START`, decoding `header.to_bytes()` succeeds
with `header` itself, and decoding the same buffer with its first four bytes
overwritten by `bad_pattern` fails with the
`StorageHeaderStartPatternError { actual_pattern: bad_pattern }`.
-/
theorem from_bytes_roundtrip_and_pattern_error (header : storage.storage_header.StorageHeader)
    (bad_pattern : Array Std.U8 4#usize)
    (h_bad : bad_pattern.val ≠ storage.storage_header.StorageHeader.PATTERN_AT_START.val) :
    storage_header_from_bytes_spec header bad_pattern := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.DltParse.StorageHeader
