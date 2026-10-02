import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::to_le_bytes` never panics and returns the little-endian base-256 digits of
the raw tick count (the value of `ft.to_raw().to_le_bytes()`).
-/
theorem to_le_bytes_roundtrip (ft : file_time.FileTime) :
    to_le_bytes_roundtrip_spec ft := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
