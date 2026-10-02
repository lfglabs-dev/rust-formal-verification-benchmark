import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::to_high_low` never panics and returns `(raw / 2^32, raw % 2^32)`, the
value of `((raw >> u32::BITS) as u32, raw as u32)`.
-/
theorem to_high_low_roundtrip (ft : file_time.FileTime) :
    to_high_low_roundtrip_spec ft := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
