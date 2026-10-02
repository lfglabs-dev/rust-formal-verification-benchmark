import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/--
`FileTime::to_unix_time_nanos` never panics (no i128 overflow) and its result lies in
`-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500`.
-/
theorem to_unix_time_nanos_roundtrip (ft : file_time.FileTime) :
    to_unix_time_nanos_roundtrip_spec ft := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.NtTime.FileTime
