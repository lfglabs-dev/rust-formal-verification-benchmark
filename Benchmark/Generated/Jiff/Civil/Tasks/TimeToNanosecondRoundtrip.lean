import Benchmark.Cases.Jiff.Civil.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open jiff_core

namespace Benchmark.Cases.Jiff.Civil

/--
Converting a valid civil `Time` to its nanosecond of the day
(`Time::to_nanosecond`) and back (`TimeNanosecond::to_time`, a chain of
unsigned divisions/remainders with early exits on zero remainders) never
panics and returns a time equal to the original one.
-/
theorem time_to_nanosecond_roundtrip (t : civil.time.Time)
    (h_hour : 0 ≤ t.hour.val ∧ t.hour.val ≤ 23)
    (h_minute : 0 ≤ t.minute.val ∧ t.minute.val ≤ 59)
    (h_second : 0 ≤ t.second.val ∧ t.second.val ≤ 59)
    (h_subsec : 0 ≤ t.subsec_nanosecond.val ∧ t.subsec_nanosecond.val ≤ 999999999) :
    time_to_nanosecond_roundtrip_spec t := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Jiff.Civil
