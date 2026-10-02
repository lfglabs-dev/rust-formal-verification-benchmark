import Benchmark.Cases.Etherparse.Link.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

/--
Serialising an Ethernet II header to its 14 wire bytes and parsing them back
never panics and yields the original header.
-/
theorem ethernet2_from_bytes_roundtrip (input : link.ethernet2_header.Ethernet2Header) :
    ethernet2_from_bytes_roundtrip_spec input := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Etherparse.Link
