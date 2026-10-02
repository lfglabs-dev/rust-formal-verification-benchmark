import Benchmark.Cases.Etherparse.Net.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/--
`Ipv4Header::payload_len` equals `total_len - 20 - options.len() as u16` when
the total length covers the header, and returns `LenError` for every smaller
`total_len`.
-/
theorem ipv4_payload_len (header : net.ipv4_header.Ipv4Header)
    (h_dscp : header.dscp.val ≤ 63)
    (h_frag : header.fragment_offset.val < 2^13)
    (h_options_len : header.options.len.val ≤ 36 ∧ header.options.len.val % 4 = 0)
    (h_total_lo : 20 + header.options.len.val ≤ header.total_len.val)
    (h_total_hi : header.total_len.val < 2^16 - 1) :
    ipv4_payload_len_spec header := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Etherparse.Net
