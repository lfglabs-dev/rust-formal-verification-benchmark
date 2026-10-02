import Benchmark.Cases.Etherparse.Net.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/--
Before `set_dscp`, `dscp()` agrees with `IpDscp::try_new(traffic_class >> 2)`;
afterwards both equal the value that was written.
-/
theorem ipv6_set_dscp (header : net.ipv6_header.Ipv6Header) (dscp : net.ip_dscp.IpDscp)
    (h_dscp : dscp.val ≤ 63) (h_flow : header.flow_label.val ≤ 2^20 - 1) :
    ipv6_set_dscp_spec header dscp := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Etherparse.Net
