import Benchmark.Cases.Etherparse.Link.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

/--
Serialising a Linux cooked-capture (SLL) header with `to_bytes` and parsing the
16 bytes back with `from_bytes` never panics and returns `Ok` of the original
header, for every header built like the test generator `linux_sll_any()`.
-/
theorem linux_sll_from_bytes_roundtrip (input : link.linux_sll_header.LinuxSllHeader)
    (packet_type_value protocol_num : Std.U16)
    (h_packet_type_value : packet_type_value.val ≤ 7)
    (h_packet_type :
      link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from
        packet_type_value = ok (core.result.Result.Ok input.packet_type))
    (h_arp_hrd_type : input.arp_hrd_type.val ∈ [824, 778, 803, 770, 1])
    (h_protocol_type :
      link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
        (input.arp_hrd_type, protocol_num) = ok (core.result.Result.Ok input.protocol_type)) :
    linux_sll_from_bytes_roundtrip_spec input := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Etherparse.Link
