import Benchmark.Cases.Etherparse.Link.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

theorem lsr_toNat_fromBEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromBEBytes l1).toNat = (BitVec.fromBEBytes l2).toNat := by
  subst h; rfl

theorem lsr_toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

theorem lsr_toNat_fromBEBytes_toBEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  simp only [BitVec.fromBEBytes, BitVec.toBEBytes, BitVec.toNat_cast]
  rw [lsr_toNat_fromLEBytes_congr (List.reverse_reverse _), BitVec.fromLEBytes_toLEBytes h,
    BitVec.toNat_cast]

/-- `u16::from_be_bytes(x.to_be_bytes()) == x` in the Aeneas byte-order model. -/
theorem lsr_be_from_to_U16 (n : Std.U16) :
    Std.core.num.U16.from_be_bytes (Std.core.num.U16.to_be_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U16.to_be_bytes n).val = n.bv.toBEBytes := by
    simp [Std.core.num.U16.to_be_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U16.from_be_bytes, UScalar.val, BitVec.toNat_cast]
  rw [lsr_toNat_fromBEBytes_congr hl, lsr_toNat_fromBEBytes_toBEBytes (by simp)]

theorem lsr_list2 {α : Type} (l : List α) (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem lsr_list8 {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a b c d e f g k, l = [a, b, c, d, e, f, g, k] := by
  match l, h with
  | [a, b, c, d, e, f, g, k], _ => exact ⟨a, b, c, d, e, f, g, k, rfl⟩

/-- `u16::from_be_bytes([b[0], b[1]])` where `b = x.to_be_bytes()` is `x`. -/
theorem lsr_be_make (n : Std.U16) (a b : Std.U8)
    (h : (Std.core.num.U16.to_be_bytes n).val = [a, b]) :
    Std.core.num.U16.from_be_bytes (Array.make 2#usize [a, b]) = n := by
  have : (Array.make 2#usize [a, b] : Std.Array Std.U8 2#usize) = Std.core.num.U16.to_be_bytes n :=
    Subtype.ext (by simp [Array.make, h])
  rw [this, lsr_be_from_to_U16]

@[simp] theorem lsr_make_val {α : Type} (n : Std.Usize) (l : List α) (h : l.length = n.val) :
    (Array.make n l h).val = l := rfl

theorem lsr_main (input : link.linux_sll_header.LinuxSllHeader) (v : Std.U16)
    (hpt : link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from
      input.packet_type = ok (core.result.Result.Ok input.packet_type))
    (hv : U16.Insts.CoreConvertFromLinuxSllProtocolType.from input.protocol_type = ok v)
    (hproto : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
      (input.arp_hrd_type, v) = ok (core.result.Result.Ok input.protocol_type)) :
    linux_sll_from_bytes_roundtrip_spec input := by
  obtain ⟨p0, p1, hp⟩ := lsr_list2 (Std.core.num.U16.to_be_bytes input.packet_type).val (by simp)
  obtain ⟨a0, a1, ha⟩ := lsr_list2 (Std.core.num.U16.to_be_bytes input.arp_hrd_type).val (by simp)
  obtain ⟨l0, l1, hl⟩ := lsr_list2
    (Std.core.num.U16.to_be_bytes input.sender_address_valid_length).val (by simp)
  obtain ⟨q0, q1, hq⟩ := lsr_list2 (Std.core.num.U16.to_be_bytes v).val (by simp)
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs⟩ := lsr_list8 input.sender_address.val
    (by simp)
  have hpt' := lsr_be_make _ _ _ hp
  have ha' := lsr_be_make _ _ _ ha
  have hl' := lsr_be_make _ _ _ hl
  have hq' := lsr_be_make _ _ _ hq
  have hsa : (Array.make 8#usize [s0, s1, s2, s3, s4, s5, s6, s7] : Std.Array Std.U8 8#usize) =
      input.sender_address := Subtype.ext (by simp [Array.make, hs])
  unfold linux_sll_from_bytes_roundtrip_spec link.linux_sll_header.LinuxSllHeader.to_bytes
    link.linux_sll_header.LinuxSllHeader.from_bytes
  simp only [U16.Insts.CoreConvertFromLinuxSllPacketType.from, U16.Insts.CoreConvertFromArpHardwareId.from,
    net.arp_hardware_id.ArpHardwareId.Insts.CoreConvertFromU16.from, hv,
    core.num.U16.to_be_bytes, core.num.U16.from_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_u16, rust_primitives.arithmetic.from_be_bytes_u16, bind_tc_ok,
    Array.index_usize, Array.getElem?_Usize_eq, hp, ha, hl, hq, hs]
  simp [hpt', ha', hl', hq', hsa, hpt, hproto, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]

theorem lsr_pt_idem (pv pt : link.linux_sll_packet_type.LinuxSllPacketType) (hpv : pv.val ≤ 7)
    (h : link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from
      pv = ok (core.result.Result.Ok pt)) :
    link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from
      pt = ok (core.result.Result.Ok pt) := by
  unfold link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from at h
  split at h
  all_goals first
    | (exfalso; revert h; simp only [Aeneas.Std.massert]; split_ifs <;> simp)
    | (simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
       unfold link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from
       simp only [link.linux_sll_packet_type.LinuxSllPacketType.HOST, link.linux_sll_packet_type.LinuxSllPacketType.BROADCAST, link.linux_sll_packet_type.LinuxSllPacketType.MULTICAST, link.linux_sll_packet_type.LinuxSllPacketType.OTHERHOST, link.linux_sll_packet_type.LinuxSllPacketType.OUTGOING, link.linux_sll_packet_type.LinuxSllPacketType.LOOPBACK, link.linux_sll_packet_type.LinuxSllPacketType.USER, link.linux_sll_packet_type.LinuxSllPacketType.KERNEL]; rfl)

set_option maxHeartbeats 1000000 in
theorem lsr_nst_left_inv (n w : Std.U16)
    (h : link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from
      n = ok (core.result.Result.Ok w)) : w = n := by
  unfold link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from at h
  split at h
  all_goals first
    | (simp at h; done)
    | (exfalso; revert h; simp only [Aeneas.Std.massert]; split_ifs <;> simp)
    | (simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
       simp only [link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.N802_3, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.AX25, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ALL, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.N802_2, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.SNAP, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.DDCMP, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.WAN_PPP, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PPP_MP, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.LOCALTALK, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CAN, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CANFD, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CANXL, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PPPTALK, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.TR_802_2, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MOBITEX, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CONTROL, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.IRDA, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ECONET, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.HDLC, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ARCNET, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.DSA, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.TRAILER, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PHONET, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.IEEE802154, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CAIF, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.XDSA, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MAP, link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MCTP]; rfl)

/-- Parsing the protocol field back: for a supported ARP hardware id, the `u16`
value of the protocol type produced by `LinuxSllProtocolType::try_from((arp, n))`
is `n`. -/
theorem lsr_proto (arp : net.arp_hardware_id.ArpHardwareId) (n : Std.U16)
    (proto : link.linux_sll_protocol_type.LinuxSllProtocolType)
    (harp : arp.val ∈ [824, 778, 803, 770, 1])
    (h : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
      (arp, n) = ok (core.result.Result.Ok proto)) :
    U16.Insts.CoreConvertFromLinuxSllProtocolType.from proto = ok n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at harp
  rcases harp with ha | ha | ha | ha | ha
  · have : arp = 824#u16 := UScalar.val_eq_imp _ _ (by simp [ha])
    subst this
    have ev : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (824#u16, n) =
        ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.NetlinkProtocolType n)) := rfl
    rw [ev] at h
    simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h; rfl
  · have : arp = 778#u16 := UScalar.val_eq_imp _ _ (by simp [ha])
    subst this
    have ev : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (778#u16, n) =
        ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.GenericRoutingEncapsulationProtocolType n)) := rfl
    rw [ev] at h
    simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h; rfl
  · have : arp = 803#u16 := UScalar.val_eq_imp _ _ (by simp [ha])
    subst this
    have ev : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (803#u16, n) =
        ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.Ignored n)) := rfl
    rw [ev] at h
    simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h; rfl
  · have : arp = 770#u16 := UScalar.val_eq_imp _ _ (by simp [ha])
    subst this
    have ev : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (770#u16, n) =
        ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.Ignored n)) := rfl
    rw [ev] at h
    simp only [RustM.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h; rfl
  · have : arp = 1#u16 := UScalar.val_eq_imp _ _ (by simp [ha])
    subst this
    have ev : link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (1#u16, n) =
        (do
          let r ← link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from n
          match r with
          | core.result.Result.Ok v => ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.LinuxNonstandardEtherType v))
          | core.result.Result.Err _ => ok (core.result.Result.Ok (link.linux_sll_protocol_type.LinuxSllProtocolType.EtherType n))) := rfl
    rw [ev] at h
    rcases hr : link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from
      n with (r | e | _) <;> rw [hr] at h
    · rcases r with v | u
      · simp only [bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        rw [lsr_nst_left_inv n v hr]
        rfl
      · simp only [bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        rfl
    · simp at h
    · simp at h

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
    linux_sll_from_bytes_roundtrip_spec input :=
  lsr_main input protocol_num (lsr_pt_idem _ _ h_packet_type_value h_packet_type)
    (lsr_proto _ _ _ h_arp_hrd_type h_protocol_type) h_protocol_type

end Benchmark.Cases.Etherparse.Link
