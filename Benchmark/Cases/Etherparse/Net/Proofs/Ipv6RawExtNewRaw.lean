import Benchmark.Cases.Etherparse.Net.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

set_option linter.unusedSimpArgs false

theorem clone_u8_mapM (l : List Std.U8) :
    List.mapM core.U8.Insts.CoreCloneClone.clone l = ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, ih, bind_tc_ok]
    rfl

theorem copy_from_slice_u8 (s src : Slice Std.U8) (h : s.length = src.length) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s src = ok src := by
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  rw [if_pos h]
  split
  · rename_i cloned hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc; rfl
  · rename_i e hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc
  · rename_i hc
    simp only [core.U8.Insts.CoreMarkerCopy, core.U8.Insts.CoreCloneClone] at hc
    rw [clone_u8_mapM] at hc
    cases hc

theorem setSlice!_eq_append {α : Type} (s l : List α) (i : Nat) (h : i + l.length ≤ s.length) :
    s.setSlice! i l = s.take i ++ l ++ s.drop (i + l.length) := by
  simp only [List.setSlice!]
  have hmin : min l.length (s.length - i) = l.length := by omega
  rw [hmin, List.take_of_length_le (le_refl _)]

theorem replicate_setSlice_prefix {α : Type} (x : α) (l : List α) (k : Nat) (h : l.length ≤ k) :
    (List.replicate k x).setSlice! 0 l = l ++ List.replicate (k - l.length) x := by
  rw [setSlice!_eq_append _ _ _ (by simp; omega)]
  simp [List.take_replicate, List.drop_replicate]

theorem slice_length_eq {α : Type} (s : Slice α) :
    rust_primitives.slice.slice_length s = ok (Slice.len s) := by
  unfold rust_primitives.slice.slice_length
  rfl

/-- `new_raw` on a slice shorter than 6 bytes is `TooSmall` of that length. -/
theorem new_raw_too_small (next : net.ip_number_impl.IpNumber) (s : Slice Std.U8)
    (h : s.length < 6) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw next s
    ⦃ r => r = core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooSmall (Slice.len s)) ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw
  simp only [core.slice.Slice.len, slice_length_eq, bind_tc_ok]
  have hlt : Slice.len s < net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN := by
    unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN
    rw [UScalar.lt_equiv, Slice.len_val]
    change s.length < 6
    exact h
  rw [if_pos hlt, spec_ok]

/-- `new_raw` on a slice longer than 2046 bytes (and at least 6) is `TooBig`. -/
theorem new_raw_too_big (next : net.ip_number_impl.IpNumber) (s : Slice Std.U8)
    (hlo : 6 ≤ s.length) (hhi : 2046 < s.length) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw next s
    ⦃ r => r = core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooBig (Slice.len s)) ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_PAYLOAD_LEN
  simp only [core.slice.Slice.len, slice_length_eq, bind_tc_ok]
  have hnot : ¬ Slice.len s < net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN := by
    unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN
    rw [UScalar.lt_equiv, Slice.len_val]
    change ¬ s.length < 6
    exact not_lt.mpr hlo
  rw [if_neg hnot]
  step as ⟨i1, hi1⟩
  step as ⟨maxl, hmax⟩
  have hgt : Slice.len s > maxl := by
    rw [GT.gt, UScalar.lt_equiv, Slice.len_val, hmax, hi1]
    change 2046 < s.length
    exact hhi
  simp only [hgt, ↓reduceIte, spec_ok]

/-- `new_raw` on an in-range slice whose length is not `6 mod 8` is `Unaligned`. -/
theorem new_raw_unaligned (next : net.ip_number_impl.IpNumber) (s : Slice Std.U8)
    (hlo : 6 ≤ s.length) (hhi : s.length ≤ 2046) (hmod : (s.length + 2) % 8 ≠ 0) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw next s
    ⦃ r => r = core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.Unaligned (Slice.len s)) ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_PAYLOAD_LEN
  simp only [core.slice.Slice.len, slice_length_eq, bind_tc_ok]
  have hnot : ¬ Slice.len s < net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN := by
    unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN
    rw [UScalar.lt_equiv, Slice.len_val]
    simpa [Slice.length, UScalar.ofNat, UScalar.ofNatCore_val_eq] using hlo
  rw [if_neg hnot]
  step as ⟨i1, hi1⟩
  step as ⟨maxl, hmax⟩
  have hngt : ¬ Slice.len s > maxl := by
    rw [GT.gt, UScalar.lt_equiv, Slice.len_val, hmax, hi1]
    simpa [Slice.length, UScalar.ofNat, UScalar.ofNatCore_val_eq] using hhi
  simp only [hngt, ↓reduceIte]
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hne : (0#usize) ≠ i3 := by
    intro heq
    apply hmod
    have hv : i3.val = 0 := by
      rw [heq.symm]
      simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
    rw [hi3, hi2, Slice.len_val, Slice.length] at hv
    exact hv
  have htrue : ((0#usize) != i3) = true := by
    simpa [bne_iff_ne] using hne
  rw [if_pos htrue, spec_ok]

theorem repeat_len (n : Std.Usize) (x : Std.U8) :
    (Array.to_slice (Array.repeat n x)).length = n.val := by
  simp [Array.to_slice, Array.repeat_val, Slice.length, List.length_replicate]

theorem as_slice_eq {α : Type} {n : Std.Usize} (a : Array α n) :
    core.array.Array.as_slice a = ok (Array.to_slice a) := by
  unfold core.array.Array.as_slice rust_primitives.slice.array_as_slice
  rfl

theorem as_mut_slice_eq {α : Type} {n : Std.Usize} (a : Array α n) :
    core.array.Array.as_mut_slice a = ok (Array.to_slice_mut a) := by
  unfold core.array.Array.as_mut_slice rust_primitives.slice.array_as_mut_slice
  rfl

theorem to_slice_mut_eq {α : Type} {n : Std.Usize} (a : Array α n) :
    Array.to_slice_mut a = (Array.to_slice a, Array.from_slice a) := by
  unfold Array.to_slice_mut
  rfl

theorem slice_index_eq {T I O : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) O) (s : Slice T) (i : I) :
    (core.Slice.Insts.CoreOpsIndexIndex inst).index s i =
      core.Slice.Insts.CoreOpsIndexIndex.index inst s i := by
  unfold core.Slice.Insts.CoreOpsIndexIndex
  rfl

theorem slice_index_mut_eq {T I O : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) O) (s : Slice T) (i : I) :
    (core.Slice.Insts.CoreOpsIndexIndexMut inst).index_mut s i =
      inst.get_unchecked_mut i s := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  rfl

theorem slice_index_mut_fn {T I O : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) O) (s : Slice T) (i : I) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut inst s i =
      inst.get_unchecked_mut i s := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  rfl

theorem rangeTo_get_eq {α : Type} (r : core.ops.range.RangeTo Std.Usize) (s : Slice α) :
    (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α).get r s =
      core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r s := by
  unfold core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
  rfl

theorem rangeTo_unchecked_eq {α : Type} (r : core.ops.range.RangeTo Std.Usize) (s : Slice α) :
    (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α).get_unchecked_mut r s =
      rust_primitives.slice.slice_slice_mut s 0#usize r.end := by
  unfold core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  rfl

theorem usize_of_len (s : Slice Std.U8) (n : Std.Usize) (h : s.length = n.val) :
    Slice.len s = n := by
  apply UScalar.val_eq_imp
  rw [Slice.len_val]
  simpa [Slice.length] using h

/-- `s[..len]` returns the prefix of length `len.val`. -/
theorem rangeTo_index_take (s : Slice Std.U8) (len : Std.Usize) (h : len.val ≤ s.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      s { «end» := len }
    ⦃ p => p.val = s.val.take len.val ∧ p.length = len.val ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
  rw [rangeTo_get_eq]
  unfold core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  simp only [slice_length_eq, bind_tc_ok]
  have hle : len ≤ Slice.len s := by
    rw [UScalar.le_equiv, Slice.len_val]
    simpa [Slice.length] using h
  rw [if_pos hle]
  have hslice :
      rust_primitives.slice.slice_slice s (0#usize) len
      ⦃ sub => sub.val = s.val.take len.val ∧ sub.length = len.val ⦄ := by
    unfold rust_primitives.slice.slice_slice Slice.subslice
    have hcond : (0#usize).val ≤ len.val ∧ len.val ≤ s.length := by
      simp [UScalar.ofNat, UScalar.ofNatCore_val_eq, Slice.length]
      omega
    rw [if_pos hcond, spec_ok]
    refine ⟨?_, ?_⟩
    · simp [List.slice_zero_j, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    · simp [Slice.length, List.slice_length, UScalar.ofNat, UScalar.ofNatCore_val_eq]
      omega
  have hinner :
      (do
        let sub ← rust_primitives.slice.slice_slice s (0#usize) len
        ok (core.option.Option.Some sub))
      ⦃ o => ∃ sub, o = core.option.Option.Some sub ∧
        sub.val = s.val.take len.val ∧ sub.length = len.val ⦄ := by
    apply spec_bind hslice
    intro sub hs
    rw [spec_ok]
    exact ⟨sub, rfl, hs⟩
  apply spec_bind hinner
  intro o ho
  obtain ⟨sub, ho1, hv, hl⟩ := ho
  rw [ho1, spec_ok]
  exact ⟨hv, hl⟩

theorem array_index_take (a : Array Std.U8 2046#usize) (e : Std.Usize) (he : e.val ≤ 2046) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
      a { «end» := e }
    ⦃ s => s.val = a.val.take e.val ∧ s.length = e.val ⦄ := by
  unfold core.Array.Insts.CoreOpsIndexIndex.index
  rw [as_slice_eq, bind_tc_ok, slice_index_eq]
  have hle : e.val ≤ (Array.to_slice a).length := by
    simp only [Array.to_slice, Slice.length, Array.length_eq, UScalar.ofNat,
      UScalar.ofNatCore_val_eq]
    omega
  apply spec_mono (rangeTo_index_take (Array.to_slice a) e hle)
  intro p hp
  simpa only [Array.to_slice] using hp

/-- `payload()` is the buffer prefix of length `6 + 8 * header_length`. -/
theorem payload_eq (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload header
    ⦃ s => s.val = header.payload_buffer.val.take (6 + 8 * header.header_length.val) ∧
      s.length = 6 + 8 * header.header_length.val ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload
  simp only [core.Usize.Insts.CoreConvertFromU8.from, bind_tc_ok]
  have hc : (UScalar.cast .Usize header.header_length).val = header.header_length.val :=
    U8.cast_Usize_val_eq _
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have he : i2.val ≤ 2046 := by
    rw [hi2, hi1, hc]
    have : header.header_length.val ≤ 255 := by scalar_tac
    omega
  apply spec_mono (array_index_take header.payload_buffer i2 he)
  intro p hp
  rw [hi2, hi1, hc, Nat.mul_comm] at hp
  exact hp

theorem header_len_val (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.header_len header
    ⦃ n => n.val = 8 + 8 * header.header_length.val ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.header_len
  simp only [core.Usize.Insts.CoreConvertFromU8.from, bind_tc_ok]
  have hc : (UScalar.cast .Usize header.header_length).val = header.header_length.val :=
    U8.cast_Usize_val_eq _
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  rw [hi3, hi2, hi1, hc]
  omega

theorem max_len_val :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_LEN ⦃ n => n.val = 2048 ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_LEN
  step as ⟨i, hi⟩
  step as ⟨j, hj⟩
  rw [hj, hi]

theorem subslice_prefix_zeros (s : Slice Std.U8) (h : s.length ≤ 2046) :
    Slice.subslice (Array.to_slice (Array.repeat 2046#usize (0#u8))) ⟨0#usize, Slice.len s⟩ =
      ok ⟨(List.replicate 2046 (0#u8)).take s.length, by
        simp only [List.length_take, List.length_replicate]
        scalar_tac⟩ := by
  unfold Slice.subslice
  have hcond : (0#usize).val ≤ (Slice.len s).val ∧
      (Slice.len s).val ≤ (Array.to_slice (Array.repeat 2046#usize (0#u8))).length := by
    rw [Slice.len_val]
    have h0 : (0#usize).val = 0 := by simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]
    have hbuf : (Array.to_slice (Array.repeat 2046#usize (0#u8))).length = 2046 := by
      simp only [Array.to_slice, Array.length_eq, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    rw [h0, hbuf]
    exact ⟨Nat.zero_le _, h⟩
  rw [if_pos hcond]
  apply congrArg ok
  apply Subtype.ext
  simp only [Array.to_slice, Array.repeat_val, Slice.len_val, Slice.length,
    UScalar.ofNat, UScalar.ofNatCore_val_eq, List.slice_zero_j]

theorem slice_mut_prefix_spec (s : Slice Std.U8) (h : s.length ≤ 2046) :
    rust_primitives.slice.slice_slice_mut
      (Array.to_slice (Array.repeat 2046#usize (0#u8))) (0#usize) (Slice.len s)
    ⦃ p => p.1.length = s.length ∧
      (p.2 s).val = (List.replicate 2046 (0#u8)).setSlice! 0 s.val ⦄ := by
  unfold rust_primitives.slice.slice_slice_mut
  rw [subslice_prefix_zeros s h]
  exact (spec_ok _).mpr ⟨
    by
      change (List.take s.length (List.replicate 2046 (0#u8))).length = s.length
      simp only [List.length_take, List.length_replicate]
      exact Nat.min_eq_left h,
    by simp only [Array.to_slice, Array.repeat_val, UScalar.ofNat, UScalar.ofNatCore_val_eq]⟩

theorem index_mut_prefix_copy (s : Slice Std.U8) (h : s.length ≤ 2046) :
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
      (Array.repeat 2046#usize (0#u8)) { «end» := Slice.len s }
    ⦃ p => p.1.length = s.length ∧
      (p.2 s).val = (List.replicate 2046 (0#u8)).setSlice! 0 s.val ⦄ := by
  simp only [core.Array.Insts.CoreOpsIndexIndexMut.index_mut]
  rw [as_mut_slice_eq, bind_tc_ok, to_slice_mut_eq, uncurry_apply_pair,
    slice_index_mut_fn, rangeTo_unchecked_eq]
  apply spec_bind (slice_mut_prefix_spec s h)
  intro q hq
  rw [uncurry_apply_pair, spec_ok]
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨hq1, ?_⟩
  have hif : ((List.replicate 2046 (0#u8)).setSlice! 0 s.val).length = 2046 := by
    simp only [List.length_setSlice!, List.length_replicate]
  simp only [Array.from_slice, hq2, Array.to_slice, Array.repeat_val,
    UScalar.ofNat, UScalar.ofNatCore_val_eq, hif, ↓reduceDIte]

theorem array_subslice_take {n : Std.Usize} (a : Array Std.U8 n) (e : Std.Usize)
    (h : e.val ≤ a.val.length) :
    Array.subslice a { start := 0#usize, «end» := e }
    ⦃ s => s.length = e.val ⦄ := by
  have hstep :
      Array.subslice a { start := 0#usize, «end» := e } =
        ok ⟨a.val.take e.val, by
          rw [Array.length_eq] at h
          simp only [List.length_take]
          scalar_tac⟩ := by
    unfold Array.subslice
    have hcond : (0#usize).val ≤ e.val ∧ e.val ≤ a.val.length := by
      constructor
      · simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]
        exact Nat.zero_le _
      · exact h
    rw [if_pos hcond]
    apply congrArg ok
    apply Subtype.ext
    simp only [List.slice_zero_j, UScalar.ofNat, UScalar.ofNatCore_val_eq]
  rw [hstep, spec_ok]
  rw [Array.length_eq] at h
  simp only [Slice.length, List.length_take]
  omega

set_option maxRecDepth 200000 in
theorem new_raw_2047 (next : net.ip_number_impl.IpNumber) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw next
      (Array.to_slice (Array.repeat 2047#usize (0#u8)))
    ⦃ r => r = core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooBig 2047#usize) ⦄ := by
  have hs : (Array.to_slice (Array.repeat 2047#usize (0#u8))).length = 2047 := repeat_len _ _
  have hlo : 6 ≤ (Array.to_slice (Array.repeat 2047#usize (0#u8))).length := by
    rw [hs]; omega
  have hhi : 2046 < (Array.to_slice (Array.repeat 2047#usize (0#u8))).length := by
    rw [hs]; omega
  have hlen : Slice.len (Array.to_slice (Array.repeat 2047#usize (0#u8))) = 2047#usize :=
    usize_of_len _ _ (by simpa only [UScalar.ofNat, UScalar.ofNatCore_val_eq] using hs)
  apply spec_mono (new_raw_too_big next (Array.to_slice (Array.repeat 2047#usize (0#u8))) hlo hhi)
  intro r hr
  rw [hr]
  exact congrArg
    (fun n => core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooBig n))
    hlen

/-- Aligned `new_raw`: the buffer prefix is the source slice and `header_length` is `(len-6)/8`. -/
theorem new_raw_aligned (next : net.ip_number_impl.IpNumber) (s : Slice Std.U8) (k : Nat)
    (hk : k ≤ 255) (hs : s.length = 6 + 8 * k) :
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw next s
    ⦃ r => ∃ h, r = core.result.Result.Ok h ∧ h.next_header = next ∧
      h.header_length.val = k ∧
      h.payload_buffer.val =
        (List.replicate 2046 (0#u8)).setSlice! 0 s.val ⦄ := by
  unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw
    net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_PAYLOAD_LEN
  simp only [core.slice.Slice.len, slice_length_eq, bind_tc_ok]
  have hnot : ¬ Slice.len s < net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN := by
    unfold net.ipv6_raw_ext_header.Ipv6RawExtHeader.MIN_PAYLOAD_LEN
    rw [UScalar.lt_equiv, Slice.len_val]
    simp [Slice.length, hs, UScalar.ofNat, UScalar.ofNatCore_val_eq]
  rw [if_neg hnot]
  step as ⟨i1, hi1⟩
  step as ⟨maxl, hmax⟩
  have hngt : ¬ Slice.len s > maxl := by
    rw [GT.gt, UScalar.lt_equiv, Slice.len_val, hmax, hi1]
    simp [Slice.length, hs, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    omega
  simp only [hngt, ↓reduceIte]
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have heq0 : i3 = 0#usize := by
    apply UScalar.val_eq_imp
    rw [hi3, hi2, Slice.len_val]
    simp [Slice.length, hs, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    omega
  have hfalse : ¬ (((0#usize) != i3) = true) := by
    simp [bne_iff_ne, heq0]
  rw [if_neg hfalse]
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  simp only [lift, bind_tc_ok]
  have hcast : (UScalar.cast .U8 i5).val = k := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hi5, hi4, Slice.len_val]
    · simp [Slice.length, hs, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    · simp only [UScalarTy.numBits, hi5, hi4, Slice.len_val, Slice.length, hs,
        UScalar.ofNat, UScalar.ofNatCore_val_eq]
      omega
  have hlen : s.length ≤ 2046 := by
    simp [Slice.length, hs]
    omega
  apply spec_bind (index_mut_prefix_copy s hlen)
  rintro ⟨sl, back⟩ ⟨hsl, hback⟩
  rw [uncurry_apply_pair, copy_from_slice_u8 sl s hsl, bind_tc_ok, spec_ok]
  refine ⟨{
      next_header := next
      header_length := UScalar.cast .U8 i5
      payload_buffer := back s
    }, rfl, rfl, hcast, hback⟩

set_option maxRecDepth 200000 in
theorem ipv6_raw_ext_new_raw (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) :
    ipv6_raw_ext_new_raw_spec header := by
  unfold ipv6_raw_ext_new_raw_spec
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply spec_bind (payload_eq header)
    intro p hp
    apply spec_bind (new_raw_aligned header.next_header p header.header_length.val
      (by scalar_tac) hp.2)
    intro r hr
    rw [spec_ok]
    obtain ⟨h, hr1, hrn, hhl, hbuf⟩ := hr
    refine ⟨h, hr1, hrn, ?_⟩
    apply spec_mono (payload_eq h)
    intro p2 hp2
    apply Subtype.ext
    rw [hp2.1, hbuf, hhl, replicate_setSlice_prefix (0#u8) p.val 2046 (by
      dsimp only [Slice.length] at hp
      rw [hp.2]
      have : header.header_length.val ≤ 255 := by scalar_tac
      omega)]
    have hN : 6 + 8 * header.header_length.val = p.val.length := by
      dsimp only [Slice.length] at hp
      exact hp.2.symm
    rw [hN, List.take_append_of_le_length (le_refl _), List.take_length]
  · intro len hlen
    apply spec_bind (payload_eq header)
    intro p hp
    have hpre : len.val ≤ p.length := by rw [hp.2]; omega
    apply spec_bind (rangeTo_index_take p len hpre)
    intro pref hpref
    apply spec_mono (new_raw_too_small header.next_header pref (by rw [hpref.2]; exact hlen))
    intro r hr
    rw [hr]
    exact congrArg
      (fun n => core.result.Result.Err
        (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooSmall n))
      (usize_of_len pref len hpref.2)
  · exact new_raw_2047 header.next_header
  · intro offset hoff
    apply spec_bind (header_len_val header)
    intro hlen hh
    step as ⟨sum, hsum⟩
    apply spec_bind max_len_val
    intro maxl hm
    rw [spec_ok]
    intro hcond
    apply spec_bind (payload_eq header)
    intro p hp
    simp only [core.slice.Slice.len, slice_length_eq, bind_tc_ok]
    step as ⟨n, hn⟩
    have hnval : n.val = p.length + offset.val := by
      rw [hn, Slice.len_val]
    have hnle : n.val ≤ 2053 := by
      rw [hnval, hp.2]
      have : header.header_length.val ≤ 255 := by scalar_tac
      omega
    apply spec_bind (array_subslice_take (Array.repeat 2053#usize (0#u8)) n
      (by simp only [Array.repeat_val, List.length_replicate, Array.length_eq,
            UScalar.ofNat, UScalar.ofNatCore_val_eq];
          exact hnle))
    intro pref hpref
    have hlo : 6 ≤ pref.length := by
      rw [hpref, hnval, hp.2]; omega
    have hhi : pref.length ≤ 2046 := by
      rw [hpref, hnval, hp.2]
      have : offset.val + (8 + 8 * header.header_length.val) < 2048 := by
        rw [hsum, hh, hm] at hcond
        exact hcond
      omega
    have hmod : (pref.length + 2) % 8 ≠ 0 := by
      rw [hpref, hnval]
      have hsumN : p.length + offset.val + 2 =
          8 * (header.header_length.val + 1) + offset.val := by
        rw [hp.2]; omega
      rw [hsumN, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : offset.val < 8)]
      omega
    apply spec_bind (new_raw_unaligned header.next_header pref hlo hhi hmod)
    intro r hr
    rw [spec_ok]
    rw [hr]
    exact congrArg
      (fun n => core.result.Result.Err
        (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.Unaligned n))
      (usize_of_len pref n hpref)

end Benchmark.Cases.Etherparse.Net
