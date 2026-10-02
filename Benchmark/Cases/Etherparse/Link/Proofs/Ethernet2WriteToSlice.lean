import Benchmark.Cases.Etherparse.Link.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

set_option linter.unusedSimpArgs false

theorem clone_u8_mapM (l : List Std.U8) :
    List.mapM core.U8.Insts.CoreCloneClone.clone l = ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, ih, bind_tc_ok]
    rfl

/-- `dst.copy_from_slice(src)` on equal-length `u8` slices returns `src`. -/
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

theorem e2w_list2 {α : Type} (l : List α) (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem e2w_list6 {α : Type} (l : List α) (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

@[simp] theorem e2w_make_val {α : Type} (n : Std.Usize) (l : List α) (h : l.length = n.val) :
    (Array.make n l h).val = l := rfl

theorem replicate_setSlice_all {α : Type} (x : α) (l : List α) (h : l.length = 14) :
    (List.replicate 14 x).setSlice! 0 l = l := by
  simp only [List.setSlice!, List.length_replicate, h, Nat.sub_zero, Nat.min_self,
    List.take_zero, List.nil_append]
  rw [← h, List.take_length]
  simp [List.drop_replicate, h]

theorem setSlice_at_len_nil {α : Type} (s : List α) :
    s.setSlice! s.length [] = s := by
  simp [List.setSlice!]

theorem let_pair {α β γ : Type} (a : α) (b : β) (f : α → β → γ) :
    (let (x, y) := (a, b); f x y) = f a b := rfl

/-- `write_to_slice` on a slice shorter than 14 bytes is `SliceWriteSpaceError`. -/
theorem write_to_slice_when_short (input : link.ethernet2_header.Ethernet2Header)
    (s : Slice Std.U8) (hlen : s.length < 14) :
    link.ethernet2_header.Ethernet2Header.write_to_slice input s
    ⦃ p => p.1 = core.result.Result.Err {
      required_len := link.ethernet2_header.Ethernet2Header.LEN,
      len := Slice.len s,
      layer := err.layer.Layer.Ethernet2Header,
      layer_start_offset := 0#usize } ⦄ := by
  unfold link.ethernet2_header.Ethernet2Header.write_to_slice
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hlt : Slice.len s < link.ethernet2_header.Ethernet2Header.LEN := by
    have hLEN : link.ethernet2_header.Ethernet2Header.LEN = 14#usize := by
      unfold link.ethernet2_header.Ethernet2Header.LEN; rfl
    rw [hLEN, UScalar.lt_equiv, Slice.len_val]
    simp only [Slice.length, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    exact hlen
  rw [if_pos hlt, spec_ok]

theorem as_mut_slice_eq {α : Type} {n : Std.Usize} (a : Array α n) :
    core.array.Array.as_mut_slice a = ok (Array.to_slice_mut a) := by
  unfold core.array.Array.as_mut_slice rust_primitives.slice.array_as_mut_slice
  rfl

theorem to_slice_mut_eq {α : Type} {n : Std.Usize} (a : Array α n) :
    Array.to_slice_mut a = (Array.to_slice a, Array.from_slice a) := by
  unfold Array.to_slice_mut
  rfl

theorem slice_index_mut_eq {T I O : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) O) (s : Slice T) (i : I) :
    (core.Slice.Insts.CoreOpsIndexIndexMut inst).index_mut s i = inst.get_unchecked_mut i s := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  rfl

theorem slice_index_mut_fn {T I O : Type}
    (inst : core.slice.index.SliceIndex I (Slice T) O) (s : Slice T) (i : I) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut inst s i = inst.get_unchecked_mut i s := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  rfl

theorem rangeTo_unchecked_eq {α : Type} (r : core.ops.range.RangeTo Std.Usize) (s : Slice α) :
    (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α).get_unchecked_mut r s =
      rust_primitives.slice.slice_slice_mut s 0#usize r.end := by
  unfold core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  rfl

theorem rangeFrom_unchecked_eq {α : Type} (r : core.ops.range.RangeFrom Std.Usize) (s : Slice α) :
    (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α).get_unchecked_mut r s =
      (do
        let n ← rust_primitives.slice.slice_length s
        rust_primitives.slice.slice_slice_mut s r.start n) := by
  unfold core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  rfl

theorem slice_length_eq {α : Type} (s : Slice α) :
    rust_primitives.slice.slice_length s = ok (Slice.len s) := by
  unfold rust_primitives.slice.slice_length
  rfl

/-- `buf[..14]` of a 14-byte slice is the slice itself. -/
theorem subslice_full14 :
    Slice.subslice (Array.to_slice (Array.repeat 14#usize (0#u8))) ⟨0#usize, 14#usize⟩ =
      ok (Array.to_slice (Array.repeat 14#usize (0#u8))) := by
  unfold Slice.subslice
  have hcond : (0#usize).val ≤ (14#usize).val ∧
      (14#usize).val ≤ (Array.to_slice (Array.repeat 14#usize (0#u8))).length := by
    simp [Array.to_slice, Array.repeat_val, Slice.length, UScalar.ofNat,
      UScalar.ofNatCore_val_eq, List.length_replicate]
  rw [if_pos hcond]
  apply congrArg ok
  apply Subtype.ext
  simp [Array.to_slice, Array.repeat_val, UScalar.ofNat, UScalar.ofNatCore_val_eq,
    List.length_replicate, List.slice]

/-- The half-open suffix starting at the slice length is empty. -/
theorem subslice_empty_suffix (l : List Std.U8) (hp : l.length ≤ Usize.max) (h : l.length = 14) :
    Slice.subslice (⟨l, hp⟩ : Slice Std.U8) ⟨14#usize, Slice.len (⟨l, hp⟩ : Slice Std.U8)⟩ =
      ok (⟨[] , by simp⟩ : Slice Std.U8) := by
  unfold Slice.subslice
  have hcond : (14#usize).val ≤ (Slice.len (⟨l, hp⟩ : Slice Std.U8)).val ∧
      (Slice.len (⟨l, hp⟩ : Slice Std.U8)).val ≤ l.length := by
    simp [Slice.len_val, Slice.length, h, UScalar.ofNat, UScalar.ofNatCore_val_eq]
  rw [if_pos hcond]
  apply congrArg ok
  apply Subtype.ext
  simp [List.slice, Slice.len_val, Slice.length, h]

theorem slice_mut_suffix_spec (l : List Std.U8) (hp : l.length ≤ Usize.max) (h : l.length = 14) :
    rust_primitives.slice.slice_slice_mut (⟨l, hp⟩ : Slice Std.U8) 14#usize
        (Slice.len (⟨l, hp⟩ : Slice Std.U8))
    ⦃ p => p.1 = (⟨[] , by simp⟩ : Slice Std.U8) ∧ (p.2 p.1).val = l ⦄ := by
  unfold rust_primitives.slice.slice_slice_mut
  rw [subslice_empty_suffix l hp h]
  exact (spec_ok _).mpr ⟨rfl, by
    have hidx : (14#usize).val = l.length := by
      simp [UScalar.ofNat, UScalar.ofNatCore_val_eq, h]
    simp only [hidx, setSlice_at_len_nil]⟩

theorem write_suffix_step (l : List Std.U8) (hp : l.length ≤ Usize.max) (h : l.length = 14) :
    (do
      let (s3, index_mut_back1) ←
        rust_primitives.slice.slice_slice_mut (⟨l, hp⟩ : Slice Std.U8) 14#usize
          (Slice.len (⟨l, hp⟩ : Slice Std.U8))
      let back :
          core.result.Result (Slice Std.U8) err.slice_write_space_error.SliceWriteSpaceError →
            Slice Std.U8 :=
        fun r =>
          index_mut_back1
            (match r with
              | core.result.Result.Ok s5 => s5
              | _ => s3)
      ok (core.result.Result.Ok s3, back))
    ⦃ p => p.1 = core.result.Result.Ok (⟨[] , by simp⟩ : Slice Std.U8) ∧ (p.2 p.1).val = l ⦄ := by
  apply spec_bind (slice_mut_suffix_spec l hp h)
  intro q hq
  rw [uncurry_apply_pair, spec_ok]
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨congrArg core.result.Result.Ok hq1, ?_⟩
  simpa [hq1] using hq2

/-- `&mut buf[..len]` of a 14-byte array yields a slice of length `len.val` when `len.val < 14`. -/
theorem index_mut_prefix_len (len : Std.Usize) (hlen : len.val < 14) :
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
      (Array.repeat 14#usize 0#u8) { «end» := len }
    ⦃ p => p.1.length = len.val ⦄ := by
  unfold core.Array.Insts.CoreOpsIndexIndexMut.index_mut
  rw [as_mut_slice_eq, bind_tc_ok, to_slice_mut_eq, uncurry_apply_pair]
  rw [slice_index_mut_eq, rangeTo_unchecked_eq]
  have hslice :
      rust_primitives.slice.slice_slice_mut
        (Array.to_slice (Array.repeat 14#usize (0#u8))) (0#usize) len
      ⦃ p => p.1.length = len.val ⦄ := by
    unfold rust_primitives.slice.slice_slice_mut
    have hcond : (0#usize).val ≤ len.val ∧
        len.val ≤ (Array.to_slice (Array.repeat 14#usize (0#u8))).length := by
      simp [Array.to_slice, Array.repeat_val, Slice.length, UScalar.ofNat,
        UScalar.ofNatCore_val_eq, List.length_replicate]
      omega
    have hsub :
        Slice.subslice (Array.to_slice (Array.repeat 14#usize (0#u8))) ⟨0#usize, len⟩
        ⦃ sub => sub.length = len.val ⦄ := by
      unfold Slice.subslice
      rw [if_pos hcond, spec_ok]
      simp only [Array.to_slice, Array.repeat_val, Slice.length, List.slice_length,
        UScalar.ofNat, UScalar.ofNatCore_val_eq, List.length_replicate]
      omega
    apply spec_bind hsub
    intro sub hlen_sub
    exact (spec_ok _).mpr hlen_sub
  apply spec_bind hslice
  intro p hp
  rw [uncurry_apply_pair, spec_ok]
  exact hp

theorem ethernet2_write_short (input : link.ethernet2_header.Ethernet2Header)
    (len : Std.Usize) (hlen : len.val < 14) :
    (do
      let buf := Array.repeat 14#usize 0#u8
      let (s, _backArr) ←
        core.Array.Insts.CoreOpsIndexIndexMut.index_mut
          (core.Slice.Insts.CoreOpsIndexIndexMut
            (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
          buf { «end» := len }
      let (r, _back) ← link.ethernet2_header.Ethernet2Header.write_to_slice input s
      ok r)
    ⦃ r => r = core.result.Result.Err {
      required_len := link.ethernet2_header.Ethernet2Header.LEN,
      len := len,
      layer := err.layer.Layer.Ethernet2Header,
      layer_start_offset := 0#usize } ⦄ := by
  apply spec_bind (index_mut_prefix_len len hlen)
  rintro ⟨s, _back⟩ hs
  have hlen' : s.length < 14 := by rw [hs]; exact hlen
  apply spec_bind (write_to_slice_when_short input s hlen')
  rintro ⟨r, _b⟩ hr
  have hlen_eq : Slice.len s = len := by
    apply UScalar.val_eq_imp
    rw [Slice.len_val, hs]
  rw [uncurry_apply_pair, spec_ok]
  rw [show r = (r, _b).1 from rfl, hr, hlen_eq]

/-- Writing into a 14-byte buffer reproduces `to_bytes`; a shorter prefix is `SliceWriteSpaceError`. -/
theorem ethernet2_write_to_slice (input : link.ethernet2_header.Ethernet2Header) :
    ethernet2_write_to_slice_spec input := by
  obtain ⟨e0, e1, he⟩ := e2w_list2 (Std.core.num.U16.to_be_bytes input.ether_type).val (by simp)
  obtain ⟨d0, d1, d2, d3, d4, d5, hd⟩ := e2w_list6 input.destination.val (by simp)
  obtain ⟨s0, s1, s2, s3, s4, s5, hs⟩ := e2w_list6 input.source.val (by simp)
  let bytes : Array Std.U8 14#usize :=
    Array.make 14#usize [d0, d1, d2, d3, d4, d5, s0, s1, s2, s3, s4, s5, e0, e1]
  have hto : link.ethernet2_header.Ethernet2Header.to_bytes input = ok bytes := by
    unfold link.ethernet2_header.Ethernet2Header.to_bytes bytes
    simp only [core.num.U16.to_be_bytes, rust_primitives.arithmetic.to_be_bytes_u16,
      bind_tc_ok, Array.index_usize, Array.getElem?_Usize_eq, he, hd, hs]
    simp [UScalar.ofNat, UScalar.ofNatCore_val_eq]
  unfold ethernet2_write_to_slice_spec
  have hLEN : link.ethernet2_header.Ethernet2Header.LEN = 14#usize := by
    unfold link.ethernet2_header.Ethernet2Header.LEN; rfl
  constructor
  · unfold link.ethernet2_header.Ethernet2Header.write_to_slice
    rw [hto]
    simp only [lift, bind_tc_ok, to_slice_mut_eq, uncurry_apply_pair,
      core.slice.Slice.len, slice_length_eq]
    have hnot : ¬ Slice.len (Array.to_slice (Array.repeat 14#usize (0#u8))) <
        link.ethernet2_header.Ethernet2Header.LEN := by
      rw [hLEN, UScalar.lt_equiv, Slice.len_val]
      simp [Array.to_slice, Array.repeat_val, Slice.length, UScalar.ofNat,
        UScalar.ofNatCore_val_eq, List.length_replicate]
    rw [if_neg hnot, hLEN, slice_index_mut_fn, rangeTo_unchecked_eq]
    unfold rust_primitives.slice.slice_slice_mut
    have hcopylen : (Array.to_slice (Array.repeat 14#usize (0#u8))).length =
        (Array.to_slice bytes).length := by
      simp [Slice.length, Array.to_slice, Array.repeat_val, e2w_make_val, Array.make,
        List.length_replicate]
    rw [subslice_full14, bind_tc_ok, bind_tc_ok, uncurry_apply_pair]
    rw [copy_from_slice_u8 _ _ hcopylen, bind_tc_ok]
    rw [slice_index_mut_fn, rangeFrom_unchecked_eq, slice_length_eq, bind_tc_ok]
    have hwlen : ((Array.to_slice (Array.repeat 14#usize (0#u8))).val.setSlice!
        (0#usize).val (Array.to_slice bytes).val).length = 14 := by
      simp [Array.to_slice, Array.repeat_val, List.length_setSlice!, List.length_replicate,
        e2w_make_val, UScalar.ofNat, UScalar.ofNatCore_val_eq]
    dsimp only []
    apply spec_bind (write_suffix_step _ _ hwlen)
    intro p hp
    rw [uncurry_apply_pair, spec_ok]
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨⟨[] , by simp⟩, hp1, ?_⟩
    apply Subtype.ext
    have hif : ((List.replicate 14 (0#u8)).setSlice! 0 bytes.val).length = 14 := by
      simp [List.length_setSlice!, List.length_replicate, e2w_make_val]
    simp only [Array.from_slice, hp2, Array.to_slice, Array.repeat_val, e2w_make_val,
      UScalar.ofNat, UScalar.ofNatCore_val_eq, hif, ↓reduceDIte]
    rw [replicate_setSlice_all (0#u8) _ (by simp [e2w_make_val])]
  · intro len hlen
    exact ethernet2_write_short input len hlen

end Benchmark.Cases.Etherparse.Link
