import Benchmark.Cases.Quantiles.GreenwaldKhanna.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open quantiles

namespace Benchmark.Cases.Quantiles.GreenwaldKhanna

private theorem lt_i32 (a b : Std.I32) :
    core.Shared1A.Insts.CoreCmpPartialOrdShared0B.lt
      core.I32.Insts.CoreCmpOrd.PartialOrdInst a b = ok (decide (a.val < b.val)) := by
  simp only [core.Shared1A.Insts.CoreCmpPartialOrdShared0B.lt, core.I32.Insts.CoreCmpOrd,
    core.mkIOrd, core.mkIPartialOrd]
  rcases lt_trichotomy a.val b.val with h | h | h
  · simp [compare_lt_iff_lt.mpr h, h]
  · simp [h]
  · simp [compare_gt_iff_gt.mpr h, not_lt.mpr h.le]

private theorem iter_next_nil (hl : ([] : List Std.I32).length ≤ Usize.max) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
      (⟨[], hl⟩ : Slice Std.I32) = ok (core.option.Option.None, ⟨[], hl⟩) := by
  have h0 : Slice.len (⟨[], hl⟩ : Slice Std.I32) = 0#usize := by
    rw [UScalar.eq_equiv, Slice.len_val]; simp
  simp [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, h0]

private theorem iter_next_cons (x : Std.I32) (t : List Std.I32) (hl : (x :: t).length ≤ Usize.max) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
      (⟨x :: t, hl⟩ : Slice Std.I32) =
      ok (core.option.Option.Some x, ⟨t, by simp at hl; omega⟩) := by
  have h0 : Slice.len (⟨x :: t, hl⟩ : Slice Std.I32) ≠ 0#usize := by
    rw [ne_eq, UScalar.eq_equiv, Slice.len_val]; simp
  simp [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, h0, rust_primitives.sequence.seq_remove]

private theorem body_nil (vs : Slice Std.I32) (v : Std.I32) (hl : ([] : List Std.I32).length ≤ Usize.max)
    (c : Std.Usize) :
    greenwald_khanna.find_insert_pos_linear_loop.body core.I32.Insts.CoreCmpOrd vs v
      { iter := (⟨[], hl⟩ : Slice Std.I32), count := c } = ok (ControlFlow.done (Slice.len vs)) := by
  simp [greenwald_khanna.find_insert_pos_linear_loop.body,
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    iter_next_nil, core.slice.Slice.len, rust_primitives.slice.slice_length]

private theorem body_cons (vs : Slice Std.I32) (v x : Std.I32) (t : List Std.I32)
    (hl : (x :: t).length ≤ Usize.max) (c c' : Std.Usize) (hc' : c + 1#usize = ok c') :
    greenwald_khanna.find_insert_pos_linear_loop.body core.I32.Insts.CoreCmpOrd vs v
      { iter := (⟨x :: t, hl⟩ : Slice Std.I32), count := c } =
      (if v.val < x.val then ok (ControlFlow.done c)
       else ok (ControlFlow.cont { iter := (⟨t, by simp at hl; omega⟩ : Slice Std.I32), count := c' })) := by
  simp [greenwald_khanna.find_insert_pos_linear_loop.body,
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    iter_next_cons, hc', lt_i32]

private theorem lin_loop (vs : Slice Std.I32) (v : Std.I32) :
    ∀ (l : List Std.I32) (hl : l.length ≤ Usize.max) (c : Std.Usize),
      c.val + l.length = vs.val.length →
      greenwald_khanna.find_insert_pos_linear_loop core.I32.Insts.CoreCmpOrd
        { iter := (⟨l, hl⟩ : Slice Std.I32), count := c } vs v
        ⦃ r => r.val = c.val + l.findIdx (fun x => decide (v.val < x.val)) ⦄ := by
  intro l
  induction l with
  | nil =>
    intro hl c hc
    unfold greenwald_khanna.find_insert_pos_linear_loop
    rw [loop]
    try dsimp only
    rw [body_nil]
    simp only [spec_ok, Slice.len_val, Slice.length, List.findIdx_nil]
    simp at hc; omega
  | cons x t ih =>
    intro hl c hc
    have hc1 : c.val + 1 ≤ Usize.max := by
      have := vs.length_ineq; simp at hc; omega
    obtain ⟨c', hc', hc'v⟩ : ∃ c' : Std.Usize, c + 1#usize = ok c' ∧ c'.val = c.val + 1 := by
      have h := spec_imp_exists (UScalar.add_bv_spec (x := c) (y := 1#usize)
        (by rw [UScalar.max_USize_eq]; simp; omega))
      obtain ⟨z, hz, hz1, -⟩ := h
      exact ⟨z, hz, by simpa using hz1⟩
    unfold greenwald_khanna.find_insert_pos_linear_loop
    rw [loop]
    try dsimp only
    rw [body_cons vs v x t hl c c' hc']
    by_cases h : v.val < x.val
    · simp only [h, if_true, spec_ok, List.findIdx_cons, decide_true, cond_true]
      omega
    · simp only [h, if_false]
      have := ih (by simp at hl; omega) c' (by simp at hc; omega)
      unfold greenwald_khanna.find_insert_pos_linear_loop at this
      refine spec_mono this ?_
      intro r hr
      simp only [List.findIdx_cons, h, decide_false, cond_false]
      omega

private theorem lin_spec (vs : Slice Std.I32) (v : Std.I32) :
    greenwald_khanna.find_insert_pos_linear core.I32.Insts.CoreCmpOrd vs v
      ⦃ r => r.val = vs.val.findIdx (fun x => decide (v.val < x.val)) ⦄ := by
  unfold greenwald_khanna.find_insert_pos_linear
  simp only [core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice, bind_tc_ok,
    core.iter.traits.iterator.Iterator.enumerate.default,
    core.iter.adapters.enumerate.Enumerate.new]
  have := lin_loop vs v vs.val vs.property 0#usize (by simp)
  refine spec_mono this ?_
  intro r hr; simpa using hr

private theorem index_ok (vs : Slice Std.I32) (i : Std.Usize) (h : i.val < vs.val.length) :
    Slice.index_usize vs i = ok (vs.val[i.val]'h) := by
  simp [Slice.index_usize, h]

private theorem findIdx_take_of_hit {α : Type} (p : α → Bool) (l : List α) (m : Nat)
    (hm : m < l.length) (h : p l[m] = true) :
    (l.take m).findIdx p = l.findIdx p := by
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.findIdx_append]
  split
  · rfl
  · rename_i hge
    rw [List.drop_eq_getElem_cons hm, List.findIdx_cons, h]
    have := List.findIdx_le_length (p := p) (xs := l.take m)
    simp only [cond_true]
    omega

private theorem findIdx_drop_of_miss (v : Std.I32) (l : List Std.I32) (m : Nat) (hm : m < l.length)
    (hs : l.Pairwise (fun a b => a.val ≤ b.val)) (h : ¬ v.val < (l[m]).val) :
    l.findIdx (fun x => decide (v.val < x.val)) =
      m + (l.drop m).findIdx (fun x => decide (v.val < x.val)) := by
  have hs' := hs
  rw [← List.take_append_drop m l, List.pairwise_append] at hs'
  have hmem : l[m] ∈ l.drop m := by
    rw [List.drop_eq_getElem_cons hm]; exact List.mem_cons_self
  have hnone : ∀ x ∈ l.take m, decide (v.val < x.val) = false := by
    intro x hx
    have := hs'.2.2 x hx l[m] hmem
    simp only [decide_eq_false_iff_not, not_lt]
    exact le_trans this (not_lt.mp h)
  conv_lhs => rw [← List.take_append_drop m l]
  rw [List.findIdx_append, List.findIdx_eq_length_of_false hnone]
  simp only [lt_irrefl, if_false, List.length_take]
  omega

private theorem range_index_ok (vs : Slice Std.I32) (b : Std.Usize) (h : b.val ≤ vs.val.length) :
    ∃ s : Slice Std.I32, core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) vs
      { start := 0#usize, «end» := b } = ok s ∧ s.val = vs.val.take b.val := by
  have h1 : (0#usize) ≤ b := by show (0#usize).val ≤ b.val; simp
  have h2 : b ≤ Slice.len vs := by show b.val ≤ (Slice.len vs).val; rw [Slice.len_val]; exact h
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, h1, h2, h]

private theorem rangefrom_index_ok (vs : Slice Std.I32) (a : Std.Usize) (h : a.val ≤ vs.val.length) :
    ∃ s : Slice Std.I32, core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) vs
      { start := a } = ok s ∧ s.val = vs.val.drop a.val := by
  have h2 : a ≤ Slice.len vs := by show a.val ≤ (Slice.len vs).val; rw [Slice.len_val]; exact h
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, h]
  rw [List.slice]; apply List.take_of_length_le; simp

private theorem fip_spec (v : Std.I32) : ∀ n (vs : Slice Std.I32), vs.val.length = n →
    vs.val.Pairwise (fun a b => a.val ≤ b.val) →
    greenwald_khanna.find_insert_pos core.I32.Insts.CoreCmpOrd vs v
      ⦃ r => r.val = vs.val.findIdx (fun x => decide (v.val < x.val)) ⦄ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro vs hn hs
  rw [greenwald_khanna.find_insert_pos]
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hlen : (Slice.len vs).val = vs.val.length := Slice.len_val vs
  by_cases hle : Slice.len vs ≤ 10#usize
  · rw [if_pos hle]; exact lin_spec vs v
  · rw [if_neg hle]
    have h10 : 10 < vs.val.length := by
      have : ¬ (Slice.len vs).val ≤ (10#usize).val := hle
      simp [Slice.len_val] at this; omega
    obtain ⟨m, hm, hmv0⟩ := UScalar.div_spec (Slice.len vs) (y := 2#usize) (by simp)
    have hmv : m.val = vs.val.length / 2 := by simpa [Slice.len_val] using hmv0
    have hmlt : m.val < vs.val.length := by omega
    rw [hm, bind_tc_ok, index_ok vs m hmlt, bind_tc_ok, lt_i32, bind_tc_ok]
    by_cases hlt : v.val < (vs.val[m.val]).val
    · simp only [hlt, decide_true, if_true]
      obtain ⟨s, hs1, hs2⟩ := range_index_ok vs m (by omega)
      rw [hs1, bind_tc_ok]
      have hslen : s.val.length = m.val := by rw [hs2, List.length_take]; omega
      have := ih m.val (by omega) s hslen (hs2 ▸ hs.sublist (List.take_sublist _ _))
      refine spec_mono this ?_
      intro r hr
      rw [hr, hs2]
      exact findIdx_take_of_hit _ _ _ hmlt (by simp [hlt])
    · simp only [hlt, decide_false, Bool.false_eq_true, if_false]
      obtain ⟨s, hs1, hs2⟩ := rangefrom_index_ok vs m (by omega)
      rw [hs1, bind_tc_ok]
      have hslen : s.val.length = vs.val.length - m.val := by rw [hs2, List.length_drop]
      have := ih (vs.val.length - m.val) (by omega) s hslen (hs2 ▸ hs.sublist (List.drop_sublist _ _))
      obtain ⟨r, hr, hrv⟩ := spec_imp_exists this
      rw [hr, bind_tc_ok]
      have hrle : r.val ≤ s.val.length := hrv ▸ List.findIdx_le_length
      obtain ⟨z, hz, hzv, -⟩ := spec_imp_exists (UScalar.add_bv_spec (x := m) (y := r)
        (by rw [UScalar.max_USize_eq]; have := vs.length_ineq; omega))
      rw [hz, spec_ok, hzv, hrv, hs2, findIdx_drop_of_miss v vs.val m.val hmlt hs hlt]

/--
On a sorted `i32` slice, the recursive binary search `find_insert_pos`
(linear scan below 11 elements, otherwise split at `len / 2` on `v < vs[len/2]`)
never panics and returns the same insertion position as the linear scan
`find_insert_pos_linear` (index of the first element greater than `v`, or `len`).
-/
theorem find_insert_pos_matches_linear (vs : Slice Std.I32) (v : Std.I32)
    (h_sorted : vs.val.Pairwise (fun a b => a.val ≤ b.val))
    (h_v_lo : -100 ≤ v.val) (h_v_hi : v.val < 100) :
    find_insert_pos_matches_linear_spec vs v := by
  unfold find_insert_pos_matches_linear_spec
  obtain ⟨a, ha, hav⟩ := spec_imp_exists (fip_spec v _ vs rfl h_sorted)
  obtain ⟨b, hb, hbv⟩ := spec_imp_exists (lin_spec vs v)
  rw [ha, bind_tc_ok, hb, bind_tc_ok, spec_ok]
  exact (UScalar.eq_equiv a b).mpr (hav.trans hbv.symm)

end Benchmark.Cases.Quantiles.GreenwaldKhanna
