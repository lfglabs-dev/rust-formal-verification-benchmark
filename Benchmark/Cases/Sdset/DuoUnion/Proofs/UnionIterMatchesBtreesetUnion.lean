import Benchmark.Cases.Sdset.DuoUnion.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sdset

namespace Benchmark.Cases.Sdset.DuoUnion

/-- The extracted `Iterator::next` of `UnionIter<i32>`. -/
abbrev nxt := duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next core.I32.Insts.CoreCmpOrd

/-- Merge model of `UnionIter` (duplicates across the inputs emitted once). -/
def umerge : List Std.I32 → List Std.I32 → List Std.I32
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x.val < y.val then x :: umerge xs (y :: ys)
    else if x.val = y.val then x :: umerge xs ys
    else y :: umerge (x :: xs) ys

theorem is_empty_eq {T : Type} (s : Slice T) :
    core.slice.Slice.is_empty s = ok (s.val.isEmpty) := by
  simp only [core.slice.Slice.is_empty, core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  congr 1
  have : (Slice.len s = 0#usize) ↔ s.val = [] := by
    rw [UScalar.eq_equiv]; simp [Slice.len]
  by_cases h : s.val = []
  · simp [h, this.mpr h]
  · have h2 : ¬ (Slice.len s = 0#usize) := fun h' => h (this.mp h')
    simp [h, h2]

theorem idx1 {T : Type} (s : Slice T) (x : T) (xs : List T) (h : s.val = x :: xs) :
    ∃ hl, core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
      { start := 1#usize } = ok ⟨xs, hl⟩ := by
  obtain ⟨l, hl⟩ := s
  subst h
  refine ⟨by simp at hl; scalar_tac, ?_⟩
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, Slice.len]

/-- `UnionIter` over `(a, b)` collects to `umerge a b` (no sortedness needed). -/
theorem collects_umerge (n : Nat) : ∀ (a b : Slice Std.I32), a.val.length + b.val.length ≤ n →
    CollectsTo nxt ⟨a, b⟩ (umerge a.val b.val) := by
  induction n with
  | zero =>
    intro a b h
    obtain ⟨la, ha⟩ := a
    obtain ⟨lb, hb⟩ := b
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      is_empty_eq, core.slice.Slice.first, core.option.Option.is_some]
  | succ n ih =>
    intro a b h
    obtain ⟨la, ha⟩ := a
    obtain ⟨lb, hb⟩ := b
    cases la with
    | nil =>
      cases lb with
      | nil =>
        simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
          is_empty_eq, core.slice.Slice.first, core.option.Option.is_some]
      | cons y ys =>
        obtain ⟨hl, hidx⟩ := idx1 ⟨y :: ys, hb⟩ y ys rfl
        have := ih ⟨[], ha⟩ ⟨ys, hl⟩ (by simp at h ⊢; omega)
        simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
          is_empty_eq, core.slice.Slice.first, core.option.Option.is_some, hidx,
          rust_primitives.slice.slice_index, Slice.index_usize] at this ⊢
        exact this
    | cons x xs =>
      obtain ⟨hla, hidxa⟩ := idx1 ⟨x :: xs, ha⟩ x xs rfl
      cases lb with
      | nil =>
        have := ih ⟨xs, hla⟩ ⟨[], hb⟩ (by simp at h ⊢; omega)
        simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
          is_empty_eq, core.slice.Slice.first, core.option.Option.is_some, hidxa,
          rust_primitives.slice.slice_index, Slice.index_usize] at this ⊢
        cases xs <;> simpa [umerge] using this
      | cons y ys =>
        obtain ⟨hlb, hidxb⟩ := idx1 ⟨y :: ys, hb⟩ y ys rfl
        rcases lt_trichotomy x.val y.val with hxy | hxy | hxy
        · have := ih ⟨xs, hla⟩ ⟨y :: ys, hb⟩ (by simp at h ⊢; omega)
          have hc : compare x.val y.val = Ordering.lt := compare_lt_iff_lt.mpr hxy
          simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
            is_empty_eq, core.slice.Slice.first, core.option.Option.is_some, hidxa, hidxb,
            rust_primitives.slice.slice_index, Slice.index_usize, core.I32.Insts.CoreCmpOrd, core.mkIOrd,
            hxy, hc] at this ⊢
          exact this
        · have := ih ⟨xs, hla⟩ ⟨ys, hlb⟩ (by simp at h ⊢; omega)
          simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
            is_empty_eq, core.slice.Slice.first, core.option.Option.is_some, hidxa, hidxb,
            rust_primitives.slice.slice_index, Slice.index_usize, core.I32.Insts.CoreCmpOrd, core.mkIOrd, hxy] at this ⊢
          exact this
        · have := ih ⟨x :: xs, ha⟩ ⟨ys, hlb⟩ (by simp at h ⊢; omega)
          have hn : ¬ x.val < y.val := by omega
          have hn2 : ¬ x.val = y.val := by omega
          have hc : compare x.val y.val = Ordering.gt := compare_gt_iff_gt.mpr hxy
          simp [umerge, CollectsTo, nxt, duo.union.UnionIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
            is_empty_eq, core.slice.Slice.first, core.option.Option.is_some, hidxa, hidxb,
            rust_primitives.slice.slice_index, Slice.index_usize, core.I32.Insts.CoreCmpOrd, core.mkIOrd, hc, hn, hn2] at this ⊢
          exact this


theorem umerge_mem (a b : List Std.I32) (z : Int) :
    z ∈ (umerge a b).map (·.val) ↔ z ∈ a.map (·.val) ∨ z ∈ b.map (·.val) := by
  fun_induction umerge a b with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih =>
    simp only [List.map_cons, List.mem_cons] at ih ⊢
    rw [ih]; tauto
  | case4 x xs y ys hxy heq ih =>
    simp only [List.map_cons, List.mem_cons] at ih ⊢
    rw [ih]; constructor
    · tauto
    · rintro ((h | h) | (h | h)) <;> first | tauto | (left; omega)
  | case5 x xs y ys hxy heq ih =>
    simp only [List.map_cons, List.mem_cons] at ih ⊢
    rw [ih]; tauto

theorem umerge_sorted (a b : List Std.I32)
    (ha : (a.map (·.val)).Pairwise (· < ·)) (hb : (b.map (·.val)).Pairwise (· < ·)) :
    ((umerge a b).map (·.val)).Pairwise (· < ·) := by
  fun_induction umerge a b with
  | case1 ys => exact hb
  | case2 x xs => exact ha
  | case3 x xs y ys hxy ih =>
    have ha' := ha
    have hb' := hb
    rw [List.map_cons, List.pairwise_cons] at ha' hb'
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun z hz => ?_, ih ha'.2 hb⟩
    rcases (umerge_mem _ _ z).mp hz with h | h
    · exact ha'.1 z h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · omega
      · have := hb'.1 z h; omega
  | case4 x xs y ys hxy heq ih =>
    have ha' := ha
    have hb' := hb
    rw [List.map_cons, List.pairwise_cons] at ha' hb'
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun z hz => ?_, ih ha'.2 hb'.2⟩
    rcases (umerge_mem _ _ z).mp hz with h | h
    · exact ha'.1 z h
    · have := hb'.1 z h; omega
  | case5 x xs y ys hxy heq ih =>
    have ha' := ha
    have hb' := hb
    rw [List.map_cons, List.pairwise_cons] at ha' hb'
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun z hz => ?_, ih ha hb'.2⟩
    rcases (umerge_mem _ _ z).mp hz with h | h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · omega
      · have := ha'.1 z h; omega
    · exact hb'.1 z h

theorem umerge_eq_sort (a b : List Std.I32)
    (ha : (a.map (·.val)).Pairwise (· < ·)) (hb : (b.map (·.val)).Pairwise (· < ·)) :
    (umerge a b).map (·.val) = btreeset_union_vec a b := by
  unfold btreeset_union_vec
  apply List.SortedLT.eq_of_mem_iff
  · exact List.sortedLT_iff_pairwise.mpr (umerge_sorted a b ha hb)
  · exact Finset.sortedLT_sort _
  · intro z
    rw [Finset.mem_sort, Finset.mem_union, List.mem_toFinset, List.mem_toFinset, umerge_mem]

/--
For any two sorted, deduplicated `i32` slices `a` and `b`, iterating
`Union { a, b }` (`into_iter`, then `next` until `None`, i.e. `collect`) never
panics and yields exactly the elements of the `BTreeSet` union of `a` and `b`,
in increasing order.
-/
theorem union_iter_matches_btreeset_union (a b : Slice Std.I32)
    (h_a : a.val.Pairwise (fun x y => x.val < y.val))
    (h_b : b.val.Pairwise (fun x y => x.val < y.val)) :
    union_iter_matches_btreeset_union_spec a b := by
  unfold union_iter_matches_btreeset_union_spec
  simp only [duo.union.Union.Insts.CoreIterTraitsCollectIntoIteratorSharedATUnionIter.into_iter,
    duo.union.Union.iter, spec_ok]
  exact ⟨umerge a.val b.val, collects_umerge _ a b le_rfl,
    umerge_eq_sort _ _ (List.pairwise_map.mpr h_a) (List.pairwise_map.mpr h_b)⟩

end Benchmark.Cases.Sdset.DuoUnion
