import Benchmark.Cases.Blue.ScrunchBinarySearch.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open scrunch

namespace Benchmark.Cases.Blue.ScrunchBinarySearch

theorem bs_index_ok (v : Slice Std.Usize) (x : Std.Usize) (h : x.val < v.length) :
    Slice.index_usize v x = ok (v.val[x.val]!) := by
  unfold Slice.index_usize
  simp [h]

theorem bs_sorted_lt_iff (l : List Std.Usize) (h : l.Pairwise (fun a b => a.val < b.val))
    (j k : Nat) (hj : j < l.length) (hk : k < l.length) :
    (l[j]!).val < (l[k]!).val ↔ j < k := by
  rw [List.pairwise_iff_getElem] at h
  rw [getElem!_pos l j hj, getElem!_pos l k hk]
  constructor
  · intro hlt
    rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · exact hjk
    · subst hjk; omega
    · have := h k j hk hj hjk; omega
  · intro hjk; exact h j k hj hk hjk

theorem bs_call_ok (elements : Slice Std.Usize)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i x : Std.Usize) (hx : x.val < elements.length) (hi : i.val < elements.length) :
    ProbeClosure.call ⟨elements, i⟩ x =
      ok (if x.val < i.val then core.cmp.Ordering.Less
          else if i.val < x.val then core.cmp.Ordering.Greater
          else core.cmp.Ordering.Equal) := by
  unfold ProbeClosure.call
  simp only [bs_index_ok _ _ hx, bs_index_ok _ _ hi, bind_tc_ok]
  simp only [core.Usize.Insts.CoreCmpOrd, core.mkUOrd]
  have h1 := bs_sorted_lt_iff elements.val h_sorted x.val i.val hx hi
  have h2 := bs_sorted_lt_iff elements.val h_sorted i.val x.val hi hx
  generalize ha : elements.val[x.val]! = a at h1 h2 ⊢
  generalize hb : elements.val[i.val]! = b at h1 h2 ⊢
  rcases Nat.lt_trichotomy x.val i.val with hxi | hxi | hxi
  · rw [Nat.compare_eq_lt.2 (h1.2 hxi)]
    simp [hxi]
  · have hxi' : x = i := by scalar_tac
    subst hxi'
    obtain rfl : a = b := ha.symm.trans hb
    rw [Nat.compare_eq_eq.2 rfl]
    simp
  · have hn : ¬ x.val < i.val := by omega
    rw [Nat.compare_eq_gt.2 (h2.2 hxi)]
    simp [hn, hxi]

theorem bs_body_spec (elements : Slice Std.Usize)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize) (hi : i.val < elements.length)
    (l r : Std.Usize)
    (hl : l.val ≤ i.val) (hr : i.val ≤ r.val) (hrl : r.val < elements.length)
    (P : Post (ControlFlow (ProbeClosure × Std.Usize × Std.Usize) Std.Usize))
    (hdone : ∀ y : Std.Usize, y.val = i.val → P (.done y))
    (hcont : ∀ l' r' : Std.Usize, l'.val ≤ i.val → i.val ≤ r'.val → r'.val < elements.length →
      r'.val - l'.val < r.val - l.val → P (.cont (⟨elements, i⟩, l', r'))) :
    binary_search.binary_search_by_loop.body ProbeClosure.Insts.FnMut ⟨elements, i⟩ l r ⦃ P ⦄ := by
  simp only [binary_search.binary_search_by_loop.body]
  split
  · rename_i hlr
    have hlr' : l.val < r.val := hlr
    step as ⟨d, hd⟩
    step as ⟨h, hh⟩
    step as ⟨mid, hmid⟩
    have hmid1 : l.val ≤ mid.val := by scalar_tac
    have hmid2 : mid.val < r.val := by scalar_tac
    have hcall := bs_call_ok elements h_sorted i mid (by omega) hi
    simp only [ProbeClosure.Insts.FnMut, hcall, bind_tc_ok]
    by_cases h1 : mid.val < i.val
    · simp only [h1, ↓reduceIte, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
      change (do
          let left1 ← mid + 1#usize
          ok (ControlFlow.cont ((⟨elements, i⟩ : ProbeClosure), left1, r))) ⦃ P ⦄
      step as ⟨l1, hl1⟩
      exact hcont l1 r (by omega) hr hrl (by omega)
    · by_cases h2 : i.val < mid.val
      · simp only [h1, h2, ↓reduceIte, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
        exact hcont l mid hl (by omega) (by omega) (by omega)
      · simp only [h1, h2, ↓reduceIte, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
        exact hdone mid (by omega)
  · rename_i hlr
    have hlr' : ¬ l.val < r.val := hlr
    simp only [WP.spec_ok]
    exact hdone l (by omega)

theorem bs_loop_spec (elements : Slice Std.Usize)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize) (hi : i.val < elements.length)
    (left right : Std.Usize)
    (hl : left.val ≤ i.val) (hr : i.val ≤ right.val) (hrl : right.val < elements.length) :
    binary_search.binary_search_by_loop ProbeClosure.Insts.FnMut ⟨elements, i⟩ left right
      ⦃ r => r.val = i.val ⦄ := by
  unfold binary_search.binary_search_by_loop
  apply loop.spec_decr_nat (measure := fun p => p.2.2.val - p.2.1.val)
    (inv := fun p => p.1 = ⟨elements, i⟩ ∧ p.2.1.val ≤ i.val ∧ i.val ≤ p.2.2.val ∧
      p.2.2.val < elements.length)
  · rintro ⟨c, l, r⟩ ⟨hc, hl, hr, hrl⟩
    simp only at hc hl hr hrl
    rw [hc]
    apply bs_body_spec elements h_sorted i hi l r hl hr hrl
    · intro y hy
      exact hy
    · intro l' r' h1 h2 h3 h4
      exact ⟨⟨rfl, h1, h2, h3⟩, h4⟩
  · exact ⟨rfl, hl, hr, hrl⟩

theorem bs_partition_point (elements : Slice Std.Usize)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize) (hi : i.val < elements.length) :
    partitionPointLt elements (elements.val[i.val]!) = i.val := by
  unfold partitionPointLt
  have hi' : i.val < elements.val.length := hi
  rw [List.findIdx_eq hi', getElem!_pos elements.val i.val hi']
  constructor
  · simp
  · intro j hj
    have hlt := (bs_sorted_lt_iff elements.val h_sorted j i.val (by omega) hi').2 hj
    rw [getElem!_pos elements.val j (by omega), getElem!_pos elements.val i.val hi'] at hlt
    simp [hlt]

/--
For a strictly increasing `usize` vector `elements` and any position `i`,
`binary_search_by(0, elements.len() - 1, |x| elements[x].cmp(&elements[i]))`
never panics and returns `i`, which is also the partition point of
`|x| *x < elements[i]`.
-/
theorem binary_search_finds_index (elements : Slice Std.Usize)
    (h_len : elements.length < 64)
    (h_sorted : elements.val.Pairwise (fun a b => a.val < b.val))
    (i : Std.Usize)
    (h_i : i.val < elements.length) :
    binary_search_finds_index_spec elements i := by
  have hpp := bs_partition_point elements h_sorted i h_i
  unfold binary_search_finds_index_spec
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hn : (Slice.len elements).val = elements.length := Slice.len_val elements
  step as ⟨last, hlast⟩
  unfold binary_search.binary_search_by
  apply spec_mono (bs_loop_spec elements h_sorted i h_i 0#usize last (by simp) (by omega) (by omega))
  intro r hr
  exact ⟨hpp, by rw [hpp, hr]⟩

end Benchmark.Cases.Blue.ScrunchBinarySearch
