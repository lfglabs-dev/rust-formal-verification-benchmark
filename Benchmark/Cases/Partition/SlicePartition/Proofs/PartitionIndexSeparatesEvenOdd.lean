import Benchmark.Cases.Partition.SlicePartition.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open partition

namespace Benchmark.Cases.Partition.SlicePartition

/-! Reference proof.

`partition_index` is a Hoare-style two-pointer loop. `pi_inner0` proves the
inner `while r > 0 && !pred(data[r]) { r -= 1 }` loop (strong induction on `r`,
unfolding `loop` with `loop.eq_1` via `pi_loop_cont` / `pi_loop_done`);
`pi_outer` proves the outer loop by strong induction on the measure
`2 * (len + r - l) + [data[l] is not an even element below len]`, with the
invariant: `data` is a permutation of the input (`pi_perm_set_set`, via
`List.perm_iff_count` / `List.count_set`), `data[..l]` is even and
`data[r+1..len]` is odd. On exit `data[..l]` is even and `data[l..]` odd, so
`filter` of the input is a permutation of `take`/`drop` (`pi_evens_odds`), and
sorted permutations coincide (`List.Perm.eq_of_pairwise`,
`List.pairwise_mergeSort`).
-/

theorem pi_usize_add_ok (a b : Std.Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ z : Std.Usize, a + b = ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (spec_of_partialSpec (@Usize.add_spec a b)
    (by intro e; cases e <;> simp <;> omega) (by simp))
  exact ⟨z, hz, hv⟩

theorem pi_usize_sub_ok (a b : Std.Usize) (h : b.val ≤ a.val) :
    ∃ z : Std.Usize, a - b = ok z ∧ z.val = a.val - b.val := by
  obtain ⟨z, hz, hv, _⟩ := spec_imp_exists (spec_of_partialSpec (@Usize.sub_spec a b)
    (by intro e; cases e <;> simp <;> omega) (by simp))
  exact ⟨z, hz, hv⟩

theorem pi_index_ok {α : Type} [Inhabited α] (v : Slice α) (i : Std.Usize) (h : i.val < v.length) :
    Slice.index_usize v i = ok (v.val[i.val]!) := by
  have h' : i.val < v.val.length := h
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, h']

theorem pi_swap_ok {α : Type} [Inhabited α] (s : Slice α) (a b : Std.Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    ∃ s' : Slice α, core.slice.Slice.swap s a b = ok s' ∧
      s'.val = (s.val.set a.val (s.val[b.val]!)).set b.val (s.val[a.val]!) := by
  have ha' : a.val < s.val.length := ha
  have hb' : b.val < s.val.length := hb
  simp only [core.slice.Slice.swap, rust_primitives.slice.slice_swap, pi_index_ok s a ha,
    pi_index_ok s b hb, bind_tc_ok]
  simp [Slice.update, ha', hb']

theorem pi_perm_set_set {α : Type} [DecidableEq α] [Inhabited α] (l : List α) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]!).set j l[i]!).Perm l := by
  rw [List.perm_iff_count]
  intro b
  have hj' : j < (l.set i l[j]!).length := by simpa using hj
  rw [List.count_set hj', List.count_set hi]
  have hget : (l.set i l[j]!)[j] = l[j]! := by
    rw [List.getElem_set]
    split
    · rfl
    · simp [hj]
  rw [hget]
  have hA : (if (l[i] == b) = true then 1 else 0) ≤ List.count b l := by
    split
    · rename_i h
      have : l[i] = b := by simpa using h
      exact List.count_pos_iff.mpr (this ▸ List.getElem_mem hi)
    · omega
  have hli : l[i]! = l[i] := by simp [hi]
  rw [hli]
  split <;> split <;> simp_all

theorem pi_loop_cont {α β : Type} {body : α → RustM (ControlFlow α β)} {x x' : α}
    (h : body x = ok (.cont x')) : loop body x = loop body x' := by
  rw [loop.eq_1, h]

theorem pi_loop_done {α β : Type} {body : α → RustM (ControlFlow α β)} {x : α} {y : β}
    (h : body x = ok (.done y)) : loop body x = ok y := by
  rw [loop.eq_1, h]

theorem pi_inner0 {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data : Slice Std.U32) :
    ∀ n (r : Std.Usize), r.val = n → r.val < data.length →
    ∃ r1 : Std.Usize, partition_index_loop0_loop0 inst data pred r = ok r1 ∧
      r1.val ≤ r.val ∧ (r1.val = 0 ∨ data.val[r1.val]!.val % 2 = 0) ∧
      ∀ i, r1.val < i → i ≤ r.val → data.val[i]!.val % 2 ≠ 0 := by
  unfold IsEvenPredicate at h_pred
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r hrn hr
  have hdef : partition_index_loop0_loop0 inst data pred r =
      loop (fun r1 => partition_index_loop0_loop0.body inst data pred r1) r := rfl
  by_cases h0 : 0 < r.val
  · have hgt : (r > 0#usize) := by scalar_tac
    by_cases hev : data.val[r.val]!.val % 2 = 0
    · have hb : partition_index_loop0_loop0.body inst data pred r = ok (.done r) := by
        simp only [partition_index_loop0_loop0.body, hgt, if_true, pi_index_ok data r hr,
          bind_tc_ok, h_pred, hev, decide_true]
      rw [hdef, pi_loop_done hb]
      exact ⟨r, rfl, le_refl _, Or.inr hev, fun i h1 h2 => by omega⟩
    · obtain ⟨r', hr', hv⟩ := pi_usize_sub_ok r 1#usize (by simp; omega)
      have hb : partition_index_loop0_loop0.body inst data pred r = ok (.cont r') := by
        simp only [partition_index_loop0_loop0.body, hgt, if_true, pi_index_ok data r hr,
          bind_tc_ok, h_pred, hev, decide_false, Bool.false_eq_true, if_false, hr']
      obtain ⟨r1, h1, h2, h3, h4⟩ :=
        ih (n - 1) (by omega) r' (by simp at hv; omega) (by simp at hv; omega)
      rw [hdef, pi_loop_cont hb]
      refine ⟨r1, h1, by simp at hv; omega, h3, ?_⟩
      intro i hi1 hi2
      by_cases hir : i = r.val
      · subst hir; exact hev
      · exact h4 i hi1 (by simp at hv; omega)
  · have hng : ¬ (r > 0#usize) := by scalar_tac
    have hb : partition_index_loop0_loop0.body inst data pred r = ok (.done r) := by
      simp only [partition_index_loop0_loop0.body, hng, if_false]
    rw [hdef, pi_loop_done hb]
    exact ⟨r, rfl, le_refl _, Or.inl (by omega), fun i h1 h2 => by omega⟩

theorem pi_inner1_eq {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (data : Slice Std.U32) (r : Std.Usize) :
    partition_index_loop0_loop1 inst data pred r = partition_index_loop0_loop0 inst data pred r := rfl

theorem pi_get_set_set {α : Type} [Inhabited α] (L : List α) (a b i : Nat) (x y : α)
    (ha : a < L.length) (hb : b < L.length) :
    ((L.set a x).set b y)[i]! = if i = b then y else if i = a then x else L[i]! := by
  by_cases hi : i < L.length
  · have hi1 : i < (L.set a x).length := by simpa using hi
    have hi2 : i < ((L.set a x).set b y).length := by simpa using hi
    rw [getElem!_pos ((L.set a x).set b y) i hi2, List.getElem_set, getElem!_pos L i hi]
    split
    · simp_all
    · rw [List.getElem_set]
      split <;> simp_all [eq_comm]
  · have hne1 : i ≠ b := by omega
    have hne2 : i ≠ a := by omega
    simp only [hne1, hne2, if_false]
    rw [getElem!_neg ((L.set a x).set b y) i (by simpa using hi), getElem!_neg L i hi]

theorem pi_outer {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data0 : Slice Std.U32) (len : Std.Usize) :
    ∀ n (d : Slice Std.U32) (l r : Std.Usize),
    2 * (len.val + r.val - l.val) +
      (if l.val < len.val ∧ d.val[l.val]!.val % 2 = 0 then 0 else 1) = n →
    d.val.Perm data0.val → len.val = d.length → l.val ≤ len.val → r.val < len.val →
    (∀ i, i < l.val → d.val[i]!.val % 2 = 0) →
    (∀ i, r.val < i → i < len.val → d.val[i]!.val % 2 ≠ 0) →
    ∃ res : Std.Usize × Slice Std.U32, partition_index_loop0 inst d pred len l r = ok res ∧
      res.2.val.Perm data0.val ∧ res.1.val ≤ len.val ∧ len.val = res.2.length ∧
      (∀ i, i < res.1.val → res.2.val[i]!.val % 2 = 0) ∧
      (∀ i, res.1.val ≤ i → i < len.val → res.2.val[i]!.val % 2 ≠ 0) := by
  have h_pred' := h_pred
  unfold IsEvenPredicate at h_pred'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d l r hn hperm hlen hl hr hev_lo hodd_hi
  have hdef : partition_index_loop0 inst d pred len l r =
      loop (fun (data1, l1, r1) => partition_index_loop0.body inst pred len data1 l1 r1)
        (d, l, r) := rfl
  have hrd : r.val < d.length := by omega
  obtain ⟨r1, hr1, hr1le, hr1ev, hr1odd⟩ := pi_inner0 inst pred h_pred d r.val r rfl hrd
  by_cases hlt : l.val < len.val
  · have hltU : l < len := by scalar_tac
    have hld : l.val < d.length := by omega
    by_cases hev : d.val[l.val]!.val % 2 = 0
    · obtain ⟨l', hl', hl'v⟩ := pi_usize_add_ok l 1#usize (by scalar_tac)
      have hb : (fun (x : Slice Std.U32 × Std.Usize × Std.Usize) => match x with
          | (data1, l1, r1) => partition_index_loop0.body inst pred len data1 l1 r1) (d, l, r) =
          ok (.cont (d, l', r)) := by
        simp only [partition_index_loop0.body, hltU, if_true, pi_index_ok d l hld, bind_tc_ok,
          h_pred', hev, decide_true, hl']
      rw [hdef, pi_loop_cont hb]
      have hl'v' : l'.val = l.val + 1 := by simpa using hl'v
      have hc : (if l'.val < len.val ∧ d.val[l'.val]!.val % 2 = 0 then 0 else 1) ≤ 1 := by
        split <;> omega
      have hn' : n = 2 * (len.val + r.val - l.val) := by
        rw [← hn, if_pos ⟨hlt, hev⟩]; rfl
      obtain ⟨res, h1, h2⟩ := ih _ (by omega) d l' r rfl hperm hlen (by omega) hr
        (by
          intro i hi
          by_cases hil : i = l.val
          · subst hil; exact hev
          · exact hev_lo i (by omega))
        hodd_hi
      exact ⟨res, h1, h2⟩
    · by_cases hge : r1.val ≤ l.val
      · have hgeU : l >= r1 := by scalar_tac
        have hb : (fun (x : Slice Std.U32 × Std.Usize × Std.Usize) => match x with
            | (data1, l1, r1) => partition_index_loop0.body inst pred len data1 l1 r1) (d, l, r) =
            ok (.done (l, d)) := by
          simp only [partition_index_loop0.body, hltU, if_true, pi_index_ok d l hld, bind_tc_ok,
            h_pred', hev, decide_false, Bool.false_eq_true, if_false, hr1, hgeU]
        rw [hdef, pi_loop_done hb]
        refine ⟨(l, d), rfl, hperm, hl, hlen, hev_lo, ?_⟩
        intro i hi1 hi2
        dsimp only at hi1 hi2 ⊢
        by_cases h1 : r.val < i
        · exact hodd_hi i h1 hi2
        · by_cases h2 : r1.val < i
          · exact hr1odd i h2 (by omega)
          · have : i = l.val := by omega
            subst this; exact hev
      · have hgeU : ¬ (l >= r1) := by scalar_tac
        have hr1d : r1.val < d.length := by omega
        obtain ⟨d1, hd1, hd1v⟩ := pi_swap_ok d l r1 hld hr1d
        have hb : (fun (x : Slice Std.U32 × Std.Usize × Std.Usize) => match x with
            | (data1, l1, r1) => partition_index_loop0.body inst pred len data1 l1 r1) (d, l, r) =
            ok (.cont (d1, l, r1)) := by
          simp only [partition_index_loop0.body, hltU, if_true, pi_index_ok d l hld, bind_tc_ok,
            h_pred', hev, decide_false, Bool.false_eq_true, if_false, hr1, hgeU, hd1]
        rw [hdef, pi_loop_cont hb]
        have hr1ev' : d.val[r1.val]!.val % 2 = 0 := by
          rcases hr1ev with h | h
          · omega
          · exact h
        have hget : ∀ i, d1.val[i]! =
            if i = r1.val then d.val[l.val]! else if i = l.val then d.val[r1.val]! else d.val[i]! := by
          intro i; rw [hd1v]; exact pi_get_set_set d.val l.val r1.val i _ _ hld hr1d
        have hlen1 : d1.length = d.length := by
          show d1.val.length = d.val.length
          rw [hd1v]; simp
        have hperm1 : d1.val.Perm data0.val := by
          rw [hd1v]; exact (pi_perm_set_set d.val l.val r1.val hld hr1d).trans hperm
        have hn' : n = 2 * (len.val + r.val - l.val) + 1 := by
          rw [← hn, if_neg (fun h => hev h.2)]
        have hmeas : (if l.val < len.val ∧ d1.val[l.val]!.val % 2 = 0 then 0 else 1) = 0 := by
          have : d1.val[l.val]! = d.val[r1.val]! := by
            rw [hget]; simp [show l.val ≠ r1.val by omega]
          rw [if_pos ⟨hlt, by rw [this]; exact hr1ev'⟩]
        obtain ⟨res, h1, h2⟩ := ih _ (by omega) d1 l r1 rfl hperm1 (by omega) hl (by omega)
          (by
            intro i hi
            rw [hget]
            simp only [show i ≠ r1.val by omega, show i ≠ l.val by omega, if_false]
            exact hev_lo i hi)
          (by
            intro i hi1 hi2
            rw [hget]
            simp only [show i ≠ r1.val by omega, show i ≠ l.val by omega, if_false]
            by_cases h : r.val < i
            · exact hodd_hi i h hi2
            · exact hr1odd i hi1 (by omega))
        exact ⟨res, h1, h2⟩
  · have hltU : ¬ (l < len) := by scalar_tac
    have hgeU : l >= r1 := by scalar_tac
    have hb : (fun (x : Slice Std.U32 × Std.Usize × Std.Usize) => match x with
        | (data1, l1, r1) => partition_index_loop0.body inst pred len data1 l1 r1) (d, l, r) =
        ok (.done (l, d)) := by
      simp only [partition_index_loop0.body, hltU, if_false, pi_inner1_eq, hr1, bind_tc_ok, hgeU,
        if_true]
    rw [hdef, pi_loop_done hb]
    refine ⟨(l, d), rfl, hperm, hl, hlen, hev_lo, ?_⟩
    intro i hi1 hi2
    dsimp only at hi1 hi2
    omega

theorem pi_sort_eq_of_perm {a b : List Std.U32} (h : a.Perm b) : sortU32 a = sortU32 b := by
  unfold sortU32
  have htrans : ∀ x y z : Std.U32, decide (x.val ≤ y.val) = true → decide (y.val ≤ z.val) = true →
      decide (x.val ≤ z.val) = true := by
    intro x y z h1 h2; simp only [decide_eq_true_eq] at *; omega
  have htot : ∀ x y : Std.U32, (decide (x.val ≤ y.val) || decide (y.val ≤ x.val)) = true := by
    intro x y; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  apply List.Perm.eq_of_pairwise (le := fun x y => decide (x.val ≤ y.val) = true)
  · intro x y _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    exact (UScalar.eq_equiv x y).mpr (by omega)
  · exact List.pairwise_mergeSort htrans htot a
  · exact List.pairwise_mergeSort htrans htot b
  · exact (List.mergeSort_perm a _).trans (h.trans (List.mergeSort_perm b _).symm)

theorem pi_evens_odds (d : List Std.U32) (idx : Nat) (hidx : idx ≤ d.length)
    (hlo : ∀ i, i < idx → d[i]!.val % 2 = 0)
    (hhi : ∀ i, idx ≤ i → i < d.length → d[i]!.val % 2 ≠ 0) :
    evens d = d.take idx ∧ odds d = d.drop idx := by
  have hsplit : d = d.take idx ++ d.drop idx := (List.take_append_drop idx d).symm
  have htake : ∀ x ∈ d.take idx, x.val % 2 = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < idx := by simp at hi; omega
    rw [List.getElem_take]
    have := hlo i hi'
    rwa [getElem!_pos d i (by simp at hi; omega)] at this
  have hdrop : ∀ x ∈ d.drop idx, x.val % 2 ≠ 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_drop]
    simp at hi
    have := hhi (idx + i) (by omega) (by omega)
    rwa [getElem!_pos d (idx + i) (by omega)] at this
  constructor
  · unfold evens
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_eq_self.mpr (fun x hx => by simp [htake x hx]),
      List.filter_eq_nil_iff.mpr (fun x hx => by simp [hdrop x hx]), List.append_nil]
  · unfold odds
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun x hx => by simp [htake x hx]),
      List.filter_eq_self.mpr (fun x hx => by simp [hdrop x hx]), List.nil_append]

theorem pi_result {P : Type} (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data : Slice Std.U32) :
    ∃ res : Std.Usize × Slice Std.U32, partition_index inst data pred = ok res ∧
      res.2.val.Perm data.val ∧ res.1.val ≤ res.2.length ∧
      (∀ i, i < res.1.val → res.2.val[i]!.val % 2 = 0) ∧
      (∀ i, res.1.val ≤ i → i < res.2.length → res.2.val[i]!.val % 2 ≠ 0) := by
  unfold partition_index
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hlenv : (Slice.len data).val = data.length := Slice.len_val data
  by_cases h0 : Slice.len data = 0#usize
  · simp only [h0, if_true]
    have hl0 : data.length = 0 := by rw [← hlenv, h0]; rfl
    refine ⟨(0#usize, data), rfl, List.Perm.refl _, by simp, ?_, ?_⟩
    · intro i hi; simp at hi
    · intro i _ hi2; simp only at hi2; omega
  · have hpos : 0 < data.length := by
      rcases Nat.eq_zero_or_pos data.length with h | h
      · exfalso; apply h0; apply (UScalar.eq_equiv _ _).mpr; rw [hlenv, h]; rfl
      · exact h
    obtain ⟨r, hr, hrv⟩ := pi_usize_sub_ok (Slice.len data) 1#usize
      (by have h1 : (1#usize).val = 1 := rfl; rw [h1, hlenv]; omega)
    simp only [h0, if_false, hr, bind_tc_ok]
    have hrv' : r.val = data.length - 1 := by rw [hrv, hlenv]; rfl
    obtain ⟨res, hres, hp, hle, hlen, hlo, hhi⟩ :=
      pi_outer inst pred h_pred data (Slice.len data) _ data 0#usize r rfl (List.Perm.refl _)
        hlenv.symm (by simp) (by omega) (by intro i hi; simp at hi) (by
          intro i h1 h2; omega)
    refine ⟨res, hres, hp, by omega, hlo, ?_⟩
    intro i h1 h2
    exact hhi i h1 (by omega)

/--
Partitioning any `u32` slice in place with the predicate "is even" never
panics and returns an index `first_false ≤ len` such that the prefix
`data[..first_false]` of the rearranged slice holds exactly the even
elements of the original slice and the suffix `data[first_false..]` exactly
the odd ones (compared as sorted vectors, as the property test does).
-/
theorem partition_index_separates_even_odd {P : Type}
    (inst : core.ops.function.Fn P Std.U32 Bool) (pred : P)
    (h_pred : IsEvenPredicate inst pred) (data : Slice Std.U32) :
    partition_index_separates_even_odd_spec inst pred data := by
  unfold partition_index_separates_even_odd_spec
  obtain ⟨res, hres, hp, hle, hlo, hhi⟩ := pi_result inst pred h_pred data
  rw [hres, spec_ok]
  obtain ⟨he, ho⟩ := pi_evens_odds res.2.val res.1.val hle hlo hhi
  refine ⟨hle, ?_, ?_⟩
  · apply pi_sort_eq_of_perm
    rw [← he]
    exact (hp.symm.filter _)
  · apply pi_sort_eq_of_perm
    rw [← ho]
    exact (hp.symm.filter _)

end Benchmark.Cases.Partition.SlicePartition
