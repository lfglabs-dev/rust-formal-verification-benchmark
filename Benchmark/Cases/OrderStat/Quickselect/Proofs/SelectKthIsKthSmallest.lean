import Benchmark.Cases.OrderStat.Quickselect.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open order_stat

namespace Benchmark.Cases.OrderStat.Quickselect

/-! Reference proof.

Strong induction on the slice length over the `partial_fixpoint` equation
`quickselect.select.eq_1`. Loops are unfolded with `loop.eq_1`
(`qs_loop_cont` / `qs_loop_done`); the pair-destructuring `let (o, iter1) ←
Range::next ..` of each loop body is reduced by stating the reduced body and
closing with `rfl` (`qs_inner_body_lt`, ...), since `simp` does not reduce
these matches here. Invariants:
* base case (`len < 5`, nested exchange loops `qs_inner` / `qs_outer`): the
  result is a permutation and `x[a] ≤ x[b]` for all `a < i`, `a < b`;
  hence fully sorted;
* Lomuto `partition` (`qs_ploop`, `qs_partition`): `y[..store] < pivot ≤
  y[store..load]`; afterwards `x2[..st] < x2[st] ≤ x2[st+1..]`;
* recursion: the recursive call permutes the prefix/suffix
  (`qs_index_mut_to` / `qs_index_mut_from`, `List.setSlice!`), so every
  element keeps its side of the pivot.
Result: `x'[a] ≤ x'[k] ≤ x'[b]` for `a < k < b`; `qs_sorted_kth` turns this
into `(mergeSort x')[k] = x'[k]` by counting elements `< x'[k]` / `≤ x'[k]`
(`List.Perm.countP_eq`, `List.pairwise_mergeSort`). Swaps are permutations
by `List.perm_iff_count` + `List.count_set`.
-/

theorem qs_usize_add_ok (a b : Std.Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ z : Std.Usize, a + b = ok z ∧ z.val = a.val + b.val := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (spec_of_partialSpec (@Usize.add_spec a b)
    (by intro e; cases e <;> simp <;> omega) (by simp))
  exact ⟨z, hz, hv⟩

theorem qs_usize_sub_ok (a b : Std.Usize) (h : b.val ≤ a.val) :
    ∃ z : Std.Usize, a - b = ok z ∧ z.val = a.val - b.val := by
  obtain ⟨z, hz, hv, _⟩ := spec_imp_exists (spec_of_partialSpec (@Usize.sub_spec a b)
    (by intro e; cases e <;> simp <;> omega) (by simp))
  exact ⟨z, hz, hv⟩

theorem qs_index_ok {α : Type} [Inhabited α] (v : Slice α) (i : Std.Usize) (h : i.val < v.length) :
    Slice.index_usize v i = ok (v.val[i.val]!) := by
  have h' : i.val < v.val.length := h
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, h']

theorem qs_swap_ok {α : Type} [Inhabited α] (s : Slice α) (a b : Std.Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    ∃ s' : Slice α, core.slice.Slice.swap s a b = ok s' ∧
      s'.val = (s.val.set a.val (s.val[b.val]!)).set b.val (s.val[a.val]!) := by
  have ha' : a.val < s.val.length := ha
  have hb' : b.val < s.val.length := hb
  simp only [core.slice.Slice.swap, rust_primitives.slice.slice_swap, qs_index_ok s a ha,
    qs_index_ok s b hb, bind_tc_ok]
  simp [Slice.update, ha', hb']

theorem qs_perm_set_set {α : Type} [DecidableEq α] [Inhabited α] (l : List α) (i j : Nat)
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

theorem qs_get_set_set {α : Type} [Inhabited α] (L : List α) (a b i : Nat) (x y : α)
    (ha : a < L.length) (hb : b < L.length) :
    ((L.set a x).set b y)[i]! = if i = b then y else if i = a then x else L[i]! := by
  by_cases hi : i < L.length
  · have hi2 : i < ((L.set a x).set b y).length := by simpa using hi
    rw [getElem!_pos ((L.set a x).set b y) i hi2, List.getElem_set, getElem!_pos L i hi]
    split
    · simp_all
    · rw [List.getElem_set]
      split <;> simp_all [eq_comm]
  · have hne1 : i ≠ b := by omega
    have hne2 : i ≠ a := by omega
    simp only [hne1, hne2, if_false]
    rw [getElem!_neg ((L.set a x).set b y) i (by simpa using hi), getElem!_neg L i hi]

theorem qs_loop_cont {α β : Type} {body : α → RustM (ControlFlow α β)} {x x' : α}
    (h : body x = ok (.cont x')) : loop body x = loop body x' := by
  rw [loop.eq_1, h]

theorem qs_loop_done {α β : Type} {body : α → RustM (ControlFlow α β)} {x : α} {y : β}
    (h : body x = ok (.done y)) : loop body x = ok y := by
  rw [loop.eq_1, h]

theorem qs_range_next_lt (i e : Std.Usize) (h : i.val < e.val) :
    ∃ i' : Std.Usize, i'.val = i.val + 1 ∧
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.Some i, { start := i', «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare i.val e.val = .lt := by simp [compare_lt_iff_lt, h]
  simp only [hc, bind_tc_ok, core.Usize.Insts.CoreCloneClone.clone,
    core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize]
  have hmax : i.val + (1#usize).val ≤ UScalar.max UScalarTy.Usize := by
    have := e.hmax; simp only [UScalar.max] at *; scalar_tac
  have := UScalar.overflowing_add_eq i 1#usize
  simp only [gt_iff_lt, Nat.not_lt.mpr hmax, if_false] at this
  obtain ⟨h1, h2⟩ := this
  generalize UScalar.overflowing_add i 1#usize = z at *
  obtain ⟨r, b⟩ := z
  simp only at h1 h2
  subst h2
  exact ⟨r, by simpa using h1, rfl⟩

theorem qs_range_next_ge (i e : Std.Usize) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

theorem qs_lt (a b : Std.I32) :
    core.I32.Insts.CoreCmpOrd.PartialOrdInst.lt a b = ok (decide (a.val < b.val)) := by
  simp only [core.I32.Insts.CoreCmpOrd, core.mkIOrd, core.mkIPartialOrd]
  by_cases h : a.val < b.val
  · have hc : compare a.val b.val = .lt := by simp [compare_lt_iff_lt, h]
    simp [hc, h]
  · have hc : compare a.val b.val ≠ .lt := by simp [compare_lt_iff_lt, h]
    split <;> simp_all



theorem qs_inner_body_lt (i j e : Std.Usize) (x : Slice Std.I32) (h : j.val < e.val) :
    ∃ j' : Std.Usize, j'.val = j.val + 1 ∧
    quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i { start := j, «end» := e } x =
      (do
        let t ← Slice.index_usize x j
        let t1 ← Slice.index_usize x i
        let b ← core.I32.Insts.CoreCmpOrd.PartialOrdInst.lt t t1
        if b then do
          let x1 ← core.slice.Slice.swap x i j
          ok (ControlFlow.cont ({ start := j', «end» := e }, x1))
        else ok (ControlFlow.cont ({ start := j', «end» := e }, x))) := by
  obtain ⟨j', hj', hn⟩ := qs_range_next_lt j e h
  refine ⟨j', hj', ?_⟩
  unfold quickselect.select_loop0_loop0.body
  simp only [hn, bind_tc_ok]
  rfl

theorem qs_inner_body_ge (i j e : Std.Usize) (x : Slice Std.I32) (h : ¬ j.val < e.val) :
    quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i { start := j, «end» := e } x =
      ok (ControlFlow.done x) := by
  unfold quickselect.select_loop0_loop0.body
  simp only [qs_range_next_ge j e h, bind_tc_ok]
  rfl

theorem qs_outer_body_lt (i e : Std.Usize) (x : Slice Std.I32) (h : i.val < e.val) :
    ∃ i' : Std.Usize, i'.val = i.val + 1 ∧
    quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd { start := i, «end» := e } x =
      (do
        let i1 ← i + 1#usize
        let i2 ← core.slice.Slice.len x
        let x1 ← quickselect.select_loop0_loop0 core.I32.Insts.CoreCmpOrd
          { start := i1, «end» := i2 } x i
        ok (ControlFlow.cont ({ start := i', «end» := e }, x1))) := by
  obtain ⟨i', hi', hn⟩ := qs_range_next_lt i e h
  refine ⟨i', hi', ?_⟩
  unfold quickselect.select_loop0.body
  simp only [hn, bind_tc_ok]
  rfl

theorem qs_outer_body_ge (i e : Std.Usize) (x : Slice Std.I32) (h : ¬ i.val < e.val) :
    quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd { start := i, «end» := e } x =
      ok (ControlFlow.done x) := by
  unfold quickselect.select_loop0.body
  simp only [qs_range_next_ge i e h, bind_tc_ok]
  rfl

theorem qs_part_body_lt (elem : Std.I32) (load e store : Std.Usize) (y : Slice Std.I32)
    (h : load.val < e.val) :
    ∃ load' : Std.Usize, load'.val = load.val + 1 ∧
    quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd elem { start := load, «end» := e }
      store y =
      (do
        let t ← Slice.index_usize y load
        let b ← core.I32.Insts.CoreCmpOrd.PartialOrdInst.lt t elem
        if b then do
          let y1 ← core.slice.Slice.swap y load store
          let store1 ← store + 1#usize
          ok (ControlFlow.cont ({ start := load', «end» := e }, store1, y1))
        else ok (ControlFlow.cont ({ start := load', «end» := e }, store, y))) := by
  obtain ⟨l', hl', hn⟩ := qs_range_next_lt load e h
  refine ⟨l', hl', ?_⟩
  unfold quickselect.partition_loop.body
  simp only [hn, bind_tc_ok]
  rfl

theorem qs_part_body_ge (elem : Std.I32) (load e store : Std.Usize) (y : Slice Std.I32)
    (h : ¬ load.val < e.val) :
    quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd elem { start := load, «end» := e }
      store y = ok (ControlFlow.done (store, y)) := by
  unfold quickselect.partition_loop.body
  simp only [qs_range_next_ge load e h, bind_tc_ok]
  rfl

theorem qs_inner (len i : Std.Usize) (hi : i.val < len.val) :
    ∀ n (j : Std.Usize) (x : Slice Std.I32), len.val - j.val = n → i.val < j.val →
    j.val ≤ len.val → x.length = len.val →
    (∀ a b, a < i.val → a < b → b < len.val → x.val[a]!.val ≤ x.val[b]!.val) →
    (∀ m, i.val < m → m < j.val → x.val[i.val]!.val ≤ x.val[m]!.val) →
    ∃ x', quickselect.select_loop0_loop0 core.I32.Insts.CoreCmpOrd
        { start := j, «end» := len } x i = ok x' ∧
      x'.val.Perm x.val ∧ x'.length = len.val ∧
      (∀ a b, a < i.val → a < b → b < len.val → x'.val[a]!.val ≤ x'.val[b]!.val) ∧
      (∀ m, i.val < m → m < len.val → x'.val[i.val]!.val ≤ x'.val[m]!.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j x hn hij hjl hx hA hB
  have hdef : quickselect.select_loop0_loop0 core.I32.Insts.CoreCmpOrd
      { start := j, «end» := len } x i =
      loop (fun (iter1, x1) => quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i
        iter1 x1) ({ start := j, «end» := len }, x) := rfl
  by_cases hjlt : j.val < len.val
  · obtain ⟨j', hj', hbody⟩ := qs_inner_body_lt i j len x hjlt
    have hjx : j.val < x.length := by omega
    have hix : i.val < x.length := by omega
    by_cases hlt : x.val[j.val]!.val < x.val[i.val]!.val
    · obtain ⟨x1, hx1, hx1v⟩ := qs_swap_ok x i j hix hjx
      have hb : (fun (p : core.ops.range.Range Std.Usize × Slice Std.I32) => match p with
          | (iter1, x1) => quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i iter1 x1)
          ({ start := j, «end» := len }, x) = ok (.cont ({ start := j', «end» := len }, x1)) := by
        show quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i
          { start := j, «end» := len } x = _
        simp only [hbody, qs_index_ok x j hjx, qs_index_ok x i hix, bind_tc_ok, qs_lt, hlt,
          decide_true, if_true, hx1]
      have hget : ∀ t, x1.val[t]! =
          if t = j.val then x.val[i.val]! else if t = i.val then x.val[j.val]! else x.val[t]! := by
        intro t; rw [hx1v]; exact qs_get_set_set x.val i.val j.val t _ _ hix hjx
      have hlen1 : x1.length = x.length := by
        show x1.val.length = x.val.length
        rw [hx1v]; simp
      have hperm1 : x1.val.Perm x.val := by
        rw [hx1v]; exact qs_perm_set_set x.val i.val j.val hix hjx
      obtain ⟨x', h1, h2, h3, h4, h5⟩ := ih (len.val - j'.val) (by omega) j' x1 rfl (by omega)
        (by omega) (by omega)
        (by
          intro a b ha hab hb
          rw [hget a, hget b]
          simp only [show a ≠ j.val by omega, show a ≠ i.val by omega, if_false]
          split
          · exact hA a i.val ha ha hi
          · split
            · exact hA a j.val ha (by omega) hjlt
            · exact hA a b ha hab hb)
        (by
          intro m hm1 hm2
          rw [hget i.val, hget m]
          simp only [show i.val ≠ j.val by omega, if_false, if_true]
          by_cases hmj : m = j.val
          · simp only [hmj, if_true]; omega
          · simp only [hmj, show m ≠ i.val by omega, if_false]
            have := hB m hm1 (by omega)
            omega)
      refine ⟨x', ?_, h2.trans hperm1, h3, h4, h5⟩
      rw [hdef, qs_loop_cont hb]
      exact h1
    · have hb : (fun (p : core.ops.range.Range Std.Usize × Slice Std.I32) => match p with
          | (iter1, x1) => quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i iter1 x1)
          ({ start := j, «end» := len }, x) = ok (.cont ({ start := j', «end» := len }, x)) := by
        show quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i
          { start := j, «end» := len } x = _
        simp only [hbody, qs_index_ok x j hjx, qs_index_ok x i hix, bind_tc_ok, qs_lt, hlt,
          decide_false, Bool.false_eq_true, if_false]
      obtain ⟨x', h1, h2, h3, h4, h5⟩ := ih (len.val - j'.val) (by omega) j' x rfl (by omega)
        (by omega) hx hA
        (by
          intro m hm1 hm2
          by_cases hmj : m = j.val
          · subst hmj; omega
          · exact hB m hm1 (by omega))
      refine ⟨x', ?_, h2, h3, h4, h5⟩
      rw [hdef, qs_loop_cont hb]
      exact h1
  · have hb : (fun (p : core.ops.range.Range Std.Usize × Slice Std.I32) => match p with
          | (iter1, x1) => quickselect.select_loop0_loop0.body core.I32.Insts.CoreCmpOrd i iter1 x1)
          ({ start := j, «end» := len }, x) = ok (.done x) := qs_inner_body_ge i j len x hjlt
    rw [hdef, qs_loop_done hb]
    refine ⟨x, rfl, List.Perm.refl _, hx, hA, ?_⟩
    intro m hm1 hm2
    exact hB m hm1 (by omega)

theorem qs_len_ok (x : Slice Std.I32) (len : Std.Usize) (h : x.length = len.val) :
    core.slice.Slice.len x = ok len := by
  unfold core.slice.Slice.len rust_primitives.slice.slice_length
  have : Slice.len x = len := (UScalar.eq_equiv _ _).mpr (by rw [Slice.len_val]; exact h)
  rw [this]

theorem qs_outer (len : Std.Usize) :
    ∀ n (i : Std.Usize) (x : Slice Std.I32), len.val - i.val = n → i.val ≤ len.val →
    x.length = len.val →
    (∀ a b, a < i.val → a < b → b < len.val → x.val[a]!.val ≤ x.val[b]!.val) →
    ∃ x', quickselect.select_loop0 core.I32.Insts.CoreCmpOrd { start := i, «end» := len } x = ok x' ∧
      x'.val.Perm x.val ∧ x'.length = len.val ∧
      (∀ a b, a < b → b < len.val → x'.val[a]!.val ≤ x'.val[b]!.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i x hn hil hx hA
  have hdef : quickselect.select_loop0 core.I32.Insts.CoreCmpOrd { start := i, «end» := len } x =
      loop (fun (iter1, x1) => quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd iter1 x1)
        ({ start := i, «end» := len }, x) := rfl
  by_cases hilt : i.val < len.val
  · obtain ⟨i', hi', hbody⟩ := qs_outer_body_lt i len x hilt
    obtain ⟨i1, hi1, hi1v⟩ := qs_usize_add_ok i 1#usize (by scalar_tac)
    have hi1v' : i1.val = i.val + 1 := by simpa using hi1v
    obtain ⟨x1, hx1, hp1, hl1, hA1, hB1⟩ := qs_inner len i hilt (len.val - i1.val) i1 x rfl
      (by omega) (by omega) hx hA (by intro m h1 h2; omega)
    have hb : (fun (p : core.ops.range.Range Std.Usize × Slice Std.I32) => match p with
        | (iter1, x1) => quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd iter1 x1)
        ({ start := i, «end» := len }, x) = ok (.cont ({ start := i', «end» := len }, x1)) := by
      show quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd { start := i, «end» := len } x = _
      rw [hbody]
      simp only [hi1, bind_tc_ok, qs_len_ok x len hx, hx1]
    obtain ⟨x', h1, h2, h3, h4⟩ := ih (len.val - i'.val) (by omega) i' x1 rfl (by omega) hl1
      (by
        intro a b ha hab hb
        by_cases hai : a = i.val
        · subst hai; exact hB1 b hab hb
        · exact hA1 a b (by omega) hab hb)
    refine ⟨x', ?_, h2.trans hp1, h3, h4⟩
    rw [hdef, qs_loop_cont hb]
    exact h1
  · have hb : (fun (p : core.ops.range.Range Std.Usize × Slice Std.I32) => match p with
        | (iter1, x1) => quickselect.select_loop0.body core.I32.Insts.CoreCmpOrd iter1 x1)
        ({ start := i, «end» := len }, x) = ok (.done x) := qs_outer_body_ge i len x hilt
    rw [hdef, qs_loop_done hb]
    exact ⟨x, rfl, List.Perm.refl _, hx, fun a b hab hb => hA a b (by omega) hab hb⟩

theorem qs_ploop (elem : Std.I32) (e : Std.Usize) :
    ∀ n (load store : Std.Usize) (y : Slice Std.I32), e.val - load.val = n →
    store.val ≤ load.val → load.val ≤ e.val → y.length = e.val →
    (∀ a, a < store.val → y.val[a]!.val < elem.val) →
    (∀ a, store.val ≤ a → a < load.val → elem.val ≤ y.val[a]!.val) →
    ∃ res : Std.Usize × Slice Std.I32,
      quickselect.partition_loop core.I32.Insts.CoreCmpOrd { start := load, «end» := e } store y
        elem = ok res ∧
      res.2.val.Perm y.val ∧ res.2.length = e.val ∧ res.1.val ≤ e.val ∧
      (∀ a, a < res.1.val → res.2.val[a]!.val < elem.val) ∧
      (∀ a, res.1.val ≤ a → a < e.val → elem.val ≤ res.2.val[a]!.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro load store y hn hsl hle hy hlo hhi
  have hdef : quickselect.partition_loop core.I32.Insts.CoreCmpOrd { start := load, «end» := e }
      store y elem =
      loop (fun (iter1, store1, y1) => quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd
        elem iter1 store1 y1) ({ start := load, «end» := e }, store, y) := rfl
  by_cases hlt : load.val < e.val
  · obtain ⟨load', hl', hbody⟩ := qs_part_body_lt elem load e store y hlt
    have hly : load.val < y.length := by omega
    have hsy : store.val < y.length := by omega
    by_cases hc : y.val[load.val]!.val < elem.val
    · obtain ⟨y1, hy1, hy1v⟩ := qs_swap_ok y load store hly hsy
      obtain ⟨s1, hs1, hs1v⟩ := qs_usize_add_ok store 1#usize (by scalar_tac)
      have hs1v' : s1.val = store.val + 1 := by simpa using hs1v
      have hb : (fun (p : core.ops.range.Range Std.Usize × Std.Usize × Slice Std.I32) =>
          match p with
          | (iter1, store1, y1) => quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd
              elem iter1 store1 y1) ({ start := load, «end» := e }, store, y) =
          ok (.cont ({ start := load', «end» := e }, s1, y1)) := by
        show quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd elem
          { start := load, «end» := e } store y = _
        rw [hbody]
        simp only [qs_index_ok y load hly, bind_tc_ok, qs_lt, hc, decide_true, if_true, hy1, hs1]
      have hget : ∀ t, y1.val[t]! =
          if t = store.val then y.val[load.val]! else if t = load.val then y.val[store.val]!
          else y.val[t]! := by
        intro t; rw [hy1v]; exact qs_get_set_set y.val load.val store.val t _ _ hly hsy
      have hlen1 : y1.length = y.length := by
        show y1.val.length = y.val.length
        rw [hy1v]; simp
      have hperm1 : y1.val.Perm y.val := by
        rw [hy1v]; exact qs_perm_set_set y.val load.val store.val hly hsy
      obtain ⟨res, h1, h2, h3, h4, h5, h6⟩ := ih (e.val - load'.val) (by omega) load' s1 y1 rfl
        (by omega) (by omega) (by omega)
        (by
          intro a ha
          rw [hget a]
          by_cases has : a = store.val
          · simp only [has, if_true]; exact hc
          · simp only [has, show a ≠ load.val by omega, if_false]
            exact hlo a (by omega))
        (by
          intro a ha1 ha2
          rw [hget a]
          simp only [show a ≠ store.val by omega, if_false]
          by_cases hal : a = load.val
          · simp only [hal, if_true]; exact hhi store.val (le_refl _) (by omega)
          · simp only [hal, if_false]; exact hhi a (by omega) (by omega))
      refine ⟨res, ?_, h2.trans hperm1, h3, h4, h5, h6⟩
      rw [hdef, qs_loop_cont hb]
      exact h1
    · have hb : (fun (p : core.ops.range.Range Std.Usize × Std.Usize × Slice Std.I32) =>
          match p with
          | (iter1, store1, y1) => quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd
              elem iter1 store1 y1) ({ start := load, «end» := e }, store, y) =
          ok (.cont ({ start := load', «end» := e }, store, y)) := by
        show quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd elem
          { start := load, «end» := e } store y = _
        rw [hbody]
        simp only [qs_index_ok y load hly, bind_tc_ok, qs_lt, hc, decide_false,
          Bool.false_eq_true, if_false]
      obtain ⟨res, h1, h2, h3, h4, h5, h6⟩ := ih (e.val - load'.val) (by omega) load' store y rfl
        (by omega) (by omega) hy hlo
        (by
          intro a ha1 ha2
          by_cases hal : a = load.val
          · subst hal; omega
          · exact hhi a ha1 (by omega))
      refine ⟨res, ?_, h2, h3, h4, h5, h6⟩
      rw [hdef, qs_loop_cont hb]
      exact h1
  · have hb : (fun (p : core.ops.range.Range Std.Usize × Std.Usize × Slice Std.I32) =>
        match p with
        | (iter1, store1, y1) => quickselect.partition_loop.body core.I32.Insts.CoreCmpOrd
            elem iter1 store1 y1) ({ start := load, «end» := e }, store, y) =
        ok (.done (store, y)) := qs_part_body_ge elem load e store y hlt
    rw [hdef, qs_loop_done hb]
    refine ⟨(store, y), rfl, List.Perm.refl _, hy, (by dsimp only; omega), hlo, ?_⟩
    intro a ha1 ha2
    exact hhi a ha1 (by omega)

theorem qs_get_append_left {α : Type} [Inhabited α] (L M : List α) (a : Nat) (h : a < L.length) :
    (L ++ M)[a]! = L[a]! := by
  rw [getElem!_pos (L ++ M) a (by simp; omega), getElem!_pos L a h, List.getElem_append_left]

theorem qs_get_append_right {α : Type} [Inhabited α] (L M : List α) (a : Nat) (h : L.length ≤ a)
    (h2 : a < L.length + M.length) :
    (L ++ M)[a]! = M[a - L.length]! := by
  rw [getElem!_pos (L ++ M) a (by simp; omega), getElem!_pos M (a - L.length) (by omega),
    List.getElem_append_right h]

theorem qs_partition (x : Slice Std.I32) (hx : 1 ≤ x.length) :
    ∃ (st : Std.Usize) (x2 : Slice Std.I32),
      quickselect.partition core.I32.Insts.CoreCmpOrd x = ok (st, x2) ∧
      x2.val.Perm x.val ∧ x2.length = x.length ∧ st.val < x.length ∧
      (∀ a, a < st.val → x2.val[a]!.val < x2.val[st.val]!.val) ∧
      (∀ a, st.val < a → a < x.length → x2.val[st.val]!.val ≤ x2.val[a]!.val) := by
  have hlen : core.slice.Slice.len x = ok (Slice.len x) := rfl
  have hlv : (Slice.len x).val = x.length := Slice.len_val x
  obtain ⟨i, hi, hiv⟩ := qs_usize_sub_ok (Slice.len x) 1#usize
    (by have h1 : (1#usize).val = 1 := rfl; rw [h1, hlv]; omega)
  have hiv' : i.val = x.length - 1 := by rw [hiv, hlv]; rfl
  -- split_at_mut
  obtain ⟨sp, hsp, hpost⟩ := spec_imp_exists (spec_of_partialSpec
    (Aeneas.Std.core.slice.Slice.split_at_mut.spec x i)
    (by intro e; cases e <;> simp <;> scalar_tac) (by simp))
  rcases sp with ⟨⟨y, elem⟩, back⟩
  simp only [uncurry'_pair] at hpost
  obtain ⟨hyl, hel, hyv, hev, hback⟩ := hpost
  have hsplit : core.slice.Slice.split_at_mut x i = ok ((y, elem), fun p => back p) := by
    unfold core.slice.Slice.split_at_mut rust_primitives.slice.slice_split_at_mut
    rw [hsp]
    rfl
  have hel1 : elem.length = 1 := by omega
  have he0 : (0#usize).val < elem.length := by have h0 : (0#usize).val = 0 := rfl; omega
  set p := elem.val[0]! with hp
  have hidx : Slice.index_mut_usize elem 0#usize = ok (p, Slice.set elem 0#usize) := by
    simp only [Slice.index_mut_usize, qs_index_ok elem 0#usize he0, bind_tc_ok]
    rfl
  obtain ⟨⟨st, y1⟩, hloop, hp1, hl1, hst, hlo, hhi⟩ := qs_ploop p i i.val 0#usize 0#usize y
    (by simp) (by simp) (by simp) hyl (by intro a ha; simp at ha) (by intro a h1 h2; simp at h2)
  simp only at hp1 hl1 hst hlo hhi
  have hstx : st.val < x.length := by omega
  set elem2 := Slice.set elem 0#usize p with helem2
  have helem2v : elem2.val = elem.val := by
    rw [helem2, Slice.set_val_eq, hp]
    have h0 : 0 < elem.val.length := by simpa using he0
    simp [h0]
  obtain ⟨hx1v, hx1l⟩ := hback y1 elem2 (by omega) (by
    show elem2.val.length + i.val = x.length
    rw [helem2v]; exact hel)
  set x1 := back (y1, elem2) with hx1
  have hx1v' : x1.val = y1.val ++ elem.val := by rw [hx1v, helem2v]
  obtain ⟨x2, hsw, hx2v⟩ := qs_swap_ok x1 st i (by omega) (by omega)
  have key : quickselect.partition core.I32.Insts.CoreCmpOrd x = ok (st, x2) := by
    unfold quickselect.partition
    rw [hlen, bind_tc_ok, hi, bind_tc_ok, hsplit, bind_tc_ok]
    show (do
      let (elem1, index_mut_back) ← Slice.index_mut_usize elem 0#usize
      let (store, y1) ← quickselect.partition_loop core.I32.Insts.CoreCmpOrd
        { start := 0#usize, «end» := i } 0#usize y elem1
      let elem2 := index_mut_back elem1
      let x1 := (fun p => back p) (y1, elem2)
      let i1 ← ok i
      let x2 ← core.slice.Slice.swap x1 store i1
      ok (store, x2)) = _
    rw [hidx, bind_tc_ok]
    show (do
      let (store, y1) ← quickselect.partition_loop core.I32.Insts.CoreCmpOrd
        { start := 0#usize, «end» := i } 0#usize y p
      let x1 := back (y1, Slice.set elem 0#usize p)
      let i1 ← ok i
      let x2 ← core.slice.Slice.swap x1 store i1
      ok (store, x2)) = _
    rw [hloop, bind_tc_ok]
    show (do
      let i1 ← ok i
      let x2 ← core.slice.Slice.swap x1 st i1
      ok (st, x2)) = _
    rw [bind_tc_ok, hsw, bind_tc_ok]
  have hx1len : x1.val.length = x.length := by
    rw [hx1v']; simp only [List.length_append]; show y1.length + elem.length = _; omega
  have hst1 : st.val < x1.val.length := by omega
  have hi1 : i.val < x1.val.length := by omega
  have hx2get : ∀ t, x2.val[t]! =
      if t = i.val then x1.val[st.val]! else if t = st.val then x1.val[i.val]! else x1.val[t]! := by
    intro t; rw [hx2v]; exact qs_get_set_set x1.val st.val i.val t _ _ hst1 hi1
  have hx1i : x1.val[i.val]! = p := by
    rw [hx1v', qs_get_append_right y1.val elem.val i.val (by show y1.length ≤ i.val; omega)
      (by show i.val < y1.length + elem.length; omega)]
    rw [hp]; congr 1; show i.val - y1.length = 0; omega
  have hx1y : ∀ a, a < i.val → x1.val[a]! = y1.val[a]! := by
    intro a ha
    rw [hx1v', qs_get_append_left y1.val elem.val a (by show a < y1.length; omega)]
  have hx2st : x2.val[st.val]! = p := by
    rw [hx2get]
    by_cases h : st.val = i.val
    · simp only [h, if_true]; exact hx1i
    · simp only [h, if_false, if_true]; exact hx1i
  refine ⟨st, x2, key, ?_, ?_, hstx, ?_, ?_⟩
  · rw [hx2v]
    refine (qs_perm_set_set x1.val st.val i.val hst1 hi1).trans ?_
    rw [hx1v']
    refine (hp1.append_right elem.val).trans ?_
    rw [hyv, hev, List.take_append_drop]
  · show x2.val.length = x.val.length
    rw [hx2v]; simp only [List.length_set]; exact hx1len
  · intro a ha
    rw [hx2st, hx2get]
    simp only [show a ≠ i.val by omega, show a ≠ st.val by omega, if_false]
    rw [hx1y a (by omega)]
    exact hlo a ha
  · intro a ha1 ha2
    rw [hx2st, hx2get]
    by_cases hai : a = i.val
    · simp only [hai, if_true]
      rw [hx1y st.val (by omega)]
      exact hhi st.val (le_refl _) (by omega)
    · simp only [hai, show a ≠ st.val by omega, if_false]
      rw [hx1y a (by omega)]
      exact hhi a (by omega) (by omega)

theorem qs_sorted_kth (L : List Std.I32) (k : Nat) (hk : k < L.length)
    (hlo : ∀ a, a < k → L[a]!.val ≤ L[k]!.val)
    (hhi : ∀ b, k < b → b < L.length → L[k]!.val ≤ L[b]!.val) :
    (sortI32 L)[k]? = some L[k]! := by
  have htrans : ∀ x y z : Std.I32, decide (x.val ≤ y.val) = true → decide (y.val ≤ z.val) = true →
      decide (x.val ≤ z.val) = true := by
    intro x y z h1 h2; simp only [decide_eq_true_eq] at *; omega
  have htot : ∀ x y : Std.I32, (decide (x.val ≤ y.val) || decide (y.val ≤ x.val)) = true := by
    intro x y; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hperm : (sortI32 L).Perm L := List.mergeSort_perm L _
  have hsorted := List.pairwise_mergeSort htrans htot L
  have hSlen : (sortI32 L).length = L.length := hperm.length_eq
  have hSk : k < (sortI32 L).length := by omega
  have hsle : ∀ a b (ha : a < (sortI32 L).length) (hb : b < (sortI32 L).length), a < b →
      ((sortI32 L)[a]).val ≤ ((sortI32 L)[b]).val := by
    intro a b ha hb hab
    exact of_decide_eq_true (List.pairwise_iff_getElem.mp hsorted a b ha hb hab)
  rw [List.getElem?_eq_getElem hSk]
  congr 1
  generalize hp : L[k]! = p at hlo hhi ⊢
  apply (IScalar.eq_equiv _ _).mpr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hL : L.countP (fun z => decide (z.val < p.val)) ≤ k := by
      rw [← List.take_append_drop k L, List.countP_append]
      have h1 : (L.take k).countP (fun z => decide (z.val < p.val)) ≤ k :=
        List.countP_le_length.trans (by simp)
      have h2 : (L.drop k).countP (fun z => decide (z.val < p.val)) = 0 := by
        rw [List.countP_eq_zero]
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        rw [List.getElem_drop]
        simp only [List.length_drop] at hi
        have : p.val ≤ (L[k+i]!).val := by
          by_cases hi0 : i = 0
          · subst hi0; rw [Nat.add_zero, hp]
          · exact hhi (k+i) (by omega) (by omega)
        rw [getElem!_pos L (k+i) (by omega)] at this
        simp only [decide_eq_true_eq]; omega
      omega
    have hS : k + 1 ≤ (sortI32 L).countP (fun z => decide (z.val < p.val)) := by
      rw [← List.take_append_drop (k+1) (sortI32 L), List.countP_append]
      have : ((sortI32 L).take (k+1)).countP (fun z => decide (z.val < p.val)) = k + 1 := by
        rw [List.countP_eq_length.mpr]
        · simp only [List.length_take]; omega
        · intro z hz
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          rw [List.getElem_take]
          simp only [List.length_take] at hi
          have : ((sortI32 L)[i]'(by omega)).val ≤ ((sortI32 L)[k]).val := by
            by_cases hik : i = k
            · subst hik; exact le_refl _
            · exact hsle i k (by omega) hSk (by omega)
          simp only [decide_eq_true_eq]; omega
      omega
    rw [hperm.countP_eq] at hS
    omega
  · have hL : k + 1 ≤ L.countP (fun z => decide (z.val ≤ p.val)) := by
      rw [← List.take_append_drop (k+1) L, List.countP_append]
      have : (L.take (k+1)).countP (fun z => decide (z.val ≤ p.val)) = k + 1 := by
        rw [List.countP_eq_length.mpr]
        · simp only [List.length_take]; omega
        · intro z hz
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          rw [List.getElem_take]
          simp only [List.length_take] at hi
          have : (L[i]!).val ≤ p.val := by
            by_cases hik : i = k
            · subst hik; rw [hp]
            · exact hlo i (by omega)
          rw [getElem!_pos L i (by omega)] at this
          simp only [decide_eq_true_eq]; omega
      omega
    have hS : (sortI32 L).countP (fun z => decide (z.val ≤ p.val)) ≤ k := by
      rw [← List.take_append_drop k (sortI32 L), List.countP_append]
      have h1 : ((sortI32 L).take k).countP (fun z => decide (z.val ≤ p.val)) ≤ k :=
        List.countP_le_length.trans (by simp)
      have h2 : ((sortI32 L).drop k).countP (fun z => decide (z.val ≤ p.val)) = 0 := by
        rw [List.countP_eq_zero]
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        rw [List.getElem_drop]
        simp only [List.length_drop] at hi
        have : ((sortI32 L)[k]).val ≤ ((sortI32 L)[k+i]'(by omega)).val := by
          by_cases hi0 : i = 0
          · subst hi0; exact le_refl _
          · exact hsle k (k+i) hSk (by omega) (by omega)
        simp only [decide_eq_true_eq]; omega
      omega
    rw [hperm.countP_eq] at hS
    omega

theorem qs_index_mut_to (x : Slice Std.I32) (e : Std.Usize) (h : e.val ≤ x.length) :
    ∃ s back, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) x
      { «end» := e } = ok (s, back) ∧
      s.val = x.val.take e.val ∧ ∀ ss : Slice Std.I32, (back ss).val = x.val.setSlice! 0 ss.val := by
  have h' : e.val ≤ x.val.length := h
  simp only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Slice.subslice]
  rw [if_pos ⟨by simp, h'⟩]
  exact ⟨_, _, rfl, by simp [List.slice], fun ss => rfl⟩

theorem qs_index_mut_from (x : Slice Std.I32) (b : Std.Usize) (h : b.val ≤ x.length) :
    ∃ s back, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) x
      { start := b } = ok (s, back) ∧
      s.val = x.val.drop b.val ∧
      ∀ ss : Slice Std.I32, (back ss).val = x.val.setSlice! b.val ss.val := by
  have h' : b.val ≤ x.val.length := h
  simp only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_length, bind_tc_ok,
    rust_primitives.slice.slice_slice_mut, Slice.subslice]
  rw [if_pos ⟨by simp; omega, by simp⟩]
  exact ⟨_, _, rfl, by simp [List.slice], fun ss => rfl⟩

theorem qs_setSlice_zero {α : Type} (L S : List α) (h : S.length ≤ L.length) :
    L.setSlice! 0 S = S ++ L.drop S.length := by
  simp only [List.setSlice!]
  simp [Nat.min_eq_left h]

theorem qs_setSlice_suffix {α : Type} (L S : List α) (b : Nat) (h : S.length + b = L.length) :
    L.setSlice! b S = L.take b ++ S := by
  simp only [List.setSlice!]
  have hm : min S.length (L.length - b) = S.length := by omega
  simp [hm, List.drop_eq_nil_of_le (show L.length ≤ b + S.length by omega)]

theorem qs_get_mem {α : Type} [Inhabited α] (L : List α) (a : Nat) (h : a < L.length) :
    L[a]! ∈ L := by
  rw [getElem!_pos L a h]; exact List.getElem_mem h

theorem qs_select : ∀ n (x : Slice Std.I32) (k : Std.Usize), x.length = n → k.val < n →
    ∃ x', quickselect.select core.I32.Insts.CoreCmpOrd x k = ok x' ∧
      x'.val.Perm x.val ∧ x'.length = n ∧
      (∀ a, a < k.val → x'.val[a]!.val ≤ x'.val[k.val]!.val) ∧
      (∀ b, k.val < b → b < n → x'.val[k.val]!.val ≤ x'.val[b]!.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x k hx hk
  have hlen : core.slice.Slice.len x = ok (Slice.len x) := rfl
  have hlv : (Slice.len x).val = x.length := Slice.len_val x
  by_cases h5 : x.length < 5
  · have hl5 : Slice.len x < 5#usize := by scalar_tac
    obtain ⟨x', h1, h2, h3, h4⟩ := qs_outer (Slice.len x) (x.length - 0) 0#usize x
      (by simp [hlv]) (by simp) hlv.symm (by intro a b ha; simp at ha)
    refine ⟨x', ?_, h2, by omega, ?_, ?_⟩
    · rw [quickselect.select.eq_1, hlen, bind_tc_ok, if_pos hl5]
      exact h1
    · intro a ha
      exact h4 a k.val ha (by omega)
    · intro b hb1 hb2
      exact h4 k.val b hb1 (by omega)
  · have hl5 : ¬ (Slice.len x < 5#usize) := by scalar_tac
    obtain ⟨st, x2, hpart, hp2, hl2, hst, hlo, hhi⟩ := qs_partition x (by omega)
    have hbase : quickselect.select core.I32.Insts.CoreCmpOrd x k =
        (if k < st then do
          let (s, index_mut_back) ← core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
              (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) x2
              { «end» := st }
          let s1 ← quickselect.select core.I32.Insts.CoreCmpOrd s k
          ok (index_mut_back s1)
        else if k > st then do
          let i1 ← st + 1#usize
          let (s, index_mut_back) ← core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
              (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) x2
              { start := i1 }
          let i2 ← k - st
          let i3 ← i2 - 1#usize
          let s1 ← quickselect.select core.I32.Insts.CoreCmpOrd s i3
          ok (index_mut_back s1)
        else ok x2) := by
      rw [quickselect.select.eq_1, hlen, bind_tc_ok, if_neg hl5, hpart, bind_tc_ok]
      rfl
    set p := x2.val[st.val]! with hp
    have hx2len : x2.val.length = n := by rw [← hx]; exact hl2
    by_cases hkl : k.val < st.val
    · -- recurse on the prefix
      have hkU : k < st := by scalar_tac
      obtain ⟨s, back, hidx, hsv, hback⟩ := qs_index_mut_to x2 st (by omega)
      have hslen : s.length = st.val := by
        show s.val.length = _; rw [hsv]; simp; omega
      obtain ⟨s1, hs1, hp1, hl1, hlo1, hhi1⟩ := ih st.val (by omega) s k hslen hkl
      have hs1len : s1.val.length = st.val := hl1
      have hres : (back s1).val = s1.val ++ x2.val.drop st.val := by
        rw [hback, qs_setSlice_zero x2.val s1.val (by omega), hs1len]
      have key : quickselect.select core.I32.Insts.CoreCmpOrd x k = ok (back s1) := by
        rw [hbase, if_pos hkU, hidx, bind_tc_ok]
        show (do
          let s1 ← quickselect.select core.I32.Insts.CoreCmpOrd s k
          ok (back s1)) = _
        rw [hs1, bind_tc_ok]
      -- elements of s are < p
      have hsmall : ∀ z ∈ s1.val, z.val < p.val := by
        intro z hz
        have hz' := hp1.subset hz
        rw [hsv] at hz'
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
        rw [List.getElem_take]
        simp only [List.length_take] at hi
        have := hlo i (by omega)
        rwa [getElem!_pos x2.val i (by omega)] at this
      have hgetL : ∀ a, a < st.val → (back s1).val[a]! = s1.val[a]! := by
        intro a ha; rw [hres, qs_get_append_left _ _ a (by omega)]
      have hgetR : ∀ a, st.val ≤ a → a < n → (back s1).val[a]! = x2.val[a]! := by
        intro a ha1 ha2
        rw [hres, qs_get_append_right _ _ a (by omega) (by simp; omega), hs1len]
        rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega), List.getElem_drop]
        congr 1; omega
      refine ⟨back s1, key, ?_, ?_, ?_, ?_⟩
      · rw [hres]
        refine (hp1.append_right _).trans ?_
        rw [hsv, List.take_append_drop]; exact hp2
      · show (back s1).val.length = n
        rw [hres]; simp; omega
      · intro a ha
        rw [hgetL a (by omega), hgetL k.val hkl]
        exact hlo1 a ha
      · intro b hb1 hb2
        rw [hgetL k.val hkl]
        by_cases hbs : b < st.val
        · rw [hgetL b hbs]; exact hhi1 b hb1 hbs
        · rw [hgetR b (by omega) hb2]
          have h1 := hsmall _ (qs_get_mem s1.val k.val (by omega))
          by_cases hbe : b = st.val
          · subst hbe; rw [← hp]; omega
          · have := hhi b (by omega) (by omega); omega
    · by_cases hkg : st.val < k.val
      · -- recurse on the suffix
        have hkU : ¬ (k < st) := by scalar_tac
        have hkG : k > st := by scalar_tac
        obtain ⟨i1, hi1, hi1v⟩ := qs_usize_add_ok st 1#usize (by scalar_tac)
        have hi1v' : i1.val = st.val + 1 := by simpa using hi1v
        obtain ⟨s, back, hidx, hsv, hback⟩ := qs_index_mut_from x2 i1 (by omega)
        obtain ⟨i2, hi2, hi2v⟩ := qs_usize_sub_ok k st (by omega)
        obtain ⟨i3, hi3, hi3v⟩ := qs_usize_sub_ok i2 1#usize (by simp; omega)
        have hi3v' : i3.val = k.val - st.val - 1 := by simp at hi3v; omega
        have hslen : s.length = n - st.val - 1 := by
          show s.val.length = _; rw [hsv]; simp; omega
        obtain ⟨s1, hs1, hp1, hl1, hlo1, hhi1⟩ :=
          ih (n - st.val - 1) (by omega) s i3 hslen (by omega)
        have hs1len : s1.val.length = n - st.val - 1 := hl1
        have hres : (back s1).val = x2.val.take (st.val + 1) ++ s1.val := by
          rw [hback, hi1v', qs_setSlice_suffix x2.val s1.val (st.val + 1) (by omega)]
        have key : quickselect.select core.I32.Insts.CoreCmpOrd x k = ok (back s1) := by
          rw [hbase, if_neg hkU, if_pos hkG, hi1, bind_tc_ok, hidx, bind_tc_ok]
          show (do
            let i2 ← k - st
            let i3 ← i2 - 1#usize
            let s1 ← quickselect.select core.I32.Insts.CoreCmpOrd s i3
            ok (back s1)) = _
          rw [hi2, bind_tc_ok, hi3, bind_tc_ok, hs1, bind_tc_ok]
        have hbig : ∀ z ∈ s1.val, p.val ≤ z.val := by
          intro z hz
          have hz' := hp1.subset hz
          rw [hsv] at hz'
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
          rw [List.getElem_drop]
          simp only [List.length_drop] at hi
          have := hhi (i1.val + i) (by omega) (by omega)
          rwa [getElem!_pos x2.val (i1.val + i) (by omega)] at this
        have htk : (x2.val.take (st.val + 1)).length = st.val + 1 := by simp; omega
        have hgetL : ∀ a, a ≤ st.val → (back s1).val[a]! = x2.val[a]! := by
          intro a ha
          rw [hres, qs_get_append_left _ _ a (by omega)]
          rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega), List.getElem_take]
        have hgetR : ∀ a, st.val < a → a < n →
            (back s1).val[a]! = s1.val[a - st.val - 1]! := by
          intro a ha1 ha2
          rw [hres, qs_get_append_right _ _ a (by omega) (by omega), htk]
          congr 1
        have hkk : (back s1).val[k.val]! = s1.val[i3.val]! := by
          rw [hgetR k.val hkg hk, hi3v']
        refine ⟨back s1, key, ?_, ?_, ?_, ?_⟩
        · rw [hres]
          refine (List.Perm.append_left _ hp1).trans ?_
          rw [hsv, hi1v', List.take_append_drop]; exact hp2
        · show (back s1).val.length = n
          rw [hres]; simp; omega
        · intro a ha
          rw [hkk]
          by_cases has : a ≤ st.val
          · rw [hgetL a has]
            have h1 := hbig _ (qs_get_mem s1.val i3.val (by omega))
            by_cases hae : a = st.val
            · subst hae; rw [← hp]; exact h1
            · have := hlo a (by omega); omega
          · rw [hgetR a (by omega) (by omega)]
            exact hlo1 (a - st.val - 1) (by omega)
        · intro b hb1 hb2
          rw [hkk, hgetR b (by omega) hb2]
          have := hhi1 (b - st.val - 1) (by omega) (by omega)
          exact this
      · -- k = pivot
        have hkU : ¬ (k < st) := by scalar_tac
        have hkG : ¬ (k > st) := by scalar_tac
        have hke : k.val = st.val := by omega
        have key : quickselect.select core.I32.Insts.CoreCmpOrd x k = ok x2 := by
          rw [hbase, if_neg hkU, if_neg hkG]
        refine ⟨x2, key, hp2, by omega, ?_, ?_⟩
        · intro a ha; rw [hke] at ha ⊢; exact le_of_lt (hlo a ha)
        · intro b hb1 hb2; rw [hke] at hb1 ⊢; exact hhi b hb1 (by omega)

/--
For every `i32` slice `x` and index `k < x.len()`, quickselect's
`select(&mut x, k)` never panics and leaves at position `k` exactly the
`k`-th smallest element of the slice, i.e. the element that sorting the
resulting slice would put at position `k`.
-/
theorem select_kth_is_kth_smallest (x : Slice Std.I32) (k : Std.Usize)
    (h_assume_k : k.val < x.length) :
    select_kth_is_kth_smallest_spec x k := by
  unfold select_kth_is_kth_smallest_spec
  obtain ⟨x', h1, h2, h3, h4, h5⟩ := qs_select x.length x k rfl h_assume_k
  have hkx : k.val < x'.length := by omega
  have h3' : x'.val.length = x.length := h3
  rw [h1, bind_tc_ok, qs_index_ok x' k hkx, bind_tc_ok, spec_ok]
  exact qs_sorted_kth x'.val k.val hkx h4 (fun b hb1 hb2 => h5 b hb1 (by omega))

end Benchmark.Cases.OrderStat.Quickselect
