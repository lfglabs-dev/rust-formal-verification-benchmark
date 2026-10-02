import Benchmark.Cases.OpenpqlPrelude.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- Non-decreasing order on `u64` values. -/
def csLe (a b : Std.U64) : Prop := a.val ≤ b.val

theorem cs_swap_list (A' B C : List Std.U64) (a x : Std.U64) :
    ((A' ++ a :: x :: (B ++ C)).set A'.length x).set (A'.length + 1) a =
      A' ++ x :: a :: (B ++ C) := by
  simp [List.set_append_right]

/-- One swapping iteration of the inner insertion loop. -/
theorem cs_inner_body_swap (arr : Std.Array Std.U64 10#usize) (j : Std.Usize)
    (hj0 : 0 < j.val) (hjl : j.val < 10)
    (hlt : (arr.val[j.val]'(by simp; omega)).val < (arr.val[j.val - 1]'(by simp; omega)).val) :
    waugh_indexer.util.const_sort_loop0_loop0.body arr j ⦃ r => ∃ j' : Std.Usize,
      j'.val = j.val - 1 ∧
      r = .cont ((arr.set j' (arr.val[j.val]'(by simp; omega))).set j
          (arr.val[j.val - 1]'(by simp; omega)), j') ⦄ := by
  unfold waugh_indexer.util.const_sort_loop0_loop0.body
  have hgt : j > 0#usize := by scalar_tac
  simp only [hgt, if_true]
  step as ⟨_h1, x, hx⟩
  step as ⟨i1, hi1⟩
  step as ⟨_h2, y, hy⟩
  have hxy : x < y := by
    show x.val < y.val
    rw [hx, hy]; simp only [hi1]; exact hlt
  simp only [hxy, if_true]
  step as ⟨_h3, tmp, htmp⟩
  step as ⟨arr1, harr1⟩
  step as ⟨a, ha⟩
  refine ⟨i1, hi1, ?_⟩
  rw [ha, harr1, htmp, hx]
  simp only [hi1]

/-- Exit of the inner insertion loop. -/
theorem cs_inner_body_done (arr : Std.Array Std.U64 10#usize) (j : Std.Usize)
    (h : j.val = 0 ∨ ∃ (hj0 : 0 < j.val) (hjl : j.val < 10),
      ¬ (arr.val[j.val]'(by simp; omega)).val < (arr.val[j.val - 1]'(by simp; omega)).val) :
    waugh_indexer.util.const_sort_loop0_loop0.body arr j ⦃ r => r = .done arr ⦄ := by
  unfold waugh_indexer.util.const_sort_loop0_loop0.body
  rcases h with h0 | ⟨hj0, hjl, hnlt⟩
  · have hgt : ¬ j > 0#usize := by scalar_tac
    simp only [hgt, if_false, WP.spec_ok]
  · have hgt : j > 0#usize := by scalar_tac
    simp only [hgt, if_true]
    step as ⟨_h1, x, hx⟩
    step as ⟨i1, hi1⟩
    step as ⟨_h2, y, hy⟩
    have hxy : ¬ x < y := by
      show ¬ x.val < y.val
      rw [hx, hy]; simp only [hi1]; exact hnlt
    simp only [hxy, if_false, WP.spec_ok]

theorem cs_getElem_mid (A' R : List Std.U64) (a x : Std.U64) (j : Nat) (hj : A'.length + 1 = j)
    (h1 : j < (A' ++ a :: x :: R).length) (h2 : j - 1 < (A' ++ a :: x :: R).length) :
    (A' ++ a :: x :: R)[j] = x ∧ (A' ++ a :: x :: R)[j - 1] = a := by
  subst hj
  constructor
  · rw [List.getElem_append_right (by simp)]; simp
  · rw [List.getElem_append_right (by simp)]; simp

theorem cs_inner_loop (arr0 : Std.Array Std.U64 10#usize) (i : Std.Usize) (hi : i.val < 10)
    (S C : List Std.U64) (x0 : Std.U64) (hS : S.length = i.val)
    (harr0 : arr0.val = S ++ x0 :: C) (hsorted : S.Pairwise csLe) :
    waugh_indexer.util.const_sort_loop0_loop0 arr0 i ⦃ arr' => ∃ A B : List Std.U64,
      arr'.val = A ++ x0 :: (B ++ C) ∧ A ++ B = S ∧ (∀ b ∈ B, x0.val < b.val) ∧
      (∀ a ∈ A, a.val ≤ x0.val) ⦄ := by
  unfold waugh_indexer.util.const_sort_loop0_loop0
  apply loop.spec_decr_nat (fun p : Std.Array Std.U64 10#usize × Std.Usize => p.2.val)
    (fun p => p.2.val ≤ i.val ∧ ∃ A B : List Std.U64, p.1.val = A ++ x0 :: (B ++ C) ∧
      A.length = p.2.val ∧ A ++ B = S ∧ ∀ b ∈ B, x0.val < b.val)
  · rintro ⟨arr, j⟩ ⟨hji, A, B, harr, hAlen, hAB, hB⟩
    simp only at hji harr hAlen hAB hB ⊢
    rcases List.eq_nil_or_concat A with hA | ⟨A', a, hA⟩
    · -- j = 0: the element is at the front
      subst hA
      apply spec_mono (cs_inner_body_done arr j (Or.inl (by simp at hAlen; omega)))
      rintro r rfl
      refine ⟨[], B, harr, hAB, hB, by simp⟩
    · subst hA
      simp only [List.concat_eq_append] at harr hAlen hAB
      have hlen : A'.length + 1 = j.val := by simpa using hAlen
      have harr' : arr.val = A' ++ a :: x0 :: (B ++ C) := by rw [harr]; simp
      have hjl : j.val < 10 := by omega
      have hmid := cs_getElem_mid A' (B ++ C) a x0 j.val hlen
        (by rw [← harr']; simp; omega) (by rw [← harr']; simp; omega)
      have hxj : arr.val[j.val]'(by simp; omega) = x0 := by
        have := hmid.1; simp only [← harr'] at this; exact this
      have haj : arr.val[j.val - 1]'(by simp; omega) = a := by
        have := hmid.2; simp only [← harr'] at this; exact this
      by_cases hlt : x0.val < a.val
      · have hlt' : (arr.val[j.val]'(by simp; omega)).val <
            (arr.val[j.val - 1]'(by simp; omega)).val := by rw [hxj, haj]; exact hlt
        apply spec_mono (cs_inner_body_swap arr j (by omega) hjl hlt')
        rintro r ⟨j', hj', rfl⟩
        simp only
        refine ⟨⟨by omega, A', a :: B, ?_, by omega, ?_, ?_⟩, by omega⟩
        · rw [Std.Array.set_val_eq, Std.Array.set_val_eq, hxj, haj, harr']
          have : j'.val = A'.length := by omega
          rw [this, ← hlen, cs_swap_list]
          simp
        · rw [← hAB]; simp
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hlt
          · exact hB b hb
      · have hnlt : ¬ (arr.val[j.val]'(by simp; omega)).val <
            (arr.val[j.val - 1]'(by simp; omega)).val := by rw [hxj, haj]; exact hlt
        apply spec_mono (cs_inner_body_done arr j (Or.inr ⟨by omega, hjl, hnlt⟩))
        rintro r rfl
        refine ⟨A' ++ [a], B, harr, hAB, hB, ?_⟩
        intro a' ha'
        have hsA : (A' ++ [a]).Pairwise csLe := by
          rw [← hAB] at hsorted
          exact (List.pairwise_append.mp hsorted).1
        simp only [List.mem_append, List.mem_singleton] at ha'
        rcases ha' with ha' | rfl
        · have := (List.pairwise_append.mp hsA).2.2 a' ha' a (by simp)
          simp only [csLe] at this
          omega
        · omega
  · exact ⟨le_refl _, S, [], by simp [harr0], hS, by simp, by simp⟩

theorem cs_outer_loop (L : List Std.U64) :
    ∀ (arr : Std.Array Std.U64 10#usize) (i : Std.Usize), i.val ≤ 10 → arr.val.Perm L →
      (arr.val.take i.val).Pairwise csLe →
      waugh_indexer.util.const_sort_loop0 arr i ⦃ res =>
        res.val.Perm L ∧ res.val.Pairwise csLe ⦄ := by
  intro arr0 i0 hi0 hperm0 hsort0
  unfold waugh_indexer.util.const_sort_loop0
  apply loop.spec_decr_nat (fun p : Std.Array Std.U64 10#usize × Std.Usize => 10 - p.2.val)
    (fun p => p.2.val ≤ 10 ∧ p.1.val.Perm L ∧ (p.1.val.take p.2.val).Pairwise csLe)
  · rintro ⟨arr, i⟩ ⟨hi, hperm, hsort⟩
    simp only at hi hperm hsort ⊢
    unfold waugh_indexer.util.const_sort_loop0.body
    have hlen : arr.val.length = 10 := by simp
    by_cases hlt : i.val < 10
    · have hlt' : i < 10#usize := by scalar_tac
      simp only [hlt', if_true]
      have hsplit : arr.val = arr.val.take i.val ++ (arr.val[i.val]'(by omega)) ::
          arr.val.drop (i.val + 1) := by
        conv_lhs => rw [← List.take_append_drop i.val arr.val]
        rw [List.drop_eq_getElem_cons (by omega)]
      apply spec_bind (cs_inner_loop arr i hlt _ _ _ (by simp; omega) hsplit hsort)
      rintro arr' ⟨A, B, harr', hAB, hB, hA⟩
      step as ⟨i1, hi1⟩
      refine ⟨by omega, ?_, ?_, by omega⟩
      · refine List.Perm.trans ?_ hperm
        rw [harr']
        conv_rhs => rw [hsplit]
        refine List.perm_middle.trans ?_
        refine List.Perm.trans ?_ List.perm_middle.symm
        rw [← hAB, List.append_assoc]
      · have hlenAB : (A ++ (arr.val[i.val]'(by omega)) :: B).length = i1.val := by
          have := congrArg List.length hAB
          simp at this ⊢; omega
        have hre : A ++ (arr.val[i.val]'(by omega)) :: (B ++ arr.val.drop (i.val + 1)) =
            (A ++ (arr.val[i.val]'(by omega)) :: B) ++ arr.val.drop (i.val + 1) := by simp
        rw [harr', hre, List.take_left' hlenAB]
        have hS : (A ++ B).Pairwise csLe := by rw [hAB]; exact hsort
        obtain ⟨hsA, hsB, hAB'⟩ := List.pairwise_append.mp hS
        rw [List.pairwise_append]
        refine ⟨hsA, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun b hb => Nat.le_of_lt (hB b hb), hsB⟩
        · intro a ha y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hA a ha
          · exact hAB' a ha y hy
    · have hge : ¬ i < 10#usize := by scalar_tac
      simp only [hge, if_false, WP.spec_ok]
      have hi10 : i.val = 10 := by omega
      rw [hi10, List.take_of_length_le (by simp)] at hsort
      exact ⟨hperm, hsort⟩
  · exact ⟨hi0, hperm0, hsort0⟩

/--
`const_sort` (insertion sort on a `[u64; 10]`) never panics and returns exactly
`sort_unstable`'s result: the non-decreasing permutation of the input.
-/
theorem const_sort_matches_sort_unstable (numbers : Std.Array Std.U64 10#usize) :
    const_sort_spec numbers := by
  unfold const_sort_spec waugh_indexer.util.const_sort
  have h1 : (numbers.val.take (1#usize).val).Pairwise csLe := by
    have hl : numbers.val.length = 10 := by simp
    obtain ⟨x, rest, hx⟩ : ∃ x rest, numbers.val = x :: rest := by
      cases h : numbers.val with
      | nil => rw [h] at hl; simp at hl
      | cons x rest => exact ⟨x, rest, rfl⟩
    rw [hx]
    simp
  apply spec_mono (cs_outer_loop numbers.val numbers 1#usize (by simp) (List.Perm.refl _) h1)
  rintro res ⟨hperm, hsort⟩
  have hM : (res.val.map (·.val)).Pairwise (fun a b : Nat => a ≤ b) := by
    rw [List.pairwise_map]; exact hsort
  have hS : ((numbers.val.map (·.val)).mergeSort).Pairwise (fun a b : Nat => a ≤ b) := by
    have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c hab hbc; simp at *; omega) (by intro a b; simp; omega)
      (numbers.val.map (·.val))
    simpa using this
  have hP : (res.val.map (·.val)).Perm ((numbers.val.map (·.val)).mergeSort) :=
    (hperm.map _).trans (List.mergeSort_perm _ _).symm
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba) hM hS hP

end Benchmark.Cases.OpenpqlPrelude.Util
