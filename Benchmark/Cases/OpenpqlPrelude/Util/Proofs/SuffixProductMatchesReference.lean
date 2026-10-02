import Benchmark.Cases.OpenpqlPrelude.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- Product of a suffix is at most the product of the whole list when all entries are positive. -/
theorem sp_prod_drop_le (L : List Nat) (hpos : ∀ x ∈ L, 1 ≤ x) (i : Nat) :
    (L.drop i).prod ≤ L.prod := by
  induction L generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.drop_succ_cons, List.prod_cons]
      have h1 := ih (fun x hx => hpos x (List.mem_cons_of_mem a hx)) i
      have h2 : 1 ≤ a := hpos a (List.mem_cons_self)
      calc (l.drop i).prod ≤ l.prod := h1
        _ = 1 * l.prod := by ring
        _ ≤ a * l.prod := Nat.mul_le_mul_right _ h2

theorem sp_prod_drop_succ (L : List Nat) (j : Nat) (hj : j < L.length) :
    (L.drop j).prod = L[j] * (L.drop (j + 1)).prod := by
  rw [List.drop_eq_getElem_cons hj, List.prod_cons]

theorem sp_update_ok (v : Slice Std.U64) (i : Std.Usize) (x : Std.U64) (h : i.val < v.val.length) :
    v.update i x = ok (v.set i x) := by
  simp only [Slice.update, Slice.set, Slice.setAtNat, List.getElem?_eq_getElem h]

theorem sp_loop_spec (xs : Slice Std.U64) (hpos : ∀ x ∈ xs.val, 1 ≤ x.val)
    (hprod : (xs.val.map (·.val)).prod < 2^64) :
    ∀ (input : Slice Std.U64) (acc : Std.U64) (i : Std.Usize),
      input.val.length = xs.val.length → i.val ≤ xs.val.length →
      (∀ j (hj : j < input.val.length) (hj' : j < xs.val.length),
        (input.val[j]).val = if j < i.val then (xs.val[j]).val
          else ((xs.val.map (·.val)).drop (j + 1)).prod) →
      acc.val = ((xs.val.map (·.val)).drop i.val).prod →
      waugh_indexer.util.suffix_product_loop input acc i ⦃ ys =>
        ys.val.map (·.val) = suffixProducts (xs.val.map (·.val)) ⦄ := by
  intro input acc i hlen hi hinp hacc
  unfold waugh_indexer.util.suffix_product_loop
  apply loop.spec_decr_nat (fun p : Slice Std.U64 × Std.U64 × Std.Usize => p.2.2.val)
    (fun p => p.1.val.length = xs.val.length ∧ p.2.2.val ≤ xs.val.length ∧
      (∀ j (hj : j < p.1.val.length) (hj' : j < xs.val.length),
        (p.1.val[j]).val = if j < p.2.2.val then (xs.val[j]).val
          else ((xs.val.map (·.val)).drop (j + 1)).prod) ∧
      p.2.1.val = ((xs.val.map (·.val)).drop p.2.2.val).prod)
  · rintro ⟨input, acc, i⟩ ⟨hlen, hi, hinp, hacc⟩
    unfold waugh_indexer.util.suffix_product_loop.body
    simp only at hlen hi hinp hacc ⊢
    split
    · rename_i hgt
      have hgt' : 0 < i.val := hgt
      step as ⟨i1, hi1⟩
      have hi1lt : i1.val < xs.val.length := by omega
      have hi1lt' : i1.val < input.val.length := by omega
      have hcurv : (input.val[i1.val]'hi1lt').val = (xs.val[i1.val]'hi1lt).val := by
        rw [hinp i1.val hi1lt' hi1lt]; simp; omega
      have hLlen : (xs.val.map (·.val)).length = xs.val.length := by simp
      have hdrop : ((xs.val.map (·.val)).drop i1.val).prod =
          (xs.val[i1.val]'hi1lt).val * ((xs.val.map (·.val)).drop i.val).prod := by
        rw [sp_prod_drop_succ _ _ (by omega)]
        simp only [List.getElem_map]
        have : i1.val + 1 = i.val := by omega
        rw [this]
      step as ⟨_hlt, cur, hcur⟩
      have hmul : acc.val * cur.val ≤ U64.max := by
        rw [hcur, hacc, hcurv, Nat.mul_comm, ← hdrop]
        have hle := sp_prod_drop_le (xs.val.map (·.val)) (by simpa using hpos) i1.val
        have : U64.max = 2^64 - 1 := by simp [U64.max, U64.numBits]
        omega
      rw [sp_update_ok input i1 acc hi1lt', bind_tc_ok]
      step as ⟨acc1, hacc1⟩
      try simp only [WP.spec_ok]
      refine ⟨by simp [hlen], by omega, ?_, ?_, by omega⟩
      · intro j hj hj'
        simp only [Slice.set_val_eq] at hj ⊢
        rw [List.getElem_set]
        by_cases hji : i1.val = j
        · subst hji
          simp only [if_true, lt_irrefl, if_false, hacc]
          have : i1.val + 1 = i.val := by omega
          rw [this]
        · simp only [hji, if_false]
          rw [hinp j (by simpa using hj) hj']
          have : (j < i.val) ↔ (j < i1.val) := by omega
          simp only [this]
      · rw [hacc1, hacc, hcur, hcurv, Nat.mul_comm, ← hdrop]
    · rename_i hgt
      have hi0 : i.val = 0 := by
        have : ¬ 0 < i.val := hgt
        omega
      simp only [WP.spec_ok]
      apply List.ext_getElem
      · simp [suffixProducts, hlen]
      · intro j hj1 hj2
        have hj' : j < xs.val.length := by simpa [hlen] using hj1
        have hj0 : j < input.val.length := by simpa using hj1
        simp only [List.getElem_map, suffixProducts, List.getElem_range]
        rw [hinp j hj0 hj', hi0]
        simp
  · exact ⟨hlen, hi, hinp, hacc⟩

/--
On every nonempty slice of `u64` values in `[1, 65535]` whose total product fits in a `u64`, the in-place `suffix_product` never panics and replaces entry `i` by the product of the entries after position `i`.
-/
theorem suffix_product_matches_reference (xs : Slice Std.U64)
    (h_nonempty : xs.val ≠ [])
    (h_elems : ∀ x ∈ xs.val, 1 ≤ x.val ∧ x.val ≤ 65535)
    (h_prod : (xs.val.map (·.val)).prod ≤ 2^64 - 1) :
    suffix_product_spec xs := by
  have _hne := h_nonempty
  unfold suffix_product_spec waugh_indexer.util.suffix_product
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hlen : (Slice.len xs).val = xs.val.length := by simp
  apply sp_loop_spec xs (fun x hx => (h_elems x hx).1) (by omega) xs 1#u64 (Slice.len xs) rfl
  · simp [hlen]
  · intro j hj hj'
    simp only [hlen, hj', if_true]
  · rw [hlen]; simp

end Benchmark.Cases.OpenpqlPrelude.Util
