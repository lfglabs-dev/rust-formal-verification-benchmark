import Benchmark.Cases.Bloom2.VecBitmap.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open bloom2

namespace Benchmark.Cases.Bloom2.VecBitmap

theorem bits_val : (UScalar.cast UScalarTy.Usize core.num.U64.BITS).val = 64 := by
  unfold core.num.U64.BITS
  simp

theorem usize_size (hp : System.Platform.numBits = 64) : Usize.size = 2 ^ 64 := by
  simp only [Usize.size_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq, hp]

theorem index_for_key_spec (key : Std.Usize) :
    bitmap.index_for_key key ⦃ q => q.val = key.val / 64 ⦄ := by
  unfold bitmap.index_for_key
  have hb := bits_val
  step*

theorem bitmask_for_key_spec (key : Std.Usize) (hp : System.Platform.numBits = 64) :
    bitmap.bitmask_for_key key ⦃ m => m.val = 2 ^ (key.val % 64) ⦄ := by
  unfold bitmap.bitmask_for_key
  have hb := bits_val
  step*
  rw [m_post1, i1_post, i_post, hb, Nat.one_shiftLeft, usize_size hp]
  apply Nat.mod_eq_of_lt
  apply Nat.pow_lt_pow_right (by norm_num)
  omega

theorem mapM_clone (l : List Std.Usize) :
    List.mapM core.Usize.Insts.CoreCloneClone.clone l = ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, core.Usize.Insts.CoreCloneClone.clone, ih]; rfl

theorem new_spec :
    bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.new_with_capacity 1028#usize ⦃ b =>
      b.bitmap.val = List.replicate 17 0#usize ⦄ := by
  unfold bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.new_with_capacity
  apply spec_bind (index_for_key_spec _)
  intro q hq
  have hq' : q.val = 16 := by rw [hq]; rfl
  step*
  have h17 : i1.val = 17 := by omega
  simp only [alloc.vec.from_elem, rust_primitives.sequence.seq_create, h17]
  simp only [core.Usize.Insts.CoreCloneClone, mapM_clone]
  have hmax : (List.replicate (17 - 1) 0#usize).length < Usize.max := by
    simp only [List.length_replicate]
    have := Usize.max_def; have := Usize.numBits_def
    scalar_tac
  have h17m : 17 ≤ Usize.max := by
    have := Usize.max_def; have := Usize.numBits_def
    scalar_tac
  simp [h17m]

theorem index_usize_eq {α : Type} (v : Slice α) (i : Std.Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok (v.val[i.val]) := by
  simp [Slice.index_usize, h]

theorem and_two_pow_ne_zero (x r : Nat) : x &&& 2 ^ r ≠ 0 ↔ x.testBit r = true := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : r = j
    · subst hj; simp_all
    · simp [hj]
  · intro h h0
    have := congrArg (fun n => n.testBit r) h0
    simp [Nat.testBit_and, Nat.testBit_two_pow, h] at this

/-- The `j`-th word of the bitmap, as a natural number. -/
def word (b : bitmap.vec.VecBitmap) (j : Nat) : Nat := (b.bitmap.val.getD j 0#usize).val

theorem get_spec (b : bitmap.vec.VecBitmap) (i : Std.Usize) (hp : System.Platform.numBits = 64)
    (hlen : b.bitmap.val.length = 17) (hi : i.val < 1028) :
    bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.get b i ⦃ r =>
      r = (word b (i.val / 64)).testBit (i.val % 64) ⦄ := by
  unfold bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.get
  apply spec_bind (index_for_key_spec _)
  intro q hq
  simp [alloc.vec.Vec.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT, core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    rust_primitives.slice.slice_index, rust_primitives.slice.slice_length, alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref,
    alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice]
  have hql : q.val < b.bitmap.val.length := by rw [hq, hlen]; omega
  simp only [hql, ↓reduceIte, index_usize_eq _ _ hql, bind_tc_ok]
  apply spec_bind (bitmask_for_key_spec _ hp)
  intro m hm
  simp only [lift, bind_tc_ok, WP.spec_ok]
  have hw : word b (i.val / 64) = (b.bitmap.val[q.val]).val := by
    rw [← hq]; simp [word, List.getD_eq_getElem?_getD, hql]
  rw [hw]
  rw [Bool.eq_iff_iff, ← and_two_pow_ne_zero, ← hm, ← UScalar.val_and]
  simp [UScalar.eq_equiv]

theorem set_spec (b : bitmap.vec.VecBitmap) (v : Std.Usize) (hp : System.Platform.numBits = 64)
    (hlen : b.bitmap.val.length = 17) (hv : v.val < 1028) :
    bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.set b v true ⦃ b' =>
      b'.bitmap.val.length = 17 ∧
      ∀ j, word b' j = if j = v.val / 64 then word b j ||| 2 ^ (v.val % 64) else word b j ⦄ := by
  unfold bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.set
  apply spec_bind (index_for_key_spec _)
  intro q hq
  simp only [↓reduceIte]
  apply spec_bind (bitmask_for_key_spec _ hp)
  intro m hm
  simp [alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT, core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get_unchecked_mut,
    rust_primitives.slice.slice_index_mut, rust_primitives.sequence.seq_to_slice_mut]
  have hql : q.val < b.bitmap.val.length := by rw [hq, hlen]; omega
  simp only [Slice.index_mut_usize, index_usize_eq _ _ hql, bind_tc_ok, lift]
  simp [word]
  refine ⟨hlen, ?_⟩
  intro j
  rw [List.getElem?_set]
  by_cases hj : j = v.val / 64
  · have hqj : q.val = j := by omega
    have hvl : v.val / 64 < b.bitmap.val.length := by omega
    simp [hqj, hj, hm, hvl]
  · have hqj : q.val ≠ j := by omega
    simp [hqj, hj]

/-- Invariant after inserting the keys of `P`: 17 words, and bit `k % 64` of word
`k / 64` is set exactly for the inserted keys `k < 1028`. -/
def Inv (P : List Std.Usize) (b : bitmap.vec.VecBitmap) : Prop :=
  b.bitmap.val.length = 17 ∧
    ∀ k, k < 1028 → (word b (k / 64)).testBit (k % 64) = decide (∃ v ∈ P, v.val = k)

theorem inv_set (P : List Std.Usize) (b b' : bitmap.vec.VecBitmap) (v : Std.Usize)
    (hinv : Inv P b) (hlen' : b'.bitmap.val.length = 17)
    (hw : ∀ j, word b' j = if j = v.val / 64 then word b j ||| 2 ^ (v.val % 64) else word b j) :
    Inv (P ++ [v]) b' := by
  refine ⟨hlen', ?_⟩
  intro k hk
  rw [hw]
  have hold := hinv.2 k hk
  by_cases hj : k / 64 = v.val / 64
  · simp only [hj, ↓reduceIte, Nat.testBit_or, Nat.testBit_two_pow]
    rw [← hj, hold]
    by_cases hvk : v.val = k
    · have : v.val % 64 = k % 64 := by omega
      simp [this, hvk]
    · have : ¬ (v.val % 64 = k % 64) := by omega
      simp [this, hvk]
  · rw [if_neg hj, hold]
    have hvk : v.val ≠ k := by intro h; apply hj; rw [h]
    simp [hvk]

theorem fold_spec (hp : System.Platform.numBits = 64) :
    ∀ (S P : List Std.Usize) (b : bitmap.vec.VecBitmap), Inv P b → (∀ v ∈ S, v.val < 1028) →
      S.foldlM (fun b v => bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.set b v true) b ⦃ b' =>
        Inv (P ++ S) b' ⦄ := by
  intro S
  induction S with
  | nil =>
    intro P b hinv _
    show WP.spec (ok b) _
    rw [WP.spec_ok]
    simpa using hinv
  | cons v S ih =>
    intro P b hinv hS
    rw [List.foldlM_cons]
    apply spec_bind (set_spec b v hp hinv.1 (hS v (by simp)))
    rintro b' ⟨hlen', hw⟩
    have h1 := inv_set P b b' v hinv hlen' hw
    have h2 := ih (P ++ [v]) b' h1 (fun u hu => hS u (by simp [hu]))
    simpa using h2

/--
Setting the bits of a set of fewer than 20 distinct keys below 1028 in a fresh
`VecBitmap::new_with_capacity(1028)` never panics, and afterwards `get(i)`
answers exactly the membership of `i` in the set, for every `i < 1028`.
-/
theorem insert_contains (values : List Std.Usize)
    (h_nodup : values.Nodup)
    (h_len : values.length < 20)
    (h_range : ∀ v ∈ values, v.val < 1028)
    (h_platform : System.Platform.numBits = 64) :
    insert_contains_spec values := by
  unfold insert_contains_spec
  apply spec_bind new_spec
  intro b0 hb0
  have hinv0 : Inv [] b0 := by
    refine ⟨by simp [hb0], ?_⟩
    intro k hk
    have : word b0 (k / 64) = 0 := by
      simp only [word, hb0, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    simp [this]
  apply spec_mono (fold_spec h_platform values [] b0 hinv0 h_range)
  intro b hb i hi
  apply spec_mono (get_spec b i h_platform hb.1 hi)
  intro r hr
  rw [hr, hb.2 i.val hi]
  simp only [List.nil_append, decide_eq_decide]
  constructor
  · rintro ⟨v, hv, hvi⟩
    have : v = i := by rw [UScalar.eq_equiv]; exact hvi
    rw [← this]; exact hv
  · intro h; exact ⟨i, h, rfl⟩

end Benchmark.Cases.Bloom2.VecBitmap
