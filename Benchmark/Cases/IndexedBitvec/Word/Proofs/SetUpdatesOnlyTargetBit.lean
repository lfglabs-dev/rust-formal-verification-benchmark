import Benchmark.Cases.IndexedBitvec.Word.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core

namespace Benchmark.Cases.IndexedBitvec.Word

theorem testBit_not64 (m : Std.U64) (k : Nat) :
    (~~~m).val.testBit k = (decide (k < 64) && !m.val.testBit k) := by
  have h1 : (~~~m).val = (~~~m.bv).toNat := rfl
  have h2 : m.val = m.bv.toNat := rfl
  rw [h1, h2, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]

theorem testBit_ge64 (x : Std.U64) (k : Nat) (hk : 64 ≤ k) : x.val.testBit k = false := by
  apply Nat.testBit_eq_false_of_lt
  have : x.val < 2^64 := by scalar_tac
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hk)

theorem set_copy_spec (x : word.Word) (idx : Std.Usize) (b : Bool) (hi : idx.val < 64) :
    word.Word.set_copy x idx b ⦃ r => ∃ y : word.Word, r = core.option.Option.Some y ∧
      ∀ k, y.val.testBit k = if k = 63 - idx.val then b else x.val.testBit k ⦄ := by
  unfold word.Word.set_copy word.Word.index_check word.Word.len
  have : ¬ (idx ≥ 64#usize) := by scalar_tac
  simp only [this, ↓reduceIte, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    U64.Insts.CoreConvertFromWord.from, core.convert.Into.Blanket.into, word.Word.Insts.CoreConvertFromU64,
    word.Word.Insts.CoreConvertFromU64.from]
  step*
  have hi1 : i1.val = 63 - idx.val := by
    rw [i1_post, UScalar.cast_val_eq, i_post1]; apply Nat.mod_eq_of_lt; simp; omega
  have hm : mask.val = 2 ^ (63 - idx.val) := by
    have : 2^(63 - idx.val) < 2^64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [mask_post1, hi1, Nat.shiftLeft_eq, one_mul]; apply Nat.mod_eq_of_lt
    simpa [U64.size, U64.numBits] using this
  rcases Bool.eq_false_or_eq_true b with hb | hb
  · simp only [hb, ↓reduceIte, bind_tc_ok, WP.spec_ok]
    refine ⟨_, rfl, fun k => ?_⟩
    rw [UScalar.val_or, Nat.testBit_or, hm, Nat.testBit_two_pow]
    by_cases hkm : k = 63 - idx.val
    · subst hkm; simp
    · simp [hkm, Ne.symm hkm]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, lift, bind_tc_ok, WP.spec_ok]
    refine ⟨_, rfl, fun k => ?_⟩
    rw [UScalar.val_and, Nat.testBit_and, testBit_not64, hm, Nat.testBit_two_pow]
    by_cases hk : k < 64
    · by_cases hkm : k = 63 - idx.val
      · subst hkm; simp
      · simp [hkm, hk, Ne.symm hkm]
    · have := testBit_ge64 x k (by omega)
      have hkm : k ≠ 63 - idx.val := by omega
      simp [hkm, hk, this]

theorem set_spec (x : word.Word) (i : Std.Usize) (b : Bool) (hi : i.val < 64) :
    word.Word.set x i b ⦃ r => r.1 = core.option.Option.Some () ∧
      ∀ k, r.2.val.testBit k = if k = 63 - i.val then b else x.val.testBit k ⦄ := by
  unfold word.Word.set
  apply WP.spec_bind (set_copy_spec x i b hi)
  rintro r ⟨y, hr, hy⟩
  simp only [hr, core.option.Option.Some]
  exact (WP.spec_ok _).mpr ⟨rfl, hy⟩

theorem get_spec (x : word.Word) (j : Std.Usize) (hj : j.val < 64) :
    word.Word.get x j ⦃ r => r = core.option.Option.Some (x.val.testBit (63 - j.val)) ⦄ := by
  unfold word.Word.get word.Word.index_check word.Word.len
  have : ¬ (j ≥ 64#usize) := by scalar_tac
  simp only [this, ↓reduceIte, bind_tc_ok]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok, U64.Insts.CoreConvertFromWord.from]
  step*
  have hi2 : i2.val = 63 - j.val := by
    rw [i2_post, UScalar.cast_val_eq, i1_post1]; apply Nat.mod_eq_of_lt; simp; omega
  have hi3 : i3.val = 2 ^ (63 - j.val) := by
    have : 2^(63 - j.val) < 2^64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [i3_post1, hi2, Nat.shiftLeft_eq, one_mul]; apply Nat.mod_eq_of_lt
    simpa [U64.size, U64.numBits] using this
  have hi4 : i4.val = x.val &&& 2 ^ (63 - j.val) := by
    rw [i4_post1, UScalar.val_and, hi3]
  congr 1
  have h0 : (i4 > 0#u64) ↔ 0 < i4.val := by constructor <;> intro h <;> scalar_tac
  rw [Bool.eq_iff_iff, decide_eq_true_iff, h0, hi4, Nat.and_two_pow]
  cases (x.val.testBit (63 - j.val)) <;> simp

/--
For every word `x` and all bit indices `i, j < 64`, `Word::set(i, true)` and
`Word::set(i, false)` succeed (return `Some(())`), after which `get(i)` reports
the written bit and `get(j)` for `j ≠ i` reports the original bit of `x`.
-/
theorem set_updates_only_target_bit (x : word.Word) :
    set_updates_only_target_bit_spec x := by
  intro i j hi hj
  apply WP.spec_bind (set_spec x i true hi)
  rintro ⟨rt, st⟩ ⟨hrt, hst⟩
  apply WP.spec_bind (set_spec x i false hi)
  rintro ⟨rf, sf⟩ ⟨hrf, hsf⟩
  simp only at hrt hst hrf hsf ⊢
  apply WP.spec_bind (get_spec st j hj)
  intro gt hgt
  apply WP.spec_bind (get_spec sf j hj)
  intro gf hgf
  apply WP.spec_bind (get_spec x j hj)
  intro g hg
  apply (WP.spec_ok _).mpr
  refine ⟨hrt, hrf, ?_⟩
  rw [hgt, hgf, hg, hst, hsf]
  split
  · rename_i hij; subst hij; simp
  · rename_i hij
    have : 63 - j.val ≠ 63 - i.val := by
      intro h; apply hij; apply UScalar.eq_of_val_eq; omega
    simp [this]

end Benchmark.Cases.IndexedBitvec.Word
