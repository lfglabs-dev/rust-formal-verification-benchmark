import Benchmark.Cases.Plonky3.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_util

namespace Benchmark.Cases.Plonky3.Util

theorem l3_pow3_loop_spec (table : Array Std.U64 41#usize) (i : Std.Usize)
    (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ 41)
    (hinv : ∀ j < i.val, (table.val[j]!).val = 3^j) :
    POWERS_OF_3_loop table i ⦃ t => ∀ j < 41, (t.val[j]!).val = 3^j ⦄ := by
  unfold POWERS_OF_3_loop
  apply loop.spec_decr_nat (fun (p : Array Std.U64 41#usize × Std.Usize) => 41 - p.2.val)
    (fun p => 1 ≤ p.2.val ∧ p.2.val ≤ 41 ∧ ∀ j < p.2.val, (p.1.val[j]!).val = 3^j)
  · rintro ⟨tb, k⟩ ⟨hk1, hk2, hk⟩
    simp only at hk1 hk2 hk ⊢
    unfold POWERS_OF_3_loop.body
    split
    · rename_i hlt
      have hk41 : k.val < 41 := by scalar_tac
      have hlen : tb.val.length = 41 := by simp
      have hprev : (tb.val[k.val - 1]!).val = 3^(k.val - 1) := hk _ (by omega)
      have hbound : 3^(k.val - 1) * 3 ≤ 2^64 - 1 := by
        have : 3^(k.val - 1) ≤ 3^39 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      step*
      · rw [i2_post2, ← getElem!_pos, i1_post1, hprev]
        scalar_tac
      · refine ⟨by omega, by omega, ?_, by omega⟩
        intro j hj
        rw [a_post, Array.set_val_eq]
        by_cases hjk : j = k.val
        · subst hjk
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega : k.val < tb.val.length),
            Option.getD_some, i3_post, i2_post2, ← getElem!_pos, i1_post1, hprev,
            ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
        · simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjk)]
          rw [← List.getElem!_eq_getElem?_getD]
          exact hk j (by omega)
    · rename_i hge
      have hk41 : k.val = 41 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj
      exact hk j (by omega)
  · exact ⟨hi1, hi2, hinv⟩


theorem l3_pow3_spec : POWERS_OF_3 ⦃ t => ∀ j < 41, (t.val[j]!).val = 3^j ⦄ := by
  unfold POWERS_OF_3
  step*
  apply l3_pow3_loop_spec
  · simp
  · simp
  · intro j hj
    have : j = 0 := by scalar_tac
    subst this
    rw [a_post]
    simp

theorem l3_pow3_eq : ∃ t, POWERS_OF_3 = ok t ∧ ∀ j < 41, (t.val[j]!).val = 3^j :=
  spec_imp_exists l3_pow3_spec

theorem l3_lz_u64_val (x : Std.U64) (hx : x.val ≠ 0) :
    (Aeneas.Std.core.num.U64.leading_zeros x).val = 63 - Nat.log 2 x.val := by
  simp only [Aeneas.Std.core.num.U64.leading_zeros]
  change (BitVec.ofNat 32 (BitVec.leadingZeros x.bv)).toNat = _
  rw [BitVec.toNat_ofNat]
  have hbv : x.bv ≠ 0 := by
    intro h
    apply hx
    change x.bv.toNat = 0
    rw [h]; rfl
  have hlog : Nat.log 2 x.val < 64 := by
    have := x.hBounds
    exact Nat.log_lt_of_lt_pow (by omega) (by simpa using this)
  simp only [BitVec.leadingZeros, hbv, if_false]
  change (64 - Nat.log 2 x.val - 1) % 2^32 = _
  omega


theorem l3_log2_pow3_strict {j i : Nat} (h : j < i) : Nat.log 2 (3^j) < Nat.log 2 (3^i) := by
  have h1 : 3^j * 2 ≤ 3^i := by
    calc 3^j * 2 ≤ 3^j * 3 := by omega
    _ = 3^(j+1) := by rw [pow_succ]
    _ ≤ 3^i := Nat.pow_le_pow_right (by norm_num) h
  have h2 : Nat.log 2 (3^j * 2) = Nat.log 2 (3^j) + 1 := Nat.log_mul_base (by norm_num) (by positivity)
  have h3 := Nat.log_mono_right (b := 2) h1
  omega

theorem l3_log2_pow3_lt {j : Nat} (h : j < 41) : Nat.log 2 (3^j) < 64 := by
  apply Nat.log_lt_of_lt_pow (by positivity)
  calc 3^j ≤ 3^40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  _ < 2^64 := by norm_num

theorem l3_log2exp_loop_spec (t : Array Std.U64 41#usize) (ht : POWERS_OF_3 = ok t)
    (htv : ∀ j < 41, (t.val[j]!).val = 3^j)
    (table : Array Std.U8 64#usize) (i : Std.Usize) (hi : i.val ≤ 41)
    (hinv : ∀ j < i.val, (table.val[Nat.log 2 (3^j)]!).val = j) :
    LOG2_TO_EXP_loop table i ⦃ r => ∀ j < 41, (r.val[Nat.log 2 (3^j)]!).val = j ⦄ := by
  unfold LOG2_TO_EXP_loop
  apply loop.spec_decr_nat (fun (p : Array Std.U8 64#usize × Std.Usize) => 41 - p.2.val)
    (fun p => p.2.val ≤ 41 ∧ ∀ j < p.2.val, (p.1.val[Nat.log 2 (3^j)]!).val = j)
  · rintro ⟨tb, k⟩ ⟨hk1, hk⟩
    simp only at hk1 hk ⊢
    unfold LOG2_TO_EXP_loop.body
    split
    · have hk41 : k.val < 41 := by scalar_tac
      simp only [CoreModels.core.num.U64.BITS, ht, CoreModels.core.num.U64.leading_zeros,
        CoreModels.rust_primitives.arithmetic.leading_zeros_u64]
      have hlog := l3_log2_pow3_lt hk41
      have hpos : 0 < 3^k.val := by positivity
      step*
      · subst i2_post2
        have hxv : ((↑t : List Std.U64)[k.val]).val = 3^k.val := by
          rw [← getElem!_pos]; exact htv _ hk41
        rw [l3_lz_u64_val _ (by omega), i1_post1, hxv]
        simp
      · subst i2_post2
        have hxv : ((↑t : List Std.U64)[k.val]).val = 3^k.val := by
          rw [← getElem!_pos]; exact htv _ hk41
        have hlz := l3_lz_u64_val _ (by omega : ((↑t : List Std.U64)[k.val]).val ≠ 0)
        rw [hxv] at hlz
        have hi1 : i1.val = 63 := by rw [i1_post1]; simp
        have hi4 : i4.val = Nat.log 2 (3^k.val) := by rw [i4_post1, hlz, hi1]; omega
        have hl : log2.val = Nat.log 2 (3^k.val) := by
          rw [log2_post, UScalar.cast_val_eq, hi4]
          apply Nat.mod_eq_of_lt
          have : 2^6 ≤ 2^UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num) (by
            rcases System.Platform.numBits_eq with h | h <;> simp [h])
          omega
        have h5 : i5.val = k.val := by
          rw [i5_post, UScalar.cast_val_eq]
          simp only [UScalarTy.numBits]
          omega
        refine ⟨by omega, ?_, by omega⟩
        intro j hj
        rw [a1_post, Array.set_val_eq]
        by_cases hjk : j = k.val
        · subst hjk
          rw [List.getElem!_eq_getElem?_getD, hl, List.getElem?_set_self (by simp; omega),
            Option.getD_some, h5]
        · have hne : Nat.log 2 (3^j) ≠ log2.val := by
            rw [hl]
            rcases Nat.lt_or_gt_of_ne hjk with h | h
            · exact Nat.ne_of_lt (l3_log2_pow3_strict h)
            · exact Nat.ne_of_gt (l3_log2_pow3_strict h)
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne),
            ← List.getElem!_eq_getElem?_getD]
          exact hk j (by omega)
    · have hk41 : k.val = 41 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj
      exact hk j (by omega)
  · exact ⟨hi, hinv⟩


theorem l3_log2exp_spec : LOG2_TO_EXP ⦃ r => ∀ j < 41, (r.val[Nat.log 2 (3^j)]!).val = j ⦄ := by
  obtain ⟨t, ht, htv⟩ := l3_pow3_eq
  unfold LOG2_TO_EXP
  apply l3_log2exp_loop_spec t ht htv
  · simp
  · intro j hj
    simp at hj

theorem l3_lz_usize_val (h_platform : System.Platform.numBits = 64) (x : Std.Usize) (hx : x.val ≠ 0) :
    (Aeneas.Std.core.num.Usize.leading_zeros x).val = 63 - Nat.log 2 x.val := by
  simp only [Aeneas.Std.core.num.Usize.leading_zeros]
  change (BitVec.ofNat 32 (BitVec.leadingZeros x.bv)).toNat = _
  rw [BitVec.toNat_ofNat]
  have hbv : x.bv ≠ 0 := by
    intro h
    apply hx
    change x.bv.toNat = 0
    rw [h]; rfl
  have hlog : Nat.log 2 x.val < 64 := by
    have := x.hBounds
    simp only [UScalarTy.numBits, h_platform] at this
    exact Nat.log_lt_of_lt_pow (by omega) this
  simp only [BitVec.leadingZeros, hbv, if_false]
  change (UScalarTy.Usize.numBits - Nat.log 2 x.val - 1) % 2^32 = _
  simp only [UScalarTy.numBits, h_platform]
  omega

/--
`log3_strict_usize(3^k) = k` for every exponent `k < 25`: neither `3usize.pow(k)` nor the
table-driven strict base-3 logarithm (leading-zeros bucket lookup in `LOG2_TO_EXP`, verified
against `POWERS_OF_3`) panics, and the exponent is recovered.
-/
theorem log3_strict_roundtrip (k : Std.U32)
    (h_k : k.val < 25)
    (h_platform : System.Platform.numBits = 64) :
    log3_strict_roundtrip_spec k := by
  unfold log3_strict_roundtrip_spec
  obtain ⟨t, ht, htv⟩ := l3_pow3_eq
  obtain ⟨L, hL, hLv⟩ := spec_imp_exists l3_log2exp_spec
  unfold log3_strict_usize
  simp only [CoreModels.core.num.Usize.pow, CoreModels.rust_primitives.arithmetic.pow_usize,
    CoreModels.core.num.Usize.BITS,
    CoreModels.core.num.Usize.leading_zeros, CoreModels.rust_primitives.arithmetic.leading_zeros_usize,
    ht, hL]
  have hk64 : 3^k.val < 2^64 := by
    calc 3^k.val ≤ 3^24 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 2^64 := by norm_num
  obtain ⟨n, hn, hnv⟩ : ∃ n, UScalar.tryMk UScalarTy.Usize (3^k.val) = ok n ∧ n.val = 3^k.val := by
    have htm := UScalar.tryMk_eq UScalarTy.Usize (3^k.val)
    have hin : UScalar.inBounds UScalarTy.Usize (3^k.val) := by
      simp [UScalar.inBounds, UScalarTy.numBits, h_platform]
      omega
    revert htm
    cases UScalar.tryMk UScalarTy.Usize (3^k.val) <;> simp_all
  simp only [show ((3#usize : Std.Usize).val) = 3 from rfl, hn, bind_tc_ok]
  have hpos : 0 < 3^k.val := by positivity
  have hk41 : k.val < 41 := by omega
  have hlz := l3_lz_usize_val h_platform n (by omega)
  rw [hnv] at hlz
  have hlog := l3_log2_pow3_lt hk41
  have hnb : UScalarTy.Usize.numBits = 64 := by simp [UScalarTy.numBits, h_platform]
  step*
  · subst i3_post2
    have hl : log2.val = Nat.log 2 (3^k.val) := by
      rw [log2_post, UScalar.cast_val_eq, i2_post1, hlz, i_post1, hnb]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hx : ((↑L : List U8)[log2.val]).val = k.val := by
      rw [← getElem!_pos, hl]; exact hLv _ hk41
    rw [res_post, UScalar.cast_val_eq, hx, hnb]
    simp
    omega
  · subst i3_post2 i4_post2
    have hl : log2.val = Nat.log 2 (3^k.val) := by
      rw [log2_post, UScalar.cast_val_eq, i2_post1, hlz, i_post1, hnb]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hx : ((↑L : List U8)[log2.val]).val = k.val := by
      rw [← getElem!_pos, hl]; exact hLv _ hk41
    have hres : res.val = k.val := by
      rw [res_post, UScalar.cast_val_eq, hx, hnb]
      simp
      omega
    have hy : ((↑t : List U64)[res.val]).val = 3^k.val := by
      rw [← getElem!_pos, hres]; exact htv _ hk41
    have hi5 : i5.val = 3^k.val := by
      rw [i5_post, UScalar.cast_val_eq, hy, hnb]
      exact Nat.mod_eq_of_lt hk64
    simp only [not_not]
    exact (UScalar.eq_equiv i5 n).mpr (by rw [hi5, hnv])
  · subst i3_post2
    have hl : log2.val = Nat.log 2 (3^k.val) := by
      rw [log2_post, UScalar.cast_val_eq, i2_post1, hlz, i_post1, hnb]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hx : ((↑L : List U8)[log2.val]).val = k.val := by
      rw [← getElem!_pos, hl]; exact hLv _ hk41
    rw [res_post, UScalar.cast_val_eq, hx, hnb]
    simp
    omega

end Benchmark.Cases.Plonky3.Util
