import Benchmark.Cases.Memchr.Twoway.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open memchr

namespace Benchmark.Cases.Memchr.Twoway


theorem drop_cons' (L : List Nat) (a : Nat) (h : a < L.length) :
    L.drop a = L[a]! :: L.drop (a + 1) := by
  rw [getElem!_pos L a h]; exact List.drop_eq_getElem_cons h

theorem drop_lt_of_mismatch (L : List Nat) :
    ∀ (d a b : Nat), (∀ s, s < d → L[a + s]! = L[b + s]!) →
      a + d < L.length → b + d < L.length → L[a + d]! < L[b + d]! →
      List.Lex (· < ·) (L.drop a) (L.drop b) := by
  intro d
  induction d with
  | zero =>
    intro a b _ ha hb hlt
    rw [drop_cons' L a (by omega), drop_cons' L b (by omega)]
    exact List.Lex.rel hlt
  | succ d ih =>
    intro a b hag ha hb hlt
    have h0 := hag 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [drop_cons' L a (by omega), drop_cons' L b (by omega), h0]
    apply List.Lex.cons
    apply ih (a + 1) (b + 1)
    · intro s hs
      have := hag (s + 1) (by omega)
      rwa [show a + 1 + s = a + (s + 1) by omega, show b + 1 + s = b + (s + 1) by omega]
    · omega
    · omega
    · rwa [show a + 1 + d = a + (d + 1) by omega, show b + 1 + d = b + (d + 1) by omega]

theorem drop_lt_of_prefix (L : List Nat) :
    ∀ (m a b : Nat), a + m = L.length → b < a →
      (∀ s, s < m → L[a + s]! = L[b + s]!) →
      List.Lex (· < ·) (L.drop a) (L.drop b) := by
  intro m
  induction m with
  | zero =>
    intro a b ha hba _
    rw [List.drop_eq_nil_of_le (by omega), drop_cons' L b (by omega)]
    exact List.Lex.nil
  | succ m ih =>
    intro a b ha hba hag
    have h0 := hag 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [drop_cons' L a (by omega), drop_cons' L b (by omega), h0]
    apply List.Lex.cons
    apply ih (a + 1) (b + 1) (by omega) (by omega)
    intro s hs
    have := hag (s + 1) (by omega)
    rwa [show a + 1 + s = a + (s + 1) by omega, show b + 1 + s = b + (s + 1) by omega]

theorem mod_add_small (r s p : Nat) (h : r % p + s < p) : (r + s) % p = r % p + s := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show s < p by omega), Nat.mod_eq_of_lt h]

theorem mod_shift (M s p : Nat) (h : M % p = 0) : (M + s) % p = s % p := by
  rw [Nat.add_mod, h, Nat.zero_add, Nat.mod_mod]

theorem block_bound (r M p : Nat) (hp : 0 < p) (hM : M % p = 0) (hr : r < M) :
    r + (p - r % p) ≤ M := by
  have h1 := Nat.div_add_mod r p
  have h2 := Nat.div_add_mod M p
  rw [hM, Nat.add_zero] at h2
  have h3 : r / p < M / p := Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero hM) hr
  have h4 : p * (r / p + 1) ≤ p * (M / p) := Nat.mul_le_mul_left p h3
  rw [Nat.mul_succ] at h4
  have h5 := Nat.mod_lt r hp
  omega

theorem mult_ge (M p : Nat) (hM : M % p = 0) (h : 0 < M) : p ≤ M := by
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hM
  omega

/-- Invariant of the `Suffix::forward` (`SuffixKind::Maximal`) loop, stated on the
byte values `L`: `i` = `suffix.pos`, `p` = `suffix.period`, `j` =
`candidate_start`, `k` = `offset`. -/
structure FwdInv (L : List Nat) (i p j k : Nat) : Prop where
  hij : i < j
  hp : 0 < p
  hkp : k < p
  hjk : j + k ≤ L.length
  hmod : (j - i) % p = 0
  per : ∀ s, i + s < j + k → L[i + s]! = L[i + s % p]!
  lyn : ∀ t, 0 < t → t < p → ∃ d, t + d < p ∧
    (∀ s, s < d → L[i + t + s]! = L[i + s]!) ∧ L[i + t + d]! < L[i + d]!
  left : ∀ q, q < i → List.Lex (· < ·) (L.drop q) (L.drop i)

theorem FwdInv.per_shift {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (r s : Nat) (hr : r % p = 0) (hb : i + r + s < j + k) :
    L[i + r + s]! = L[i + s]! := by
  have h1 := h.per (r + s) (by omega)
  have h2 := h.per s (by omega)
  rw [mod_shift r s p hr] at h1
  rw [Nat.add_assoc, h1, h2]

theorem FwdInv.per_off {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (r s : Nat) (hs : r % p + s < p) (hb : i + r + s < j + k) :
    L[i + r + s]! = L[i + r % p + s]! := by
  have h1 := h.per (r + s) (by omega)
  rw [mod_add_small r s p hs] at h1
  rw [Nat.add_assoc, h1, Nat.add_assoc]

theorem FwdInv.nonspecial_lt {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (r : Nat) (hr : r % p ≠ 0) (hq : i + r < j) :
    List.Lex (· < ·) (L.drop (i + r)) (L.drop i) := by
  have hp := h.hp
  have ht := Nat.mod_lt r hp
  obtain ⟨d, hd, hag, hlt⟩ := h.lyn (r % p) (by omega) ht
  have hblk := block_bound r (j - i) p hp h.hmod (by omega)
  have hjk := h.hjk
  apply drop_lt_of_mismatch L d (i + r) i
  · intro s hs
    rw [h.per_off r s (by omega) (by omega)]
    exact hag s hs
  · omega
  · omega
  · rw [h.per_off r d (by omega) (by omega)]
    exact hlt

theorem lex_trans {a b c : List Nat} (h1 : List.Lex (· < ·) a b) (h2 : List.Lex (· < ·) b c) :
    List.Lex (· < ·) a c := List.lt_trans (α := Nat) h1 h2

theorem FwdInv.final {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (hend : j + k = L.length) :
    i < L.length ∧ ∀ q, q < L.length →
      List.Lex (· < ·) (L.drop q) (L.drop i) ∨ L.drop q = L.drop i := by
  have hp := h.hp
  have hij := h.hij
  refine ⟨by omega, ?_⟩
  intro q hq
  rcases Nat.lt_trichotomy q i with hqi | hqi | hqi
  · exact Or.inl (h.left q hqi)
  · subst hqi; exact Or.inr rfl
  · apply Or.inl
    obtain ⟨r, rfl⟩ : ∃ r, q = i + r := ⟨q - i, by omega⟩
    by_cases hr : r % p = 0
    · apply drop_lt_of_prefix L (L.length - (i + r)) (i + r) i (by omega) (by omega)
      intro s hs
      exact h.per_shift r s hr (by omega)
    · have ht := Nat.mod_lt r hp
      obtain ⟨d, hd, hag, hlt⟩ := h.lyn (r % p) (by omega) ht
      have htr : r % p ≤ r := Nat.mod_le r p
      by_cases hqd : i + r + d < L.length
      · apply drop_lt_of_mismatch L d (i + r) i
        · intro s hs
          rw [h.per_off r s (by omega) (by omega)]
          exact hag s hs
        · omega
        · omega
        · rw [h.per_off r d (by omega) (by omega)]
          exact hlt
      · apply drop_lt_of_prefix L (L.length - (i + r)) (i + r) i (by omega) (by omega)
        intro s hs
        rw [h.per_off r s (by omega) (by omega)]
        exact hag s (by omega)

theorem FwdInv.init (L : List Nat) (hn : 0 < L.length) : FwdInv L 0 1 1 0 where
  hij := by omega
  hp := by omega
  hkp := by omega
  hjk := by omega
  hmod := by simp
  per := by
    intro s hs
    obtain rfl : s = 0 := by omega
    rfl
  lyn := by intro t ht1 ht2; omega
  left := by intro q hq; omega

theorem FwdInv.accept {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (hlen : j + k < L.length) (hlt : L[i + k]! < L[j + k]!) :
    FwdInv L j 1 (j + 1) 0 := by
  have hp := h.hp
  have hij := h.hij
  have hkp := h.hkp
  have hjj : ∀ s, s < k → L[j + s]! = L[i + s]! := by
    intro s hs
    have := h.per_shift (j - i) s h.hmod (by omega)
    rwa [show i + (j - i) + s = j + s by omega] at this
  have hji : List.Lex (· < ·) (L.drop i) (L.drop j) := by
    apply drop_lt_of_mismatch L k i j
    · intro s hs; rw [hjj s hs]
    · omega
    · omega
    · exact hlt
  refine ⟨by omega, by omega, by omega, by omega, by simp, ?_, ?_, ?_⟩
  · intro s hs
    rw [show s = 0 by omega]
  · intro t ht1 ht2; omega
  · intro q hq
    rcases Nat.lt_or_ge q i with hqi | hqi
    · exact lex_trans (h.left q hqi) hji
    · obtain ⟨r, rfl⟩ : ∃ r, q = i + r := ⟨q - i, by omega⟩
      by_cases hr : r % p = 0
      · apply drop_lt_of_mismatch L k (i + r) j
        · intro s hs
          rw [h.per_shift r s hr (by omega), hjj s hs]
        · omega
        · omega
        · rw [h.per_shift r k hr (by omega)]
          exact hlt
      · exact lex_trans (h.nonspecial_lt r hr hq) hji

theorem FwdInv.per_ext {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (heq : L[j + k]! = L[i + k]!) :
    ∀ s, i + s < j + k + 1 → L[i + s]! = L[i + s % p]! := by
  intro s hs
  by_cases hs' : i + s < j + k
  · exact h.per s hs'
  · have hij := h.hij
    have hkp := h.hkp
    have hs2 : s = (j - i) + k := by omega
    rw [hs2, mod_shift (j - i) k p h.hmod, Nat.mod_eq_of_lt hkp,
      show i + (j - i + k) = j + k by omega, heq]

theorem FwdInv.push_period {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (heq : L[j + k]! = L[i + k]!) (hlen : j + k < L.length) (hk : k + 1 = p) :
    FwdInv L i p (j + p) 0 := by
  have hij := h.hij
  have hp := h.hp
  refine ⟨by omega, hp, hp, by omega, ?_, ?_, h.lyn, h.left⟩
  · rw [show j + p - i = (j - i) + p by omega, Nat.add_mod_right]; exact h.hmod
  · intro s hs
    exact h.per_ext heq s (by omega)

theorem FwdInv.push_offset {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (heq : L[j + k]! = L[i + k]!) (hlen : j + k < L.length) (hk : k + 1 ≠ p) :
    FwdInv L i p j (k + 1) := by
  have hkp := h.hkp
  refine ⟨h.hij, h.hp, by omega, by omega, h.hmod, ?_, h.lyn, h.left⟩
  intro s hs
  exact h.per_ext heq s (by omega)

theorem FwdInv.skip {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k)
    (hlen : j + k < L.length) (hlt : L[j + k]! < L[i + k]!) :
    FwdInv L i (j + k + 1 - i) (j + k + 1) 0 := by
  have hp := h.hp
  have hij := h.hij
  have hkp := h.hkp
  refine ⟨by omega, by omega, by omega, by omega, by simp, ?_, ?_, h.left⟩
  · intro s hs
    rw [Nat.mod_eq_of_lt (by omega)]
  · intro t ht1 ht2
    by_cases hC : j < i + t
    · -- the candidate lies in the partial period `(j, j + k]`
      obtain ⟨t', rfl⟩ : ∃ t', t = (j - i) + t' := ⟨t - (j - i), by omega⟩
      have hjj : ∀ s, t' + s < k → L[i + (j - i + t') + s]! = L[i + t' + s]! := by
        intro s hs
        have := h.per_shift (j - i) (t' + s) h.hmod (by omega)
        rw [show i + (j - i + t') + s = i + (j - i) + (t' + s) by omega,
          show i + t' + s = i + (t' + s) by omega]
        exact this
      obtain ⟨d0, hd0, hag0, hlt0⟩ := h.lyn t' (by omega) (by omega)
      by_cases hsmall : t' + d0 < k
      · refine ⟨d0, by omega, ?_, ?_⟩
        · intro s hs
          rw [hjj s (by omega)]
          exact hag0 s hs
        · rw [hjj d0 hsmall]
          exact hlt0
      · refine ⟨k - t', by omega, ?_, ?_⟩
        · intro s hs
          rw [hjj s (by omega)]
          exact hag0 s (by omega)
        · rw [show i + (j - i + t') + (k - t') = j + k by omega]
          by_cases hgt : k < t' + d0
          · have := hag0 (k - t') (by omega)
            rw [show i + t' + (k - t') = i + k by omega] at this
            rw [← this]; exact hlt
          · have hEq : t' + d0 = k := by omega
            rw [show i + t' + d0 = i + k by omega] at hlt0
            rw [show k - t' = d0 by omega]
            exact Nat.lt_trans hlt hlt0
    · by_cases hr : t % p = 0
      · -- a full-period shift of `i` (`i < i + t ≤ j`)
        refine ⟨j + k - i - t, by omega, ?_, ?_⟩
        · intro s hs
          exact h.per_shift t s hr (by omega)
        · rw [show i + t + (j + k - i - t) = j + k by omega]
          have hm : (j - i - t) % p = 0 := by
            apply Nat.sub_mod_eq_zero_of_mod_eq
            rw [h.hmod, hr]
          have := h.per_shift (j - i - t) k hm (by omega)
          rw [show i + (j - i - t) + k = i + (j + k - i - t) by omega] at this
          rw [this]; exact hlt
      · -- a non-special position of the current window
        have ht := Nat.mod_lt t hp
        obtain ⟨d, hd, hag, hlt'⟩ := h.lyn (t % p) (by omega) ht
        have htne : t ≠ j - i := fun he => hr (he ▸ h.hmod)
        have hblk := block_bound t (j - i) p hp h.hmod (by omega)
        refine ⟨d, by omega, ?_, ?_⟩
        · intro s hs
          rw [h.per_off t s (by omega) (by omega)]
          exact hag s hs
        · rw [h.per_off t d (by omega) (by omega)]
          exact hlt'

theorem FwdInv.accept_measure {L : List Nat} {i p j k : Nat} (h : FwdInv L i p j k) :
    i + j + k < j + (j + 1) + 0 := by
  have := mult_ge (j - i) p h.hmod (by have := h.hij; omega)
  have := h.hkp
  omega


@[local step]
theorem slice_len_spec' (s : Slice Std.U8) :
    core.slice.Slice.len s ⦃ r => r.val = s.length ⦄ := by
  simp [core.slice.Slice.len, rust_primitives.slice.slice_length]

@[local step]
theorem cmp_maximal_spec (a b : Std.U8) :
    arch.all.twoway.SuffixKind.cmp arch.all.twoway.SuffixKind.Maximal a b ⦃ r =>
      (a.val < b.val → r = arch.all.twoway.SuffixOrdering.Accept) ∧
      (b.val < a.val → r = arch.all.twoway.SuffixOrdering.Skip) ∧
      (a.val = b.val → r = arch.all.twoway.SuffixOrdering.Push) ⦄ := by
  unfold arch.all.twoway.SuffixKind.cmp
  by_cases h1 : a.val < b.val
  · simp [h1]; try omega
  · by_cases h2 : b.val < a.val
    · simp [h1, h2]; try omega
    · simp [h1, h2]; try omega

theorem byteVals_getElem! (l : List Std.U8) (a : Nat) (h : a < l.length) :
    (byteVals l)[a]! = (l[a]'h).val := by
  simp [byteVals, getElem!_pos, h]

theorem byteVals_length (l : List Std.U8) : (byteVals l).length = l.length := by
  simp [byteVals]

theorem forward_loop_spec (needle : Slice Std.U8) (i p j k : Std.Usize)
    (h : FwdInv (byteVals needle.val) i.val p.val j.val k.val) :
    arch.all.twoway.Suffix.forward_loop needle arch.all.twoway.SuffixKind.Maximal i p j k
      ⦃ r => r.1.val < (byteVals needle.val).length ∧ ∀ q, q < (byteVals needle.val).length →
          List.Lex (· < ·) ((byteVals needle.val).drop q) ((byteVals needle.val).drop r.1.val) ∨
          (byteVals needle.val).drop q = (byteVals needle.val).drop r.1.val ⦄ := by
  unfold arch.all.twoway.Suffix.forward_loop
  apply loop.spec_decr_nat
    (fun (x : Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
      2 * needle.length - (x.1.val + x.2.2.1.val + x.2.2.2.val))
    (fun x => FwdInv (byteVals needle.val) x.1.val x.2.1.val x.2.2.1.val x.2.2.2.val)
  · rintro ⟨i, p, j, k⟩ hinv
    simp only at hinv ⊢
    have hlenL := byteVals_length needle.val
    have hmax : needle.length ≤ Usize.max := needle.property
    have hjk := hinv.hjk
    have hij := hinv.hij
    have hkp := hinv.hkp
    unfold arch.all.twoway.Suffix.forward_loop.body
    have hsum : i.val + j.val + k.val < 2 * needle.length := by
      rw [hlenL] at hjk; simp only [Slice.length] at hmax ⊢; omega
    let* ⟨ i2, i2_post ⟩ ← Usize.add_spec.step_spec
    let* ⟨ i3, i3_post ⟩ ← slice_len_spec'
    spec_split
    · rename_i hloop
      have hlt23 : j.val + k.val < (byteVals needle.val).length := by
        rw [hlenL]; have := (UScalar.lt_equiv i2 i3).mp hloop; simp only [Slice.length] at i3_post; omega
      let* ⟨ i4, i4_post ⟩ ← Usize.add_spec.step_spec
      let* ⟨ hcur_lt, current, current_post2 ⟩ ← Slice.index_usize_spec.step_spec
      let* ⟨ hcand_lt, candidate, candidate_post2 ⟩ ← Slice.index_usize_spec.step_spec
      have hcur : (byteVals needle.val)[i.val + k.val]! = current.val := by
        rw [current_post2, byteVals_getElem! _ _ (by omega)]; simp only [i4_post]
      have hcand : (byteVals needle.val)[j.val + k.val]! = candidate.val := by
        rw [candidate_post2, byteVals_getElem! _ _ (by omega)]; simp only [i2_post]
      let* ⟨ so, so_post1, so_post2, so_post3 ⟩ ← cmp_maximal_spec
      spec_split
      · rename_i hso
        have hlt : current.val < candidate.val := by
          rcases Nat.lt_trichotomy current.val candidate.val with h | h | h
          · exact h
          · have := so_post3 h; rw [hso] at this; cases this
          · have := so_post2 h; rw [hso] at this; cases this
        let* ⟨ candidate_start1, candidate_start1_post ⟩ ← Usize.add_spec.step_spec
        have hacc := hinv.accept hlt23 (by rw [hcur, hcand]; exact hlt)
        have hm := hinv.accept_measure
        refine ⟨?_, ?_⟩
        · rw [candidate_start1_post]; simpa using hacc
        · rw [candidate_start1_post]; scalar_tac
      · rename_i hso
        have hlt : candidate.val < current.val := by
          rcases Nat.lt_trichotomy current.val candidate.val with h | h | h
          · have := so_post1 h; rw [hso] at this; cases this
          · have := so_post3 h; rw [hso] at this; cases this
          · exact h
        let* ⟨ i5, i5_post ⟩ ← Usize.add_spec.step_spec
        let* ⟨ candidate_start1, candidate_start1_post ⟩ ← Usize.add_spec.step_spec
        let* ⟨ i6, i6_post1, i6_post2 ⟩ ← Usize.sub_spec.step_spec
        have hskip := hinv.skip hlt23 (by rw [hcur, hcand]; exact hlt)
        have e1 : i6.val = j.val + k.val + 1 - i.val := by omega
        have e2 : candidate_start1.val = j.val + k.val + 1 := by omega
        refine ⟨?_, ?_⟩
        · rw [e1, e2]; simpa using hskip
        · rw [e2]; scalar_tac
      · rename_i hso
        have heq : current.val = candidate.val := by
          rcases Nat.lt_trichotomy current.val candidate.val with h | h | h
          · have := so_post1 h; rw [hso] at this; cases this
          · exact h
          · have := so_post2 h; rw [hso] at this; cases this
        have heqL : (byteVals needle.val)[j.val + k.val]! = (byteVals needle.val)[i.val + k.val]! := by
          rw [hcur, hcand, heq]
        let* ⟨ i5, i5_post ⟩ ← Usize.add_spec.step_spec
        spec_split
        · rename_i hper
          have hk : k.val + 1 = p.val := by rw [← i5_post, hper]
          let* ⟨ candidate_start1, candidate_start1_post ⟩ ← Usize.add_spec.step_spec
          have hpp := hinv.push_period heqL hlt23 hk
          refine ⟨?_, ?_⟩
          · rw [candidate_start1_post]; simpa using hpp
          · rw [candidate_start1_post]; scalar_tac
        · rename_i hper
          have hk : k.val + 1 ≠ p.val := by
            intro hc; apply hper; apply UScalar.eq_of_val_eq; rw [i5_post, hc]
          simp only [step_simps]
          have hpo := hinv.push_offset heqL hlt23 hk
          refine ⟨?_, ?_⟩
          · rw [i5_post]; exact hpo
          · rw [i5_post]; omega
    · rename_i hloop
      simp only [step_simps]
      have hend : j.val + k.val = (byteVals needle.val).length := by
        rw [hlenL]; have := (UScalar.lt_equiv i2 i3).not.mp hloop; simp only [Slice.length] at i3_post hjk; omega
      exact hinv.final hend
  · exact h


theorem index_range_from_spec (s : Slice Std.U8) (a : Std.Usize) (h : a.val ≤ s.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      s { start := a } ⦃ r => r.val = s.val.drop a.val ⦄ := by
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice]
  simp [h, Slice.subslice, List.slice]

/--
For every non-empty byte string, the Crochemore-Perrin maximal-suffix
routine `Suffix::forward(bytes, SuffixKind::Maximal)` of the Two-Way
substring searcher terminates without panicking, and `&bytes[s.pos..]` is
the lexicographically greatest non-empty suffix of `bytes` (the value of the
naive sort-all-suffixes reference implementation).
-/
theorem suffix_forward_maximal (bytes : Slice Std.U8)
    (h_assume_nonempty : 0 < bytes.length) :
    suffix_forward_maximal_spec bytes := by
  unfold suffix_forward_maximal_spec arch.all.twoway.Suffix.forward
  have hinit : FwdInv (byteVals bytes.val) (0#usize : Std.Usize).val (1#usize : Std.Usize).val
      (1#usize : Std.Usize).val (0#usize : Std.Usize).val := by
    have := FwdInv.init (byteVals bytes.val) (by rw [byteVals_length]; exact h_assume_nonempty)
    simpa using this
  have hloop := forward_loop_spec bytes _ _ _ _ hinit
  step with hloop as ⟨r, hr1, hr2⟩
  obtain ⟨i, i1⟩ := r
  simp only at hr1 hr2 ⊢
  rw [byteVals_length] at hr1
  step with index_range_from_spec as ⟨got, hgot⟩
  rw [hgot]
  refine ⟨⟨i.val, hr1, rfl⟩, ?_⟩
  intro q hq
  unfold BytesLe byteVals
  rw [List.map_drop, List.map_drop]
  exact hr2 q (by rw [byteVals_length]; exact hq)

end Benchmark.Cases.Memchr.Twoway
