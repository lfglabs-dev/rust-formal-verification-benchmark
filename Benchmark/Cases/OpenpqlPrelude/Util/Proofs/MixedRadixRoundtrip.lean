import Benchmark.Cases.OpenpqlPrelude.Util.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open openpql_prelude

namespace Benchmark.Cases.OpenpqlPrelude.Util

/-- `mrTail D O r = Σ_{k ≥ r} D[k] * O[k]`. -/
def mrTail (D O : List Nat) (r : Nat) : Nat := ((List.zipWith (· * ·) D O).drop r).sum

/-- `mrHead D O r = Σ_{k < r} D[k] * O[k]`. -/
def mrHead (D O : List Nat) (r : Nat) : Nat := ((List.zipWith (· * ·) D O).take r).sum

theorem mr_tail_succ (D O : List Nat) (r : Nat) (hD : r < D.length) (hO : r < O.length) :
    mrTail D O r = D[r] * O[r] + mrTail D O (r + 1) := by
  unfold mrTail
  rw [List.drop_eq_getElem_cons (by simp; omega), List.sum_cons, List.getElem_zipWith]

theorem mr_head_succ (D O : List Nat) (r : Nat) (hD : r < D.length) (hO : r < O.length) :
    mrHead D O (r + 1) = mrHead D O r + D[r] * O[r] := by
  unfold mrHead
  rw [List.sum_take_succ _ _ (by simp; omega), List.getElem_zipWith]

theorem mr_head_le (D O : List Nat) (r : Nat) : mrHead D O r ≤ mrHead D O D.length := by
  unfold mrHead
  have h1 := List.sum_take_add_sum_drop (List.zipWith (· * ·) D O) r
  have h2 : (List.zipWith (· * ·) D O).take D.length = List.zipWith (· * ·) D O := by
    apply List.take_of_length_le; simp
  rw [h2]; omega

/-- The dot-product loop accumulates `Σ a[k] * b[k]` (no overflow if the total fits). -/
theorem mr_dot_loop (a b : Std.Array Std.U64 4#usize)
    (hfit : mrHead (a.val.map (·.val)) (b.val.map (·.val)) 4 ≤ U64.max) :
    ∀ (res : Std.U64) (i : Std.Usize), i.val ≤ 4 →
      res.val = mrHead (a.val.map (·.val)) (b.val.map (·.val)) i.val →
      waugh_indexer.util.dot_product_loop a b res i ⦃ r =>
        r.val = mrHead (a.val.map (·.val)) (b.val.map (·.val)) 4 ⦄ := by
  intro res0 i0 hi0 hres0
  unfold waugh_indexer.util.dot_product_loop
  apply loop.spec_decr_nat (fun p : Std.U64 × Std.Usize => 4 - p.2.val)
    (fun p => p.2.val ≤ 4 ∧ p.1.val = mrHead (a.val.map (·.val)) (b.val.map (·.val)) p.2.val)
  · rintro ⟨res, i⟩ ⟨hi, hres⟩
    simp only at hi hres ⊢
    unfold waugh_indexer.util.dot_product_loop.body
    by_cases hlt : i.val < 4
    · have hlt' : i < 4#usize := by scalar_tac
      simp only [hlt', if_true]
      have hla : (a.val.map (·.val)).length = 4 := by simp
      have hlb : (b.val.map (·.val)).length = 4 := by simp
      have hsucc := mr_head_succ (a.val.map (·.val)) (b.val.map (·.val)) i.val (by omega) (by omega)
      have hle := mr_head_le (a.val.map (·.val)) (b.val.map (·.val)) (i.val + 1)
      rw [hla] at hle
      simp only [List.getElem_map] at hsucc
      step as ⟨_h1, x, hx⟩
      step as ⟨_h2, y, hy⟩
      have hxy : x.val * y.val ≤ U64.max := by
        rw [hx, hy]; omega
      step as ⟨z, hz⟩
      have hsum : res.val + z.val ≤ U64.max := by rw [hz, hx, hy, hres]; omega
      step as ⟨res1, hres1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by omega, ?_, by omega⟩
      rw [hres1, hz, hx, hy, hres, hi1, hsucc]
    · have hge : ¬ i < 4#usize := by scalar_tac
      simp only [hge, if_false, WP.spec_ok]
      have : i.val = 4 := by omega
      rw [hres, this]
  · exact ⟨hi0, hres0⟩

theorem mr_div_mod (d o t : Nat) (ht : t < o) :
    (d * o + t) / o = d ∧ (d * o + t) % o = t := by
  have ho : 0 < o := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ ho, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- The decoding loop recovers the digits `D` from `Σ D[k] * O[k]`. -/
theorem mr_decode_loop (self : waugh_indexer.mixed_radix.MixedRadix 4#usize) (D : List Nat)
    (hD : D.length = 4)
    (hcond : ∀ r < 4, mrTail D (self.offsets.val.map (·.val)) (r + 1) <
      (self.offsets.val.map (·.val))[r]!) :
    ∀ (idx : Std.U64) (digits : Std.Array Std.U64 4#usize) (round : Std.Usize),
      round.val ≤ 4 → idx.val = mrTail D (self.offsets.val.map (·.val)) round.val →
      (∀ k < round.val, (digits.val[k]!).val = D[k]!) →
      waugh_indexer.mixed_radix.MixedRadix.decode_loop self idx digits round ⦃ out =>
        ∀ k < 4, (out.val[k]!).val = D[k]! ⦄ := by
  intro idx0 digits0 round0 hr0 hidx0 hdig0
  unfold waugh_indexer.mixed_radix.MixedRadix.decode_loop
  apply loop.spec_decr_nat (fun p : Std.U64 × Std.Array Std.U64 4#usize × Std.Usize => 4 - p.2.2.val)
    (fun p => p.2.2.val ≤ 4 ∧ p.1.val = mrTail D (self.offsets.val.map (·.val)) p.2.2.val ∧
      ∀ k < p.2.2.val, (p.2.1.val[k]!).val = D[k]!)
  · rintro ⟨idx, digits, round⟩ ⟨hr, hidx, hdig⟩
    simp only at hr hidx hdig ⊢
    unfold waugh_indexer.mixed_radix.MixedRadix.decode_loop.body
    by_cases hlt : round.val < 4
    · have hlt' : round < 4#usize := by scalar_tac
      simp only [hlt', if_true]
      have hlo : (self.offsets.val.map (·.val)).length = 4 := by simp
      have htail := mr_tail_succ D (self.offsets.val.map (·.val)) round.val (by omega) (by omega)
      have hc := hcond round.val hlt
      have hget : (self.offsets.val.map (·.val))[round.val]! =
          (self.offsets.val.map (·.val))[round.val]'(by omega) := by
        simp [getElem!_pos, hlo, hlt]
      rw [hget] at hc
      have hdm := mr_div_mod (D[round.val]'(by omega)) _ _ hc
      rw [← htail] at hdm
      simp only [List.getElem_map] at hc hdm
      step as ⟨_h1, o, ho⟩
      have ho0 : o.val ≠ 0 := by rw [ho]; omega
      step as ⟨q, hq⟩
      step as ⟨a, ha⟩
      step as ⟨idx1, hidx1⟩
      step as ⟨round1, hround1⟩
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hidx1, hidx, ho, hround1, hdm.2]
      · intro k hk
        rw [ha, Std.Array.set_val_eq]
        by_cases hkr : k = round.val
        · subst hkr
          rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_self, hq, hidx, ho, hdm.1]
          simp [getElem!_pos, hD, hlt]
        · rw [getElem!_pos _ _ (by simp; omega), List.getElem_set_ne (by omega),
            ← getElem!_pos _ _ (by simp; omega)]
          exact hdig k (by omega)
    · have hge : ¬ round < 4#usize := by scalar_tac
      simp only [hge, if_false, WP.spec_ok]
      have : round.val = 4 := by omega
      intro k hk
      exact hdig k (by omega)
  · exact ⟨hr0, hidx0, hdig0⟩

/-- Product of a suffix is at most the product of the whole list when all entries are positive. -/
theorem mrs_prod_drop_le (L : List Nat) (hpos : ∀ x ∈ L, 1 ≤ x) (i : Nat) :
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

theorem mrs_prod_drop_succ (L : List Nat) (j : Nat) (hj : j < L.length) :
    (L.drop j).prod = L[j] * (L.drop (j + 1)).prod := by
  rw [List.drop_eq_getElem_cons hj, List.prod_cons]

theorem mrs_update_ok (v : Slice Std.U64) (i : Std.Usize) (x : Std.U64) (h : i.val < v.val.length) :
    v.update i x = ok (v.set i x) := by
  simp only [Slice.update, Slice.set, Slice.setAtNat, List.getElem?_eq_getElem h]

theorem mrs_loop_spec (xs : Slice Std.U64) (hpos : ∀ x ∈ xs.val, 1 ≤ x.val)
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
        rw [mrs_prod_drop_succ _ _ (by omega)]
        simp only [List.getElem_map]
        have : i1.val + 1 = i.val := by omega
        rw [this]
      step as ⟨_hlt, cur, hcur⟩
      have hmul : acc.val * cur.val ≤ U64.max := by
        rw [hcur, hacc, hcurv, Nat.mul_comm, ← hdrop]
        have hle := mrs_prod_drop_le (xs.val.map (·.val)) (by simpa using hpos) i1.val
        have : U64.max = 2^64 - 1 := by simp [U64.max, U64.numBits]
        omega
      rw [mrs_update_ok input i1 acc hi1lt', bind_tc_ok]
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

theorem mrs_suffix_product (xs : Slice Std.U64) (hpos : ∀ x ∈ xs.val, 1 ≤ x.val)
    (hprod : (xs.val.map (·.val)).prod < 2^64) :
    waugh_indexer.util.suffix_product xs ⦃ ys =>
      ys.val.map (·.val) = suffixProducts (xs.val.map (·.val)) ⦄ := by
  unfold waugh_indexer.util.suffix_product
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hlen : (Slice.len xs).val = xs.val.length := by simp
  apply mrs_loop_spec xs hpos hprod xs 1#u64 (Slice.len xs) rfl
  · simp [hlen]
  · intro j hj hj'
    simp only [hlen, hj', if_true]
  · rw [hlen]; simp

theorem mr_four (a : Std.Array Std.U64 4#usize) : ∃ x0 x1 x2 x3, a.val = [x0, x1, x2, x3] := by
  obtain ⟨l, hl⟩ := a
  match l, hl with
  | [x0, x1, x2, x3], _ => exact ⟨x0, x1, x2, x3, rfl⟩

theorem mr_arith (b0 b1 b2 b3 d0 d1 d2 d3 : Nat)
    (hb0 : 1 ≤ b0) (hb1 : 1 ≤ b1) (hb2 : 1 ≤ b2) (hb3 : 1 ≤ b3)
    (hb0' : b0 ≤ 65536) (hb1' : b1 ≤ 65536) (hb2' : b2 ≤ 65536) (hb3' : b3 ≤ 65536)
    (hd0 : d0 < b0) (hd1 : d1 < b1) (hd2 : d2 < b2) (hd3 : d3 < b3)
    (hnot : ¬(b0 = 65536 ∧ b1 = 65536 ∧ b2 = 65536 ∧ b3 = 65536)) :
    b0 * (b1 * (b2 * b3)) < 2^64 ∧
    d3 < b3 ∧ d2 * b3 + d3 < b2 * b3 ∧
    d1 * (b2 * b3) + (d2 * b3 + d3) < b1 * (b2 * b3) ∧
    d0 * (b1 * (b2 * b3)) + (d1 * (b2 * b3) + (d2 * b3 + d3)) < b0 * (b1 * (b2 * b3)) := by
  have e2 : (d2 + 1) * b3 ≤ b2 * b3 := Nat.mul_le_mul_right _ hd2
  have e1 : (d1 + 1) * (b2 * b3) ≤ b1 * (b2 * b3) := Nat.mul_le_mul_right _ hd1
  have e0 : (d0 + 1) * (b1 * (b2 * b3)) ≤ b0 * (b1 * (b2 * b3)) := Nat.mul_le_mul_right _ hd0
  rw [Nat.add_mul, Nat.one_mul] at e2 e1 e0
  refine ⟨?_, hd3, by omega, by omega, by omega⟩
  have key : ∀ x0 x1 x2 x3 : Nat, x0 ≤ 65535 → x1 ≤ 65536 → x2 ≤ 65536 → x3 ≤ 65536 →
      x0 * (x1 * (x2 * x3)) < 2^64 := by
    intro x0 x1 x2 x3 h0 h1 h2 h3
    have := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3))
    have hc : (65535 : Nat) * (65536 * (65536 * 65536)) < 2^64 := by norm_num
    omega
  by_cases h0 : b0 = 65536
  · by_cases h1 : b1 = 65536
    · by_cases h2 : b2 = 65536
      · have h3 : b3 ≤ 65535 := by omega
        have := key b3 b0 b1 b2 h3 hb0' hb1' hb2'
        have hc : b0 * (b1 * (b2 * b3)) = b3 * (b0 * (b1 * b2)) := by ring
        omega
      · have := key b2 b0 b1 b3 (by omega) hb0' hb1' hb3'
        have hc : b0 * (b1 * (b2 * b3)) = b2 * (b0 * (b1 * b3)) := by ring
        omega
    · have := key b1 b0 b2 b3 (by omega) hb0' hb2' hb3'
      have hc : b0 * (b1 * (b2 * b3)) = b1 * (b0 * (b2 * b3)) := by ring
      omega
  · exact key b0 b1 b2 b3 (by omega) hb1' hb2' hb3'

theorem mr_new_spec (bs : Std.Array Std.U64 4#usize) (hpos : ∀ x ∈ bs.val, 1 ≤ x.val)
    (hprod : (bs.val.map (·.val)).prod < 2^64) :
    waugh_indexer.mixed_radix.MixedRadix.new bs ⦃ radix =>
      radix.offsets.val.map (·.val) = suffixProducts (bs.val.map (·.val)) ⦄ := by
  unfold waugh_indexer.mixed_radix.MixedRadix.new
  simp only [lift, Std.Array.to_slice_mut, bind_tc_ok]
  apply spec_bind (mrs_suffix_product (Std.Array.to_slice bs) hpos hprod)
  intro s1 hs1
  simp only [WP.spec_ok]
  have hl : s1.val.length = 4 := by
    have := congrArg List.length hs1
    simp [suffixProducts] at this
    exact this
  rw [Std.Array.from_slice_val _ _ (by simpa using hl)]
  exact hs1

/-- The round trip on every generated input except `[65536; 4]`. -/
theorem mr_roundtrip_ok (block_sizes digits : Std.Array Std.U64 4#usize)
    (h_block_sizes : ∀ b ∈ block_sizes.val, 1 ≤ b.val ∧ b.val ≤ 65536)
    (h_digits : List.Forall₂ (fun d b => d.val < b.val) digits.val block_sizes.val)
    (h_not_all_max : ¬ ∀ b ∈ block_sizes.val, b.val = 65536) :
    (do
      let radix ← waugh_indexer.mixed_radix.MixedRadix.new block_sizes
      let idx ← waugh_indexer.mixed_radix.MixedRadix.encode radix digits
      waugh_indexer.mixed_radix.MixedRadix.decode radix idx) ⦃ decoded => decoded = digits ⦄ := by
  obtain ⟨b0, b1, b2, b3, hb⟩ := mr_four block_sizes
  obtain ⟨d0, d1, d2, d3, hd⟩ := mr_four digits
  rw [hb] at h_block_sizes h_digits h_not_all_max
  rw [hd] at h_digits
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h_block_sizes h_not_all_max
  simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at h_digits
  obtain ⟨⟨hb0l, hb0h⟩, ⟨hb1l, hb1h⟩, ⟨hb2l, hb2h⟩, hb3l, hb3h⟩ := h_block_sizes
  obtain ⟨hd0, hd1, hd2, hd3⟩ := h_digits
  have har := mr_arith b0.val b1.val b2.val b3.val d0.val d1.val d2.val d3.val
    hb0l hb1l hb2l hb3l hb0h hb1h hb2h hb3h hd0 hd1 hd2 hd3 h_not_all_max
  apply spec_bind (mr_new_spec block_sizes (by rw [hb]; simp; omega) (by rw [hb]; simp; omega))
  intro radix hradix
  rw [hb] at hradix
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  simp [suffixProducts, hr4] at hradix
  have hD : digits.val.map (·.val) = [d0.val, d1.val, d2.val, d3.val] := by rw [hd]; simp
  obtain ⟨har0, har3, har2, har1, harE⟩ := har
  have hmax : U64.max = 2^64 - 1 := by simp [U64.max, U64.numBits]
  unfold waugh_indexer.mixed_radix.MixedRadix.encode waugh_indexer.util.dot_product
  apply spec_bind (mr_dot_loop digits radix.offsets
    (by rw [hD, hradix, hmax]; simp [mrHead]; omega) 0#u64 0#usize (by simp) (by simp [mrHead]))
  intro idx hidx
  unfold waugh_indexer.mixed_radix.MixedRadix.decode
  apply spec_mono (mr_decode_loop radix (digits.val.map (·.val)) (by simp)
    (by
      intro r hr
      rw [hD, hradix]
      obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      · simp [mrTail]; omega
      · simp [mrTail]; omega
      · simp [mrTail]; omega
      · simp [mrTail])
    idx (Std.Array.repeat 4#usize 0#u64) 0#usize (by simp)
    (by rw [hidx, hD, hradix]; simp [mrHead, mrTail]) (by simp))
  intro out hout
  apply Subtype.ext
  apply List.ext_getElem (by simp)
  intro k hk1 hk2
  apply UScalar.eq_of_val_eq
  have := hout k (by simpa using hk1)
  have e1 : (out.val[k]!) = out.val[k] := getElem!_pos out.val k hk1
  have e2 : (digits.val.map (·.val))[k]! = (digits.val.map (·.val))[k]'(by simpa using hk2) :=
    getElem!_pos _ k (by simpa using hk2)
  rw [e1, e2, List.getElem_map] at this
  exact this

/-! Panic on `block_sizes = [65536; 4]` (lemmas from the semantic review's NonVacuity.lean):
the extracted `suffix_product` loop multiplies four entries 65536; the last `acc *= cur` is `2^64`. -/

theorem usize_sub_one (i : Std.Usize) (h : 0 < i.val) :
    ∃ j : Std.Usize, i - 1#usize = ok j ∧ j.val = i.val - 1 := by
  have := UScalar.sub_equiv i 1#usize
  revert this
  cases hz : i - 1#usize with
  | ok z => intro h'; exact ⟨z, rfl, by simp at h'; omega⟩
  | fail e => intro h'; simp at h'; omega
  | div => intro h'; simp at h'

theorem u64_mul (x y : Std.U64) :
    (x.val * y.val ≤ 2^64 - 1 → ∃ z : Std.U64, x * y = ok z ∧ z.val = x.val * y.val) ∧
    (2^64 ≤ x.val * y.val → x * y = fail .panic) := by
  have := UScalar.mul_equiv x y
  have hm : x * y = UScalar.mul x y := rfl
  have hmax : UScalar.max UScalarTy.U64 = 2^64 - 1 := by simp [U64.max, U64.numBits]
  rw [hm]
  revert this
  cases hz : UScalar.mul x y with
  | ok z => intro h'; rw [hmax] at h'; exact ⟨fun _ => ⟨z, rfl, h'.2.1⟩, fun h2 => by omega⟩
  | fail e => intro h'; rw [hmax] at h'; exact ⟨fun h2 => by omega, fun _ => by rw [h'.1]⟩
  | div => intro h'; simp at h'

theorem body_step (s : Slice Std.U64) (acc : Std.U64) (i : Std.Usize)
    (hlen : s.val.length = 4) (hi : 0 < i.val) (hi4 : i.val ≤ 4)
    (hM : ∀ k < i.val, (s.val[k]!).val = 65536) (hacc : acc.val = 65536 ^ (4 - i.val)) :
    (i.val = 1 → waugh_indexer.util.suffix_product_loop.body s acc i = fail .panic) ∧
    (1 < i.val → ∃ s' acc' i', waugh_indexer.util.suffix_product_loop.body s acc i =
        ok (.cont (s', acc', i')) ∧ s'.val.length = 4 ∧ i'.val = i.val - 1 ∧
        (∀ k < i'.val, (s'.val[k]!).val = 65536) ∧ acc'.val = 65536 ^ (4 - i'.val)) := by
  obtain ⟨j, hj, hjv⟩ := usize_sub_one i hi
  have hjl : j.val < s.val.length := by omega
  have hidx : Slice.index_usize s j = ok (s.val[j.val]) := by
    simp [Slice.index_usize, List.getElem?_eq_getElem hjl]
  have hupd : s.update j acc = ok (s.set j acc) := by
    simp only [Slice.update, Slice.set, Slice.setAtNat, List.getElem?_eq_getElem hjl]
  have hcur : (s.val[j.val]).val = 65536 := by
    have := hM j.val (by omega); rwa [getElem!_pos s.val j.val hjl] at this
  have hgt : (i > 0#usize) = True := by simp; scalar_tac
  unfold waugh_indexer.util.suffix_product_loop.body
  simp only [hgt, if_true, hj, hidx, hupd, bind_tc_ok]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have : 2^64 ≤ acc.val * (s.val[j.val]).val := by
      rw [hacc, hcur, h1]; norm_num
    rw [(u64_mul _ _).2 this, bind_tc_fail]
  · have hle : acc.val * (s.val[j.val]).val ≤ 2^64 - 1 := by
      rw [hacc, hcur]
      have : 4 - i.val ≤ 2 := by omega
      have : (65536:Nat) ^ (4 - i.val) ≤ 65536 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      have : (65536:Nat) ^ 2 * 65536 ≤ 2^64 - 1 := by norm_num
      nlinarith
    obtain ⟨z, hz, hzv⟩ := (u64_mul _ _).1 hle
    rw [hz, bind_tc_ok]
    refine ⟨_, _, _, rfl, by simp [Slice.set_val_eq, hlen], hjv, ?_, ?_⟩
    · intro k hk
      have hk' : k < s.val.length := by omega
      have hks : k < (s.val.set j.val acc).length := by simp; omega
      rw [Slice.set_val_eq, getElem!_pos _ k hks, List.getElem_set_ne (by omega),
        ← getElem!_pos s.val k hk']
      exact hM k (by omega)
    · rw [hzv, hacc, hcur, hjv]
      have : 4 - (i.val - 1) = (4 - i.val) + 1 := by omega
      rw [this, pow_succ]

theorem loop_fails : ∀ n : Nat, ∀ (s : Slice Std.U64) (acc : Std.U64) (i : Std.Usize),
    i.val = n + 1 → n < 4 → s.val.length = 4 →
    (∀ k < i.val, (s.val[k]!).val = 65536) → acc.val = 65536 ^ (4 - i.val) →
    loop (fun x => waugh_indexer.util.suffix_product_loop.body x.1 x.2.1 x.2.2) (s, acc, i) =
      fail .panic := by
  intro n
  induction n with
  | zero =>
    intro s acc i hi _ hlen hM hacc
    rw [loop.eq_1, (body_step s acc i hlen (by omega) (by omega) hM hacc).1 hi]
  | succ n ih =>
    intro s acc i hi hn hlen hM hacc
    obtain ⟨s', acc', i', hb, hl', hi', hM', hacc'⟩ :=
      (body_step s acc i hlen (by omega) (by omega) hM hacc).2 (by omega)
    rw [loop.eq_1, hb]
    exact ih s' acc' i' (by omega) (by omega) hl' hM' hacc'

theorem sp_panics {n : Std.Usize} (bs : Std.Array Std.U64 n)
    (h : bs.val = [65536#u64, 65536#u64, 65536#u64, 65536#u64]) :
    waugh_indexer.util.suffix_product (Std.Array.to_slice bs) = fail .panic := by
  have hlen : (Std.Array.to_slice bs).val.length = 4 := by simp [Std.Array.to_slice, h]
  have hM : ∀ k < (Slice.len (Std.Array.to_slice bs)).val,
      ((Std.Array.to_slice bs).val[k]!).val = 65536 := by
    intro k hk
    simp [Std.Array.to_slice, h] at hk ⊢
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals simp
  unfold waugh_indexer.util.suffix_product waugh_indexer.util.suffix_product_loop
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  have hn : n.val = 4 := by have := bs.property; rw [h] at this; simp at this; omega
  exact loop_fails 3 _ _ _ (by simp [hn]) (by omega) hlen hM (by simp [hn])

theorem new_panics {n : Std.Usize} (bs : Std.Array Std.U64 n)
    (h : bs.val = [65536#u64, 65536#u64, 65536#u64, 65536#u64]) :
    waugh_indexer.mixed_radix.MixedRadix.new bs = fail .panic := by
  unfold waugh_indexer.mixed_radix.MixedRadix.new
  simp only [lift, Std.Array.to_slice_mut, bind_tc_ok]
  show (do
    let s1 ← waugh_indexer.util.suffix_product (Std.Array.to_slice bs)
    ok ({ block_sizes := bs, offsets := Std.Array.from_slice bs s1 } :
      waugh_indexer.mixed_radix.MixedRadix n)) = fail .panic
  rw [sp_panics bs h, bind_tc_fail]

/--
For block sizes in `[1, 65536]` and digits below their block sizes, building `MixedRadix::new(block_sizes)`, encoding the digits and decoding the index panics exactly when all block sizes are `65536` (the product `2^64` overflows: an upstream bug) and otherwise never panics and returns the original digits.
-/
theorem mixed_radix_roundtrip (block_sizes digits : Std.Array Std.U64 4#usize)
    (h_block_sizes : ∀ b ∈ block_sizes.val, 1 ≤ b.val ∧ b.val ≤ 65536)
    (h_digits : List.Forall₂ (fun d b => d.val < b.val) digits.val block_sizes.val) :
    mixed_radix_roundtrip_spec block_sizes digits := by
  unfold mixed_radix_roundtrip_spec
  refine ⟨fun hall => ?_, fun hnot => mr_roundtrip_ok block_sizes digits h_block_sizes h_digits hnot⟩
  have hv : block_sizes.val = [65536#u64, 65536#u64, 65536#u64, 65536#u64] := by
    obtain ⟨l, hl⟩ := block_sizes
    match l, hl with
    | [a, b, c, d], _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
      obtain ⟨ha, hb, hc, hd⟩ := hall
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UScalar.eq_of_val_eq <;> simp [*]
  show (do
      let radix ← waugh_indexer.mixed_radix.MixedRadix.new block_sizes
      let idx ← waugh_indexer.mixed_radix.MixedRadix.encode radix digits
      waugh_indexer.mixed_radix.MixedRadix.decode radix idx) = fail .panic
  rw [new_panics block_sizes hv, bind_tc_fail]

end Benchmark.Cases.OpenpqlPrelude.Util
