import Benchmark.Cases.RevBits.U32.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open rev_bits

namespace Benchmark.Cases.RevBits.U32

/-! Reference proof: `to_array` produces the list of bits of `x` (LSB first)
(`rt_to_array_spec`, by induction over the `0..N` loop with `loop.eq_1`), and
`to_u32` on a list `l` of bits returns the little-endian value `rt_bitsVal l`
modulo `2^32` (`rt_to_u32_loop_spec`, by induction over the `.iter().rev()`
loop). -/

theorem rt_range_next_lt (i e : Std.Usize) (h : i.val < e.val) :
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

theorem rt_or_one_even (m : Nat) : 2 * m ||| 1 = 2 * m + 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases j with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    simp [h1, h2]

theorem rt_range_next_ge (i e : Std.Usize) (h : ¬ i.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } =
      ok (core.option.Option.None, { start := i, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hc : compare i.val e.val ≠ .lt := by simp [compare_lt_iff_lt, h]
  split <;> simp_all

theorem rt_shr_one (x : Std.U32) : ∃ z : Std.U32, z.val = x.val / 2 ∧ x >>> (1#i32) = ok z := by
  have hs := U32.ShiftRight_IScalar_spec x 1#i32
  cases h : x >>> 1#i32 with
  | ok z =>
    rw [h] at hs
    simp only [partialSpec_ok] at hs
    refine ⟨z, ?_, rfl⟩
    rw [hs.1]
    simp [Nat.shiftRight_eq_div_pow]
  | fail e =>
    rw [h] at hs
    cases e <;> simp [partialSpec] at hs
  | div =>
    rw [h] at hs
    simp [partialSpec] at hs

theorem rt_shl_one (x : Std.U32) : ∃ z : Std.U32, z.val = (2 * x.val) % 2^32 ∧ x <<< (1#i32) = ok z := by
  have hs := U32.ShiftLeft_IScalar_spec x 1#i32
  cases h : x <<< 1#i32 with
  | ok z =>
    rw [h] at hs
    simp only [partialSpec_ok] at hs
    refine ⟨z, ?_, rfl⟩
    rw [hs.1]
    simp [Nat.shiftLeft_eq, U32.size, Nat.mul_comm, U32.numBits]
  | fail e =>
    rw [h] at hs
    cases e <;> simp [partialSpec] at hs
  | div =>
    rw [h] at hs
    simp [partialSpec] at hs

theorem rt_update_ok (arr : Array Bool 32#usize) (i : Std.Usize) (v : Bool) (h : i.val < 32) :
    arr.update i v = ok (arr.set i v) := by
  have hs := Array.update_spec arr i v
  cases hu : arr.update i v with
  | ok a =>
    rw [hu] at hs
    simp only [partialSpec_ok] at hs
    rw [hs]
  | fail e =>
    rw [hu] at hs
    cases e <;> simp [partialSpec] at hs
    have := arr.property
    simp at hs this
    omega
  | div =>
    rw [hu] at hs
    simp [partialSpec] at hs

theorem rt_to_array_body_lt (i e : Std.Usize) (input : Std.U32) (arr : Array Bool 32#usize)
    (h : i.val < e.val) (he : e.val = 32) :
    ∃ i' : Std.Usize, ∃ input' : Std.U32, ∃ arr' : Array Bool 32#usize,
      i'.val = i.val + 1 ∧ input'.val = input.val / 2 ∧
      arr'.val = (if input.val % 2 = 1 then arr.val.set i.val true else arr.val) ∧
      u32.ref_impl.to_array_loop.body { start := i, «end» := e } input arr =
        ok (.cont ({ start := i', «end» := e }, input', arr')) := by
  obtain ⟨i', hi', hn⟩ := rt_range_next_lt i e h
  unfold u32.ref_impl.to_array_loop.body
  rw [hn]
  obtain ⟨z, hz, hsh⟩ := rt_shr_one input
  have hand : (input &&& 1#u32).val = input.val % 2 := by
    simp [UScalar.val_and, Nat.and_one_is_mod]
  have hi32 : i.val < 32 := by omega
  by_cases hb : input.val % 2 = 1
  · have heq : (input &&& 1#u32) = 1#u32 := by
      apply UScalar.eq_of_val_eq; rw [hand, hb]; rfl
    refine ⟨i', z, arr.set i true, hi', hz, by simp [hb], ?_⟩
    simp only [bind_tc_ok, lift, heq, if_true, hsh]
    show (do
        let array1 ← arr.update i true
        ok (ControlFlow.cont (({ start := i', «end» := e } : core.ops.range.Range Std.Usize), z, array1))) = _
    rw [rt_update_ok arr i true hi32]
    rfl
  · have heq : (input &&& 1#u32) ≠ 1#u32 := by
      intro hc; have := congrArg UScalar.val hc; rw [hand] at this; simp at this; omega
    refine ⟨i', z, arr, hi', hz, by simp [hb], ?_⟩
    simp only [bind_tc_ok, lift, heq, if_false, hsh]
    rfl

theorem rt_arr_len (a : Array Bool 32#usize) : a.val.length = 32 := by
  simp

theorem rt_to_array_body_ge (i e : Std.Usize) (input : Std.U32) (arr : Array Bool 32#usize)
    (h : ¬ i.val < e.val) :
    u32.ref_impl.to_array_loop.body { start := i, «end» := e } input arr = ok (.done arr) := by
  unfold u32.ref_impl.to_array_loop.body
  rw [rt_range_next_ge i e h]
  rfl

theorem rt_to_array_loop_spec (x : Std.U32) : ∀ (k : Nat) (i e : Std.Usize) (input : Std.U32)
    (arr : Array Bool 32#usize),
    32 - i.val = k → i.val ≤ 32 → e.val = 32 → input.val = x.val / 2 ^ i.val →
    (∀ j (hj : j < arr.val.length), arr.val[j] = (decide (j < i.val) && x.val.testBit j)) →
    ∃ res : Array Bool 32#usize,
      u32.ref_impl.to_array_loop { start := i, «end» := e } input arr = ok res ∧
      ∀ j (hj : j < res.val.length), res.val[j] = x.val.testBit j := by
  intro k
  induction k with
  | zero =>
    intro i e input arr hk hi he hin harr
    have hge : ¬ i.val < e.val := by omega
    refine ⟨arr, ?_, ?_⟩
    · unfold u32.ref_impl.to_array_loop
      rw [loop.eq_1]
      simp only [rt_to_array_body_ge i e input arr hge]
    · intro j hj
      rw [harr j hj]
      have : j < 32 := by have := rt_arr_len arr; omega
      simp; omega
  | succ k ih =>
    intro i e input arr hk hi he hin harr
    have hlt : i.val < e.val := by omega
    obtain ⟨i', z, arr', hi', hz, harr', hb⟩ := rt_to_array_body_lt i e input arr hlt he
    have hlen' : arr'.val.length = arr.val.length := by
      rw [harr']; split <;> simp
    have hz' : z.val = x.val / 2 ^ i'.val := by
      rw [hz, hin, hi', Nat.pow_succ, Nat.div_div_eq_div_mul]
    have htb : x.val.testBit i.val = decide (input.val % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hin]
    have harr2 : ∀ j (hj : j < arr'.val.length),
        arr'.val[j] = (decide (j < i'.val) && x.val.testBit j) := by
      intro j hj
      have hj0 : j < arr.val.length := by omega
      by_cases hji : j = i.val
      · subst hji
        by_cases hbit : input.val % 2 = 1
        · simp only [harr', hbit, if_true, List.getElem_set_self]
          rw [htb]; simp [hbit, hi']
        · simp only [harr', hbit, if_false]
          rw [harr i.val hj0, htb]; simp [hbit]
      · have : arr'.val[j] = arr.val[j] := by
          simp only [harr']
          split
          · rw [List.getElem_set_ne (by omega)]
          · rfl
        rw [this, harr j hj0, hi']
        have : (j < i.val) ↔ (j < i.val + 1) := by omega
        simp [this]
    obtain ⟨res, hres, hresv⟩ := ih i' e z arr' (by omega) (by omega) he hz' harr2
    refine ⟨res, ?_, hresv⟩
    unfold u32.ref_impl.to_array_loop
    rw [loop.eq_1]
    simp only [hb]
    exact hres

/-- Little-endian value of a list of bits (`l[0]` is the least significant bit). -/
def rt_bitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * rt_bitsVal bs

theorem rt_bitsVal_append_single (l : List Bool) (b : Bool) :
    rt_bitsVal (l ++ [b]) = rt_bitsVal l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => simp [rt_bitsVal]
  | cons a l ih =>
    simp only [List.cons_append, rt_bitsVal, ih, List.length_cons, Nat.pow_succ]
    ring

theorem rt_bitsVal_testBit : ∀ (l : List Bool) (x : Nat),
    (∀ j (hj : j < l.length), l[j] = x.testBit j) → rt_bitsVal l = x % 2 ^ l.length := by
  intro l
  induction l with
  | nil => intro x _; simp [rt_bitsVal, Nat.mod_one]
  | cons b bs ih =>
    intro x h
    have h0 : b = x.testBit 0 := h 0 (by simp)
    have hs : ∀ j (hj : j < bs.length), bs[j] = (x / 2).testBit j := by
      intro j hj
      have := h (j + 1) (by simp; omega)
      simpa [Nat.testBit_succ] using this
    rw [rt_bitsVal, ih (x / 2) hs, List.length_cons, Nat.pow_succ, Nat.mul_comm _ 2, Nat.mod_mul, h0,
      Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> simp [hx]

theorem rt_next_back_nil (s : core.slice.iter.Iter Bool) (h : s.val = []) :
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back s =
      ok (core.option.Option.None, s) := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    rust_primitives.sequence.seq_len]
  have : Slice.len s = 0#usize := by
    simp [Slice.len, h]; rfl
  simp [this]

theorem rt_usize_sub_one (n : Std.Usize) (h : 1 ≤ n.val) :
    ∃ i : Std.Usize, n - 1#usize = ok i ∧ i.val = n.val - 1 := by
  have hs := UScalar.sub_equiv n 1#usize
  cases hc : n - 1#usize with
  | ok z =>
    rw [hc] at hs
    refine ⟨z, rfl, ?_⟩
    simp at hs
    omega
  | fail e =>
    rw [hc] at hs
    simp at hs
    omega
  | div =>
    rw [hc] at hs
    simp at hs

theorem rt_next_back_snoc (s : core.slice.iter.Iter Bool) (l : List Bool) (b : Bool)
    (h : s.val = l ++ [b]) :
    ∃ s' : core.slice.iter.Iter Bool, ∃ v : Bool, s'.val = l ∧ v = b ∧
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back s =
      ok (core.option.Option.Some v, s') := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove]
  have hn : (Slice.len s).val = l.length + 1 := by simp [h]
  have hne : Slice.len s ≠ 0#usize := by
    intro hc
    have := congrArg UScalar.val hc
    rw [hn] at this
    simp at this
  obtain ⟨i, hi, hiv⟩ := rt_usize_sub_one (Slice.len s) (by omega)
  have hlt : i.val < s.val.length := by rw [h]; simp; omega
  simp only [bind_tc_ok, hne, if_false, hi, dif_pos hlt]
  refine ⟨_, _, ?_, ?_, rfl⟩
  · simp only [h, hiv, hn]
    simp
  · simp only [List.get_eq_getElem]
    simp only [h, hiv, hn]
    simp

theorem rt_to_u32_body_nil (it : core.iter.adapters.rev.Rev (core.slice.iter.Iter Bool))
    (out : Std.U32) (h : it.iter.val = []) :
    u32.ref_impl.to_u32_loop.body it out = ok (.done out) := by
  unfold u32.ref_impl.to_u32_loop.body
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next]
  rw [rt_next_back_nil it.iter h]
  rfl

theorem rt_to_u32_body_snoc (it : core.iter.adapters.rev.Rev (core.slice.iter.Iter Bool))
    (out : Std.U32) (l : List Bool) (b : Bool) (h : it.iter.val = l ++ [b]) :
    ∃ it' : core.iter.adapters.rev.Rev (core.slice.iter.Iter Bool), ∃ out' : Std.U32,
      it'.iter.val = l ∧ out'.val = (2 * out.val + b.toNat) % 2 ^ 32 ∧
      u32.ref_impl.to_u32_loop.body it out = ok (.cont (it', out')) := by
  obtain ⟨s', v, hs', hv, hnb⟩ := rt_next_back_snoc it.iter l b h
  subst hv
  obtain ⟨o1, ho1, hsh⟩ := rt_shl_one out
  unfold u32.ref_impl.to_u32_loop.body
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next]
  rw [hnb]
  simp only [bind_tc_ok, hsh, lift]
  have hout := out.hmax
  cases v with
  | false =>
    refine ⟨{ iter := s' }, o1, hs', ?_, rfl⟩
    rw [ho1]; simp
  | true =>
    refine ⟨{ iter := s' }, o1 ||| 1#u32, hs', ?_, rfl⟩
    rw [UScalar.val_or, ho1]
    have heven : (2 * out.val) % 2 ^ 32 = 2 * ((2 * out.val) % 2 ^ 32 / 2) := by omega
    rw [show (1#u32).val = 1 from rfl, heven, rt_or_one_even]
    simp
    omega

theorem rt_mod_mul_add (a c d m : Nat) : (a % m * c + d) % m = (a * c + d) % m := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem rt_to_u32_loop_spec : ∀ (n : Nat) (it : core.iter.adapters.rev.Rev (core.slice.iter.Iter Bool))
    (out : Std.U32), it.iter.val.length = n →
    ∃ r : Std.U32, u32.ref_impl.to_u32_loop it out = ok r ∧
      r.val = (out.val * 2 ^ n + rt_bitsVal it.iter.val) % 2 ^ 32 := by
  intro n
  induction n with
  | zero =>
    intro it out hlen
    have hnil : it.iter.val = [] := List.eq_nil_of_length_eq_zero hlen
    refine ⟨out, ?_, ?_⟩
    · unfold u32.ref_impl.to_u32_loop
      rw [loop.eq_1]
      simp only [rt_to_u32_body_nil it out hnil]
    · have : out.val < 2 ^ 32 := by scalar_tac
      rw [hnil]
      simp only [rt_bitsVal, pow_zero, Nat.mul_one, Nat.add_zero]
      omega
  | succ n ih =>
    intro it out hlen
    have hne : it.iter.val ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨l, b, hsplit⟩ : ∃ l b, it.iter.val = l ++ [b] :=
      ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨it', out', hit', hout', hb⟩ :=
      rt_to_u32_body_snoc it out l b hsplit
    have hl : l.length = n := by rw [hsplit] at hlen; simpa using hlen
    have hlen' : it'.iter.val.length = n := by rw [hit', hl]
    obtain ⟨r, hr, hrv⟩ := ih it' out' hlen'
    refine ⟨r, ?_, ?_⟩
    · unfold u32.ref_impl.to_u32_loop
      rw [loop.eq_1]
      simp only [hb]
      exact hr
    · rw [hrv, hout', rt_mod_mul_add, hsplit, rt_bitsVal_append_single, hit', hl, Nat.pow_succ]
      congr 1
      ring

theorem rt_to_array_spec (x : Std.U32) :
    ∃ arr : Array Bool 32#usize, u32.ref_impl.to_array x = ok arr ∧
      ∀ j (hj : j < arr.val.length), arr.val[j] = x.val.testBit j := by
  have hbits : u32.BITS.val = 32 := by unfold u32.BITS; rfl
  have he : (UScalar.cast .Usize u32.BITS).val = 32 := by
    rw [UScalar.cast_val_eq, hbits]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  obtain ⟨res, h1, h2⟩ := rt_to_array_loop_spec x 32 0#usize (UScalar.cast .Usize u32.BITS) x
    (Array.repeat 32#usize false) (by simp) (by simp) he (by simp)
    (by intro j hj; simp only [Array.repeat, List.getElem_replicate]; simp)
  refine ⟨res, ?_, h2⟩
  unfold u32.ref_impl.to_array u32.ref_impl.N
  simp only [bind_tc_ok]
  exact h1

/--
For every `u32` value `x`, expanding it into a `[bool; 32]` bit array with
the reference implementation's `to_array` (bit `i` at index `i`) and
packing the array back with `to_u32` (which folds the bits from the last
index down with `out = out << 1 | bit`) never panics and returns `x`.
-/
theorem to_array_to_u32 (x : Std.U32) :
    to_array_to_u32_spec x := by
  unfold to_array_to_u32_spec
  obtain ⟨arr, harr, hv⟩ := rt_to_array_spec x
  have hlen : arr.val.length = 32 := rt_arr_len arr
  have hx : x.val < 2 ^ 32 := by scalar_tac
  have hbits : rt_bitsVal arr.val = x.val := by
    rw [rt_bitsVal_testBit arr.val x.val hv, hlen]
    exact Nat.mod_eq_of_lt hx
  obtain ⟨r, hr, hrv⟩ := rt_to_u32_loop_spec 32
    ({ iter := Array.to_slice arr } : core.iter.adapters.rev.Rev (core.slice.iter.Iter Bool)) 0#u32
    (by simp [Array.to_slice, hlen])
  have hto : u32.ref_impl.to_u32 (Array.to_slice arr) = ok r := by
    unfold u32.ref_impl.to_u32
    simp only [core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice, bind_tc_ok,
      core.iter.traits.iterator.Iterator.rev.default, core.iter.adapters.rev.Rev.new]
    exact hr
  simp only [harr, lift, bind_tc_ok, hto, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  rw [hrv]
  simp only [Array.to_slice, hbits]
  simp

end Benchmark.Cases.RevBits.U32
