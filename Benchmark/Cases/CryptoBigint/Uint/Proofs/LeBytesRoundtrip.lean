import Benchmark.Cases.CryptoBigint.Uint.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

theorem u64_lt (x : Std.U64) : x.val < 2^64 := by
  have := x.hBounds; simpa [UScalarTy.numBits] using this

theorem limbsVal_lt (l : List Std.U64) : limbsVal l < 2^(64 * l.length) := by
  induction l with
  | nil => simp [limbsVal]
  | cons x xs ih =>
    simp only [limbsVal, List.length_cons]
    have hx := u64_lt x
    rw [Nat.mul_succ, pow_add, Nat.mul_comm (2^(64*xs.length))]
    have : limbsVal xs + 1 ≤ 2^(64*xs.length) := ih
    nlinarith

/-- Little-endian value of a list of bytes. -/
def bytesVal : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesVal bs

theorem bytesVal_lt (l : List (BitVec 8)) : bytesVal l < 2^(8 * l.length) := by
  induction l with
  | nil => simp [bytesVal]
  | cons b bs ih =>
    simp only [bytesVal, List.length_cons]
    have hb := b.isLt
    rw [Nat.mul_succ, pow_add, Nat.mul_comm (2^(8*bs.length))]
    have : bytesVal bs + 1 ≤ 2^(8*bs.length) := ih
    have h256 : (2:Nat)^8 = 256 := by norm_num
    rw [h256]
    nlinarith

theorem fromLEBytes_toNat (l : List (BitVec 8)) : (BitVec.fromLEBytes l).toNat = bytesVal l := by
  induction l with
  | nil => simp [BitVec.fromLEBytes, bytesVal]
  | cons b bs ih =>
    rw [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, ih]
    simp only [bytesVal, List.length_cons]
    have hb := b.isLt
    have hbs := bytesVal_lt bs
    have hp : 2^(8*(bs.length+1)) = 2^(8*bs.length) * 256 := by
      rw [Nat.mul_succ, pow_add]; norm_num
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by rw [hp]; nlinarith [Nat.one_le_two_pow (n := 8*bs.length)]),
      Nat.mod_eq_of_lt (a := bytesVal bs) (by rw [hp]; nlinarith),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by rw [hp]; norm_num; nlinarith)]
    rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
    ring

theorem bytesVal_ofFn (k w : Nat) :
    bytesVal (List.ofFn (n := k) (fun s => BitVec.ofNat 8 (w / 2^(8*s.val)))) = w % 2^(8*k) := by
  induction k generalizing w with
  | zero => simp [bytesVal, Nat.mod_one]
  | succ k ih =>
    rw [List.ofFn_succ]
    simp only [bytesVal, Fin.val_zero, Nat.mul_zero, pow_zero, Nat.div_one, BitVec.toNat_ofNat,
      Fin.val_succ]
    have hw : ∀ s : Nat, w / 2^(8*(s+1)) = (w / 256) / 2^(8*s) := by
      intro s
      rw [Nat.div_div_eq_div_mul, Nat.mul_succ, pow_add, Nat.mul_comm]
      norm_num
    simp only [hw]
    rw [ih (w / 256)]
    have hp : 2^(8*(k+1)) = 256 * 2^(8*k) := by rw [Nat.mul_succ, pow_add, Nat.mul_comm]; norm_num
    rw [hp, Nat.mod_mul]

theorem limbsVal_extract (l : List Std.U64) (t : Nat) (ht : t < l.length) :
    (limbsVal l / 2^(64*t)) % 2^64 = (l[t]).val := by
  induction l generalizing t with
  | nil => simp at ht
  | cons x xs ih =>
    have hx := u64_lt x
    cases t with
    | zero =>
      simp only [limbsVal, Nat.mul_zero, pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ t =>
      simp only [limbsVal, List.getElem_cons_succ]
      have hp : 2^(64*(t+1)) = 2^64 * 2^(64*t) := by rw [Nat.mul_succ, pow_add, Nat.mul_comm]
      rw [hp, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx,
        Nat.zero_add]
      exact ih t (by simp at ht; omega)

theorem leBytes32_chunk (v t : Nat) (ht : t < 4) :
    ((leBytes32 v).val.drop (8*t)).take 8 = List.ofFn (n := 8) (fun s => leByte v (8*t + s.val)) := by
  apply List.ext_getElem
  · simp [leBytes32]; omega
  · intro s h1 h2
    simp only [leBytes32, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem chunk_val (v t : Nat) (ht : t < 4) :
    bytesVal (List.map (fun b : Std.U8 => b.bv) (((leBytes32 v).val.drop (8*t)).take 8))
      = (v / 2^(64*t)) % 2^64 := by
  rw [leBytes32_chunk v t ht, List.map_ofFn]
  have : (fun s : Fin 8 => (leByte v (8*t + s.val)).bv) =
      (fun s : Fin 8 => BitVec.ofNat 8 ((v / 2^(64*t)) / 2^(8*s.val))) := by
    funext s
    have e : v / 2^(8*(8*t + s.val)) = v / 2^(64*t) / 2^(8*s.val) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      ring
    simp only [leByte, e]
  rw [Function.comp_def, this, bytesVal_ofFn]

theorem bytes_eq : limb.Limb.BYTES = 8#usize := by unfold limb.Limb.BYTES; rfl

theorem take_succ_set {α} (l : List α) (i : Nat) (x : α) (hi : i < l.length) :
    (l.set i x).take (i+1) = l.take i ++ [x] := by
  rw [List.take_add_one]
  have h1 : (l.set i x)[i]? = some x := by simp [hi]
  rw [h1, List.take_set_of_le (Nat.le_refl i)]
  rfl

/-- Invariant of the inner byte-copy loop of `from_le_slice` (limb `i`, `j` bytes copied). -/
def InnerInv (bytes : Slice Std.U8) (i : Std.Usize) (st : Array Std.U8 8#usize × Std.Usize) : Prop :=
  st.2.val ≤ 8 ∧ st.1.val.take st.2.val = (bytes.val.drop (8*i.val)).take st.2.val

theorem inner_loop_spec (bytes : Slice Std.U8) (buf : Array Std.U8 8#usize) (i j : Std.Usize)
    (hlen : 8 * i.val + 8 ≤ bytes.length) (h : InnerInv bytes i (buf, j)) :
    uint.encoding.Uint.from_le_slice_loop0_loop0 bytes buf i j
    ⦃ r => r.val = (bytes.val.drop (8*i.val)).take 8 ⦄ := by
  unfold uint.encoding.Uint.from_le_slice_loop0_loop0
  apply loop.spec_decr_nat (fun st => 8 - st.2.val) (InnerInv bytes i)
  · intro st hst
    obtain ⟨s, k⟩ := st
    obtain ⟨hk, hv⟩ := hst
    simp only at hk hv
    dsimp only
    unfold uint.encoding.Uint.from_le_slice_loop0_loop0.body
    rw [bytes_eq]
    have hls : s.val.length = 8 := s.property
    have hbl : bytes.val.length = bytes.length := rfl
    split
    · rename_i hlt
      have hk8 : k.val < 8 := by scalar_tac
      step*
      subst a_post
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show j1.val ≤ 8
        omega
      · show (s.set k _).val.take j1.val = (bytes.val.drop (8*i.val)).take j1.val
        simp only [j1_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), hv, List.take_add_one (l := List.drop _ _),
          List.getElem?_drop, List.getElem?_eq_getElem (by omega), Option.toList_some, i3_post2]
        congr 3
        omega
      · show 8 - j1.val < 8 - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hk8 : k.val = 8 := by scalar_tac
      rw [hk8, List.take_of_length_le (by omega)] at hv
      exact hv
  · exact h

theorem cm_from_le_bytes_eq (buf : Array Std.U8 8#usize) :
    CoreModels.core.num.U64.from_le_bytes buf = ok (Aeneas.Std.core.num.U64.from_le_bytes buf) := rfl

theorem from_le_bytes_val (buf : Array Std.U8 8#usize) :
    (Aeneas.Std.core.num.U64.from_le_bytes buf).val = bytesVal (buf.val.map (fun b : Std.U8 => b.bv)) := by
  simp only [Aeneas.Std.core.num.U64.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  rw [fromLEBytes_toNat]

/-- Invariant of the outer limb loop of `from_le_slice` on the bytes `leBytes32 (uintVal a)`. -/
def OuterInv (u : uint.Uint 4#usize)
    (st : Array limb.Limb 4#usize × Array Std.U8 8#usize × Std.Usize) : Prop :=
  st.2.2.val ≤ 4 ∧ st.1.val.take st.2.2.val = u.limbs.val.take st.2.2.val

theorem outer_loop_spec (u : uint.Uint 4#usize) (res : Array limb.Limb 4#usize)
    (buf : Array Std.U8 8#usize) (i : Std.Usize) (h : OuterInv u (res, buf, i)) :
    uint.encoding.Uint.from_le_slice_loop0 (Array.to_slice (leBytes32 (uintVal u))) res buf i
    ⦃ r => r.val = u.limbs.val ⦄ := by
  unfold uint.encoding.Uint.from_le_slice_loop0
  apply loop.spec_decr_nat (fun st => 4 - st.2.2.val) (OuterInv u)
  · intro st hst
    obtain ⟨s, b, k⟩ := st
    obtain ⟨hk, hv⟩ := hst
    simp only at hk hv
    dsimp only
    unfold uint.encoding.Uint.from_le_slice_loop0.body
    have hls : s.val.length = 4 := s.property
    have hla : u.limbs.val.length = 4 := u.limbs.property
    split
    · rename_i hlt
      have hk4 : k.val < 4 := by scalar_tac
      have hlen : 8 * k.val + 8 ≤ (Array.to_slice (leBytes32 (uintVal u))).length := by
        simp [Array.to_slice, leBytes32]; omega
      apply spec_bind (inner_loop_spec _ b k 0#usize hlen (by simp [InnerInv]))
      intro buf1 hbuf1
      rw [cm_from_le_bytes_eq]
      simp only [bind_tc_ok]
      have hlimb : Aeneas.Std.core.num.U64.from_le_bytes buf1 = u.limbs.val[k.val] := by
        apply UScalar.eq_of_val_eq
        rw [from_le_bytes_val, hbuf1]
        have := chunk_val (uintVal u) k.val hk4
        simp only [Array.to_slice] at this ⊢
        rw [this]
        exact limbsVal_extract _ _ (by omega)
      rw [hlimb]
      step*
      subst a_post
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show i2.val ≤ 4
        omega
      · show (s.set k _).val.take i2.val = u.limbs.val.take i2.val
        simp only [i2_post, Array.set_val_eq]
        rw [take_succ_set _ _ _ (by omega), hv, List.take_add_one (l := u.limbs.val),
          List.getElem?_eq_getElem (by omega), Option.toList_some]
      · show 4 - i2.val < 4 - k.val
        omega
    · rename_i hge
      simp only [WP.spec_ok]
      have hk4 : k.val = 4 := by scalar_tac
      rw [hk4, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      exact hv
  · exact h

/--
Decoding the 32-byte little-endian encoding of the value of any `U256` `a` with `U256::from_le_slice` never panics and returns `a` itself.
-/
theorem le_bytes_roundtrip (a : uint.Uint 4#usize) :
    le_bytes_roundtrip_spec a := by
  unfold le_bytes_roundtrip_spec uint.encoding.Uint.from_le_slice core.slice.Slice.len
    rust_primitives.slice.slice_length
  rw [bytes_eq]
  step*
  apply spec_bind (outer_loop_spec a _ _ _ (by simp [OuterInv]))
  intro r hr
  unfold uint.Uint.new
  simp only [WP.spec_ok]
  obtain ⟨la⟩ := a
  simp only at hr ⊢
  congr
  exact Subtype.ext hr

end Benchmark.Cases.CryptoBigint.Uint
