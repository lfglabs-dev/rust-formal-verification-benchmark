import Benchmark.Cases.DltParse.StorageHeader.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open dlt_parse

namespace Benchmark.Cases.DltParse.StorageHeader

set_option linter.unusedSimpArgs false

/-! ### CoreModels' monadic `to_le_bytes` agrees with Aeneas' pure encoding
     (helpers following the Byteorder case) -/

theorem eq_ok_of_spec {α : Type} {e : RustM α} {v : α} (h : e ⦃ r => r = v ⦄) : e = ok v := by
  cases e with
  | ok x => simp only [WP.spec_ok] at h; rw [h]
  | fail _ => simp only [WP.spec_fail] at h
  | div => simp only [WP.spec_div] at h

theorem usize_ofNat_val (k : Nat) (hk : k < 16) :
    (⟨BitVec.ofNat UScalarTy.Usize.numBits k⟩ : Std.Usize).val = k := by
  simp only [UScalar.val, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    apply Nat.pow_le_pow_right (by omega)
    simp [UScalarTy.numBits]
  omega

theorem closure_spec (n : Std.U32) (k : Nat) (hk : k < 4) :
    core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut n
      ⟨BitVec.ofNat _ k⟩ ⦃ r => r = (⟨(n.bv >>> (8 * k)).setWidth 8⟩, n) ⦄ := by
  unfold core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  have hk' := usize_ofNat_val k (by omega)
  have hi : (UScalar.cast UScalarTy.U32 (⟨BitVec.ofNat UScalarTy.Usize.numBits k⟩ : Std.Usize)).val = k := by
    rw [UScalar.cast_val_eq, hk']; simp; omega
  step*
  · have h2 : i2.val = 8 * k := by rw [i2_post, i1_post, i_post, hi]; omega
    rw [i4_post]
    apply U8.bv_eq_imp_eq
    rw [UScalar.cast_bv_eq, i3_post2, h2]
    rfl

theorem closure_eq (n : Std.U32) (k : Nat) (hk : k < 4) :
    core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut n
      ⟨BitVec.ofNat _ k⟩ = ok (⟨(n.bv >>> (8 * k)).setWidth 8⟩, n) :=
  eq_ok_of_spec (closure_spec n k hk)

theorem to_le_bytes_go (n : Std.U32) : ∀ m, m ≤ 4 →
    rust_primitives.slice.array_from_fn_go
      core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 n m =
      ok ((List.range m).map (fun k => (⟨(n.bv >>> (8 * k)).setWidth 8⟩ : Std.U8)), n) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [rust_primitives.slice.array_from_fn_go, ih (by omega)]
    simp only [bind_tc_ok, core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8]
    rw [closure_eq n m (by omega)]
    simp [List.range_succ]

theorem toLEBytes_getElem!_eq {w : Nat} (v : BitVec w) (i : Nat) :
    v.toLEBytes[i]! = (v >>> (8 * i)).setWidth 8 := by
  rw [Byte.eq_iff]
  intro j hj
  rw [BitVec.toLEBytes_getElem!_testBit v i j hj, BitVec.getElem!_eq_testBit_toNat]
  simp only [Byte.testBit, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, hj, decide_true, Bool.true_and]

theorem toLEBytes_eq_map_range {w : Nat} (v : BitVec w) :
    v.toLEBytes = (List.range ((w + 7) / 8)).map (fun k => (v >>> (8 * k)).setWidth 8) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [← getElem!_pos v.toLEBytes i h1, toLEBytes_getElem!_eq]
    simp

theorem to_le_bytes_eq (n : Std.U32) :
    core.num.U32.to_le_bytes n = ok (Std.core.num.U32.to_le_bytes n) := by
  unfold core.num.U32.to_le_bytes rust_primitives.slice.array_from_fn
  rw [to_le_bytes_go n _ (by simp)]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp)]
  congr 1
  apply Subtype.ext
  simp only [Std.core.num.U32.to_le_bytes]
  rw [toLEBytes_eq_map_range]
  simp

theorem toNat_fromLEBytes_congr {l1 l2 : List Byte} (h : l1 = l2) :
    (BitVec.fromLEBytes l1).toNat = (BitVec.fromLEBytes l2).toNat := by
  subst h; rfl

theorem toNat_fromLEBytes_toLEBytes {w : Nat} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromLEBytes b.toLEBytes).toNat = b.toNat := by
  rw [BitVec.fromLEBytes_toLEBytes h, BitVec.toNat_cast]

theorem le_from_to_U32 (n : Std.U32) :
    Std.core.num.U32.from_le_bytes (Std.core.num.U32.to_le_bytes n) = n := by
  have hl : List.map U8.bv (Std.core.num.U32.to_le_bytes n).val = n.bv.toLEBytes := by
    simp [Std.core.num.U32.to_le_bytes, List.map_map]
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U32.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr hl, toNat_fromLEBytes_toLEBytes (by simp)]

/-- The monadic `from_le_bytes` wrapper agrees with Aeneas' pure decoder. -/
theorem from_le_bytes_eq (arr : Array Std.U8 4#usize) :
    core.num.U32.from_le_bytes arr = ok (Std.core.num.U32.from_le_bytes arr) := rfl

/-- Decoding the little-endian serialization of `n` as a fresh 4-byte array
returns `n`. -/
theorem from_le_bytes_make_eq {n : Std.U32} {a b c d : Std.U8}
    (h : List.map U8.bv [a, b, c, d] = n.bv.toLEBytes) :
    Std.core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d]) = n := by
  apply UScalar.val_eq_imp
  simp only [Std.core.num.U32.from_le_bytes, Array.make, UScalar.val, BitVec.toNat_cast]
  rw [toNat_fromLEBytes_congr h, toNat_fromLEBytes_toLEBytes (by simp)]

/-! ### Array helpers -/

/-- A monadic in-bounds array read returns the element. -/
theorem index_usize_ok {α : Type} {n : Std.Usize} (v : Array α n) (i : Std.Usize)
    (h : i.val < v.val.length) : Array.index_usize v i = ok v.val[i.val] := by
  simp only [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem h]

/-- Any `[u8; 4]` array has exactly four elements. -/
theorem arr4_len (v : Array Std.U8 4#usize) : v.val.length = 4 := by
  have h := v.property
  simp at h ⊢

/-- Any `[u8; 16]` array has exactly sixteen elements. -/
theorem arr16_len (v : Array Std.U8 16#usize) : v.val.length = 16 := by
  have h := v.property
  simp at h ⊢

/-- A monadic in-bounds array read from a `[u8; 16]` buffer. -/
theorem index16_ok (v : Array Std.U8 16#usize) (i : Std.Usize) (h : i.val < 16) :
    Array.index_usize v i = ok (v.val[i.val]'(by have := arr16_len v; omega)) :=
  index_usize_ok v i (by have := arr16_len v; omega)

/-- Reading the four elements of a length-4 list and prepending them to `rest`
yields `l ++ rest`. -/
theorem list4_getElem_append {l : List Std.U8} (h : l.length = 4) (rest : List Std.U8) :
    l[0] :: l[1] :: l[2] :: l[3] :: rest = l ++ rest := by
  match l, h with
  | [a, b, c, d], _ => simp
  | [], h' => simp at h'
  | [a], h' => simp at h'
  | [a, b], h' => simp at h'
  | [a, b, c], h' => simp at h'
  | a :: b :: c :: d :: e :: tl, h' => simp at h'

/-- A length-4 array is determined by its four `getElem!` reads. -/
theorem arr_getElem!_val (bp : Array Std.U8 4#usize) (k : Nat) (hk : k < 4) :
    bp[k]! = bp.val[k]'(by have := arr4_len bp; omega) := by
  have hi : k < bp.val.length := by have := arr4_len bp; omega
  show (bp.val[k]?).getD default = bp.val[k]
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem arr4_getElem!_ext (bp : Array Std.U8 4#usize) :
    [bp[0]!, bp[1]!, bp[2]!, bp[3]!] = bp.val := by
  have hl := arr4_len bp
  rw [arr_getElem!_val bp 0 (by omega), arr_getElem!_val bp 1 (by omega),
    arr_getElem!_val bp 2 (by omega), arr_getElem!_val bp 3 (by omega)]
  rw [list4_getElem_append hl [], List.append_nil]

/-! ### The array equality loop used by `from_bytes` -/

theorem array4_eq_true_spec (a b : Array Std.U8 4#usize) (h : a.val = b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
      ⦃ r => r = true ⦄ := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  apply loop.spec_decr_nat (fun i : Std.Usize => 4 - i.val) (fun i => i.val ≤ 4)
  · intro i hi
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    by_cases hc : i.val < 4
    · have h' : i < 4#usize := by scalar_tac
      have hia : i.val < a.val.length := by have := arr4_len a; omega
      have hib' : i.val < b.val.length := by have := arr4_len b; omega
      have hidxa : rust_primitives.slice.array_index a i = ok a.val[i.val] := by
        simp [rust_primitives.slice.array_index, Slice.index_usize, Std.Array.to_slice,
          Array.getElem?_Usize_eq, List.getElem?_eq_getElem hia]
      have hidxb : rust_primitives.slice.array_index b i = ok b.val[i.val] := by
        simp [rust_primitives.slice.array_index, Slice.index_usize, Std.Array.to_slice,
          Array.getElem?_Usize_eq, List.getElem?_eq_getElem hib']
      have hio : a.val[i.val] = b.val[i.val] := by
        rw [← getElem!_pos a.val i.val hia, ← getElem!_pos b.val i.val hib']
        exact congrArg (fun l => l[i.val]!) h
      simp only [h', if_true, hidxa, hidxb, bind_tc_ok,
        core.U8.Insts.CoreCmpPartialEqU8, hio, beq_self_eq_true, if_true]
      step as ⟨i1, hi1⟩
      exact ⟨by omega, by omega⟩
    · have h' : ¬ i < 4#usize := by scalar_tac
      simp only [h', if_false, WP.spec_ok]
  · simp

theorem array4_eq_true (a b : Array Std.U8 4#usize) (h : a.val = b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
      = ok true :=
  eq_ok_of_spec (array4_eq_true_spec a b h)

theorem array4_eq_false_spec (a b : Array Std.U8 4#usize) (h : a.val ≠ b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
      ⦃ r => r = false ⦄ := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  apply loop.spec_decr_nat (fun i : Std.Usize => 4 - i.val)
    (fun i => i.val ≤ 4 ∧ ∀ j : Nat, j < i.val → a.val[j]! = b.val[j]!)
  · intro i hi
    obtain ⟨hib, hpre⟩ := hi
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    by_cases hc : i.val < 4
    · have h' : i < 4#usize := by scalar_tac
      have hia : i.val < a.val.length := by have := arr4_len a; omega
      have hib' : i.val < b.val.length := by have := arr4_len b; omega
      have hidxa : rust_primitives.slice.array_index a i = ok a.val[i.val] := by
        simp [rust_primitives.slice.array_index, Slice.index_usize, Std.Array.to_slice,
          Array.getElem?_Usize_eq, List.getElem?_eq_getElem hia]
      have hidxb : rust_primitives.slice.array_index b i = ok b.val[i.val] := by
        simp [rust_primitives.slice.array_index, Slice.index_usize, Std.Array.to_slice,
          Array.getElem?_Usize_eq, List.getElem?_eq_getElem hib']
      simp only [h', if_true, hidxa, hidxb, bind_tc_ok,
        core.U8.Insts.CoreCmpPartialEqU8]
      by_cases he : a.val[i.val] = b.val[i.val]
      · have hio : (a.val[i.val] == b.val[i.val]) = true := by
          rw [beq_iff_eq]; exact he
        simp only [hio, if_true]
        step as ⟨i1, hi1⟩
        refine ⟨by omega, ⟨?_, by omega⟩⟩
        intro j hj
        have hjc : j = i.val ∨ j < i.val := by omega
        rcases hjc with rfl | hjlt
        · rw [getElem!_pos a.val i.val hia, getElem!_pos b.val i.val hib']
          exact he
        · exact hpre j hjlt
      · have hbf : (a.val[i.val] == b.val[i.val]) = false :=
          @Lean.Grind.beq_eq_false_of_diseq Std.U8 _ instLawfulBEqUScalar
            a.val[i.val] b.val[i.val] he
        simp only [hbf, Bool.false_eq_true, if_false, WP.spec_ok]
    · have h' : ¬ i < 4#usize := by scalar_tac
      have hla := arr4_len a
      have hlb := arr4_len b
      have hval : a.val = b.val := by
        apply List.ext_getElem
        · simp [arr4_len a, arr4_len b]
        · intro j hj1 hj2
          have hjlt : j < i.val := by omega
          rw [← getElem!_pos a.val j hj1, ← getElem!_pos b.val j hj2]
          exact hpre j hjlt
      simp only [h', if_false, WP.spec_ok]
      exact absurd hval h
  · simp

theorem array4_eq_false (a b : Array Std.U8 4#usize) (h : a.val ≠ b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
      = ok false :=
  eq_ok_of_spec (array4_eq_false_spec a b h)

theorem array4_ne_true (a b : Array Std.U8 4#usize) (h : a.val ≠ b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.ne core.U8.Insts.CoreCmpPartialEqU8 a b
      = ok true := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.ne
  rw [array4_eq_false a b h]
  simp

theorem array4_ne_false (a b : Array Std.U8 4#usize) (h : a.val = b.val) :
    core.Array.Insts.CoreCmpPartialEqArray.ne core.U8.Insts.CoreCmpPartialEqU8 a b
      = ok false := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.ne
  rw [array4_eq_true a b h]
  simp

/-! ### Closed forms -/

/-- The 16-byte serialization of `header` (see `ToBytesMatchesLayout`). -/
def storage_header_bytes (header : storage.storage_header.StorageHeader) :
    Array Std.U8 16#usize :=
  ⟨[68#u8, 76#u8, 84#u8, 1#u8] ++
    (Std.core.num.U32.to_le_bytes header.timestamp_seconds).val ++
    (Std.core.num.U32.to_le_bytes header.timestamp_microseconds).val ++
    header.ecu_id.val,
    by
      have h1 := arr4_len (Std.core.num.U32.to_le_bytes header.timestamp_seconds)
      have h2 := arr4_len (Std.core.num.U32.to_le_bytes header.timestamp_microseconds)
      have h3 := arr4_len header.ecu_id
      simp [List.length_append, h1, h2, h3]⟩

theorem to_bytes_eq (header : storage.storage_header.StorageHeader) :
    storage.storage_header.StorageHeader.to_bytes header = ok (storage_header_bytes header) := by
  unfold storage.storage_header.StorageHeader.to_bytes
  simp only [bind_tc_ok, to_le_bytes_eq]
  rw [index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len]),
      index_usize_ok _ _ (by simp [arr4_len])]
  simp [list4_getElem_append, arr4_len,
    storage.storage_header.StorageHeader.PATTERN_AT_START, storage_header_bytes]
  rfl

/-- The magic pattern as a plain list. -/
theorem pattern_val :
    storage.storage_header.StorageHeader.PATTERN_AT_START.val = [68#u8, 76#u8, 84#u8, 1#u8] := by
  unfold storage.storage_header.StorageHeader.PATTERN_AT_START
  rfl

theorem storage_header_bytes_val (header : storage.storage_header.StorageHeader) :
    (storage_header_bytes header).val = [68#u8, 76#u8, 84#u8, 1#u8] ++
      (Std.core.num.U32.to_le_bytes header.timestamp_seconds).val ++
      (Std.core.num.U32.to_le_bytes header.timestamp_microseconds).val ++
      header.ecu_id.val := rfl

set_option maxHeartbeats 1000000 in
/-- Decoding a well-formed serialization returns the header. -/
theorem from_bytes_ok (header : storage.storage_header.StorageHeader) :
    storage.storage_header.StorageHeader.from_bytes (storage_header_bytes header) =
      ok (core.result.Result.Ok header) := by
  unfold storage.storage_header.StorageHeader.from_bytes
  rw [index16_ok _ 0#usize (by decide),
      index16_ok _ 1#usize (by decide),
      index16_ok _ 2#usize (by decide),
      index16_ok _ 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [array4_ne_false]
  · simp only [bind_tc_ok, Bool.false_eq_true, if_false]
    simp only [from_le_bytes_eq]
    rw [index16_ok _ 4#usize (by decide),
        index16_ok _ 5#usize (by decide),
        index16_ok _ 6#usize (by decide),
        index16_ok _ 7#usize (by decide),
        index16_ok _ 8#usize (by decide),
        index16_ok _ 9#usize (by decide),
        index16_ok _ 10#usize (by decide),
        index16_ok _ 11#usize (by decide),
        index16_ok _ 12#usize (by decide),
        index16_ok _ 13#usize (by decide),
        index16_ok _ 14#usize (by decide),
        index16_ok _ 15#usize (by decide)]
    simp only [bind_tc_ok]
    have hb : (storage_header_bytes header).val = [68#u8, 76#u8, 84#u8, 1#u8] ++
        (Std.core.num.U32.to_le_bytes header.timestamp_seconds).val ++
        (Std.core.num.U32.to_le_bytes header.timestamp_microseconds).val ++
        header.ecu_id.val := rfl
    have hlen16 : ∀ k : Nat, k < 16 → k < (storage_header_bytes header).val.length := by
      intro k hk
      have := arr16_len (storage_header_bytes header)
      omega
    have h4 : 4 < (storage_header_bytes header).val.length := hlen16 4 (by omega)
    have h5 : 5 < (storage_header_bytes header).val.length := hlen16 5 (by omega)
    have h6 : 6 < (storage_header_bytes header).val.length := hlen16 6 (by omega)
    have h7 : 7 < (storage_header_bytes header).val.length := hlen16 7 (by omega)
    have h8 : 8 < (storage_header_bytes header).val.length := hlen16 8 (by omega)
    have h9 : 9 < (storage_header_bytes header).val.length := hlen16 9 (by omega)
    have h10 : 10 < (storage_header_bytes header).val.length := hlen16 10 (by omega)
    have h11 : 11 < (storage_header_bytes header).val.length := hlen16 11 (by omega)
    have h12 : 12 < (storage_header_bytes header).val.length := hlen16 12 (by omega)
    have h13 : 13 < (storage_header_bytes header).val.length := hlen16 13 (by omega)
    have h14 : 14 < (storage_header_bytes header).val.length := hlen16 14 (by omega)
    have h15 : 15 < (storage_header_bytes header).val.length := hlen16 15 (by omega)
    have hAts := arr4_len (Std.core.num.U32.to_le_bytes header.timestamp_seconds)
    have hAus := arr4_len (Std.core.num.U32.to_le_bytes header.timestamp_microseconds)
    have hEc := arr4_len header.ecu_id
    have hmap4 : List.map U8.bv [(storage_header_bytes header).val[4],
        (storage_header_bytes header).val[5], (storage_header_bytes header).val[6],
        (storage_header_bytes header).val[7]] = header.timestamp_seconds.bv.toLEBytes := by
      have hl : List.map U8.bv (Std.core.num.U32.to_le_bytes header.timestamp_seconds).val
          = header.timestamp_seconds.bv.toLEBytes := by
        simp [Std.core.num.U32.to_le_bytes, List.map_map]
      simp only [hb]
      simp [hl, list4_getElem_append, List.append_nil, List.map_append, List.getElem_append,
        hAts, hAus, hEc]
    have hsec := from_le_bytes_make_eq (n := header.timestamp_seconds) hmap4
    have hmap8 : List.map U8.bv [(storage_header_bytes header).val[8],
        (storage_header_bytes header).val[9], (storage_header_bytes header).val[10],
        (storage_header_bytes header).val[11]] = header.timestamp_microseconds.bv.toLEBytes := by
      have hl : List.map U8.bv (Std.core.num.U32.to_le_bytes header.timestamp_microseconds).val
          = header.timestamp_microseconds.bv.toLEBytes := by
        simp [Std.core.num.U32.to_le_bytes, List.map_map]
      simp only [hb]
      simp [hl, list4_getElem_append, List.append_nil, List.map_append, List.getElem_append,
        hAts, hAus, hEc]
    have hus := from_le_bytes_make_eq (n := header.timestamp_microseconds) hmap8
    have hecu : Array.make 4#usize [(storage_header_bytes header).val[12],
        (storage_header_bytes header).val[13], (storage_header_bytes header).val[14],
        (storage_header_bytes header).val[15]] (by simp) = header.ecu_id := by
      apply Subtype.ext
      simp only [hb]
      simp [list4_getElem_append, List.append_nil, List.getElem_append, hAts, hAus, hEc]
      rfl
    simp [WP.spec_ok, hsec, hus, hecu]
  · simp [Array.make, storage_header_bytes_val, pattern_val, list4_getElem_append, arr4_len]

/-- Decoding a buffer whose first four bytes are `bad_pattern` (not the magic
pattern) fails with the pattern error carrying `bad_pattern`. -/
theorem from_bytes_err (bytes : Array Std.U8 16#usize) (bp : Array Std.U8 4#usize)
    (hval : [bytes.val[0], bytes.val[1], bytes.val[2], bytes.val[3]] = bp.val)
    (hbp : bp.val ≠ storage.storage_header.StorageHeader.PATTERN_AT_START.val) :
    storage.storage_header.StorageHeader.from_bytes bytes =
      ok (core.result.Result.Err { actual_pattern := bp }) := by
  unfold storage.storage_header.StorageHeader.from_bytes
  rw [index16_ok _ 0#usize (by decide),
      index16_ok _ 1#usize (by decide),
      index16_ok _ 2#usize (by decide),
      index16_ok _ 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [array4_ne_true]
  · simp only [bind_tc_ok, WP.spec_ok]
    have hmk : Array.make 4#usize [bytes.val[0], bytes.val[1], bytes.val[2],
        bytes.val[3]] (by simp) = bp := by
      apply Subtype.ext
      exact hval
    simp [hmk]
  · show [bytes.val[0], bytes.val[1], bytes.val[2], bytes.val[3]]
        ≠ storage.storage_header.StorageHeader.PATTERN_AT_START.val
    rw [hval]
    exact hbp

/-! ### The theorem -/

/--
For every storage header `header` and 4-byte pattern `bad_pattern` different
from `StorageHeader::PATTERN_AT_START`, decoding `header.to_bytes()` succeeds
with `header` itself, and decoding the same buffer with its first four bytes
overwritten by `bad_pattern` fails with the
`StorageHeaderStartPatternError { actual_pattern: bad_pattern }`.
-/
theorem from_bytes_roundtrip_and_pattern_error
    (header : storage.storage_header.StorageHeader)
    (bad_pattern : Array Std.U8 4#usize)
    (h_bad : bad_pattern.val ≠ storage.storage_header.StorageHeader.PATTERN_AT_START.val) :
    storage_header_from_bytes_spec header bad_pattern := by
  unfold storage_header_from_bytes_spec
  rw [to_bytes_eq]
  simp only [bind_tc_ok]
  rw [from_bytes_ok header]
  simp only [bind_tc_ok]
  rw [from_bytes_err
    ((((storage_header_bytes header).set 0#usize bad_pattern[0]!)
        |>.set 1#usize bad_pattern[1]! |>.set 2#usize bad_pattern[2]!)
      |>.set 3#usize bad_pattern[3]!)
    bad_pattern ?_hval h_bad]
  · simp [WP.spec_ok]
  · have hext := arr4_getElem!_ext bad_pattern
    simp only [Array.set_val_eq, storage_header_bytes_val]
    simp [arr4_len]
    rw [← arr_getElem!_val bad_pattern 0 (by omega),
        ← arr_getElem!_val bad_pattern 1 (by omega),
        ← arr_getElem!_val bad_pattern 2 (by omega),
        ← arr_getElem!_val bad_pattern 3 (by omega)]
    exact hext

end Benchmark.Cases.DltParse.StorageHeader