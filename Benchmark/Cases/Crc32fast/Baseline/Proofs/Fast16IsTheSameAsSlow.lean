import Benchmark.Cases.Crc32fast.Baseline.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crc32fast

namespace Benchmark.Cases.Crc32fast.Baseline

def z1 (c : BitVec 32) : BitVec 32 := (c >>> 1) ^^^ (if c.getLsbD 0 then 0xEDB88320#32 else 0#32)

theorem z1_xor (a b : BitVec 32) : z1 (a ^^^ b) = z1 a ^^^ z1 b := by
  unfold z1
  rw [BitVec.ushiftRight_xor_distrib, BitVec.getLsbD_xor]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> simp
  · ac_rfl
  · ac_rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor]
    cases (a >>> 1).getLsbD i <;> cases (b >>> 1).getLsbD i <;> cases (3988292384#32).getLsbD i <;> rfl

theorem z1_of_lsb (y : BitVec 32) (h : y.getLsbD 0 = false) : z1 y = y >>> 1 := by
  simp only [z1, h, Bool.false_eq_true, if_false, BitVec.xor_zero]

def z8 (c : BitVec 32) : BitVec 32 := z1 (z1 (z1 (z1 (z1 (z1 (z1 (z1 c)))))))

theorem z8_xor (a b : BitVec 32) : z8 (a ^^^ b) = z8 a ^^^ z8 b := by
  simp only [z8, z1_xor]

theorem z8_high (x : BitVec 32) : z8 (x &&& 0xFFFFFF00#32) = x >>> 8 := by
  unfold z8
  simp (disch := simp) only [z1_of_lsb]
  simp only [← BitVec.shiftRight_add]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]
  intro h
  have h8 : 8 + i < 32 := by
    by_contra hc
    rw [BitVec.getLsbD_of_ge x _ (by omega)] at h
    exact absurd h (by simp)
  have key : ∀ j < 24, (4294967040#32).getLsbD (8 + j) = true := by decide
  exact key i (by omega)
noncomputable def tb (k i : Nat) : BitVec 32 := ((table.CRC32_TABLE.val[k]!).val[i]!).bv
noncomputable def Zt (c : BitVec 32) : BitVec 32 := tb 0 (c &&& 0xFF#32).toNat ^^^ (c >>> 8)

set_option maxRecDepth 100000 in
/-- Row 0 of `CRC32_TABLE` is the byte-wise CRC table: entry `x` is `x` shifted
through 8 zero bits (checked by kernel evaluation of all 256 entries). -/
theorem F0 : ∀ x : Fin 256, tb 0 x = z8 (BitVec.ofNat 32 x) := by decide +kernel
-- Row `k+1` of `CRC32_TABLE` is row `k` pushed through one more zero byte
-- (slicing-by-16 table recurrence; kernel evaluation, row by row).
set_option maxRecDepth 100000 in
theorem F1_0 : ∀ x : Fin 256, tb 1 x = Zt (tb 0 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_1 : ∀ x : Fin 256, tb 2 x = Zt (tb 1 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_2 : ∀ x : Fin 256, tb 3 x = Zt (tb 2 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_3 : ∀ x : Fin 256, tb 4 x = Zt (tb 3 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_4 : ∀ x : Fin 256, tb 5 x = Zt (tb 4 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_5 : ∀ x : Fin 256, tb 6 x = Zt (tb 5 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_6 : ∀ x : Fin 256, tb 7 x = Zt (tb 6 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_7 : ∀ x : Fin 256, tb 8 x = Zt (tb 7 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_8 : ∀ x : Fin 256, tb 9 x = Zt (tb 8 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_9 : ∀ x : Fin 256, tb 10 x = Zt (tb 9 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_10 : ∀ x : Fin 256, tb 11 x = Zt (tb 10 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_11 : ∀ x : Fin 256, tb 12 x = Zt (tb 11 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_12 : ∀ x : Fin 256, tb 13 x = Zt (tb 12 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_13 : ∀ x : Fin 256, tb 14 x = Zt (tb 13 x) := by decide +kernel
set_option maxRecDepth 100000 in
theorem F1_14 : ∀ x : Fin 256, tb 15 x = Zt (tb 14 x) := by decide +kernel

theorem F1 (k x : Nat) (hk : k < 15) (hx : x < 256) : tb (k+1) x = Zt (tb k x) := by
  match k, hk with
  | 0, _ => exact F1_0 ⟨x, hx⟩
  | 1, _ => exact F1_1 ⟨x, hx⟩
  | 2, _ => exact F1_2 ⟨x, hx⟩
  | 3, _ => exact F1_3 ⟨x, hx⟩
  | 4, _ => exact F1_4 ⟨x, hx⟩
  | 5, _ => exact F1_5 ⟨x, hx⟩
  | 6, _ => exact F1_6 ⟨x, hx⟩
  | 7, _ => exact F1_7 ⟨x, hx⟩
  | 8, _ => exact F1_8 ⟨x, hx⟩
  | 9, _ => exact F1_9 ⟨x, hx⟩
  | 10, _ => exact F1_10 ⟨x, hx⟩
  | 11, _ => exact F1_11 ⟨x, hx⟩
  | 12, _ => exact F1_12 ⟨x, hx⟩
  | 13, _ => exact F1_13 ⟨x, hx⟩
  | 14, _ => exact F1_14 ⟨x, hx⟩
  | k + 15, hk => exact absurd hk (by omega)

def zp : Nat → BitVec 32 → BitVec 32
  | 0, c => c
  | n + 1, c => z8 (zp n c)

theorem zp_xor (n : Nat) (a b : BitVec 32) : zp n (a ^^^ b) = zp n a ^^^ zp n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zp, ih, z8_xor]

theorem zp_z8 (n : Nat) (c : BitVec 32) : zp n (z8 c) = zp (n + 1) c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zp] at *; rw [ih]

theorem split_low (w : BitVec 32) : w = (w &&& 0xFF#32) ^^^ (w &&& 0xFFFFFF00#32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  have key : ∀ j < 32, ((0xFF#32).getLsbD j && (0xFFFFFF00#32).getLsbD j) = false ∧
      ((0xFF#32).getLsbD j || (0xFFFFFF00#32).getLsbD j) = true := by decide
  obtain ⟨k1, k2⟩ := key i hi
  clear key
  generalize (0xFF#32).getLsbD i = p at *
  generalize (0xFFFFFF00#32).getLsbD i = q at *
  generalize w.getLsbD i = r
  cases p <;> cases q <;> cases r <;> simp_all

theorem z8_decomp (w : BitVec 32) : z8 w = z8 (w &&& 0xFF#32) ^^^ (w >>> 8) := by
  conv_lhs => rw [split_low w]
  rw [z8_xor, z8_high]

theorem zp_decomp (n : Nat) (w : BitVec 32) :
    zp (n + 1) w = zp (n + 1) (w &&& 0xFF#32) ^^^ zp n (w >>> 8) := by
  rw [← zp_z8, z8_decomp, zp_xor, zp_z8]

theorem zp16_bytes (w : BitVec 32) :
    zp 16 w = zp 16 (w &&& 0xFF#32) ^^^ zp 15 ((w >>> 8) &&& 0xFF#32) ^^^
      zp 14 ((w >>> 16) &&& 0xFF#32) ^^^ zp 13 (w >>> 24) := by
  rw [zp_decomp 15, zp_decomp 14, zp_decomp 13]
  simp only [← BitVec.shiftRight_add]
  ac_rfl

theorem ofNat_toNat32 (y : BitVec 32) : BitVec.ofNat 32 y.toNat = y := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem z8_split (x : BitVec 32) : z8 x = Zt x := by
  have hlt : (x &&& 0xFF#32).toNat < 256 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [z8_decomp, Zt, F0 ⟨_, hlt⟩]
  simp only [ofNat_toNat32]

theorem tb_zp (k x : Nat) (hk : k < 16) (hx : x < 256) : tb k x = zp (k + 1) (BitVec.ofNat 32 x) := by
  induction k with
  | zero => exact F0 ⟨x, hx⟩
  | succ k ih =>
    rw [F1 k x (by omega) hx, ih (by omega), ← z8_split]
    rfl

/-- One byte step of `update_slow` on the raw register. -/
noncomputable def sstep (c : BitVec 32) (b : Std.U8) : BitVec 32 :=
  tb 0 ((c.toNat % 256) ^^^ b.val) ^^^ (c >>> 8)

theorem sstep_eq (c : BitVec 32) (b : Std.U8) : sstep c b = z8 (c ^^^ BitVec.ofNat 32 b.val) := by
  have hb : b.val < 256 := by have := b.hBounds; simpa using this
  rw [z8_split, Zt, sstep]
  congr 1
  · congr 1
    rw [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show b.val < 2^32 by omega)]
    rw [show (0xFF#32).toNat = 2^8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow,
      Nat.mod_eq_of_lt (show b.val < 2^8 by omega)]
  · rw [BitVec.ushiftRight_xor_distrib]
    have : BitVec.ofNat 32 b.val >>> 8 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b.val < 2^32 by omega),
        Nat.shiftRight_eq_div_pow]
      simp; omega
    rw [this, BitVec.xor_zero]

theorem z8_shl (x : BitVec 32) (hx : x.toNat < 2^24) : z8 (x <<< 8) = x := by
  have h1 : (x <<< 8) &&& 0xFFFFFF00#32 = x <<< 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    have key : ∀ j < 32, (decide (j < 8) = false) → (0xFFFFFF00#32).getLsbD j = true := by decide
    by_cases h : i < 8
    · simp [h]
    · simp [h, key i hi (by simp [h])]
  rw [← h1, z8_high]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega)]
  simp

theorem zp_shl (n : Nat) (x : BitVec 32) (hx : x.toNat < 2^24) : zp (n + 1) (x <<< 8) = zp n x := by
  rw [← zp_z8, z8_shl x hx]

theorem le_bytes (a0 a1 a2 a3 : Std.U8) (h) :
    (Aeneas.Std.core.num.U32.from_le_bytes (Array.make 4#usize [a0, a1, a2, a3] h)).bv =
      BitVec.ofNat 32 a0.val ^^^ (BitVec.ofNat 32 a1.val <<< 8) ^^^ (BitVec.ofNat 32 a2.val <<< 16) ^^^
        (BitVec.ofNat 32 a3.val <<< 24) := by
  simp only [Aeneas.Std.core.num.U32.from_le_bytes, Array.make]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  change (BitVec.cast (by simp) (BitVec.fromLEBytes (List.map U8.bv [a0, a1, a2, a3]))).getLsbD j = _
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_eq_getElem (by simp; omega), BitVec.fromLEBytes_getElem]
  simp only [List.map_cons, List.map_nil, Byte.testBit]
  have hv : ∀ (a : Std.U8) (t : Nat), 8 ≤ t → a.val.testBit t = false := by
    intro a t ht
    apply Nat.testBit_lt_two_pow
    have := a.hBounds
    calc a.val < 2^8 := by simpa using this
      _ ≤ 2^t := Nat.pow_le_pow_right (by norm_num) ht
  have hbv : ∀ (a : Std.U8), a.bv.toNat = a.val := fun a => rfl
  rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 32) by omega) with h0 | h0 | h0 | h0
  · have e1 : j / 8 = 0 := by omega
    have e2 : j % 8 = j := by omega
    have f1 : j < 16 := by omega
    have f2 : j < 24 := by omega
    simp [e1, e2, h0, f1, f2, hbv, hj]
  · have e1 : j / 8 = 1 := by omega
    have e2 : j % 8 = j - 8 := by omega
    have f0 : ¬ j < 8 := by omega
    have f1 : j < 16 := by omega
    have f2 : j < 24 := by omega
    have f3 : j - 8 < 32 := by omega
    simp [e1, e2, f0, f1, f2, f3, hbv, hv a0 j (by omega), hj]
  · have e1 : j / 8 = 2 := by omega
    have e2 : j % 8 = j - 16 := by omega
    have f0 : ¬ j < 8 := by omega
    have f1 : ¬ j < 16 := by omega
    have f2 : j < 24 := by omega
    have f3 : j - 8 < 32 := by omega
    have f4 : j - 16 < 32 := by omega
    simp [e1, e2, f0, f1, f2, f3, f4, hbv, hv a0 j (by omega), hv a1 (j - 8) (by omega), hj]
  · have e1 : j / 8 = 3 := by omega
    have e2 : j % 8 = j - 24 := by omega
    have f0 : ¬ j < 8 := by omega
    have f1 : ¬ j < 16 := by omega
    have f2 : ¬ j < 24 := by omega
    have f3 : j - 8 < 32 := by omega
    have f4 : j - 16 < 32 := by omega
    have f5 : j - 24 < 32 := by omega
    simp [e1, e2, f0, f1, f2, f3, f4, f5, hbv, hv a0 j (by omega), hv a1 (j - 8) (by omega),
      hv a2 (j - 16) (by omega), hj]

theorem u8_lt (b : Std.U8) : b.val < 256 := by have := b.hBounds; simpa using this

theorem fold16_math (c : BitVec 32) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Std.U8)
    (w : BitVec 32)
    (hw : w = (BitVec.ofNat 32 b0.val ^^^ (BitVec.ofNat 32 b1.val <<< 8) ^^^
      (BitVec.ofNat 32 b2.val <<< 16) ^^^ (BitVec.ofNat 32 b3.val <<< 24)) ^^^ c) :
    tb 0 b15.val ^^^ tb 1 b14.val ^^^ tb 2 b13.val ^^^ tb 3 b12.val ^^^ tb 4 b11.val ^^^
      tb 5 b10.val ^^^ tb 6 b9.val ^^^ tb 7 b8.val ^^^ tb 8 b7.val ^^^ tb 9 b6.val ^^^
      tb 10 b5.val ^^^ tb 11 b4.val ^^^ tb 12 (w >>> 24).toNat ^^^
      tb 13 ((w >>> 16) &&& 0xFF#32).toNat ^^^ tb 14 ((w >>> 8) &&& 0xFF#32).toNat ^^^
      tb 15 (w &&& 0xFF#32).toNat =
    [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15].foldl sstep c := by
  have hand : ∀ y : BitVec 32, (y &&& 0xFF#32).toNat < 256 := fun y => by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have h24 : (w >>> 24).toNat < 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := w.isLt
    omega
  rw [tb_zp 0 _ (by omega) (u8_lt _), tb_zp 1 _ (by omega) (u8_lt _), tb_zp 2 _ (by omega) (u8_lt _),
    tb_zp 3 _ (by omega) (u8_lt _), tb_zp 4 _ (by omega) (u8_lt _), tb_zp 5 _ (by omega) (u8_lt _),
    tb_zp 6 _ (by omega) (u8_lt _), tb_zp 7 _ (by omega) (u8_lt _), tb_zp 8 _ (by omega) (u8_lt _),
    tb_zp 9 _ (by omega) (u8_lt _), tb_zp 10 _ (by omega) (u8_lt _), tb_zp 11 _ (by omega) (u8_lt _),
    tb_zp 12 _ (by omega) h24, tb_zp 13 _ (by omega) (hand _), tb_zp 14 _ (by omega) (hand _),
    tb_zp 15 _ (by omega) (hand _)]
  simp only [ofNat_toNat32]
  have hw16 := zp16_bytes w
  have hX : zp 16 w = zp 16 (BitVec.ofNat 32 b0.val) ^^^ zp 15 (BitVec.ofNat 32 b1.val) ^^^
      zp 14 (BitVec.ofNat 32 b2.val) ^^^ zp 13 (BitVec.ofNat 32 b3.val) ^^^ zp 16 c := by
    have hB : ∀ b : Std.U8, (BitVec.ofNat 32 b.val).toNat < 256 := fun b => by
      rw [BitVec.toNat_ofNat]; exact lt_of_le_of_lt (Nat.mod_le _ _) (u8_lt b)
    have s1 : ∀ b : Std.U8, (BitVec.ofNat 32 b.val <<< 8).toNat < 2^16 := fun b => by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have := hB b
      exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    have s2 : ∀ b : Std.U8, (BitVec.ofNat 32 b.val <<< 8 <<< 8).toNat < 2^24 := fun b => by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have := s1 b
      exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    rw [hw, zp_xor, zp_xor, zp_xor, zp_xor]
    rw [show (24 : Nat) = 8 + 8 + 8 by rfl, show (16 : Nat) = 8 + 8 by rfl]
    simp only [BitVec.shiftLeft_add]
    rw [show zp (8 + 8) = zp (15 + 1) from rfl, zp_shl 15 _ (by have := hB b1; omega)]
    rw [zp_shl 15 _ (s2 b3), zp_shl 14 _ (by have := s1 b3; omega), zp_shl 13 _ (by have := hB b3; omega)]
    rw [zp_shl 15 _ (by have := s1 b2; omega), zp_shl 14 _ (by have := hB b2; omega)]
  have hL : ∀ A : BitVec 32, A ^^^ zp 13 (w >>> 24) ^^^ zp 14 ((w >>> 16) &&& 0xFF#32) ^^^
      zp 15 ((w >>> 8) &&& 0xFF#32) ^^^ zp 16 (w &&& 0xFF#32) = A ^^^ zp 16 w := by
    intro A; rw [hw16]; ac_rfl
  rw [hL, hX]
  simp only [List.foldl, sstep_eq, z8_xor]
  simp only [zp]
  ac_rfl


theorem arr_idx {α : Type} {n : Usize} (a : Aeneas.Std.Array α n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok (a.val[i.val]'(by have := a.property; omega)) := by
  have h' : i.val < a.val.length := by have := a.property; omega
  simp [Array.index_usize, List.getElem?_eq_getElem h']

theorem shr_i32 (x : Std.U32) (k : Std.I32) (h0 : 0 ≤ k.val) (h : k.toNat < 32) :
    x >>> k = ok ⟨x.bv >>> k.toNat⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  rw [if_pos h0, if_pos (by simpa using h)]

theorem slice_idx {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.length) :
    s.index_usize i = ok (s.val[i.val]'h) := by
  simp [Slice.index_usize, h]

theorem cast_u32_val (x : Std.U32) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; have := x.hBounds; scalar_tac

theorem and255_lt (x : Std.U32) : (x &&& 255#u32).val < 256 := by
  have : (x &&& 255#u32).val = x.val &&& 255 := by
    simp [UScalar.val_and]
  rw [this]; exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem shr24_lt (x : Std.U32) : (⟨x.bv >>> 24⟩ : Std.U32).val < 256 := by
  show (x.bv >>> 24).toNat < 256
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.bv.isLt
  omega

theorem row_idx (a : Aeneas.Std.Array Std.U32 256#usize) (i : Usize) (h : i.val < 256) :
    a.index_usize i = ok (a.val[i.val]'(by rw [a.property]; exact h)) :=
  arr_idx a i h

theorem t8 : (8#i32).toNat = 8 := by decide
theorem t16 : (16#i32).toNat = 16 := by decide
theorem t24 : (24#i32).toNat = 24 := by decide

theorem cast_u8_val (x : Std.U8) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; have := x.hBounds; scalar_tac

theorem tb_eq (k : Nat) (i : Nat) (hk : k < (table.CRC32_TABLE.val).length) (hi : i < ((table.CRC32_TABLE.val[k]'hk).val).length) :
    ((table.CRC32_TABLE.val[k]'hk).val[i]'hi).bv = tb k i := by
  unfold tb
  rw [getElem!_pos (table.CRC32_TABLE.val) k hk, getElem!_pos ((table.CRC32_TABLE.val[k]'hk).val) i hi]

theorem usz (n : Nat) (h) : (Usize.ofNat n h).val = n := by
  rfl

theorem u32_and_val (a b : Std.U32) : (a &&& b).val = (a.bv &&& b.bv).toNat := rfl
theorem u32_mk_bv (x : BitVec 32) : (⟨x⟩ : Std.U32).bv = x := rfl
theorem c255 : (255#u32).bv = 0xFF#32 := rfl

theorem u32_xor_bv (a b : Std.U32) : (a ^^^ b).bv = a.bv ^^^ b.bv := rfl
theorem u32_and_bv (a b : Std.U32) : (a &&& b).bv = a.bv &&& b.bv := rfl
theorem u32_mk_val (x : BitVec 32) : (⟨x⟩ : Std.U32).val = x.toNat := rfl


theorem take16 {α : Type} (l : List α) (h : 16 ≤ l.length) :
    l.take 16 = [l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], l[9], l[10], l[11],
      l[12], l[13], l[14], l[15]] := by
  match l, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: rest, _ =>
    simp

theorem fold_16_eq (crc : Std.U32) (block : Slice Std.U8) (h : 16 ≤ block.length) :
    ∃ r, baseline.fold_16 crc block = ok r ∧ r.bv = (block.val.take 16).foldl sstep crc.bv := by
  unfold baseline.fold_16
  simp only [core.num.U32.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u32, lift, bind_tc_ok]
  simp (disch := scalar_tac) only [slice_idx, bind_tc_ok]
  simp (disch := first | decide | simp | scalar_tac) only [shr_i32, bind_tc_ok]
  simp only [t8, t16, t24]
  simp (disch := first | decide | (simp only [cast_u8_val]; scalar_tac) | (rw [cast_u32_val]; exact and255_lt _) | (rw [cast_u32_val]; exact shr24_lt _)) only [row_idx, bind_tc_ok]
  simp (disch := decide) only [arr_idx, bind_tc_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [u32_xor_bv, tb_eq, cast_u8_val, cast_u32_val, u32_mk_val]
  simp only [usz, u32_and_val, u32_mk_bv, c255, u32_xor_bv]
  have hlen : 16 ≤ block.val.length := h
  rw [take16 block.val hlen]
  exact fold16_math crc.bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [le_bytes])

theorem arr_len256 (x : Aeneas.Std.Array Std.U32 256#usize) : x.length = 256 := by
  have := x.property
  simp only [Aeneas.Std.Array.length]
  rw [this]; rfl

theorem u8_xor_val (a b : Std.U8) : (a ^^^ b).val = a.val ^^^ b.val := by
  simp [UScalar.val_xor]

theorem cast_u32_u8_val (x : Std.U32) : (UScalar.cast .U8 x).val = x.val % 256 := by
  rw [UScalar.cast_val_eq]; rfl

theorem len_eq_zero_iff {α : Type} (s : Slice α) : (Slice.len s = 0#usize) ↔ s.val.length = 0 := by
  constructor
  · intro h
    have := congrArg UScalar.val h
    rw [Slice.len_val] at this
    simpa using this
  · intro h
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val]
    simpa using h

theorem slow_body_nil (hl) (crc : Std.U32) :
    baseline.update_slow_loop.body ⟨[], hl⟩ crc = ok (ControlFlow.done crc) := by
  simp [baseline.update_slow_loop.body, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, len_eq_zero_iff]

/-- The tail of a non-empty sequence, typed as a CoreModels `Seq`. -/
def tailSeq (b : Std.U8) (rest : List Std.U8) (hl : (b :: rest).length ≤ Usize.max) :
    rust_primitives.sequence.Seq Std.U8 :=
  ⟨rest, by simp at hl; scalar_tac⟩

theorem seq_remove_cons (b : Std.U8) (rest : List Std.U8) (hl) :
    rust_primitives.sequence.seq_remove (⟨b :: rest, hl⟩ : Slice Std.U8) 0#usize =
      ok (b, tailSeq b rest hl) := by
  simp [rust_primitives.sequence.seq_remove, tailSeq]

theorem slow_body_cons (b : Std.U8) (rest : List Std.U8) (hl) (crc : Std.U32) :
    baseline.update_slow_loop.body ⟨b :: rest, hl⟩ crc ⦃ r =>
      ∃ crc1 : Std.U32, r = ControlFlow.cont (tailSeq b rest hl, crc1) ∧ crc1.bv = sstep crc.bv b ⦄ := by
  simp only [baseline.update_slow_loop.body, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, lift, bind_tc_ok]
  rw [if_neg (by rw [len_eq_zero_iff]; simp), seq_remove_cons]
  step*
  · simp only [cast_u8_val, arr_len256]; exact u8_lt _
  · subst_vars
    refine ⟨_, rfl, ?_⟩
    simp only [u32_xor_bv, i4_post2, tb_eq, cast_u8_val, u8_xor_val, cast_u32_u8_val, sstep]
    rfl

theorem slow_loop_spec (it : core.slice.iter.Iter Std.U8) (crc : Std.U32) :
    baseline.update_slow_loop it crc ⦃ r => r.bv = it.val.foldl sstep crc.bv ⦄ := by
  unfold baseline.update_slow_loop
  apply loop.spec_decr_nat (measure := fun p => p.1.val.length)
    (inv := fun p => p.1.val.foldl sstep p.2.bv = it.val.foldl sstep crc.bv)
  · rintro ⟨⟨l, hl⟩, c⟩ hinv
    simp only at hinv
    cases l with
    | nil =>
      simp only [slow_body_nil, spec_ok]
      simpa using hinv
    | cons b rest =>
      apply spec_mono (slow_body_cons b rest hl c)
      rintro r ⟨crc1, rfl, hc⟩
      refine ⟨?_, ?_⟩
      · simp only [tailSeq, hc]; simpa using hinv
      · simp [tailSeq]
  · rfl

theorem u32_not_bv (a : Std.U32) : (~~~ a).bv = ~~~ a.bv := rfl

theorem update_slow_spec (prev : Std.U32) (buf : Slice Std.U8) :
    baseline.update_slow prev buf ⦃ r => r.bv = ~~~ (buf.val.foldl sstep (~~~ prev.bv)) ⦄ := by
  unfold baseline.update_slow
  simp only [lift, bind_tc_ok, core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice]
  apply spec_bind (slow_loop_spec _ _)
  intro r hr
  rw [spec_ok, u32_not_bv, hr, u32_not_bv]

theorem slice_from16 (buf : Slice Std.U8) (h : 16 ≤ buf.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8) buf
      { start := 16#usize } ⦃ r => r.val = buf.val.drop 16 ⦄ := by
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, bind_tc_ok]
  have hle : 16#usize ≤ buf.len := by
    show (16#usize).val ≤ (buf.len).val
    rw [Slice.len_val]; exact h
  rw [if_pos hle]
  have hsub : buf.subslice { start := 16#usize, «end» := buf.len } =
      ok ⟨buf.val.slice 16 buf.val.length, by
        have := buf.val.slice_length_le 16 buf.val.length; have := buf.property; omega⟩ := by
    unfold Slice.subslice
    rw [if_pos (by simp only [Slice.len_val]; exact ⟨by simpa using h, le_refl _⟩)]
    simp [Slice.len_val]
  rw [hsub]
  simp only [bind_tc_ok, spec_ok]
  simp [List.slice]

theorem next_lt (s e : Usize) (h : s.val < e.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.Usize.Insts.CoreIterRangeStep
      { start := s, «end» := e } ⦃ r => r.1 = some s ∧ r.2.start.val = s.val + 1 ∧ r.2.«end» = e ⦄ := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, core.IteratorRange.next,
    core.Usize.Insts.CoreIterRangeStep, core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
    core.Usize.Insts.CoreCloneClone, core.Usize.Insts.CoreCloneClone.clone,
    core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket, bind_tc_ok]
  have hc : compare s.val e.val = .lt := Nat.compare_eq_lt.mpr h
  simp only [hc, if_true, core.convert.From.Blanket.from, bind_tc_ok, core.num.Usize.checked_add,
    core.num.Usize.overflowing_add, rust_primitives.arithmetic.overflowing_add_usize]
  have hov := UScalar.overflowing_add_eq s 1#usize
  have hmax : ¬ (s.val + (1#usize).val > UScalar.max .Usize) := by
    have := e.hBounds
    have h1 : (1#usize).val = 1 := rfl
    rw [h1]; scalar_tac
  simp only [hmax, if_false] at hov
  generalize UScalar.overflowing_add s 1#usize = z at *
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h1, h2⟩ := hov
  simp only at h1 h2
  simp only [h2, Bool.false_eq_true, if_false, bind_tc_ok, spec_ok]
  refine ⟨rfl, ?_, rfl⟩
  rw [h1]; rfl

theorem next_ge (s e : Usize) (h : e.val ≤ s.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.Usize.Insts.CoreIterRangeStep
      { start := s, «end» := e } = ok (none, { start := s, «end» := e }) := by
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, core.IteratorRange.next,
    core.Usize.Insts.CoreIterRangeStep, core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, bind_tc_ok]
  have hc : compare s.val e.val ≠ .lt := by
    intro hh; have := Nat.compare_eq_lt.mp hh; omega
  cases hcmp : compare s.val e.val with
  | lt => exact absurd hcmp hc
  | eq => simp
  | gt => simp

theorem unroll_val : baseline.update_fast_16.UNROLL.val = 4 := by
  unfold baseline.update_fast_16.UNROLL; rfl

theorem bytes_at_once : baseline.update_fast_16.BYTES_AT_ONCE ⦃ r => r.val = 64 ⦄ := by
  unfold baseline.update_fast_16.BYTES_AT_ONCE
  have := unroll_val
  step*

theorem len_ok (buf : Slice Std.U8) : core.slice.Slice.len buf = ok (Slice.len buf) := rfl

theorem loop1_spec (buf : Slice Std.U8) (crc : Std.U32) :
    baseline.update_fast_16_loop1 buf crc ⦃ r =>
      r.1.val.foldl sstep r.2.bv = buf.val.foldl sstep crc.bv ⦄ := by
  unfold baseline.update_fast_16_loop1
  apply loop.spec_decr_nat (measure := fun p => p.1.val.length)
    (inv := fun p => p.1.val.foldl sstep p.2.bv = buf.val.foldl sstep crc.bv)
  · rintro ⟨b, c⟩ hinv
    simp only at hinv
    simp only [baseline.update_fast_16_loop1.body, len_ok, bind_tc_ok]
    split
    · rename_i hge
      have hlen : 16 ≤ b.length := by
        have : (16#usize).val ≤ (Slice.len b).val := hge
        rw [Slice.len_val] at this; simpa using this
      obtain ⟨r, hr, hrv⟩ := fold_16_eq c b hlen
      rw [hr, bind_tc_ok]
      apply spec_bind (slice_from16 b hlen)
      intro b1 hb1
      rw [spec_ok]
      refine ⟨?_, ?_⟩
      · simp only
        rw [hb1, hrv, ← List.foldl_append, List.take_append_drop]; exact hinv
      · simp only
        rw [hb1, List.length_drop]
        have : b.val.length = b.length := rfl
        omega
    · rw [spec_ok]; exact hinv
  · rfl

theorem next_lt_eq (s e : Usize) (h : s.val < e.val) :
    ∃ s', core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.Usize.Insts.CoreIterRangeStep
      { start := s, «end» := e } = ok (some s, { start := s', «end» := e }) ∧ s'.val = s.val + 1 := by
  have := next_lt s e h
  cases hn : core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next core.Usize.Insts.CoreIterRangeStep
      { start := s, «end» := e } with
  | ok v =>
    rw [hn, spec_ok] at this
    obtain ⟨h1, h2, h3⟩ := this
    obtain ⟨o, ⟨s', e'⟩⟩ := v
    simp only at h1 h2 h3
    subst h1; subst h3
    exact ⟨s', rfl, h2⟩
  | fail e => rw [hn] at this; simp at this
  | div => rw [hn] at this; simp at this

theorem inner_spec (buf : Slice Std.U8) (crc : Std.U32) (h : 64 ≤ buf.length) :
    baseline.update_fast_16_loop0_loop0
      { start := 0#usize, «end» := baseline.update_fast_16.UNROLL } buf crc ⦃ r =>
      r.1.val.foldl sstep r.2.bv = buf.val.foldl sstep crc.bv ∧ r.1.length + 64 = buf.length ⦄ := by
  unfold baseline.update_fast_16_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p => 4 - p.1.start.val)
    (inv := fun p => p.1.«end» = baseline.update_fast_16.UNROLL ∧ p.1.start.val ≤ 4 ∧
      p.2.1.val.foldl sstep p.2.2.bv = buf.val.foldl sstep crc.bv ∧
      p.2.1.length + 16 * p.1.start.val = buf.length)
  · rintro ⟨it, b, c⟩ ⟨hend, hs, hinv, hlen⟩
    obtain ⟨s, e⟩ := it
    simp only at hend hs hinv hlen
    simp only [baseline.update_fast_16_loop0_loop0.body]
    by_cases hlt : s.val < 4
    · obtain ⟨s1, hn, hs1⟩ := next_lt_eq s e (by rw [hend, unroll_val]; exact hlt)
      rw [hn, bind_tc_ok]
      have hb16 : 16 ≤ b.length := by omega
      obtain ⟨r, hr, hrv⟩ := fold_16_eq c b hb16
      rw [hr]
      apply spec_bind (slice_from16 b hb16)
      intro b1 hb1
      rw [spec_ok]
      have hb1len : b1.length = b.length - 16 := by
        show b1.val.length = b.val.length - 16
        rw [hb1, List.length_drop]
      refine ⟨⟨hend, ?_, ?_, ?_⟩, ?_⟩
      · show s1.val ≤ 4
        omega
      · show List.foldl sstep r.bv b1.val = List.foldl sstep crc.bv buf.val
        rw [hb1, hrv, ← List.foldl_append, List.take_append_drop]; exact hinv
      · show b1.length + 16 * s1.val = buf.length
        rw [hb1len, hs1]
        omega
      · show 4 - s1.val < 4 - s.val
        omega
    · rw [next_ge s _ (by rw [hend, unroll_val]; omega), bind_tc_ok]
      apply (spec_ok (ControlFlow.done (b, c))).mpr
      have hs4 : s.val = 4 := by omega
      refine ⟨hinv, ?_⟩
      show b.length + 64 = buf.length
      rw [hs4] at hlen; omega
  · refine ⟨rfl, by simp, rfl, by simp⟩

theorem loop0_spec (buf : Slice Std.U8) (crc : Std.U32) :
    baseline.update_fast_16_loop0 buf crc ⦃ r =>
      r.1.val.foldl sstep r.2.bv = buf.val.foldl sstep crc.bv ⦄ := by
  unfold baseline.update_fast_16_loop0
  apply loop.spec_decr_nat (measure := fun p => p.1.val.length)
    (inv := fun p => p.1.val.foldl sstep p.2.bv = buf.val.foldl sstep crc.bv)
  · rintro ⟨b, c⟩ hinv
    simp only at hinv
    simp only [baseline.update_fast_16_loop0.body, len_ok, bind_tc_ok]
    apply spec_bind bytes_at_once
    intro i1 hi1
    split
    · rename_i hge
      have hlen : 64 ≤ b.length := by
        have : i1.val ≤ (Slice.len b).val := hge
        rw [Slice.len_val, hi1] at this; exact this
      apply spec_bind (inner_spec b c hlen)
      rintro ⟨b1, c1⟩ ⟨hf, hl⟩
      apply (spec_ok (ControlFlow.cont (b1, c1))).mpr
      refine ⟨?_, ?_⟩
      · show List.foldl sstep c1.bv b1.val = List.foldl sstep crc.bv buf.val
        rw [hf]; exact hinv
      · show b1.val.length < b.val.length
        have : b1.length + 64 = b.length := hl
        have e1 : b1.length = b1.val.length := rfl
        have e2 : b.length = b.val.length := rfl
        omega
    · rw [spec_ok]; exact hinv
  · rfl

theorem fast16_spec (prev : Std.U32) (buf : Slice Std.U8) :
    baseline.update_fast_16 prev buf ⦃ r => r.bv = ~~~ (buf.val.foldl sstep (~~~ prev.bv)) ⦄ := by
  unfold baseline.update_fast_16
  rw [show (lift (~~~ prev) : RustM Std.U32) = ok (~~~ prev) from rfl, bind_tc_ok]
  apply spec_bind (loop0_spec buf (~~~ prev))
  rintro ⟨b1, c1⟩ h1
  apply spec_bind (loop1_spec b1 c1)
  rintro ⟨b2, c2⟩ h2
  apply spec_mono (update_slow_spec (~~~ c2) b2)
  intro r hr
  rw [hr, u32_not_bv, BitVec.not_not]
  have h1' : List.foldl sstep c1.bv b1.val = List.foldl sstep (~~~ prev).bv buf.val := h1
  have h2' : List.foldl sstep c2.bv b2.val = List.foldl sstep c1.bv b1.val := h2
  rw [h2', h1', u32_not_bv]

/--
For every initial CRC value `crc` and every byte vector `bytes`, the
slicing-by-16 implementation `update_fast_16(crc, &bytes)` and the
byte-at-a-time implementation `update_slow(crc, &bytes)` both run without
panicking and return the same CRC-32.
-/
theorem fast_16_is_the_same_as_slow (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) :
    fast_16_is_the_same_as_slow_spec crc bytes := by
  unfold fast_16_is_the_same_as_slow_spec
  simp only [alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice, bind_tc_ok]
  apply spec_bind (fast16_spec crc _)
  intro f hf
  apply spec_bind (update_slow_spec crc _)
  intro sl hsl
  rw [spec_ok]
  show f = sl
  cases f; cases sl
  simp only [u32_mk_bv] at hf hsl
  rw [hf, hsl]

end Benchmark.Cases.Crc32fast.Baseline
