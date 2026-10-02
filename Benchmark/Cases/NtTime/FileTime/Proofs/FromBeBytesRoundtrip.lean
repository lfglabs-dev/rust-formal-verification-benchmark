import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- Value of Aeneas' `BitVec.fromLEBytes`: little-endian base-256 evaluation. -/
theorem fbeb_fromLE_toNat (l : List Byte) :
    (BitVec.fromLEBytes l).toNat = l.foldr (fun b acc => b.toNat + 256 * acc) 0 := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    rw [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, ih, List.foldr_cons]
    have hb := b.isLt
    have hr := (BitVec.fromLEBytes l).isLt
    rw [ih] at hr
    simp only [List.length_cons] at hr ⊢
    generalize List.foldr (fun b acc => b.toNat + 256 * acc) 0 l = r at hr ⊢
    have hp : 2 ^ (8 * (l.length + 1)) = 2^8 * 2 ^ (8 * l.length) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h1 := Nat.one_le_two_pow (n := 8 * l.length)
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by rw [hp]; simp at hb; nlinarith)]
    rw [Nat.mod_eq_of_lt (a := r) (by rw [hp]; omega)]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by rw [hp]; simp at hb ⊢; omega)]
    rw [Nat.mul_comm, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hb]
    ring

/--
`FileTime::from_be_bytes` never panics and decodes its 8 bytes as a big-endian base-256
number (the value of `FileTime::new(u64::from_be_bytes(bytes))`).
-/
theorem from_be_bytes_roundtrip (bytes : Std.Array Std.U8 8#usize) :
    from_be_bytes_roundtrip_spec bytes := by
  unfold from_be_bytes_roundtrip_spec file_time.FileTime.from_be_bytes
    core.num.U64.from_be_bytes rust_primitives.arithmetic.from_be_bytes_u64 file_time.FileTime.new
  simp only [bind_tc_ok, WP.spec_ok]
  simp only [Aeneas.Std.core.num.U64.from_be_bytes, UScalar.val, BitVec.toNat_cast,
    BitVec.fromBEBytes, fbeb_fromLE_toNat, List.foldl_eq_foldr_reverse]
  rw [← List.map_reverse, ← List.map_reverse, List.foldr_map, List.foldr_map]
  apply congrArg (fun f => List.foldr f 0 _)
  funext x y
  simp only [U8.bv]
  ring

end Benchmark.Cases.NtTime.FileTime
