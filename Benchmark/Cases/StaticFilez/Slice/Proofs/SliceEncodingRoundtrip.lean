import Benchmark.Cases.StaticFilez.Slice.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open static_filez

namespace Benchmark.Cases.StaticFilez.Slice

/-- High half: masking with `0xFFFF_FFFF_0000_0000` and shifting right by 32
recovers `b` from `a ||| b <<< 32` (both below `2^32`). -/
theorem nat_hi (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    ((a ||| b <<< 32) &&& 18446744069414584320) >>> 32 = b := by
  have hM : (18446744069414584320 : Nat) = (2^32 - 1) <<< 32 := by decide
  rw [hM]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  have h1 : a.testBit (32 + j) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
  by_cases hj : j < 32
  · simp [h1, hj]
  · have h2 : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h2]

/-- Low half: masking with `0x0000_0000_FFFF_FFFF` recovers `a`. -/
theorem nat_lo (a b : Nat) (ha : a < 2^32) :
    (a ||| b <<< 32) &&& 4294967295 = a := by
  have hM : (4294967295 : Nat) = 2^32 - 1 := by decide
  rw [hM, Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha,
    Nat.shiftLeft_eq]
  omega

/-- `x as usize as u64` is the identity on `u32` values (for either `usize` width). -/
theorem cast_usize_u64_val (x : Std.U32) :
    (UScalar.cast .U64 (UScalar.cast .Usize x)).val = x.val := by
  have hx : x.val < 2^32 := by scalar_tac
  rw [UScalar.cast_val_eq, U32.cast_Usize_val_eq]
  simp only [UScalarTy.U64_numBits_eq]
  omega

/--
Packing an (offset, length) pair of `u32`-range `usize`s into one `u64` with
`pack_in_u64` and unpacking it again with `unpack_from_u64` never panics and
returns exactly the original pair.
-/
theorem slice_encoding_roundtrip (i l : Std.U32) :
    slice_encoding_roundtrip_spec i l := by
  unfold slice_encoding_roundtrip_spec slice.pack_in_u64 slice.unpack_from_u64
  simp only [lift]
  step*
  have hi32 : i.val < 2^32 := by scalar_tac
  have hl32 : l.val < 2^32 := by scalar_tac
  have hx : x.val = i.val <<< 32 := by
    have hsz : U64.size = 2^64 := by simp [U64.size, U64.numBits]
    rw [x_post1, cast_usize_u64_val, Nat.shiftLeft_eq, hsz]
    exact Nat.mod_eq_of_lt (by omega)
  have hsmall : ∀ n : Nat, n < 2^32 → n % 2^System.Platform.numBits = n := fun n hn => by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  refine ⟨?_, ?_⟩
  · rw [UScalar.eq_equiv, UScalar.cast_val_eq, U32.cast_Usize_val_eq, i1_post1]
    simp only [UScalar.val_and, UScalar.val_or, cast_usize_u64_val, hx]
    rw [show (18446744069414584320#u64 : U64).val = 18446744069414584320 from rfl,
      nat_hi _ _ hl32 hi32]
    simp [hsmall _ hi32]
  · rw [UScalar.eq_equiv, UScalar.cast_val_eq, U32.cast_Usize_val_eq]
    simp only [UScalar.val_and, UScalar.val_or, cast_usize_u64_val, hx]
    rw [show (4294967295#u64 : U64).val = 4294967295 from rfl, nat_lo _ _ hl32]
    simp [hsmall _ hl32]

end Benchmark.Cases.StaticFilez.Slice
