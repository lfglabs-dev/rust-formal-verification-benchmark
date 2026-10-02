import Benchmark.Cases.Varing.Packable.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

theorem pack_u32_u64_spec' (a : Std.U32) (b : Std.U64) :
    packable.builtin.pack_u32_u64 a b ⦃ p => p.val = b.val * 2^32 + a.val ⦄ := by
  unfold packable.builtin.pack_u32_u64
  simp only [core.num.U32.BITS]
  step*
  have ha : a.val < 2^32 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hs : small.val = a.val := by
    rw [small_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hl : large.val = b.val := by
    rw [large_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hi : i.val = b.val * 2^32 := by
    rw [i_post1, hl]; simp only [UScalarTy.numBits]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    simp [U128.size, U128.numBits]; omega
  rw [UScalar.val_or, hs, hi, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha]

theorem unpack_u32_u64_spec' (p : Std.U128) :
    packable.builtin.unpack_u32_u64 p ⦃ r => r.1.val = p.val % 2^32 ∧ r.2.val = p.val / 2^32 % 2^64 ⦄ := by
  unfold packable.builtin.unpack_u32_u64
  simp only [core.num.U32.BITS]
  step*
  · have hi : i.val = 2^32 := by
      rw [i_post1]; simp [UScalarTy.numBits, U128.size, U128.numBits]
    have hm : small_mask.val = 2^32 - 1 := by rw [small_mask_post1, hi]
    have hs : small.val = p.val % 2^32 := by
      rw [small_post1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    have hl : large.val = p.val / 2^32 := by
      rw [large_post1, Nat.shiftRight_eq_div_pow]; simp [UScalarTy.numBits]
    constructor
    · rw [i1_post, UScalar.cast_val_eq, hs]; simp [UScalarTy.numBits]
    · rw [i2_post, UScalar.cast_val_eq, hl]; simp [UScalarTy.numBits]

/--
Packing a `u32` and a `u64` into a `u128` in either order (`a.pack(&b)` and `b.pack(&a)`) and unpacking with the matching `Packable` impl never panics and returns the original values in both directions.
-/
theorem mix_roundtrip_u32_u64 (a : Std.U32) (b : Std.U64) :
    mix_roundtrip_u32_u64_spec a b := by
  unfold mix_roundtrip_u32_u64_spec U32.Insts.VaringPackablePackableU64U128.pack
    U32.Insts.VaringPackablePackableU64U128.unpack U64.Insts.VaringPackablePackableU32U128.pack
    U64.Insts.VaringPackablePackableU32U128.unpack packable.builtin.pack_u64_u32
    packable.builtin.unpack_u64_u32
  have ha : a.val < 2^32 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  step with pack_u32_u64_spec' as ⟨p, hp⟩
  step with unpack_u32_u64_spec' as ⟨r, hr1, hr2⟩
  step with pack_u32_u64_spec' as ⟨q, hq⟩
  step with unpack_u32_u64_spec' as ⟨s, hs1, hs2⟩
  obtain ⟨s1, s2⟩ := s
  step*
  dsimp only at hs1 hs2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [UScalar.eq_equiv]
  · rw [hr1, hp]; omega
  · rw [hr2, hp]; omega
  · rw [hs1, hq]; omega
  · rw [hs2, hq]; omega

end Benchmark.Cases.Varing.Packable
