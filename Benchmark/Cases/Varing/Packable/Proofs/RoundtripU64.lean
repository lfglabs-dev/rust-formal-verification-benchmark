import Benchmark.Cases.Varing.Packable.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open varing

namespace Benchmark.Cases.Varing.Packable

theorem pack_u64_spec' (a b : Std.U64) :
    packable.builtin.pack_u64 a b ⦃ p => p.val = b.val * 2^64 + a.val ⦄ := by
  unfold packable.builtin.pack_u64
  step*
  have ha : a.val < 2^64 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hi : i.val = a.val := by
    rw [i_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hi1 : i1.val = b.val := by
    rw [i1_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]; omega
  have hi2 : i2.val = b.val * 2^64 := by
    rw [i2_post1, hi1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    simp [U128.size, U128.numBits]; omega
  rw [UScalar.val_or, hi, hi2, Nat.or_comm, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha]

theorem unpack_u64_spec' (p : Std.U128) :
    packable.builtin.unpack_u64 p ⦃ r => r.1.val = p.val % 2^64 ∧ r.2.val = p.val / 2^64 ⦄ := by
  unfold packable.builtin.unpack_u64
  step*
  have hp : p.val < 2^128 := by scalar_tac
  constructor
  · rw [low_post, UScalar.cast_val_eq]; simp [UScalarTy.numBits]
  · rw [high_post, UScalar.cast_val_eq, i_post1, Nat.shiftRight_eq_div_pow]
    simp [UScalarTy.numBits]; omega

/--
Packing two `u64` values into a `u128` with `<u64 as Packable<u64, u128>>::pack` and unpacking the result never panics and returns the original pair.
-/
theorem roundtrip_u64 (a : Std.U64) (b : Std.U64) :
    roundtrip_u64_spec a b := by
  unfold roundtrip_u64_spec U64.Insts.VaringPackablePackableU64U128.pack
    U64.Insts.VaringPackablePackableU64U128.unpack
  step with pack_u64_spec' as ⟨p, hp⟩
  step with unpack_u64_spec' as ⟨r, hr1, hr2⟩
  have ha : a.val < 2^64 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  constructor
  · rw [UScalar.eq_equiv, hr1, hp]; omega
  · rw [UScalar.eq_equiv, hr2, hp]; omega

end Benchmark.Cases.Varing.Packable
