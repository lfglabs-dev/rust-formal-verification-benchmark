import Benchmark.Cases.NtTime.FileTime.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- One call of the `to_le_bytes` closure: byte `n` of `c` (for `n < 8`), state unchanged. -/
theorem tlb_closure_spec (c : Std.U64) (n : Nat) (hn : n < 8) :
    core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut c
      ⟨BitVec.ofNat _ n⟩ ⦃ q => q.2 = c ∧ q.1.val = c.val / 256^n % 256 ⦄ := by
  unfold core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  have hi : (UScalar.cast UScalarTy.U32 (⟨BitVec.ofNat _ n⟩ : Std.Usize)).val = n := by
    rw [UScalar.cast_val_eq]
    have h1 : (⟨BitVec.ofNat _ n⟩ : Std.Usize).val = n := by
      simp only [UScalar.val, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      rw [UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with h | h
      · rw [h]; omega
      · rw [h]; omega
    rw [h1]; simp; omega
  step*
  rw [i4_post, UScalar.cast_val_eq, i3_post1, i2_post, i1_post, i_post, hi,
    Nat.shiftRight_eq_div_pow]
  simp only [UScalarTy.U8_numBits_eq]
  have h8 : 8 * n % 64 = 8 * n := Nat.mod_eq_of_lt (by omega)
  rw [h8, pow_mul]
  norm_num

/-- The first `n ≤ 8` iterations of `array_from_fn` produce bytes `0 .. n-1` of `c`. -/
theorem tlb_go_spec (c : Std.U64) : ∀ n, n ≤ 8 →
    rust_primitives.slice.array_from_fn_go
      core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 c n
      ⦃ p => p.2 = c ∧ p.1.map (·.val) = (List.range n).map (fun k => c.val / 256^k % 256) ⦄
  | 0, _ => by simp [rust_primitives.slice.array_from_fn_go]
  | n+1, hn => by
    rw [rust_primitives.slice.array_from_fn_go]
    apply spec_bind (tlb_go_spec c n (by omega))
    rintro ⟨l, c'⟩ ⟨hc, hl⟩
    simp only at hc hl
    subst hc
    apply spec_bind (tlb_closure_spec c' n (by omega))
    rintro ⟨b, c''⟩ ⟨hc, hb⟩
    simp only at hc hb
    subst hc
    simp only [WP.spec_ok, List.map_append, hl, List.range_succ, List.map_cons, List.map_nil, hb]
    simp

/-- CoreModels `u64::to_le_bytes` returns the little-endian digits. -/
theorem tlb_to_le_spec (c : Std.U64) :
    core.num.U64.to_le_bytes c ⦃ bytes =>
      bytes.val.map (·.val) = (List.range 8).map (fun k => c.val / 256^k % 256) ⦄ := by
  unfold core.num.U64.to_le_bytes rust_primitives.slice.array_from_fn
  apply spec_bind (tlb_go_spec c 8 (le_refl _))
  rintro ⟨l, c'⟩ ⟨hc, hl⟩
  simp only at hc hl
  have hlen : l.length = (8#usize).val := by
    have := congrArg List.length hl
    simp at this
    simpa using this
  rw [dif_pos hlen]
  simp only [WP.spec_ok]
  exact hl

/--
`FileTime::to_le_bytes` never panics and returns the little-endian base-256 digits of
the raw tick count (the value of `ft.to_raw().to_le_bytes()`).
-/
theorem to_le_bytes_roundtrip (ft : file_time.FileTime) :
    to_le_bytes_roundtrip_spec ft := by
  unfold to_le_bytes_roundtrip_spec file_time.FileTime.to_le_bytes file_time.FileTime.to_raw
  simp only [bind_tc_ok]
  apply spec_bind (tlb_to_le_spec ft)
  intro bytes hb
  simp only [WP.spec_ok]
  rw [hb]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append]
  norm_num

end Benchmark.Cases.NtTime.FileTime
