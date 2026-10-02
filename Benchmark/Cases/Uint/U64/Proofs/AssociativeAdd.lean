import Benchmark.Cases.Uint.U64.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ethereum_types

namespace Benchmark.Cases.Uint.U64

/-- A one-limb `U64` with limb `a`. -/
def ua_mk (a : Std.U64) : uint.U64 := ⟨[a], by simp⟩

theorem ua_cases (x : uint.U64) : ∃ a, x = ua_mk a := by
  obtain ⟨l, hl⟩ := x
  match l, hl with
  | [a], _ => exact ⟨a, rfl⟩

theorem ua_overflowing_add_eq (a b : Std.U64) :
    uint.U64.overflowing_add (ua_mk a) (ua_mk b) =
      ok (ua_mk (UScalar.overflowing_add a b).1, (UScalar.overflowing_add a b).2) := by
  unfold uint.U64.overflowing_add
  rw [uint.U64.overflowing_add.i.eq_1]
  have h1 : ((0#u64 != 0#u64) = true) = False := by decide
  simp only [h1, if_false, ge_iff_le, le_refl, if_true]
  simp [Array.index_usize, Array.update, ua_mk, core.num.U64.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u64, lift, Array.repeat]
  generalize UScalar.overflowing_add a b = p
  obtain ⟨r, o⟩ := p
  cases o
  · simp [UScalar.cast_fromBool]; rfl
  · simp [UScalar.cast_fromBool]; decide

theorem ua_ovf_val (a b : Std.U64) :
    ((UScalar.overflowing_add a b).2 = false ↔ a.val + b.val < 2^64) ∧
    (a.val + b.val < 2^64 → (UScalar.overflowing_add a b).1.val = a.val + b.val) := by
  have h := UScalar.overflowing_add_eq a b
  have hmax : UScalar.max UScalarTy.U64 = 2^64 - 1 := by simp [U64.max, U64.numBits]
  simp only [hmax] at h
  split at h
  · refine ⟨?_, ?_⟩
    · simp [h.2]; omega
    · intro; omega
  · exact ⟨by simp [h.2]; omega, fun _ => h.1⟩

theorem ua_add_eq (a b : Std.U64) (h : a.val + b.val < 2^64) :
    add (ua_mk a) (ua_mk b) = ok (ua_mk (UScalar.overflowing_add a b).1) := by
  have hf := (ua_ovf_val a b).1.mpr h
  simp only [add, uint.U64.Insts.CoreOpsArithAddTU64.add, core.convert.Into.Blanket,
    core.convert.Into.Blanket.into, core.convert.From.Blanket, core.convert.From.Blanket.from,
    bind_tc_ok, ua_overflowing_add_eq, hf]
  simp

theorem ua_eq_self (a : Std.U64) :
    uint.U64.Insts.CoreCmpPartialEqU64.eq (ua_mk a) (ua_mk a) ⦃ b => b = true ⦄ := by
  unfold uint.U64.Insts.CoreCmpPartialEqU64.eq core.Array.Insts.CoreCmpPartialEqArray.eq
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  apply loop.spec_decr_nat (fun i : Std.Usize => 1 - i.val) (fun i => i.val ≤ 1)
  · intro i hi
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    by_cases h : i.val < 1
    · have h' : i < 1#usize := by scalar_tac
      have hi0 : i.val = 0 := by omega
      have hidx : rust_primitives.slice.array_index (ua_mk a) i = ok a := by
        simp [rust_primitives.slice.array_index, Slice.index_usize, Std.Array.to_slice, ua_mk, hi0]
      simp only [h', if_true, hidx, bind_tc_ok, core.U64.Insts.CoreCmpPartialEqU64, beq_self_eq_true]
      step as ⟨i1, hi1⟩
      exact ⟨by omega, by omega⟩
    · have h' : ¬ i < 1#usize := by scalar_tac
      simp only [h', if_false, WP.spec_ok]
  · simp

theorem ua_ovf_hyp (a b : Std.U64)
    (h : uint.U64.overflowing_add (ua_mk a) (ua_mk b) ⦃ r => r.2 = false ⦄) :
    a.val + b.val < 2^64 := by
  rw [ua_overflowing_add_eq, WP.spec_ok] at h
  exact (ua_ovf_val a b).1.mp h

/-- `(x + y) + z == x + (y + z)` holds whenever the test does not discard. -/
theorem associative_add (x y z : uint.U64)
    (h_assume_xy : uint.U64.overflowing_add x y ⦃ r => r.2 = false ⦄)
    (h_assume_yz : uint.U64.overflowing_add y z ⦃ r => r.2 = false ⦄)
    (h_assume_xyz : (do
      let xy ← add x y
      uint.U64.overflowing_add xy z) ⦃ r => r.2 = false ⦄) :
    associative_add_spec x y z := by
  obtain ⟨a, rfl⟩ := ua_cases x
  obtain ⟨b, rfl⟩ := ua_cases y
  obtain ⟨c, rfl⟩ := ua_cases z
  have hab := ua_ovf_hyp a b h_assume_xy
  have hbc := ua_ovf_hyp b c h_assume_yz
  have habv := (ua_ovf_val a b).2 hab
  have hbcv := (ua_ovf_val b c).2 hbc
  rw [ua_add_eq a b hab, bind_tc_ok] at h_assume_xyz
  have habc := ua_ovf_hyp _ c h_assume_xyz
  rw [habv] at habc
  have ha_bc : a.val + (UScalar.overflowing_add b c).1.val < 2^64 := by rw [hbcv]; omega
  have hl : (UScalar.overflowing_add (UScalar.overflowing_add a b).1 c).1.val = a.val + b.val + c.val := by
    rw [(ua_ovf_val _ c).2 (by rw [habv]; exact habc), habv]
  have hr : (UScalar.overflowing_add a (UScalar.overflowing_add b c).1).1.val = a.val + b.val + c.val := by
    rw [(ua_ovf_val a _).2 ha_bc, hbcv]; omega
  have heq : (UScalar.overflowing_add (UScalar.overflowing_add a b).1 c).1 =
      (UScalar.overflowing_add a (UScalar.overflowing_add b c).1).1 := by
    apply UScalar.eq_of_val_eq; rw [hl, hr]
  unfold associative_add_spec
  rw [ua_add_eq a b hab, bind_tc_ok, ua_add_eq _ c (by rw [habv]; exact habc), bind_tc_ok,
    ua_add_eq b c hbc, bind_tc_ok, ua_add_eq a _ ha_bc, bind_tc_ok, heq]
  exact ua_eq_self _

end Benchmark.Cases.Uint.U64
