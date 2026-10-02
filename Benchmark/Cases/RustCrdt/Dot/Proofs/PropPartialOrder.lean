import Benchmark.Cases.RustCrdt.Dot.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

theorem u8_peq_eq (x y : Std.U8) :
    core.U8.Insts.CoreCmpPartialEqU8.eq x y = ok (x == y) := rfl

theorem u8_peq_ne (x y : Std.U8) :
    core.U8.Insts.CoreCmpPartialEqU8.ne x y = ok (x != y) := rfl

theorem u8_po_peq (x y : Std.U8) :
    core.U8.Insts.CoreCmpPartialOrdU8.PartialEqInst.eq x y = ok (x == y) := rfl

theorem u64_partial_cmp (x y : Std.U64) :
    core.U64.Insts.CoreCmpPartialOrdU64.partial_cmp x y =
      ok (core.option.Option.Some
        (match compare x.val y.val with
         | .lt => core.cmp.Ordering.Less
         | .eq => core.cmp.Ordering.Equal
         | .gt => core.cmp.Ordering.Greater)) := rfl

theorem u64_lt (x y : Std.U64) :
    core.U64.Insts.CoreCmpPartialOrdU64.lt x y =
      ok (match compare x.val y.val with | .lt => true | _ => false) := rfl

theorem u64_gt (x y : Std.U64) :
    core.U64.Insts.CoreCmpPartialOrdU64.gt x y =
      ok (match compare x.val y.val with | .gt => true | _ => false) := rfl

theorem u64_peq_eq (x y : Std.U64) :
    core.U64.Insts.CoreCmpPartialEqU64.eq x y = ok (x == y) := rfl

/-- PBT `crdts::dot::test::prop_partial_order` (src/dot.rs:160): the four
outcomes of `a.partial_cmp(&b)` / `b.partial_cmp(&a)` exactly mirror the actor
equality and the counter order. -/
theorem prop_partial_order (a b : dot.Dot Std.U8) :
    prop_partial_order_spec a b := by
  unfold prop_partial_order_spec
  simp only [dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp, bind_tc_ok, u8_po_peq]
  cases hab : a.actor == b.actor with
  | true =>
    have hba : (b.actor == a.actor) = true := beq_iff_eq.mpr (beq_iff_eq.mp hab).symm
    rw [if_pos rfl, if_pos hba]
    rcases Nat.lt_trichotomy a.counter.val b.counter.val with h | h | h
    · have c1 : compare a.counter.val b.counter.val = .lt := Nat.compare_eq_lt.mpr h
      have c2 : compare b.counter.val a.counter.val = .gt :=
        Nat.compare_eq_gt.mpr (show b.counter.val > a.counter.val by omega)
      simp only [u64_partial_cmp, bind_tc_ok, u8_peq_eq, u64_lt, c1, c2, hab]
      exact (spec_ok _).mp rfl
    · have c1 : compare a.counter.val b.counter.val = .eq := Nat.compare_eq_eq.mpr h
      have c2 : compare b.counter.val a.counter.val = .eq :=
        Nat.compare_eq_eq.mpr (show b.counter.val = a.counter.val by omega)
      simp only [u64_partial_cmp, bind_tc_ok, u8_peq_eq, u64_peq_eq, c1, c2,
        hab]
      exact (spec_ok _).mp (by simp [show a.counter = b.counter by scalar_tac, beq_iff_eq])
    · have c1 : compare a.counter.val b.counter.val = .gt := Nat.compare_eq_gt.mpr h
      have c2 : compare b.counter.val a.counter.val = .lt :=
        Nat.compare_eq_lt.mpr (show b.counter.val < a.counter.val by omega)
      simp only [u64_partial_cmp, bind_tc_ok, u8_peq_eq, u64_gt, c1, c2, hab]
      exact (spec_ok _).mp rfl
  | false =>
    have hba : (b.actor == a.actor) = false := by
      cases hba' : b.actor == a.actor with
      | true =>
        rw [← beq_iff_eq.mp hba'] at hab
        simp at hab
      | false => rfl
    rw [if_neg (show ¬((false : Bool) = true) from by decide),
        if_neg (show ¬((b.actor == a.actor) = true) from by simp [hba])]
    simp only [bind_tc_ok, u8_peq_ne]
    exact (spec_ok _).mp (show (a.actor != b.actor) = true by
      simp [bne, hab])

end Benchmark.Cases.RustCrdt.Dot
