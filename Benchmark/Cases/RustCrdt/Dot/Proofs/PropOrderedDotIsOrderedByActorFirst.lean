import Benchmark.Cases.RustCrdt.Dot.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crdts

namespace Benchmark.Cases.RustCrdt.Dot

theorem u8_ord_cmp (x y : Std.U8) :
    core.U8.Insts.CoreCmpOrd.cmp x y =
      ok (match compare x.val y.val with
          | .lt => core.cmp.Ordering.Less
          | .eq => core.cmp.Ordering.Equal
          | .gt => core.cmp.Ordering.Greater) := rfl

theorem u64_ord_cmp (x y : Std.U64) :
    core.U64.Insts.CoreCmpOrd.cmp x y =
      ok (match compare x.val y.val with
          | .lt => core.cmp.Ordering.Less
          | .eq => core.cmp.Ordering.Equal
          | .gt => core.cmp.Ordering.Greater) := rfl

theorem u64_partial_cmp (x y : Std.U64) :
    core.U64.Insts.CoreCmpPartialOrdU64.partial_cmp x y =
      ok (core.option.Option.Some
        (match compare x.val y.val with
         | .lt => core.cmp.Ordering.Less
         | .eq => core.cmp.Ordering.Equal
         | .gt => core.cmp.Ordering.Greater)) := rfl

/-- PBT `crdts::dot::test::prop_ordered_dot_is_ordered_by_actor_first`
(src/dot.rs:180): converting two `Dot`s to `OrdDot` and comparing, the actor
comparison decides the order, and on equal actors the `OrdDot` order agrees
with the counter order. -/
theorem prop_ordered_dot_is_ordered_by_actor_first (a b : dot.Dot Std.U8) :
    prop_ordered_dot_is_ordered_by_actor_first_spec a b := by
  unfold prop_ordered_dot_is_ordered_by_actor_first_spec
  simp only [dot.OrdDot.Insts.CoreConvertFromDot.from, bind_tc_ok, u8_ord_cmp]
  rcases Nat.lt_trichotomy a.actor.val b.actor.val with h | h | h
  · have c1 : compare a.actor.val b.actor.val = .lt := Nat.compare_eq_lt.mpr h
    simp only [c1, core.cmp.PartialOrd.lt.default, bind_tc_ok,
      dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp,
      core.U8.Insts.CoreCmpOrd, core.mkUOrd, core.mkUPartialOrd, bind_tc_ok]
    exact (spec_ok _).mp rfl
  · have c1 : compare a.actor.val b.actor.val = .eq := Nat.compare_eq_eq.mpr h
    rcases Nat.lt_trichotomy a.counter.val b.counter.val with h2 | h2 | h2
    · have cc1 : compare a.counter.val b.counter.val = .lt := Nat.compare_eq_lt.mpr h2
      simp only [c1, cc1, u64_ord_cmp, bind_tc_ok,
        dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp,
        core.U8.Insts.CoreCmpOrd, core.mkUOrd, core.mkUPartialOrd, bind_tc_ok,
        u64_partial_cmp, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
      exact (spec_ok _).mp rfl
    · have cc1 : compare a.counter.val b.counter.val = .eq := Nat.compare_eq_eq.mpr h2
      simp only [c1, cc1, u64_ord_cmp, bind_tc_ok,
        dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp,
        core.U8.Insts.CoreCmpOrd, core.mkUOrd, core.mkUPartialOrd, bind_tc_ok,
        u64_partial_cmp, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
      exact (spec_ok _).mp rfl
    · have cc1 : compare a.counter.val b.counter.val = .gt := Nat.compare_eq_gt.mpr h2
      simp only [c1, cc1, u64_ord_cmp, bind_tc_ok,
        dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp,
        core.U8.Insts.CoreCmpOrd, core.mkUOrd, core.mkUPartialOrd, bind_tc_ok,
        u64_partial_cmp, core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
      exact (spec_ok _).mp rfl
  · have c1 : compare a.actor.val b.actor.val = .gt :=
      Nat.compare_eq_gt.mpr h
    simp only [c1, core.cmp.PartialOrd.gt.default, bind_tc_ok,
      dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp,
      core.U8.Insts.CoreCmpOrd, core.mkUOrd, core.mkUPartialOrd, bind_tc_ok]
    exact (spec_ok _).mp rfl

end Benchmark.Cases.RustCrdt.Dot
