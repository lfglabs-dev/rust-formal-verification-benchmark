import RustCrdtDot.Extraction

/-!
# rust-crdt — `Dot` specifications

Implementation: `extracted/RustCrdtDot` (verbatim `cargo hax extract
rust-crdt-dot` output for rust-crdt/rust-crdt@c92f8d1).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.RustCrdt.Dot

open crdts

/-- PBT `crdts::dot::test::prop_partial_order` (src/dot.rs:160): the four
outcomes of `a.partial_cmp(&b)` / `b.partial_cmp(&a)` exactly mirror the actor
equality and the counter order. -/
def prop_partial_order_spec (a b : dot.Dot Std.U8) : Prop :=
  (do
    let cmp_ab ←
      dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp
        core.U8.Insts.CoreCmpPartialOrdU8 a b
    let cmp_ba ←
      dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp
        core.U8.Insts.CoreCmpPartialOrdU8 b a
    match cmp_ab, cmp_ba with
    | core.option.Option.None, core.option.Option.None =>
        core.U8.Insts.CoreCmpPartialEqU8.ne a.actor b.actor
    | core.option.Option.Some core.cmp.Ordering.Less,
      core.option.Option.Some core.cmp.Ordering.Greater => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let lt ← core.U64.Insts.CoreCmpPartialOrdU64.lt a.counter b.counter
      ok (eq && lt)
    | core.option.Option.Some core.cmp.Ordering.Greater,
      core.option.Option.Some core.cmp.Ordering.Less => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let gt ← core.U64.Insts.CoreCmpPartialOrdU64.gt a.counter b.counter
      ok (eq && gt)
    | core.option.Option.Some core.cmp.Ordering.Equal,
      core.option.Option.Some core.cmp.Ordering.Equal => do
      let eq ← core.U8.Insts.CoreCmpPartialEqU8.eq a.actor b.actor
      let eqc ← core.U64.Insts.CoreCmpPartialEqU64.eq a.counter b.counter
      ok (eq && eqc)
    | _, _ => ok false) ⦃ eq => eq = true ⦄

/-- PBT `crdts::dot::test::prop_ordered_dot_is_ordered_by_actor_first`
(src/dot.rs:180): converting two `Dot`s to `OrdDot` and comparing, the actor
comparison decides the order (`<`/`>` are `PartialOrd::lt`/`gt`), and on equal
actors `ord_dot_a.cmp(&ord_dot_b)` (the derived `Ord::cmp` of `OrdDot`, as in
the test) agrees with the counter order. (v1.1: v1.0 used `partial_cmp` here.) -/
def prop_ordered_dot_is_ordered_by_actor_first_spec (a b : dot.Dot Std.U8) :
    Prop :=
  (do
    let oa ← dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd a
    let ob ← dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd b
    let actor_cmp ← core.U8.Insts.CoreCmpOrd.cmp oa.actor ob.actor
    let ord_inst := dot.OrdDot.Insts.CoreCmpOrd core.U8.Insts.CoreCmpOrd
      core.U8.Insts.CoreCmpOrd
    match actor_cmp with
    | core.cmp.Ordering.Less =>
        core.cmp.PartialOrd.lt.default ord_inst.PartialOrdInst oa ob
    | core.cmp.Ordering.Greater =>
        core.cmp.PartialOrd.gt.default ord_inst.PartialOrdInst oa ob
    | core.cmp.Ordering.Equal => do
      let counter_cmp ← core.U64.Insts.CoreCmpOrd.cmp oa.counter ob.counter
      let full_cmp ← ord_inst.cmp oa ob
      core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq counter_cmp full_cmp)
    ⦃ eq => eq = true ⦄

end Benchmark.Cases.RustCrdt.Dot
