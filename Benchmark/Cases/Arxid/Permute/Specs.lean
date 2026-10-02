import ArxidPermute.Extraction

/-!
# arxid — specifications (module `arxid::permute`)

Implementation: `extracted/ArxidPermute` (verbatim `cargo hax extract
arxid-permute` output for lucasolopes/arxid@35a9a085, crate `impl/rust`,
rooted at `arxid::permute`).

`permute::obfuscate(id, key)` masks `id` to the 40-bit domain
(`id & MAX_ID`, `MAX_ID = (1 << 40) - 1`) and runs a balanced 6-round Feistel
network over two 20-bit halves (`feistel_n`); `permute::deobfuscate` masks and
runs the rounds backwards (`feistel_n_inv`). The round function (`round_fn`,
`subkey`) is ARX arithmetic on `u32`/`u64` with wrapping adds, rotations and a
wrapping multiply.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
Constants: `MAX_ID = 2^40 - 1 = 1099511627775`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Arxid.Permute

open arxid

/-- PBT `round_trip_over_the_whole_domain` (impl/rust/tests/properties.rs:10):
for `key: u64` and `id in 0u64..=MAX_ID`,
`prop_assert_eq!(deobfuscate(obfuscate(id, key), key), id)`. -/
def round_trip_over_the_whole_domain_spec (key id : Std.U64) : Prop :=
  (do
    let code ← permute.obfuscate id key
    permute.deobfuscate code key) ⦃ back => back = id ⦄

/-- PBT `output_never_leaves_the_domain` (impl/rust/tests/properties.rs:15):
for arbitrary `key: u64` and `id: u64`,
`prop_assert!(obfuscate(id, key) <= MAX_ID)` and then
`prop_assert!(deobfuscate(id, key) <= MAX_ID)` (`MAX_ID = 2^40 - 1`). -/
def output_never_leaves_the_domain_spec (key id : Std.U64) : Prop :=
  (do
    let code ← permute.obfuscate id key
    let back ← permute.deobfuscate id key
    ok (code, back)) ⦃ (code, back) =>
      code.val ≤ 2^40 - 1 ∧ back.val ≤ 2^40 - 1 ⦄

/-- PBT `out_of_domain_input_is_reduced_not_rejected`
(impl/rust/tests/properties.rs:21): for arbitrary `key: u64` and `id: u64`,
`prop_assert_eq!(obfuscate(id, key), obfuscate(id & MAX_ID, key))` and then
`prop_assert_eq!(deobfuscate(obfuscate(id, key), key), id & MAX_ID)`.
`id & MAX_ID` is computed with the crate constant `permute::MAX_ID`. -/
def out_of_domain_input_is_reduced_not_rejected_spec (key id : Std.U64) : Prop :=
  (do
    let max_id ← permute.MAX_ID
    let lhs ← permute.obfuscate id key
    let rhs ← permute.obfuscate (id &&& max_id) key
    let code ← permute.obfuscate id key
    let back ← permute.deobfuscate code key
    ok (lhs, rhs, back, id &&& max_id)) ⦃ (lhs, rhs, back, masked) =>
      lhs = rhs ∧ back = masked ⦄

end Benchmark.Cases.Arxid.Permute
