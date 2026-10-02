import SuccinctBroadword.Extraction

/-!
# succinct (broadword) — specifications

Implementation: `extracted/SuccinctBroadword` (verbatim `cargo hax extract
succinct-broadword` output for tov/succinct-rs@b394d4d1, rooted at the free
functions `broadword::{count_ones, u_nz8, u_le8}`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

The byte-wise tests read byte `i` of a word with the crate helper
`BlockType::get_bits(8 * i, 8)` (`(w >> 8i) & low_mask(8)`), for `i < 8`. That
helper is test-side (it is not the code under test) and never panics for these
arguments (`8i + 8 ≤ 64`); its value is the natural number `w / 2^(8i) % 256`,
written `byteAt w i` below.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Succinct.Broadword

open succinct

/-- Byte `i` (little-endian, `i < 8`) of a 64-bit word, i.e. the value of the
test helper `w.get_bits(8 * i, 8)`. -/
def byteAt (w : Std.U64) (i : Nat) : Nat := w.val / 2 ^ (8 * i) % 256

/-- PBT `broadword::test::count_ones_qc` (src/broadword.rs:151-154), property
`count_ones_prop` (src/broadword.rs:143-145):
`count_ones(word) == word.count_ones() as usize`.
The reference side `u64::count_ones` is executed with its hax CoreModels model
`core.num.U64.count_ones`; the `as usize` cast of the `u32` result preserves the
value, so the returned words are compared through `.val`. -/
def count_ones_matches_std_spec (word : Std.U64) : Prop :=
  (do
    let fast ← broadword.count_ones word
    let reference ← core.num.U64.count_ones word
    ok (fast, reference)) ⦃ r => r.1.val = r.2.val ⦄

/-- PBT `broadword::test::u_nz8_qc` (src/broadword.rs:233-236), property
`u_nz8_prop` (src/broadword.rs:219-231):
```
let n = hash(&(n0, n1, n2, n3));
let r = u_nz8(n);
for i in 0..8 {
    let ni = n.get_bits(8 * i, 8);
    let ri = r.get_bits(8 * i, 8);
    if (ni != 0) != (ri == 0x80) { return false; }
}
true
```
The generated tuple is only hashed to obtain a well-spread word `n`; the
property is stated for every word `n` (see translation notes). -/
def u_nz8_bytewise_spec (n : Std.U64) : Prop :=
  broadword.u_nz8 n ⦃ r => ∀ i, i < 8 → (byteAt n i ≠ 0 ↔ byteAt r i = 0x80) ⦄

/-- PBT `broadword::test::u_le8_qc` (src/broadword.rs:320-323), property
`u_le8_prop` (src/broadword.rs:306-318):
```
let r = u_le8(n, m);
for i in 0..8 {
    let ni = n.get_bits(8 * i, 8);
    let mi = m.get_bits(8 * i, 8);
    let ri = r.get_bits(8 * i, 8);
    if (ni <= mi) != (ri == 0x80) { return false; }
}
true
``` -/
def u_le8_bytewise_spec (n m : Std.U64) : Prop :=
  broadword.u_le8 n m ⦃ r => ∀ i, i < 8 → (byteAt n i ≤ byteAt m i ↔ byteAt r i = 0x80) ⦄

end Benchmark.Cases.Succinct.Broadword
