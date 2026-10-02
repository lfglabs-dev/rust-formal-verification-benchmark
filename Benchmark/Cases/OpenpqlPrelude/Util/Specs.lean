import OpenpqlPreludeUtil.Extraction

/-!
# openpql-prelude — specifications (combinatorial index arithmetic)

Implementation: `extracted/OpenpqlPreludeUtil` (verbatim `cargo hax extract
openpql-prelude-util` output for solve-poker/Poker-Query-Language@157235d6,
crate `openpql-prelude`): `iterator::binomial::coefficient::binom`,
`waugh_indexer::util::{suffix_product, dot_product, const_sort}` and
`waugh_indexer::mixed_radix::MixedRadix::{new, encode, decode}`.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (`+ - * /` panic on
overflow / division by zero, `debug_assert!` is checked), which is the
configuration `cargo test` runs the original quickcheck properties under.
Every quickcheck property here fails on a panic, so panics falsify the specs.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.OpenpqlPrelude.Util

open openpql_prelude

/-- quickcheck `iterator::binomial::coefficient::tests::test_pascals_identity`
(openpql-prelude/src/iterator/binomial/coefficient.rs:26-37):

```rust
let lhs = binom(n, r);
let rhs1 = binom(n - 1, r - 1);
let rhs2 = binom(n - 1, r);
TestResult::from_bool(lhs == rhs1 + rhs2)
```

The test body runs in the extracted semantics: the `usize` subtractions
`n - 1`, `r - 1` and the addition `rhs1 + rhs2` are the checked Rust
operations; the `bool` result must be `true`. -/
def binom_pascals_identity_spec (n r : Std.Usize) : Prop :=
  (do
    let lhs ← iterator.binomial.coefficient.binom n r
    let n1 ← n - 1#usize
    let r1 ← r - 1#usize
    let rhs1 ← iterator.binomial.coefficient.binom n1 r1
    let rhs2 ← iterator.binomial.coefficient.binom n1 r
    let rhs ← rhs1 + rhs2
    ok (lhs, rhs)) ⦃ p => p.1 = p.2 ⦄

/-- The test's reference value for `suffix_product`:
`xs.iter().enumerate().map(|(i, _)| xs[i + 1..].iter().product::<u64>())`,
i.e. entry `i` is the product of the entries strictly after position `i`
(the empty product is `1`). -/
def suffixProducts (xs : List Nat) : List Nat :=
  (List.range xs.length).map (fun i => (xs.drop (i + 1)).prod)

/-- quickcheck `waugh_indexer::util::tests::test_suffix_product`
(openpql-prelude/src/waugh_indexer/util.rs:225-251):

```rust
let mut xs = build_xs(&numbers);
let product = xs.iter().enumerate()
    .map(|(i, _)| xs[i + 1..].iter().product::<WaughIndex>())
    .collect::<Vec<_>>();
suffix_product(&mut xs);
assert_eq!(product, xs);
```

`suffix_product(&mut xs)` on the vector's slice returns the updated slice; its
values must equal the reference list. The reference side is computed by the
test with checked `u64` products of suffixes of `xs`; under the theorem's
hypotheses (product of all entries `< 2^64`) none of them overflows, so it is
stated with `Nat` products (`suffixProducts`). -/
def suffix_product_spec (xs : Slice Std.U64) : Prop :=
  waugh_indexer.util.suffix_product xs ⦃ ys =>
    ys.val.map (·.val) = suffixProducts (xs.val.map (·.val)) ⦄

/-- quickcheck `waugh_indexer::util::tests::test_const_sort`
(openpql-prelude/src/waugh_indexer/util.rs:253-261):

```rust
let mut expected = [0; 10];
expected.copy_from_slice(&numbers);
expected.sort_unstable();
const_sort(&mut numbers);
assert_eq!(expected, numbers);
```

`expected` is `numbers` sorted by the standard library's `sort_unstable`,
i.e. the unique non-decreasing permutation of `numbers`; it is stated with
Lean's `List.mergeSort` (non-decreasing order on the `u64` values), which
computes the same list. -/
def const_sort_spec (numbers : Std.Array Std.U64 10#usize) : Prop :=
  waugh_indexer.util.const_sort numbers ⦃ sorted =>
    sorted.val.map (·.val) = (numbers.val.map (·.val)).mergeSort ⦄

/-- quickcheck `waugh_indexer::mixed_radix::tests::test_roundtrip`
(openpql-prelude/src/waugh_indexer/mixed_radix.rs:52-60):

```rust
fn test_roundtrip(block_sizes: [RoundIndex; 4], digits: [RoundIndex; 4]) {
    let block_sizes = block_sizes.map(|b| WaughIndex::from(b) + 1);
    let digits = array::from_fn(|i| WaughIndex::from(digits[i]) % block_sizes[i]);
    let radix = MixedRadix::new(block_sizes);
    assert_eq!(radix.decode(radix.encode(digits)), digits);
}
```

The spec takes the two `[u64; 4]` arrays after the test's input
preprocessing (`block_sizes`, `digits`); the theorem's hypotheses describe
exactly the set of arrays that preprocessing produces
(`1 ≤ block_sizes[i] ≤ 65536`, `digits[i] < block_sizes[i]`).

`MixedRadix::new(block_sizes)` computes the product of all four block sizes
(`suffix_product` also multiplies the first entry into its accumulator); for
`block_sizes = [65536; 4]` (test inputs `[u16::MAX; 4]`) it is `2^64` and the test
panics ("attempt to multiply with overflow": an upstream bug, essentially never
sampled by quickcheck). The spec states the test's actual outcome on its whole
domain: the computation panics exactly on `[65536; 4]` and otherwise returns the
original digits. -/
def mixed_radix_roundtrip_spec (block_sizes digits : Std.Array Std.U64 4#usize) : Prop :=
  let run : RustM (Std.Array Std.U64 4#usize) := do
    let radix ← waugh_indexer.mixed_radix.MixedRadix.new block_sizes
    let idx ← waugh_indexer.mixed_radix.MixedRadix.encode radix digits
    waugh_indexer.mixed_radix.MixedRadix.decode radix idx
  ((∀ b ∈ block_sizes.val, b.val = 65536) → run = fail .panic) ∧
  ((¬ ∀ b ∈ block_sizes.val, b.val = 65536) → run ⦃ decoded => decoded = digits ⦄)

end Benchmark.Cases.OpenpqlPrelude.Util
