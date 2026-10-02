import CryptoBigintUint.Extraction

/-!
# crypto-bigint — fixed-width `Uint<LIMBS>` arithmetic — specifications

Implementation: `extracted/CryptoBigintUint` (verbatim `cargo hax extract
crypto-bigint-uint` output for RustCrypto/crypto-bigint@67aecbd4, 64-bit
target): the inherent methods `Uint::{wrapping_add, carrying_add,
wrapping_sub, borrowing_sub, sub_mod, bitand, bitand_limb, wrapping_and,
bitor, wrapping_or, bitxor, wrapping_xor, from_le_slice}` and the limb-level
primitives they call (`Limb::{carrying_add, borrowing_sub, bitand, bitor,
bitxor}`, `primitives::{carrying_add, borrowing_sub}`).

The property tests are in `tests/uint.rs` ("Equivalence tests between
`crypto_bigint::Uint` and `num_bigint::BigUint`"). They use `U256 = Uint<4>`
(four 64-bit limbs, least significant first) and compare against
`num_bigint::BigUint` through two test helpers:

* `to_biguint(&a)` (`tests/common/mod.rs`) concatenates `limb.to_le_bytes()`
  of all limbs and reads them with `BigUint::from_bytes_le`: its value is
  `uintVal a = Σ a.limbs[i] · 2^(64·i)` (`uintVal` below);
* `to_uint(n)` (`tests/uint.rs:24-31`) copies the low 32 bytes of
  `n.to_bytes_le()` into a zeroed `[u8; 32]` and decodes it with the crate's
  `U256::from_le_slice`: its value is `n % 2^256`. It cannot panic (the buffer
  always has the expected 32 bytes), so where it only builds the expected
  value of a comparison the specs state that value as the Nat
  `n % 2^256` (the `roundtrip` task is exactly the statement that
  `from_le_slice` of these bytes returns the `Uint` with this value).

`prop_assert_eq!(x, y)` on `U256` uses the crate's constant-time `PartialEq`,
which is equality of the limb arrays; since `uintVal` is injective on
`Uint<4>` this is stated as equality of values (`uintVal r = …`) or, where both
sides are `Uint`s, as Lean `=`. The comparisons `a < P`, `b > a` use the
crate's `Ord`, i.e. the numeric order of the values.

Generated inputs: `uint()` is `U256::from_le_slice(&bytes)` for
`bytes in any::<[u8; 32]>()`, which ranges over every `U256` (decoding 32
bytes is a bijection onto `Uint<4>`, see the `roundtrip` task), so a `uint()`
input is an arbitrary `a : uint.Uint 4#usize`. `uint_mod_p(P)` is
`a.wrapping_rem_vartime(&P)` for `a in uint()`, i.e. every value `< P`.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.CryptoBigint.Uint

open crypto_bigint

/-- Little-endian value of a list of 64-bit limbs: `Σ l[i] · 2^(64·i)`. -/
def limbsVal : List Std.U64 → Nat
  | [] => 0
  | x :: xs => x.val + 2^64 * limbsVal xs

/-- The mathematical value of a `Uint<LIMBS>` (limbs stored least significant
first), i.e. the value of the test helper `to_biguint(&a)`. -/
def uintVal {LIMBS : Std.Usize} (a : uint.Uint LIMBS) : Nat := limbsVal a.limbs.val

/-- `P` (tests/uint.rs:20-22): the NIST P-256 curve order
`0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551`, built in
the test by the `const fn` `Odd::<U256>::from_be_hex(..)`; here its four
little-endian limbs. `P.as_nz_ref()` reinterprets it as `&NonZero<U256>`, whose
extraction `non_zero.NonZero T` is `T` itself. -/
def P : uint.Uint 4#usize :=
  { limbs := Array.make 4#usize
      [0xf3b9cac2fc632551#u64, 0xbce6faada7179e84#u64,
       0xffffffffffffffff#u64, 0xffffffff00000000#u64] }

/-- Byte `i` of the little-endian encoding of `v`. -/
def leByte (v i : Nat) : Std.U8 := ⟨BitVec.ofNat 8 (v / 2^(8*i))⟩

/-- The buffer `to_uint(n)` builds: `input = [0u8; 32]` overwritten with the
first `min(len, 32)` bytes of `n.to_bytes_le()`, i.e. the 32 low
little-endian bytes of `n` (zero padded). -/
def leBytes32 (v : Nat) : Array Std.U8 32#usize :=
  ⟨List.ofFn (n := 32) (fun i => leByte v i.val), by simp⟩

/-- PBT `roundtrip` (tests/uint.rs:88-91):
```
fn roundtrip(a in uint()) {
    prop_assert_eq!(a, to_uint(to_biguint(&a)));
}
```
`to_biguint(&a)` has value `uintVal a`; `to_uint` builds the 32-byte
little-endian buffer `leBytes32 (uintVal a)` and decodes it with the crate's
`U256::from_le_slice(&input)` (the `&[u8; 32]` → `&[u8]` coercion is
`Array.to_slice`). The assertion compares the decoded `U256` with `a`. -/
def le_bytes_roundtrip_spec (a : uint.Uint 4#usize) : Prop :=
  (uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice (leBytes32 (uintVal a))))
    ⦃ r => r = a ⦄

/-- PBT `wrapping_add` (tests/uint.rs:143-152):
```
fn wrapping_add(a in uint(), b in uint()) {
    let expected = to_uint(a_bi + b_bi);
    let actual = a.wrapping_add(&b);
    prop_assert_eq!(expected, actual);
}
```
`expected` has value `(uintVal a + uintVal b) % 2^256`. -/
def wrapping_add_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.add.Uint.wrapping_add a b) ⦃ r => uintVal r = (uintVal a + uintVal b) % 2^256 ⦄

/-- PBT `wrapping_sub` (tests/uint.rs:214-227):
```
fn wrapping_sub(mut a in uint(), mut b in uint()) {
    if b > a { mem::swap(&mut a, &mut b); }
    let expected = to_uint(a_bi - b_bi);
    let actual = a.wrapping_sub(&b);
    prop_assert_eq!(expected, actual);
}
```
After the swap `a` holds the larger and `b` the smaller input (`hi`/`lo`
below), so the `BigUint` subtraction `a_bi - b_bi` does not underflow and
`expected` has value `(uintVal hi - uintVal lo) % 2^256`. -/
def wrapping_sub_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  let hi := if uintVal b > uintVal a then b else a -- `a` after the swap
  let lo := if uintVal b > uintVal a then a else b -- `b` after the swap
  (uint.sub.Uint.wrapping_sub hi lo) ⦃ r => uintVal r = (uintVal hi - uintVal lo) % 2^256 ⦄

/-- PBT `sub_mod_nist_p256` (tests/uint.rs:172-192):
```
fn sub_mod_nist_p256(mut a in uint_mod_p(P), mut b in uint_mod_p(P)) {
    if b > a { mem::swap(&mut a, &mut b); }
    prop_assert!(a < P);
    prop_assert!(b < P);
    let expected = to_uint((a_bi - b_bi) % p_bi);
    let actual = a.sub_mod(&b, P.as_nz_ref());
    prop_assert!(expected < P);
    prop_assert!(actual < P);
    prop_assert_eq!(expected, actual);
}
```
`hi`/`lo` are `a`/`b` after the swap; `expected` has value
`((uintVal hi - uintVal lo) % uintVal P) % 2^256`. All five assertions are
kept, in order. -/
def sub_mod_nist_p256_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  let hi := if uintVal b > uintVal a then b else a -- `a` after the swap
  let lo := if uintVal b > uintVal a then a else b -- `b` after the swap
  let expected := ((uintVal hi - uintVal lo) % uintVal P) % 2^256
  (uint.sub_mod.Uint.sub_mod hi lo P) ⦃ r =>
    uintVal hi < uintVal P ∧ uintVal lo < uintVal P ∧
    expected < uintVal P ∧ uintVal r < uintVal P ∧ expected = uintVal r ⦄

/-- PBT `wrapping_or` (tests/uint.rs:475-483):
```
fn wrapping_or(a in uint(), b in uint()) {
    let expected = to_uint(a_bi | b_bi);
    let actual = a.wrapping_or(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `|` is `Nat.lor` (`|||`) on the values. -/
def wrapping_or_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_or.Uint.wrapping_or a b) ⦃ r => uintVal r = (uintVal a ||| uintVal b) % 2^256 ⦄

/-- PBT `wrapping_and` (tests/uint.rs:485-493):
```
fn wrapping_and(a in uint(), b in uint()) {
    let expected = to_uint(a_bi & b_bi);
    let actual = a.wrapping_and(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `&` is `Nat.land` (`&&&`) on the values. -/
def wrapping_and_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_and.Uint.wrapping_and a b) ⦃ r => uintVal r = (uintVal a &&& uintVal b) % 2^256 ⦄

/-- PBT `wrapping_xor` (tests/uint.rs:495-503):
```
fn wrapping_xor(a in uint(), b in uint()) {
    let expected = to_uint(a_bi ^ b_bi);
    let actual = a.wrapping_xor(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `^` is `Nat.xor` (`^^^`) on the values. -/
def wrapping_xor_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_xor.Uint.wrapping_xor a b) ⦃ r => uintVal r = (uintVal a ^^^ uintVal b) % 2^256 ⦄

end Benchmark.Cases.CryptoBigint.Uint
