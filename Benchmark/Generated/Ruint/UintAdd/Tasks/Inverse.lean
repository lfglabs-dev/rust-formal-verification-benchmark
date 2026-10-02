import Benchmark.Cases.Ruint.UintAdd.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ruint

namespace Benchmark.Cases.Ruint.UintAdd

/--
For every supported width `BITS` (with `LIMBS = nlimbs(BITS)`) and every
`a : Uint<BITS, LIMBS>` produced by the proptest strategy, wrapping negation is
an additive inverse and an involution: `a + (-a) == U::ZERO`,
`a - a == U::ZERO` and `-(-a) == a`.
-/
theorem inverse (BITS LIMBS : Std.Usize) (la : Std.Array Std.U64 LIMBS)
    (h_bits : BITS.val ∈ [0, 1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096])
    (h_limbs : nlimbs BITS = ok LIMBS) :
    inverse_spec BITS LIMBS la := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Ruint.UintAdd
