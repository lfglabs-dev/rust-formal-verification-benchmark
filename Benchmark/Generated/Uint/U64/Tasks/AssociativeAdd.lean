import Benchmark.Cases.Uint.U64.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ethereum_types

namespace Benchmark.Cases.Uint.U64

/--
`(x + y) + z == x + (y + z)` holds whenever the test does not discard.
-/
theorem associative_add (x y z : uint.U64)
    (h_assume_xy : uint.U64.overflowing_add x y ⦃ r => r.2 = false ⦄)
    (h_assume_yz : uint.U64.overflowing_add y z ⦃ r => r.2 = false ⦄)
    (h_assume_xyz : (do
      let xy ← add x y
      uint.U64.overflowing_add xy z) ⦃ r => r.2 = false ⦄) :
    associative_add_spec x y z := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Uint.U64
