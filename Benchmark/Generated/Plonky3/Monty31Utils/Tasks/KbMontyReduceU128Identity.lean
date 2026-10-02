import Benchmark.Cases.Plonky3.Monty31Utils.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31

namespace Benchmark.Cases.Plonky3.Monty31Utils

/--
`monty_reduce_u128(x) * 2^32 ≡ x (mod P)` for every `x = hi * 2^64 + lo` (`hi: u32`, `lo: u64`),
KoalaBear parameters, without panicking.
-/
theorem kb_monty_reduce_u128_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (lo : Std.U64) (hi : Std.U32) :
    kb_monty_reduce_u128_identity_spec inst lo hi := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Plonky3.Monty31Utils
