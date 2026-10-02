import Benchmark.Cases.Memchr.Twoway.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open memchr

namespace Benchmark.Cases.Memchr.Twoway

/--
For every non-empty byte string, the Crochemore-Perrin maximal-suffix
routine `Suffix::forward(bytes, SuffixKind::Maximal)` of the Two-Way
substring searcher terminates without panicking, and `&bytes[s.pos..]` is
the lexicographically greatest non-empty suffix of `bytes` (the value of the
naive sort-all-suffixes reference implementation).
-/
theorem suffix_forward_maximal (bytes : Slice Std.U8)
    (h_assume_nonempty : 0 < bytes.length) :
    suffix_forward_maximal_spec bytes := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Memchr.Twoway
