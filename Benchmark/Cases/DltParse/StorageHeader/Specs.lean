import DltParseStorageHeader.Extraction

/-!
# dlt-parse-rs — specifications

Implementation: `extracted/DltParseStorageHeader` (verbatim `cargo hax extract
dlt-parse-storage-header` output for JulianSchmid/dlt-parse-rs@e84c7ee, module
`src/storage/storage_header.rs` with the `io`-generic `read`/`write`, the
string-returning `ecu_id_str` and the derived `Debug` impl excluded — none of
them is a callee of the properties below).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

Byte arrays: Aeneas models `[u8; N]` as `Std.Array Std.U8 N` (a subtype of
`List Std.U8`), so the specifications compare the returned array against the
expected `List Std.U8` built from `Std.core.num.U32.to_le_bytes` (Aeneas' pure
little-endian encoding; `CoreModels`' monadic `core.num.U32.to_le_bytes` is
proven equal to it by `to_le_bytes_eq` below, following the Byteorder case).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.DltParse.StorageHeader

open dlt_parse

/-- PBT `storage::storage_header::storage_header_tests::from_bytes`
(src/storage/storage_header.rs:132), with the two assertions of the property
test run in sequence on a pair:

* ok case: `Ok(header.clone()) == StorageHeader::from_bytes(header.to_bytes())`
  (`clone` on `StorageHeader` is the identity, so this is
  `from_bytes(to_bytes header) = Ok header`);
* error case: with the first four bytes overwritten by `bad_pattern`
  (filtered by the strategy to differ from `PATTERN_AT_START`),
  `from_bytes` fails with `StorageHeaderStartPatternError` carrying exactly
  `bad_pattern` as the actual pattern. -/
def storage_header_from_bytes_spec (header : storage.storage_header.StorageHeader)
    (bad_pattern : Array Std.U8 4#usize) : Prop :=
  (do
    let bytes ← storage.storage_header.StorageHeader.to_bytes header
    let ok_case ← storage.storage_header.StorageHeader.from_bytes bytes
    let mutated ← ok
      ((((bytes.set 0#usize bad_pattern[0]!).set 1#usize bad_pattern[1]!)
        |>.set 2#usize bad_pattern[2]!).set 3#usize bad_pattern[3]!)
    let bad_case ← storage.storage_header.StorageHeader.from_bytes mutated
    ok (ok_case, bad_case)) ⦃ r =>
    r.1 = core.result.Result.Ok header ∧
    r.2 = core.result.Result.Err
      { actual_pattern := bad_pattern :
        error.storage_header_start_pattern_error.StorageHeaderStartPatternError } ⦄

end Benchmark.Cases.DltParse.StorageHeader