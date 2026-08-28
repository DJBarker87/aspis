# Extraction normalizations

Production Rust has one extraction-friendly change:

- `PairForestVerifierRuntimeV1::invoke` takes `&[AccountInfo; 5]` rather than an
  unsized slice; `SolanaPairForestVerifierRuntimeV1` immediately calls
  `account_infos.as_slice()`.  The caller already constructs exactly five
  accounts, so observable behavior is unchanged.

Generated Lean has two checked normalizations:

- The overloaded `read_discriminant` call is pinned to the source Pool error
  enum's `u32` discriminant, avoiding accidental selection of ProgramError's
  `isize` instance.
- `POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES` is normalized from the literal
  source arithmetic `8 + 3 * 32 + 688` to `792#usize`.

Generated module import prefixes were mechanically renamed to stable bundle
names (`ASQ8Dispatch` and `ASQ8NextLane`).
