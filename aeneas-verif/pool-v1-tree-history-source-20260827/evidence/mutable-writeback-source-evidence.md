# Pool V1 mutable write-back source evidence

## Pure write-back suffix

- Rust target: `normalized_prepared_history_writeback` in `harness/src/lib.rs`
- Charon output: `extraction/PoolV1NormalizedPreparedWriteback.llbc`
- LLBC SHA-256: `cc3f38b1ae7d35e9cab94910f9fd64af9ec93eed7931f68110d03dde90961090`
- Aeneas output: fully transparent `PoolV1NormalizedPreparedWriteback.Funs`
- Lean capstones:
  - `normalized_writeback_success_exact`
  - `checked_history_images_have_exact_normalized_writeback`
- Focused Cargo check: exit 0
- Focused Lean builds: exit 0

The normalization starts only after all required mutable runtime borrows have
successfully returned fixed arrays.  It contains the exact assignment and
optional-rollover grammar; it contains no Pool predicate, root theorem or
account-runtime assumption.

## Literal state/result-image checker

- Production target:
  `prepared_settlement::source_state_and_result_image_match`
- Charon output: `extraction/PoolV1SourceStateResultImage.llbc`
- LLBC SHA-256: `0c9b56696bd96173f7f601ced1f61d47d0c28c892a7a5b30d4f95855b81d1f3b`
- Aeneas target: transparent
  `PoolV1SourceStateResultImage.prepared_settlement.source_state_and_result_image_match`
- Lean capstone:
  `literal_source_state_result_image_success_has_exact_checks`
- Focused local Lean build: exit 0, wall 9.18 s, peak RSS 2,402,861,056 bytes,
  zero swaps
- Axiom report: `[propext, Classical.choice, Quot.sound,
  aspis_statement.atomic_statement.encode_digest_canonical]`

The canonical encoder name is independently source-closed by
`PoolV1HistoryCodecRoundTripBridge.lean`. There is no `sorry`, `admit`,
`sorryAx`, `native_decide`, whole-validator callback or Pool semantic axiom.

## Focused NUC Charon extraction

- Successful unit: `aspis-pool-source-state-result-02`
- Invocation: `ee07858d52e242e5885512c32bdf957f`
- MemoryHigh: 8 GiB
- MemoryMax: 10 GiB
- MemorySwapMax: 0
- Wall: 16.85 s
- Peak RSS: 503,976 KiB
- Swap: 0
- Exit: 0

The preceding unit `aspis-pool-source-state-result-01` used the wrong toolchain
environment and was discarded. It exited nonzero after duplicate-symbol link
errors and produced no accepted artifact.
