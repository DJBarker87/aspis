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

## Account-key uniqueness projection

- Literal production Charon unit: `aspis-pool-unique-accounts-01`
- Invocation: `f897a3a03cae4c01980cdb40f6d8caf8`
- Exit: 0
- Wall: 16.96 s
- Peak RSS: 504,552 KiB
- Swap: 0
- Literal LLBC SHA-256:
  `96b5bc2a99f842740a69da08423d5221ccd2af59a92cd082024e044ddcde7777`
- Aeneas blocker: shared indexing of lifetime-bearing `AccountInfo`
- Normalized-key Charon unit: `aspis-pool-normalized-unique-01`
- Invocation: `e5e5ee0f48854c408e52d7421f01e1a6`
- Exit: 0
- Wall: 13.31 s
- Peak RSS: 504,812 KiB
- Swap: 0
- Normalized LLBC SHA-256:
  `e48db99a0004f56099de62172c9eed45d02fdcca36688e6697d8855bad95eaef`
- Inner-loop equal-pair rejection theorem: exit 0, standard Lean trio only

The projection changes only the element type from `AccountInfo` to the exact
32-byte key field read by the production loop. Its loop bounds, checked
`left + 1`, equality gate and first-duplicate return are unchanged.
