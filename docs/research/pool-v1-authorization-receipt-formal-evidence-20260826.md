# Pool V1 authorization-receipt formal evidence — 2026-08-26

This record freezes the focused Lean check for the exact Pool V1 authorization
receipt model introduced by commit `3278a48f`. It is a model/composition gate,
not an implementation-source or Solana-runtime claim.

## Exact target

- Source: `AspisFormal/AspisFormal/Pool/AuthorizationReceiptV1.lean`
- Source SHA-256:
  `59e82b9b173c29632df22b8530024fbfe47157b2217b80198d0d2ac6d75d6c49`
- Output `.olean` SHA-256:
  `07b074a73e736e3b5382ff72e707a4928a3ed6a8322967ef7d1f9c1cc178028b`
- Complete command-log SHA-256:
  `fb2f9e737e807ecea276fd6f89a231d639312ee9939ec4cca2132b36715b6efe`

The target was checked in an isolated NUC copy with the exact imported source
files and Mathlib revision `81a5d257...`. The measured command was:

```sh
/usr/bin/time -v env LEAN_NUM_THREADS=1 \
  <lean-toolchain>/bin/lake env lean \
  -o <build-root>/output/AuthorizationReceiptV1.olean \
  AspisFormal/Pool/AuthorizationReceiptV1.lean
```

It ran inside a user scope with `MemoryMax=8G`, `MemorySwapMax=0`, and
`TasksMax=64`.

## Result

- Exit status: `0`
- Elapsed time: `4.85 s`
- Maximum resident set: `6,520,916 KiB`
- Swap: `0`
- Invocation identifier: `ce838075e8704852b08ff8b2c2064bd7`

Exact `#print axioms` results:

- `accepted_receipt_reconstructs_exact_direct_verification`: none
- `accepted_receipt_binds_exact_active_release`: none
- `receipt_and_direct_transfer_gates_are_state_identical`: `propext`
- `receipt_and_direct_withdrawal_gates_are_state_identical`: `propext`
- `replayed_transfer_receipt_cannot_repeat_settlement`: `propext`
- `replayed_withdrawal_receipt_cannot_repeat_settlement`: `propext`

There is no `sorryAx`. The explicit `IssuerSound` premise remains the exact
production-verifier/source obligation: the verifier-owned receipt PDA must be
issued only after acceptance of the byte-identical binding recorded in it.

## Boundary

The checked model proves that an authentic exact receipt reconstructs the same
direct-verification fact, binds the exact active registry release, preserves
the transfer/withdrawal state transformer, and cannot repeat settlement after
nullifier consumption. It does not yet prove the verifier instruction that
creates the receipt, the Pool instruction that authenticates it, or Solana
transaction rollback; those remain separate source/runtime gates.
