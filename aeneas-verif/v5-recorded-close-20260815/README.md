# Recorded mainnet proof close and refund

This bundle checks the source used to build the mainnet program, not a later
version of the repository.

The recorded source is commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`, tree
`9b6bdfddb3c213addc2bb705c8130cce4fb2c351`. Its close instruction does the
following on a successful run:

1. It reads the proof account first and the refund account second.
2. It checks that the proof was fully uploaded and finalized.
3. It checks ownership, both signatures, write access, distinct addresses, a
   nonzero proof balance, and overflow of the refund addition.
4. It overwrites the first four proof bytes with `ASPC`.
5. It credits the proof account's entire live balance to the second account.
6. It sets the proof account balance to zero.

The refund address is therefore supplied by the transaction. It is not a
wallet address embedded in the program. The balance is read when the close
runs, so an extra inbound lamport is included in the refund rather than being
left behind or changing the recipient.

`AspisFormal.V5RecordedCloseBytes` proves these facts for the executable Lean
model. It also proves that the proof-data suffix and length are unchanged and
that the earlier pool and spent-marker state are unchanged by the close.

## Mainnet source versus current source

The mainnet source checked that the spent-marker address was the address
derived by Solana, but it did not separately reject a derived numeric bump
below 255. The observed mainnet address had bump 255. The current source adds
an explicit numeric-bump check. The Lean files keep these two claims separate;
they do not say the deployed program contained the later check.

## What the replay establishes

The replay:

- verifies the recorded commit, tree, and exact Rust source blobs;
- verifies the separate current-source blob containing the numeric-bump check;
- runs the recorded Rust test that checks the exact refund and `ASPC` write;
- uses the pinned Charon build to extract the exact recorded refund function;
- checks that the target body is present and that only the three Solana
  `AccountInfo` access methods are opaque in the extraction; and
- compiles the Lean model and checks its reported axioms.

## Exact remaining boundary

The pinned Aeneas version cannot translate this function all the way to Lean.
Solana's `AccountInfo` stores mutable balances and data through
`Rc<RefCell<&mut _>>`; Aeneas stops at the `lamports()` projection in
`solana-account-info` 2.3.0. The replay requires that exact named failure so it
cannot be mistaken for a successful Rust-to-Lean proof.

The remaining source-level statement is
`ExactRecordedRustRawCloseEquality`: for every input, the extracted Rust path
has the same result as `runRecordedClose`. The external meanings of
`AccountInfo` reads and mutable borrows are listed separately in
`RecordedAccountInfoSemantics`. Solana rollback, atomic commit, zero-balance
account removal, and finalized observation are listed separately in
`RecordedCloseRuntimeSemantics`.

In short: the exact close/refund result is proved in the Lean model, and the
model is pinned tightly to the exact source and its passing production test.
The final universal Rust-to-model equality is still explicit, not claimed as
finished.

## Replay

```bash
ASPIS_CHARON_REPO=/path/to/charon \
ASPIS_AENEAS_REPO=/path/to/aeneas \
  ./aeneas-verif/v5-recorded-close-20260815/replay-lean432.sh
```
