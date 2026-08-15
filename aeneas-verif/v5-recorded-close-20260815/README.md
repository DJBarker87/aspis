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
- translates a small, source-shaped version of the successful mutation whose
  inputs are plain booleans, bytes, and u64 balances; proves from the generated
  Lean that checked addition is exact below `2^64`, the prefix becomes `ASPC`,
  the suffix is unchanged, the proof balance becomes zero, and the refund
  balance becomes the exact sum; and
- compiles the Lean model and checks its reported axioms.

## Exact remaining boundary

The pinned Aeneas version cannot translate this function all the way to Lean.
Solana's `AccountInfo` stores mutable balances and data through
`Rc<RefCell<&mut _>>`; Aeneas stops at the `lamports()` projection in
`solana-account-info` 2.3.0. The replay requires that exact named failure so it
cannot be mistaken for a successful Rust-to-Lean proof.

The successful arithmetic and byte mutation no longer depend only on a
handwritten Lean function: the separate projection harness is translated by
Charon/Aeneas, and `generated_successful_path_is_exact` proves its result. The
harness is deliberately identified as a projection; it is not substituted for
the immutable production source.

The remaining source-level statement is now the wrapper connection: the
successful `AccountInfo` reads and mutable borrows in the exact recorded body
must supply the same values and targets as that proved projection. The broader
predicate `ExactRecordedRustRawCloseEquality` records the resulting universal
equality with `runRecordedClose`. The meanings of the individual
`AccountInfo` operations are listed in `RecordedAccountInfoSemantics`. Solana
rollback, atomic commit, zero-balance account removal, and finalized
observation are listed separately in `RecordedCloseRuntimeSemantics`.

In short: the exact close/refund result is proved both in the maintained Lean
model and for an Aeneas-generated source-shaped mutation. Both are pinned to
the exact source and its passing production test. The last wrapper connection
through Solana's `AccountInfo` representation is still explicit, not claimed
as finished.

## Replay

```bash
ASPIS_CHARON_REPO=/path/to/charon \
ASPIS_AENEAS_REPO=/path/to/aeneas \
LEAN432_AENEAS_ROOT=/path/to/aeneas-lean-4.32 \
  ./aeneas-verif/v5-recorded-close-20260815/replay-lean432.sh
```
