# V7 one-transaction Pool caller Rust-to-Lean bridge

This focused bundle pins the selected eight-lane Pool terminal caller at the
activated one-transaction base
`d0bfca5c6e7218caa25c261584bc0ca65ed80021`. It adds no production semantic
change. Charon/Aeneas translates a fixed-width operational projection of the
successful and failing caller control flow; `source-audit.sh` separately pins
the literal activated production files, six-account CPI construction and
persistence order byte-for-byte. The refreshed pin includes the final
stack-safe helper factoring and selected Tag-73 basis/sparsity dispatcher.

The projected caller follows the production order:

1. decode and authenticate ASQ8, Pool state and immutable registry release;
2. construct the exact read-only six-account verifier CPI image;
3. consume verifier success and exact 792-byte ASR8 identity/source binding;
4. choose same-page or rollover history write;
5. acquire all mutable Pool borrows;
6. for withdrawal, authenticate the exact five token accounts, invoke the SPL
   transfer and verify both balance deltas;
7. write the next lane, history root, nullifier marker and returned result;
8. expose Solana all-or-nothing instruction commit as a named runtime wrapper.

The Rust tests instantiate all four selected paths: transfer/withdrawal times
same-page/rollover. They also exercise rejection after verifier CPI, failed
borrows, failed/incorrect withdrawal CPI, spent marker, stale lane, wrong
release and malformed ASR8.

## Strongest results

`translated_accepted_atomic_transaction_has_exact_writeback` starts from an
actual successful execution of the translated atomic wrapper. It constructs
the translated caller run and proves `ExactAcceptedWriteback`, including:

- exact ASQ8, Pool, proof/master/checkpoint/lane, registry/entry and selected
  verifier bindings;
- six pairwise-distinct read-only CPI account metas in the order proof,
  master, checkpoint, lane, registry, entry;
- exact verifier-program return identity, 792-byte result length and decoded
  ASR8 transition/master/lane/nullifier/source-root/source-frontier/index;
- selected-lane `index + 1`, root and frontier writeback while preserving the
  activated Pool-owned lane invariant capability;
- exact same-page or rollover history image;
- exact program-owned nullifier-marker contents;
- unchanged transfer custody or checked withdrawal vault/destination deltas;
- preservation of unrelated state.

`translated_rejected_atomic_transaction_is_exact_prestate` proves that every
translated rejected transaction has the exact pre-state, no acceptance
certificate and a concrete error. The equality is the source model of Solana
rollback; the runtime guarantee itself remains an explicit boundary below.

The intermediate results isolate authentication, ASR8, marker, preparation,
history/lane finalization, withdrawal and final writeback:

- `translated_authentication_success_is_exact`
- `translated_result_success_is_exact`
- `translated_marker_success_is_exact`
- `translated_prepare_success_is_exact`
- `translated_finalize_success_is_exact`
- `translated_withdrawal_apply_success_is_exact`
- `translated_apply_prepared_success_is_exact`
- `translated_accepted_caller_has_exact_writeback`

Every printed theorem depends on a subset of `propext`, `Classical.choice` and
`Quot.sound`. Compiled source contains no `sorry`, `admit`, `sorryAx`,
`native_decide`, project axiom or conclusion-shaped restore function. The
generated external template contains one uncompiled standard-library
`Option<T>` equality axiom; `FunsExternal.lean` replaces it with a transparent
definition.

## Composition with the Pool mathematics

This source bridge supplies the byte/account/control-flow side required by the
existing mathematical composition:

- `authenticated_result_gives_identical_semantic_reconstruction`
- `compact_transfer_has_exact_atomic_custody_postcondition`
- `compact_withdrawal_has_exact_atomic_custody_postcondition`
- `authorized_compact_transfer_closes_registry_transport_and_custody`
- `authorized_compact_withdrawal_closes_registry_transport_and_custody`
- `accepted_pool_spend_has_exact_one_transaction_postcondition`

The source-to-math seam is explicit. `ExactReleaseAuthentication` supplies the
authorized release/account facts; `ExactResultBinding` supplies
`ResultAuthenticates`; `ExactFinalizedCore`, `ExactHistoryState`,
`ExactMarkerBinding` and `ExactWithdrawalState` realize the mathematical
one-transaction post-state. Cryptographic acceptance of the selected verifier
supplies the already-proved `CompactTransferAccepted` or
`CompactWithdrawalAccepted` semantic relation; it is not re-assumed as a
source conclusion.

The fast lane decoder additionally consumes the fresh-PDA program invariant
proved by the earlier source bridge at `3c390c38`; this bundle proves successful
authentication requires that capability and every terminal write preserves
it. Ownership alone is not treated as the invariant.

## Fresh marker lifecycle refinement at `da77d5f5`

The original generated caller model begins its writeback seam with a
program-owned zero marker. Production now constructs that state atomically
from one of four exact entry shapes immediately before verifier CPI. The
focused successor bundle
`../v7-pool-nullifier-marker-source-20260830/` discharges that seam without
changing this historical generated model. It proves the payer/System Program
authentication, canonical Rent schedule, create versus dusted
transfer/allocate/assign paths, post-CPI replan, exact verifier/core/consume
order, failure rollback and replay rejection. Its four path statements remain
separate rather than treating marker preparation as an unchecked abstraction.

`source-audit.sh` is refreshed to the `da77d5f5` production hashes and ordering.
The hashes and replay result originally recorded in this directory remain the
historical `2026-08-28` evidence for its generated caller; current marker
lifecycle evidence lives in the successor bundle.

## Explicit trust and refinement boundaries

- SHA-256 and Poseidon primitive behavior and the selected Tag-73 verifier's
  cryptographic acceptance theorem;
- Charon, Aeneas, Lean's kernel, Rust compiler lowering and the audited
  fixed-width projection correspondence to the hash-pinned production caller;
- Solana account ownership/PDA derivation, CPI execution, borrow semantics,
  return-data program identity and instruction-level atomic rollback;
- SPL Token program behavior for the five-account withdrawal CPI;
- immutable production deployment IDs. The selected invariant release IDs are
  still audit-build constants until release generation freezes them.

These are runtime/tool/primitive boundaries, not hidden theorem premises.

## Replay

```sh
./source-audit.sh
./replay-rust.sh
CHARON_BIN=/path/to/charon AENEAS_BIN=/path/to/aeneas ./replay-extraction.sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
  LEAN_BIN=/path/to/lean-4.31.0 ./replay-lean.sh
```

The replay uses one Cargo job and one Lean thread. The final NUC invocation is
recorded in `REPLAY-RESULT.txt`.
