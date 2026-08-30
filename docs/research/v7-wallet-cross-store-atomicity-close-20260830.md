# V7 wallet cross-store atomicity close — 2026-08-30

## Revision and scope

- Repository: `/Users/dominic/ZK`
- Isolated worktree: `/Users/dominic/ZK/.worktrees/ZK-v7-wallet-security-close-20260830`
- Branch: `research/v7-wallet-security-close-20260830`
- Original V7 security frozen base: `45145fe3494de8d6599c00fd65fa4872b44cddfd`
- Atomicity milestone input commit: `a07dfcff41d40cee854f90ce36213ef9326ac658`
- Final audited implementation commit:
  `e2883d6b505f07595bac1e637f3e7eab3be20d1b`

This milestone is offline Rust wallet/indexer/relayer work. It did not deploy,
sign, submit a transaction, merge, delete a worktree, clean a shared cache, or
contact public devnet/mainnet.

The implementation audit covered `durable_state.rs`,
`lane_forest_durable_v2.rs`, `lane_forest_rpc_v2.rs`, the new
`lane_forest_wallet_txn_v2.rs`, and the existing note-store, scanner, witness,
checkpoint, relayer finality/journal, lane client, and wallet-transition
boundaries named by the parent V7 security milestone. Production changes were
confined to `crates/aspis-pool-wallet-v1/`.

## Audit result and chosen persistence shape

At the input commit, individual files were crash-safe but the wallet ecosystem
was not one transaction:

- `ASDW` atomically combined the V1 scan cursor, sealed notes, spent markers,
  and plan lifecycle.
- `ASWJ` independently persisted V1 witness history.
- `ASD8` independently persisted V2 lanes, forest events, witnesses,
  checkpoints, and its finalized head.
- `ASRQ`, `ASRJ`, and `ASJ8` independently persisted relayer admission,
  execution/finality, and checkpoint-operator state.

Each file had its own lock and same-directory replacement. In particular, the
V2 RPC adapter persisted `ASD8` and only then returned recovered note
associations to its caller. A crash in that gap could retain the lane append
without retaining the owned encrypted note. No shared generation, lock, or
commit record linked the stores.

A multi-file WAL would still leave independently readable component files at
mixed physical generations between renames. Preventing those reads requires a
global lock and routing all access through a manifest/WAL, making that manifest
the authoritative state anyway. The smaller design implemented here is
therefore one authoritative, locked V2 envelope. It contains logically distinct
note, spend/nullifier, lane/forest/witness, finalized-chain/checkpoint, and
relayer-observation sections, but no separately mutable active copies.

Legacy files are migration inputs only. The coordinator never mirrors or
partially rewrites them.

## State machine

The local V2 envelope has three explicit phases:

```text
Committed(S0)
    |
    | validate the complete candidate before disk mutation
    v
Prepared(pre=S0, post=S1, transaction/event binding)
    |
    v
StoresApplied(pre=S0, post=S1)
    |
    v
Committed(S1)
```

Every phase is a complete checksummed canonical image written through the
existing `AtomicStateFileV1` lock and atomic replacement. `StoresApplied` means
that all logical afterstates are staged together inside the authoritative
envelope; it does not mean separate legacy files were rewritten.

The transaction binding covers the prior generation/state digest, complete
canonical event content rather than only its output identity, chain point and
parent, finality transition, checkpoint state, note/cipher metadata,
spent/nullifier update, lane-state image, and relayer observation when one is
present. A monotonic generation prevents an in-process stale candidate from
committing under the lock.

## Commit and recovery algorithm

1. Hold the authoritative envelope's nonblocking OS lock.
2. Decode and validate the current committed image. A pending phase is
   recovered before any read or new mutation is exposed.
3. Build `S1` on an in-memory clone. Before `Prepared`, validate canonical event
   equality/order, finalized parent linkage, lane/forest transition, checkpoint
   support, XChaCha opening and event/access AAD, cipher ID, nonce history,
   note identity/commitment, spend authorization/nullifier uniqueness, and
   relayer binding.
4. Atomically replace the envelope with `Prepared(S0,S1)`.
5. Atomically replace it with `StoresApplied(S0,S1)`.
6. Atomically replace it with `Committed(S1)` and only then update the live
   in-memory view.

Recovery is monotone and requires no RPC or signer. Reopening first requires
the configured `NoteStoreCipherV1` so every retained note and pending candidate
can be authenticated; after that validated open, advancing the durable phases
requires no further key operation:

- `Committed(S)` is validated and exposed.
- Valid `Prepared(S0,S1)` rolls forward to `StoresApplied(S0,S1)` and then
  `Committed(S1)`.
- Valid `StoresApplied(S0,S1)` rolls forward to `Committed(S1)`.
- A corrupt, truncated, noncanonical, digest-inconsistent, or unknown phase
  fails closed and exposes neither candidate.

A crash before the `Prepared` target rename retains exactly `S0`. At or after a
durable `Prepared` rename, reopening validates a pending `S1` while blocking
normal readers; explicit deterministic recovery then produces and exposes
exactly `S1`. Repeating recovery is idempotent. Roll-forward also ensures a
nonce recorded in a durable prepared transaction cannot be forgotten and later
reused.

Any replacement error poisons the open coordinator. This matters because an
error after `rename` or during the parent-directory fsync may mean the disk
already advanced while the cached object did not. The only allowed next step
is drop, reopen, validate, and recover.

## Durable boundaries and fault injection

`AtomicStateFileV1` now exposes a crate-internal deterministic hook after each
real replacement primitive:

1. temporary-file `write_all`;
2. temporary-file `sync_all`;
3. same-directory target `rename`;
4. parent-directory `sync_all`.

The hook is threaded through `Prepared`, `StoresApplied`, `Committed`, and
recovery replacements. The matrix therefore exercises the four boundaries for
each applicable phase, including the ambiguous post-rename failure. An
unrenamed torn temporary image is ignored; a damaged authoritative image fails
closed.

`AtomicStateFileV1` continues to enforce a private regular target, private
regular sibling lock, a nonblocking OS file lock, a fixed same-directory
temporary path, a 64 MiB maximum image, and target/parent validation. Concurrent
scanners for the same envelope cannot both hold the lock.

## Established invariants

- Exact replay requires the same canonical event identity **and** content and
  is a byte-preserving no-op. Identity reuse with different content fails
  before any replacement.
- Processed/unfinalized and confirmed observations remain tentative. They do
  not create a note, advance forest/checkpoint state, or mark a spend.
  Finalization atomically promotes the exact bound observation.
- Reorg removes only tentative observations. A finalized event, note, or spend
  is terminal and cannot be rolled back.
- Retained event-bearing finalized points include parent linkage, so an event
  cursor cannot exist without retained event support. Cursor-only finalized
  blocks are not represented yet; this is an activation blocker recorded
  below, not a property claimed by this milestone.
- Lane sequences and checkpoint lane sequences must agree with retained
  canonical events; note and forest state share one generation.
- Every owned note record binds its cipher ID, XChaCha nonce, access class,
  canonical event identity, output identity, and commitment. Opening and
  recomputation occur before `Prepared`.
- A `(cipher ID, nonce)` pair is unique across retained nonce history, including
  spent notes. Wrong key ID, corrupt ciphertext, metadata substitution, and a
  nonce collision leave the committed image unchanged.
- A spend requires the existing `LocalSpendAuthenticatorV1` boundary; secret
  nullifier-key material never enters the durable envelope. Nullifiers are
  unique and a finalized spent marker is never cleared by replay or restart.
- Relayer observations preserve unfinalized, confirmed, and finalized states.
  An observation cannot manufacture finalized wallet state, and a finalized
  result must bind to the same canonical event/transaction evidence.

## Replay and finalized-RPC fixes found by the audit

The lower-level `LaneForestDurableStateV2` already compared an exact canonical
event on replay, but the finalized RPC adapter checked only that the output
event IDs existed. A replay carrying altered authenticated payload/content
could therefore be accepted when the public account snapshot was unchanged.
The adapter now reconstructs the retained canonical program event and compares
all fields before returning `Replayed`; a content mismatch returns
`ReplayMismatch` with no mutation.

The adapter also previously rewound retained finalized events to an older
checkpoint when a later batch named that checkpoint as its parent. Such a
rewind is incompatible with atomic note/spend state: it could lose a finalized
note or resurrect a finalized spend. That path now returns
`FinalizedRollback`. Tentative confirmation/reorg handling belongs only to the
authoritative coordinator.

## Activation and migration

The crate's `eight-lane-plumbing-v2` feature remains default-off. The new
coordinator has no default dispatch or automatic activation path.

Activation is mechanically available only when all supplied V1 wallet,
witness, and relayer inputs are empty and mutually anchored, the initial V2
forest has no finalized history/checkpoint, and the note cipher ID is nonzero.
The activation digest binds those inputs and the initial lane image. Nonempty
V1 activation is rejected.

That restriction is necessary: `ASDW` and `ASWJ` do not by themselves contain
an authenticated mapping from V1 outputs to V2 lane, pair index, pair slot, and
witness history. A complete nonempty migration needs an authenticated V2
rescan/mapping protocol. Downgrade/rollback after the first V2 finalized commit
is likewise unsafe and is not provided.

Consequently V2 cannot honestly be enabled in production by this milestone.
The V2 RPC module also still documents that no deployed Pool instruction emits
its frozen consumer ABI.

## Deterministic test and fault matrix

The executable reference model represents five logical stores (notes,
lane/forest, cursor/checkpoint, spend/nullifier, and relayer) with one logical
generation. It enumerates 34 modeled write/fsync/rename/remove boundaries and
128 fixed-seed crash/replay programs. This model is an independent oracle; it
does not share coordinator transition code.

The production coordinator tests additionally exercise the real
`AtomicStateFileV1` replacement path:

- 3 journal phase writes × 4 physical boundaries = 12 basic event fault cases;
- 3 journal phase writes × 4 physical boundaries = 12 rich private-transfer
  fault cases, each containing two sealed output notes, an authenticated input
  spend/nullifier, cross-lane forest/witness advancement, finalized cursor, and
  an authenticated checkpoint;
- before and after each of the 3 phase replacements = 6 logical interruption
  cases;
- 4 activation and 4 tentative-observation physical-boundary cases;
- 6 fixed seeds × 4 sequential same/cross-lane events = 24 production
  crash/reopen/recover/replay steps compared with `PureExpected` after every
  step.

The same suite covers clean application, exact and conflicting replay,
same-block ordering, cross-lane order, stale/unknown/valid checkpoints,
unfinalized → confirmed → reorg, confirmed → finalized, finalized rollback
rejection, repeated recovery, corrupt authoritative images and note records,
wrong cipher ID, event/AAD substitution, nonce collision, spend authorization,
spent-note restart behavior, and same-wallet lock contention.

A real `ASRJ` capability test separately establishes that unknown,
simulation-only, signed-only, terminal-failure, and finalized-failure records
cannot become a finalized wallet observation. A signed record may become
finalized with no durable submission receipt (the lost-response case); exact
finality replay is idempotent, conflicting finality is rejected, and the
capability survives journal restart. The pre-existing relayer replay test
exercises restart before submission/finality, conflicting RPC quorum, lost RPC
response, byte-for-byte retry, duplicate finalized status, and post-finality
restart/completion.

## Remaining honest boundaries

- Cursor-only/empty finalized blocks are not yet durable records in the V2
  envelope. A later event whose direct parent is such an empty block is
  therefore rejected rather than allowing an unsupported cursor. This must be
  implemented before production activation.
- RPC providers and the source of `FinalizedChainPointV1` remain external. The
  local type and journal do not prove ledger consensus or provider honesty.
- Deliberate rollback to an older but internally valid envelope requires an
  external monotonic anchor to detect. Checksums and parent digests detect
  corruption and internal discontinuity, not hostile whole-file rollback.
- Filesystem rename/fsync guarantees, private-directory integrity, disk health,
  backups, and platform power-loss qualification remain operational concerns.
- Note cipher keys, nullifier keys, signer keys, entropy/CSPRNG quality, and
  HSM/OS-keystore policy remain outside the file format.
- A deployed authenticated V2 event emitter, complete nonempty V1 history
  migration, provider/ledger qualification, alerting, and operational recovery
  drills remain necessary before activation.
- First-time ASL2 creation verifies the legacy V1 snapshots but does not
  durably retire or tombstone the old files. Production dispatch must not be
  enabled until activation and legacy-store retirement are one coordinated,
  one-way operation.
- Finalized ASRJ evidence is copied under the relayer journal's lock into the
  ASL2 transaction; the two physical files are reconciled, not updated by one
  cross-file rename. ASL2 never infers finality from an unconfirmed record.
- The rich every-boundary phase matrix does not instantiate the optional
  finalized-ASRJ field in the same private-transfer intent. Its capability,
  canonical codec/hash/replay path, and restart behavior are tested
  separately; combining that capability with the rich fault fixture remains a
  useful evidence-strengthening test before activation.
- Relayer correlation is accepted only when exact evidence is available. A
  lane event lacking an authenticated relayer request link remains explicitly
  uncorrelated rather than inferred.

## Commands, results, and resource use

- `/usr/bin/time -l cargo test --no-default-features --features
  eight-lane-plumbing-v2 --test v7_cross_store_atomicity_integration` — exit 0;
  11 passed; 7.13 s wall; 447,479,808-byte max RSS; 0 swaps.
- `/usr/bin/time -l cargo test --no-default-features --features
  eight-lane-plumbing-v2 --test v7_cross_store_atomicity_model` — exit 0; 6
  passed; 0.73 s wall; 122,634,240-byte max RSS; 0 swaps.
- `/usr/bin/time -l cargo test --no-default-features --features
  eight-lane-plumbing-v2 --lib` — exit 0; 144 passed; 5.32 s wall;
  1,019,494,400-byte max RSS; 0 swaps.
- `/usr/bin/time -l cargo test --no-default-features --features
  eight-lane-plumbing-v2` — exit 0; 168 total passed (144 unit, 11 atomicity
  integration, 6 reference-model, 5 note-store adversarial, and 2 scanner
  restart); 8.43 s wall; 296,648,704-byte max RSS; 0 swaps.
- `/usr/bin/time -l cargo test --no-default-features --lib` — exit 0; 110
  passed; 3.91 s wall; 736,575,488-byte max RSS; 0 swaps.
- `/usr/bin/time -l cargo clippy --no-default-features --features
  eight-lane-plumbing-v2 --all-targets --no-deps` — exit 0; 3.39 s wall;
  684,883,968-byte max RSS; 0 swaps. Existing crate/dependency warnings remain;
  Clippy also reports `too_many_arguments` on one test fixture helper. A
  stricter `-D warnings` gate is not green at the frozen input revision.
- `rustfmt --edition 2021 --check` on the six substantive changed/new Rust
  files other than `lib.rs` — exit 0. The two-line `lib.rs` registration was
  manually inspected; whole-file rustfmt check reports unrelated pre-existing
  ordering/function-layout drift, which this milestone intentionally did not
  reformat.
- `git diff --check` — exit 0.

All normal tests are deterministic and offline. Peak RSS is reported from
`/usr/bin/time -l`; no measured command used swap.

## Formal, verifier, and on-chain non-change statement

No file under `AspisFormal/`, no K1.x file, no Lean theorem, no
`programs/aspis-verifier/` file, no Pool on-chain program Rust, no Aeneas
bundle, no SBF/release/devnet artifact, no wire-format cryptographic relation,
and no proof relation changed.
