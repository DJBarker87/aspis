# V7 wallet V2 activation close — 2026-08-30

## Revision and scope

- Repository/worktree: `/Users/dominic/ZK-v7`
- Branch: `research/v7-wallet-v2-activation-close-20260830`
- Frozen base: `76936a4f6b1f572307c32dc61c2c7e18565c789f`
- Rust implementation/test commit: `cd432745` (`feat(wallet): add crash-safe V2 activation migration`)
- Final documentation commit: the commit containing this report; its exact SHA is recorded in the external final handoff because a Git commit cannot contain its own SHA without changing it.
- Production source changes are confined to `crates/aspis-pool-wallet-v1/`.

No cryptographic proof relation, cryptographic mathematics, Lean source, verifier code, Pool or Registry on-chain program, Aeneas bundle, deployment artifact, public network, or transaction was changed. The only format change is the local wallet ASL2 durable image upgrade from schema V2 to V3; no on-chain or protocol wire format changed.

## Result

This milestone closes a useful default-off migration and ownership-transfer slice, but it is **not a complete wallet production sign-off**.

It adds:

- authenticated empty-finalized-block records that advance the ASL2 cursor without fabricating an Aspis event;
- strict projection of populated, quiescent ASDW/ASWJ/ASD8/ASRQ/ASRJ legacy state into one ASL2 migration genesis;
- a physical ASMG/ASRT one-way ownership journal with exact path, source-image, target-image, and authority-directory bindings;
- full-source locked preflight before any ownership or tombstone mutation;
- unconditional cooperative writer fencing in all five managed legacy constructors;
- externally anchored generation/finalized-point/content commitments through an injectable monotonic-store interface;
- explicit backend qualification bound to the exact ASL2 protection ID (the in-memory implementation is deliberately unqualified);
- a single explicit, default-disabled activation predicate covering migration, ownership, retirement, schema, monotonic, startup, provider, and finality prerequisites.

V2 remains default-off. There is no production dispatch installed and no code consumes the opaque activation permit.

## Authoritative stores and migration validation

The populated migration opens and holds all five legacy stores together:

1. ASDW wallet/note/scanner state;
2. ASWJ witness journal;
3. ASD8 V2 lane/forest state and checkpoints;
4. ASRQ relayer admission state;
5. ASRJ relayer execution journal.

Before ASMG `Prepared`, migration validates without mutation:

- all paths have one common parent and unique canonical path/device/inode identity, with one hard link each on Unix;
- exact source bytes, magic, version, length, digest, canonical decoder, and current cursor;
- ASDW and ASWJ block/event/root history equality;
- the ASDW public append set equals the ASD8 retained output set;
- every retained wallet note opens under the configured existing note cipher with its canonical event identity, AAD, access class, commitment, and unique nonce;
- ASWJ and ASD8 tracked identities exactly equal the wallet note set;
- lane, slot, pair index, event identity, commitment, finalized head, and checkpoint relationships agree;
- spent markers, when present, must be spendable, locally authenticated, nullifier-valid, and backed by the exact retained ASD8 transition;
- ASRQ is empty and every ASRJ record is terminal. Pending admission or signed/submitted-but-unsettled ASRJ work is rejected rather than silently dropped;
- the complete exact terminal ASRJ image is archived in the ASL2 migration genesis.

The successful populated fixture contains one real finalized RPC deposit, its encrypted spendable note, exact ASWJ history, an HPKE-associated ASD8 output and finalized checkpoint, and a terminal ASRJ record. A populated finalized-spend migration fixture remains missing; see Remaining boundaries.

## ASMG/ASRT ownership state machine

The physical handoff is monotone:

```text
legacy authoritative
    |
    | all five legacy locks held; full validation complete
    v
Prepared (ASMG)
    |
    | install exact protected ASL2 genesis
    v
TargetInstalled (ASMG)
    |
    | validate cipher/protection/monotonic state;
    | lock exact target + all five exact sources
    v
OwnershipCommitted (ASMG)
    |
    | replace each exact source with its bound ASRT tombstone
    v
LegacyRetired (ASMG)
```

Important ordering properties:

- `Prepared` is written while every source lock is still held, closing the scanner/migration race.
- Every legacy constructor checks the common authority before and after taking its own source lock.
- Recovery verifies the exact prepared target, note cipher, protection identity, and external monotonic commitment before retirement.
- The guarded composite locks and validates the complete source set before `OwnershipCommitted` or the first ASRT write. A corrupt later source therefore cannot follow an earlier tombstone.
- The exact ASL2 target lock and all source locks remain held through every ASRT write and the final `LegacyRetired` decision.
- Unguarded ownership/retirement primitives exist only under `cfg(test)`. Production has one target-guarded phase-changing path; its separate completion API can only verify an already-`LegacyRetired` state.
- Exact replay returns the same receipt. A conflicting migration identity, target/source path, image, or tombstone fails without mutation.
- After `Prepared`, recovery is roll-forward. ASMG remains the single authority selector, so the physically retained preimage and ASL2 target are never independently writable authorities.

The cooperative locking order is ASMG authority, ASL2 target, then all legacy sources in canonical role order. No inverse order exists in the managed APIs.

## Empty finalized blocks

ASL2 schema V3 stores a tagged operation: eventful V2 intent or authenticated empty finalized block. An empty block binds:

- exact finalized point and parent;
- canonical empty-event-set digest;
- account snapshot digest;
- startup receipt digest;
- provider-set digest.

It advances only the common finalized cursor. It cannot mutate notes, spends, witnesses, lanes, checkpoints, or relayer observations. Exact replay is an idempotent no-op; identity/content conflict, stale parent, cursor regression, or collision with a tentative event observation fails closed. Slot gaps are allowed only when the supplied finalized parent is the exact current head, accommodating chains with skipped slots.

## Monotonic rollback protection

ASL2 V3 binds each image to:

- nonzero protection ID;
- monotonic generation;
- predecessor commitment;
- finalized slot/hash;
- a digest over the complete authoritative activation, records, tentative observations, notes/spends, lane/checkpoint state, and cursor.

The injected store exposes an atomic compare-and-advance operation. Exact current replay is idempotent; generation regression/gap/conflict, predecessor mismatch, finalized-slot regression, and same-slot fork fail closed. Startup accepts only the exact externally anchored image or one predecessor-linked generation ahead, covering the crash window in which ASL2 replacement completed before external compare-and-advance.

The deterministic in-memory store is public for tests but reports no production qualification. Activation additionally requires a nonzero injected backend identity/configuration qualification bound to the exact protection ID. This is an attestation supplied by the deployment integration; the wallet cannot prove that the external backend is actually rollback-independent.

An attacker able to roll back the ASL2 file and every trusted monotonic/authority mechanism together is outside this model. An attacker able to manufacture and checksum a structurally valid one-generation-ahead ASL2 image is also not closed by the current two-step replace-then-CAS protocol; a production backend needs a prepared-next commitment/capability protocol before this can be treated as adversarial local-write protection.

## Activation predicate

`WalletV2ActivationMode::default()` is `Disabled`. The sole predicate returns an opaque permit only when all of these agree exactly:

- ASL2 magic and schema V3;
- activation schema;
- wallet and note-cipher identities;
- populated migration genesis and migration ID;
- ASMG receipt authenticating the exact target path and bytes;
- `LegacyRetired` ownership phase and all five retired writer roles;
- no pending ASL2 transaction;
- exact current ASL2/external monotonic commitment;
- protection ID and qualified monotonic-backend digest;
- exactly one nonzero qualified startup, provider, and finality digest.

Missing, zero, ambiguous, or mismatched prerequisites fail closed. Tests independently break 38 runtime prerequisites and all 10 nonzero configuration bindings.

The predicate itself installs no runtime. The permit has no production consumer in this repository, so V2 cannot honestly be enabled merely by constructing a successful test predicate. Configuration also pins the current monotonic commitment; an operational activation lifecycle must define whether that pin is regenerated at each startup or persisted as a one-time transition.

## Durable boundaries and fault matrix

All local durable replacement uses the existing `AtomicStateFileV1` temporary-file protocol. Each real write is faulted at:

1. temporary write;
2. temporary-file fsync;
3. target rename;
4. parent-directory fsync.

ASMG/ASRT exercises 10 writes × 4 boundaries = 40 injected physical crash cases:

- ASMG `Prepared`;
- ASL2 target image;
- ASMG `TargetInstalled`;
- ASMG `OwnershipCommitted`;
- five ASRT tombstones (ASDW, ASWJ, ASD8, ASRQ, ASRJ);
- ASMG `LegacyRetired`.

Empty-block ASL2 exercises 3 phase writes × 4 boundaries = 12 physical cases, plus before/after logical interruption around `Prepared`, `StoresApplied`, and `Committed` = 6 logical cases.

The prior ASL2 cross-store integration remains green with 11 executable tests, including eventful 3 × 4 phase-boundary matrices, rich transfer/spend/checkpoint 3 × 4 matrices, tentative-ledger boundaries, deterministic replay, concurrent duplicate application, and finalized-spend non-resurrection. The executable reference model remains green with 6 tests.

The populated high-level handoff additionally stops after ownership but before the first tombstone and proves that wrong cipher, wrong protection ID, corrupt later legacy source, and corrupt ASL2 target do not retire any source. Restoring exact bytes then completes and repeated recovery returns the same receipt.

## Commands, results, and resources

All commands ran locally and offline from `crates/aspis-pool-wallet-v1`. Peak RSS values are `/usr/bin/time -l` maximum resident set size; every measured command reported zero swaps.

| Command | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| `cargo test --lib` | 119 passed | 8.49 s | 675,250,176 B |
| `env RUST_MIN_STACK=16777216 cargo test --features eight-lane-plumbing-v2 --lib -- --test-threads=1` | 163 passed | 4.27 s | 94,846,976 B |
| `cargo test --features eight-lane-plumbing-v2 wallet_store_migration_v2::tests --lib` | 9 passed; includes 40 physical handoff faults | 2.55 s | 94,420,992 B |
| `cargo test --features eight-lane-plumbing-v2 wallet_monotonic_v2::tests --lib` | 6 passed | 4.02 s | 844,365,824 B |
| `cargo test --features eight-lane-plumbing-v2 wallet_v2_activation::tests --lib` | 4 passed; 38 broken runtime prerequisites and 10 zero config bindings inside | 0.15 s | 94,470,144 B |
| `cargo test --features eight-lane-plumbing-v2 --test v7_populated_wallet_migration` | 4 passed | 8.10 s | 489,488,384 B |
| `cargo test --features eight-lane-plumbing-v2 --test v7_empty_finalized_block` | 3 passed; 12 physical + 6 logical empty-block faults | 5.75 s | 264,470,528 B |
| `env RUST_MIN_STACK=16777216 cargo test --features eight-lane-plumbing-v2 --test v7_cross_store_atomicity_integration` | 11 passed | 7.02 s | 95,633,408 B |
| `cargo test --features eight-lane-plumbing-v2 --test v7_cross_store_atomicity_model` | 6 passed | 1.17 s | 243,580,928 B |
| `cargo clippy --all-targets --features eight-lane-plumbing-v2 --no-deps` | exit 0; 16 existing lib warnings, 19 existing lib-test warnings, none in milestone files | 3.27 s | 595,083,264 B |
| changed-file `rustfmt --edition 2021 --config skip_children=true --check ...` | exit 0 | <1 s | not measured |
| `git diff --check` | exit 0 | <1 s | not measured |

One initial parallel feature-library run reported 162 passed and one untouched checkpoint-operator test failed with `Durable(AlreadyLocked)`. The exact test passed immediately in isolation (1 passed, 94,437,376 B RSS), and the complete feature library then passed 163/163 serially. This is recorded as a pre-existing parallel test-path collision, not hidden as a successful first run.

The pre-existing 11-test cross-store integration initially overflowed the default Rust test-thread stack after ASL2 V3 enlarged the in-memory state. It passes with `RUST_MIN_STACK=16777216`. The two new large-state integration files use explicit 16 MiB worker threads so their normal commands pass without environment configuration.

`cargo fmt --all -- --check` was also probed and reported unrelated pre-existing formatting differences in `aspis-core`, `aspis-statement`, and the Pool program. Those files were not edited. The changed-file rustfmt check above is green.

The base-to-HEAD forbidden-path scan found no `AspisFormal`, verifier, Pool/Registry program, Aeneas, or K1 path. No deployment, signing, RPC submission, or public-network command was run.

## Remaining boundaries and exclusions

V2 must remain default-off. It is not ready for production activation until at least:

1. A real durable, rollback-independent monotonic backend implements the interface and its backend/configuration qualification is operationally verified. The in-memory backend is intentionally rejected by authoritative activation.
2. The monotonic protocol gains a prepared-next commitment/capability if adversarial forward rewriting of local ASL2 bytes is in scope. Current one-ahead crash reconciliation is safe for crash recovery, not a MAC against a local writer.
3. A production dispatch consumes the opaque activation permit. Today coordinator APIs remain library APIs and no runtime dispatch is installed.
4. The activation commitment lifecycle is defined after the first protected write; the configured exact current commitment otherwise changes on every generation.
5. Provider quorum, ledger correctness, finality qualification, startup qualification, and reorg evidence remain external. ASL2 validates supplied bindings but does not query or prove provider honesty.
6. Key custody, backup, secure deletion, hardware-backed storage, and recovery of the note-cipher/nullifier keys remain external.
7. Migration currently requires quiescence: ASRQ must be empty and all ASRJ entries terminal. Continuing pending/submitted legacy relayer work is deliberately unsupported.
8. Add a populated V1 finalized-spend migration fixture with a matching ASD8 transition, restart proof that the note remains spent, restored-pre-spend snapshot rejection, and mismatched-nullifier negative. The production validation exists, and eventful ASL2 finalized-spend non-resurrection is covered, but the legacy migration branch is not directly exercised.
9. Add a real threaded scanner-versus-migration/migration-versus-migration test. Current lock/fence tests and duplicate-scanner model coverage are deterministic but the migration fence test is synchronous.
10. The 40 handoff boundary cases use generic exact source images. Only one populated semantic high-level interruption is injected. A populated semantic matrix at all 40 boundaries would strengthen integration evidence.
11. Add direct populated migration negatives for prepared-plan history, duplicate nonce, invalid spend, path alias, malformed ASRJ, and deliberately spliced partial history. Lower layers reject canonical corruption/conflict, but these precise projection branches are not all directly exercised.
12. ASMG/ASRT writer retirement assumes cooperative current binaries and local authority files have not all been rolled back together. Restoring every local authority/tombstone plus every trusted external anchor is outside the stated model.

## Cherry-pick assessment

The implementation commit is internally coherent, default-off, focused to the wallet crate, and suitable for review/cherry-pick as a guarded research milestone. It should **not** be cherry-picked together with a claim of production activation or complete wallet sign-off. The unresolved external backend, permit-consumer, activation-lifecycle, adversarial-forward-rewrite, and populated-spend-migration boundaries must remain explicit.
