# V7 wallet prepared monotonic/runtime close — 2026-08-30

## Revision, scope, and classification

- Repository/worktree: `/Users/dominic/ZK-v7`
- Branch: `research/v7-wallet-v2-activation-close-20260830`
- Frozen base: `32002a3417f3656ba00535710ae7abe3aee26621`
- Final audited implementation revision: `1ad7a1fe70e06d81b94af197ce6bc1c58a739ad7`
- Final documentation revision: the documentation-only commit containing this report. Its exact SHA is reported in the external handoff because a Git commit cannot contain its own SHA without changing it.
- Classification: **B — RUNTIME CLOSED; EXTERNAL MONOTONIC PROVIDER QUALIFICATION REMAINS**

V2 remains default-off and may **not** be activated in production. No locally available backend honestly supplies the required rollback-independent trust property. The complete provider-neutral prepared-next protocol and fail-closed runtime enforcement are implemented, while the deterministic and fault-injectable backends are explicitly non-production.

Production changes are confined to `crates/aspis-pool-wallet-v1/`. No cryptographic mathematics or relation, Lean source, verifier code, Pool or Registry on-chain program, Aeneas bundle, SBF/release artifact, transaction builder, deployment code, public network, signature, or transaction was changed or exercised. Main was not modified, merged, rebased, or cleaned.

## Threat model

The closed threat is rollback or substitution of the local ASL2 file while an independent trusted monotonic service remains correct and available. The service contract must provide authenticated, durable, wallet/protection-scoped compare-and-swap operations for both the prepared reservation and committed value. A local attacker may copy an older valid checksummed ASL2 image or manufacture a structurally valid successor, but cannot forge, substitute, delete, or roll back the trusted service's exact reservation/current state.

The following remain outside the claim:

- an attacker that can roll back or forge both ASL2 and every trusted monotonic persistence mechanism;
- provider compromise, equivocation, loss of its authentication key, incorrect scoping, or false durability claims;
- provider/ledger/finality honesty beyond the qualified digests passed to the wallet;
- note/nullifier-key custody, backup, secure deletion, and host compromise while keys are live;
- denial of service. An unavailable or stale service response fails closed.

Ordinary filesystem persistence is not described as rollback-proof.

## Prepared-next state machine

Each protected local replacement follows one ordering:

```text
external current C(n, hash_n)
        |
        | authenticated CAS prepare
        v
prepared P(Cn, Cn+1, physical_hash_n+1, all bindings)
        |
        | temp write -> file fsync -> rename -> parent-directory fsync
        v
local ASL2 image n+1 durable
        |
        | authenticated CAS commit exact P; consume P
        v
external current C(n+1, hash_n+1)
```

`WalletMonotonicPreparedNextV2` binds all of:

- exact optional current commitment and exact immediate successor;
- generation, predecessor commitment, finalized slot/hash, and complete authoritative ASL2 content digest;
- digest of the complete checksummed physical next ASL2 image;
- wallet identity and V2 activation identity;
- monotonic protection ID;
- note-cipher identity, which binds the existing cipher parameters;
- operation identity derived from the exact authoritative next content, including canonical event/empty-block identity and all retained state.

The external service interface exposes exact current/prepared reads and atomic `compare_and_prepare_next_v2`, `compare_and_commit_prepared_v2`, and `compare_and_abort_prepared_v2` operations. It must retain enough authenticated last-operation identity to distinguish an exact lost-response replay from a different preparation that happens to name the same logical successor. The deterministic backend now retains and compares the exact last committed/aborted preparation; same-successor metadata substitution fails.

The protocol extends the existing ASL2 transaction phases and ASMG/ASRT migration handoff. It does not create a second wallet persistence authority. Populated migration prepares the exact ASMG-authenticated ASL2 target before target installation, and normal scanner/tentative/relayer/empty-block mutations prepare before every ASL2 replacement.

## Crash recovery

Recovery reads and validates the complete local image, external current, and external prepared record before accepting or mutating wallet state:

| Observed state | Recovery result |
|---|---|
| local `n`, external current `n`, no preparation | exact committed pre-state |
| local `n`, external current `n`, exact prepared `n+1` | abort exact preparation; recover pre-state |
| local `n+1`, external current `n`, exact prepared `n+1` | commit exact preparation; recover post-state |
| local `n+1`, external current `n+1`, no preparation | exact committed post-state |
| local `n`, external current `n+1` | reject; correct ordering cannot create this state |
| local `n+1`, external current `n`, missing or substituted preparation | reject |
| stale, forked, skipped, malformed, wrong-wallet, wrong-protection, wrong-cipher, or wrong-image state | reject |

Recovery is deterministic and idempotent. `AfterPrepare`, `AfterCommit`, and `AfterAbort` faults apply the trusted atomic mutation and lose the response; an exact retry reaches the same result. A conflicting retry fails rather than being called idempotent.

External commit is invoked only after local rename and parent-directory fsync. Therefore “external commit succeeds, then the local rename crashes” is unreachable in the implemented ordering. The adversarial equivalent—external current is committed while the local file is restored to its predecessor—is tested and rejected. Conversely, local rename succeeding before an external commit fault is tested and completes from the exact preparation on restart.

Deleting or substituting a preparation cannot authorize a one-generation-ahead image. Restoring a prior ASL2 image after the external commitment advanced is rejected on every reopen, so rolling back only local files cannot resurrect finalized notes or undo finalized spends.

## Backend qualification

`InMemoryWalletMonotonicStoreV2` is a deterministic executable reference backend. `FaultInjectableWalletMonotonicStoreV2` shares that volatile state across test restarts and can interrupt every trusted protocol boundary. Both always return no production qualification.

`WalletMonotonicStoreQualificationV2` is an opaque production capability with no public constructor in this milestone. Consequently neither a test nor an out-of-crate in-memory implementation can mint production qualification. A future concrete trusted provider adapter must be reviewed and integrated with an in-crate qualification path after demonstrating real anti-rollback durability, authentication, exact wallet/protection scoping, CAS semantics, last-operation replay identity, operational recovery, and failure behavior.

No backend is production-qualified in this repository.

## Activation consumer and runtime authority

`ActivatedWalletRuntimeV2` is the permit-consuming V2 startup/scanner facade. Its coordinator is private, so a caller that selects this runtime cannot bypass permit and policy checks through the returned handle.

Startup behavior is:

1. require an explicit permit; no permit fails before opening ASL2;
2. perform a side-effect-free preflight against the selected mode, wallet, cipher, migration, ASMG ownership receipt/target path, protection ID, monotonic-provider qualification/configuration, startup receipt, provider set, and finality policy;
3. open and reconcile protected ASL2 only after preflight succeeds;
4. recover any exact pending ASL2 phase through the prepared-next protocol;
5. reconstruct every prerequisite from the live ASL2/ASMG/ASRT/external service state;
6. reevaluate the activation predicate and require byte-for-byte equality with the supplied permit.

The permit binds a stable migration target/path identity rather than a serialized “enabled” boolean or the changing current generation. Startup independently proves that the evolving current ASL2 image exactly agrees with the external commitment. A permit copied to another wallet or combined with a different provider/configuration is rejected.

Runtime operations route through the authoritative coordinator:

- eventful finalized scanner application;
- empty finalized blocks;
- tentative confirmed observation and reorg deferral;
- relayer observation/provider binding;
- restart recovery;
- shutdown recovery and final external agreement.

No failed V2 startup falls back to V1. `WalletV2ActivationMode::default()` remains `Disabled`. The pre-existing V1 path is unchanged when V2 is not selected. Successful V2 startup requires an ASMG `LegacyRetired` receipt, and all five managed legacy store constructors continue to reject writes after retirement. There is no reverse activation path.

The crate contains library APIs rather than a standalone production wallet binary. Downstream process wiring must instantiate this facade; it cannot honestly instantiate `Production` mode until a real qualified monotonic adapter exists. The feature-gated `ReferenceOnly` mode exists solely to execute the complete runtime path in offline tests and cannot produce production qualification.

## Adversarial and lifecycle coverage

The final tests establish:

- exact prepare/commit/abort replay and same-successor conflicting replay rejection;
- prepared image-hash, generation, wallet, activation, protection, cipher, and operation substitution rejection;
- forged checksummed one-generation-ahead ASL2 rejection without the exact preparation;
- stale current response and unavailable provider rejection;
- local ASL2 recovery after every write/fsync/rename boundary;
- lost response before/after every external prepare/commit/abort CAS boundary;
- local rename success followed by external commit failure and exact restart completion;
- externally committed successor followed by old-local-image restoration rejection;
- missing permit, copied permit, provider/config mismatch, and default-disabled activation failure before scanner mutation;
- real activated empty finalized-block apply and duplicate replay;
- tentative confirmation followed by reorg without accidental finalization, then a later real finalized event;
- clean shutdown through the authoritative runtime;
- populated V1 migration containing a real finalized note and locally authenticated finalized spend, preserving exact spent/lane/checkpoint state;
- restored pre-spend V1 bytes cannot reopen a writer after retirement;
- existing ASL2 finalized-spend crash/replay tests continue to reject resurrection;
- real threaded scanner open cannot race the migration while the migration holds authority and legacy-store locks.

The deterministic monotonic backend is the executable reference transition model for the trusted-service portion. The existing ASL2 reference/crash model and cross-store integration remain the production-state comparison oracle for pre/post recovery, duplicate/reorder, spend, lane, checkpoint, tentative, and journal phases.

## Durable fault matrix

Trusted-service fault points:

1. current read;
2. prepared read;
3. before prepare CAS;
4. after prepare CAS/lost response;
5. before commit CAS;
6. after commit CAS/lost response;
7. before abort CAS;
8. after abort CAS/lost response.

Each ASL2 physical replacement is interruptible after:

1. temporary write;
2. temporary-file fsync;
3. target rename;
4. parent-directory fsync.

The retained cross-store suite also interrupts before and after the logical `Prepared`, `StoresApplied`, and `Committed` phase replacements and covers all four physical boundaries for each phase. The retained ASMG/ASRT suite covers the same four physical boundaries for ASMG `Prepared`, target installation, `TargetInstalled`, `OwnershipCommitted`, five ASRT tombstones, and `LegacyRetired` (40 physical migration cases), plus before/after logical migration writes. The high-level populated handoff exercises the new monotonic reservation before target installation and exact recovery/replay.

## Commands, results, and resources

All tests were deterministic, local, and offline from `crates/aspis-pool-wallet-v1`. RSS is `/usr/bin/time -l` maximum resident set size. Every measured command reported zero swaps.

| Command | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| `cargo test --features wallet-v2-reference-tests --lib wallet_monotonic_v2::tests --no-fail-fast` | 8 passed | 4.02 s | 800,505,856 B |
| `cargo test --features wallet-v2-reference-tests --lib --no-fail-fast` | 166 passed | 2.99 s | 94,289,920 B |
| `cargo test --features wallet-v2-reference-tests --test v7_populated_wallet_migration --no-fail-fast` | 6 passed | 5.02 s | 779,272,192 B |
| `env RUST_MIN_STACK=33554432 cargo test --features eight-lane-plumbing-v2 --test v7_cross_store_atomicity_integration --no-fail-fast` | 11 passed | 7.85 s | 774,815,744 B |
| `cargo test --lib --no-fail-fast` | 119 passed | 4.33 s | 437,600,256 B |
| `cargo clippy --features wallet-v2-reference-tests --lib --tests --no-deps` | exit 0; existing warnings only, none introduced in milestone code | 2.54 s | 534,069,248 B |
| changed-file `rustfmt --edition 2021 --check --config skip_children=true ...` | exit 0 | <1 s | not measured |
| `git diff --check` | exit 0 | <1 s | not measured |
| changed-path forbidden-scope scan | exit 0 | <1 s | not measured |

The 166 feature-library tests include the 8 focused monotonic tests; counts are not added together as distinct tests. The 119 default-library tests are also a configuration run, not 119 additional unique cases.

One initial cross-store run without `RUST_MIN_STACK` reached an existing large test's default thread-stack limit and aborted with stack overflow (4.67 s, 970,227,712 B RSS, zero swap). It was not hidden or called successful. The identically scoped rerun with a 32 MiB test-thread stack passed 11/11 as recorded above. No job approached the 12 GiB stop threshold.

Clippy reported pre-existing warnings in untouched code (including type complexity, large enum variants, deprecated Solana imports, and test helper argument counts). It exited zero and reported no warning in the new monotonic/runtime implementation. A first changed-file formatting probe allowed `rustfmt` to traverse `lib.rs` children and showed an unrelated pre-existing formatting preference in `operator_startup.rs`; that file was not changed. The final child-disabled changed-file check passed.

## Files changed

- `crates/aspis-pool-wallet-v1/Cargo.toml`
- `crates/aspis-pool-wallet-v1/src/lane_forest_wallet_txn_v2.rs`
- `crates/aspis-pool-wallet-v1/src/lib.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_monotonic_v2.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_populated_migration_v2.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_store_migration_v2.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_v2_activation.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_v2_runtime.rs`
- `crates/aspis-pool-wallet-v1/tests/v7_populated_wallet_migration.rs`
- `docs/research/v7-wallet-monotonic-runtime-close-20260830.md`

## Strongest guarantees and remaining release gates

Given a correct rollback-independent service satisfying the trait contract, a protected ASL2 successor is accepted only after an authenticated exact preparation; crash recovery chooses the exact predecessor or exact fully committed successor; exact replay is idempotent; conflicting identity/content replay fails; and rolling back only local files cannot resurrect finalized notes or spends. V2 startup now consumes and rederives its complete permit before exposing scanner mutations, with no fallback and one-way legacy retirement.

Production activation still requires:

1. a concrete rollback-independent monotonic provider and adapter, with authentication, durable atomic CAS, protected last-operation identity, wallet/protection namespace isolation, operational backup/recovery rules, and an evidence-backed production qualification path;
2. deployment-specific qualification of provider quorum, ledger/finality policy, startup receipt, and reorg evidence;
3. downstream wallet-process configuration that selects `ActivatedWalletRuntimeV2`, preserves fail-closed error handling, and never enables the test-only reference feature in production;
4. production key custody and recovery controls;
5. release review of the provider adapter and an end-to-end exercise against that real service without weakening the default-off gate.

Until those gates are closed, production mode cannot obtain a qualification capability and fails closed. This milestone is safe to cherry-pick as a scoped, default-off Rust/runtime security improvement, but it is not a production wallet sign-off.
