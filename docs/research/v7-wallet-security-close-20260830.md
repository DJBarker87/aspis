# V7 wallet security close — 2026-08-30

## Frozen scope

- Repository: `/Users/dominic/ZK`
- Isolated worktree: `/Users/dominic/ZK/.worktrees/ZK-v7-wallet-security-close-20260830`
- Branch: `research/v7-wallet-security-close-20260830`
- Frozen base revision: `45145fe3494de8d6599c00fd65fa4872b44cddfd`
- Work type: deterministic offline Rust wallet/indexer/relayer audit and tests

No deployment, signing, RPC submission, transaction submission, merge, worktree
deletion, or shared-cache cleanup was performed. The tests use deterministic
local fixtures and mock finalized RPC/event inputs.

## Audited modules

The audit read the existing implementation and tests before adding coverage:

- `src/note_store_crypto.rs`
- `src/scan_state.rs`
- `src/durable_state.rs`
- `src/durable_witness_state.rs`
- `src/finalized_indexer.rs`
- `src/relayer_finality_join.rs`
- `src/relayer_execution_journal.rs`
- `src/lane_forest_durable_v2.rs`
- `src/lane_forest_client_v2.rs`
- `src/wallet_transition.rs`
- `README.md`
- `INDEXER.md`

## Existing behavior and gaps

| Area | Existing behavior at the frozen base | Gap found |
| --- | --- | --- |
| Note storage | The 128-byte `ASNS` envelope already uses XChaCha20-Poly1305, a random 24-byte nonce, and AAD containing the cipher generation, exact 108-byte event identity, and access class. Zero keys are rejected; key/nullifier/note `Debug` output is redacted; nullifier material is obtained through `LocalNullifierKeyStoreV1`. | The existing happy-path tests did not exhaust framing, AAD, byte-mutation, authenticated-malformed-plaintext, redaction, or key-store boundary cases. No cryptographic flaw was found. |
| Finalized scan and durable wallet | Finalized RPC ingestion works on a clone. `DurableWalletStateV1` atomically commits the public cursor, required caller-sealed recovered notes, lifecycle records, and authenticated spent markers. Exact head replay is idempotent; conflicting event bytes and non-finalized data fail closed. | There was no single deterministic lifecycle target covering receive/commit/restart/replay, missing-note atomicity, witness-journal interruption, access classes, unrelated recipients, and a spent note across restart. |
| Witness durability | The witness journal replays authenticated public appends and refuses to open against a different durable scan head/root. | The crash boundary between the separately atomic wallet and witness files needed an integration test showing detection and deterministic repair from retained finalized evidence. |
| Relayer/finality | The exact signed wire is journaled before submission. Pending/not-found/finalized observations are constructor-sealed, and finalized outcomes are immutable/idempotent. | The lost-submit-response, status-before-retry, duplicate finality, conflicting outcome, and provider-disagreement sequence lacked one integrated restart test. |
| V2 lane forest | The default-off V2 state authenticates master/lane/checkpoint images, maintains per-lane witnesses, and persists canonical checksummed history. | Exact canonical event replay and conflicting identity reuse both returned `DuplicateEvent`; an exact replay was not idempotent. |
| Existing finality-join test | Production validation binds the provider set into the startup receipt digest before performing redundant provider equality checks. | One pre-existing test varied the provider set but expected `ProviderSetMismatch`. Its own fixture necessarily changed the receipt digest, so the actual fail-closed result was correctly `StartupReceiptMismatch`. |

The existing `README.md` and `INDEXER.md` descriptions remained accurate and
did not need production-documentation edits.

## Changes made

1. `LaneForestDurableStateV2::ingest_finalized_append_v2` now treats an exact
   canonical replay of an already retained event as a state-preserving
   `Ok(Vec::new())`. Reuse of either stable output identity with different
   canonical event data still returns `DuplicateEvent`.
2. The stale finality-join test fixture now uses the original manifest digest
   and expects the earlier, correct `StartupReceiptMismatch`. Production
   finality logic was not changed.
3. `tests/v7_note_store_adversarial.rs` adds focused XChaCha envelope and local
   key-boundary adversarial tests.
4. `tests/v7_scanner_durable_restart.rs` adds the finalized RPC, durable
   wallet/witness, spent-note, and feature-gated two-wallet V2 lane/checkpoint
   lifecycle tests.
5. `src/v7_relayer_finality_replay_tests.rs`, registered as a test-only child
   of `relayer_finality_join`, adds the relayer restart/finality/journal test.

No authenticated-encryption algorithm, HPKE suite, commitment, nullifier,
statement, verifier input, or cryptographic proof relation was changed.

## Security invariants exercised

| Required invariant | Executed coverage |
| --- | --- |
| Two wallet recipients plus an unrelated recipient | Independent durable V2 wallet scanners A and B ingest the same A/B/C stream. A alone recovers A's deposit and transfer recipient output; B alone recovers B's deposit and transfer change; both classify C as `NotForViewingKey`. |
| Deposits and private-transfer outputs across lanes/checkpoints | Deposits route through lanes 0, 1, and 3; a two-output private transfer appends in lane 2; both scanners persist and restore two checkpoints. The linear test also parses a private transfer through the real finalized RPC/root-page ingestion API. |
| Owned-note-only scanning | A/B/C classifications are asserted for each recipient. Unrelated ciphertext never becomes a tracked output. |
| Spendable versus view-only | A local owner-key store promotes one recovered deposit to `Spendable`; another recovered note remains `ViewOnly`. Both access classes survive serialization and restart. |
| Existing XChaCha envelope | Every stored note has the exact 128-byte `ASNS`, version 1, flags 0, algorithm 1 framing. No substitute encryption was introduced. |
| Durable restart | Wallet, witness, two lane-forest files, relayer queue, and relayer journal are dropped and reopened from disk in the relevant tests. |
| Exact cursor resume and no duplicate notes | The wallet resumes at the exact finalized head and tree cursor. Exact block/root-page replay returns `AlreadyCurrent`/`Duplicate`; exact V2 event replay is a no-op; note count and tracked witnesses do not grow. |
| Duplicate input idempotence | Exact RPC block/page, lane event, finalized journal evidence, queue completion, and signed-wire retry cases are idempotent. |
| Bad input handling | Conflicting event bytes, identity reuse, an out-of-order lane event, a non-finalized RPC block, malformed authenticated lane afterstate, a confirmed/finalized provider disagreement, and conflicting finality evidence all leave their durable baseline unchanged. |
| Spent notes do not resurrect | A finalized private-transfer nullifier is authenticated against the sealed spendable input. Its spent marker survives restart and exact replay; re-storing the same sealed record returns `AlreadyPresent` without clearing the marker. |
| Pending is not finalized | A lost submission response leaves submission and outcome unset. A later pending observation remains `AwaitingFinality` and does not resubmit or finalize. Only sealed finalized evidence records the outcome. |
| Witness history survives | Both V2 scanners retain identical authenticated lane/master/checkpoint history and distinct owned-output witnesses after two restarts. V1 witnesses reopen at the exact scan root and leaf cursor. |

## Adversarial encryption matrix

The note-store target asserts:

- zero local key rejection and wrong-key authentication failure;
- wrong event identity/AAD, ciphertext copied to another event, and access-class
  substitution failure;
- every magic byte, version/flags byte, algorithm byte, and reserved byte;
- every truncation length and a trailing byte;
- individual mutation of all 24 nonce bytes and every ciphertext/tag byte;
- authenticated but malformed `ASPN` magic/version/digest-version/reserved
  fields, noncanonical owner/salt digests, out-of-range value, and out-of-range
  asset ID;
- exact redacted `Debug` output for the cipher, nullifier material, and note;
- distinct deterministic nonces and ciphertexts when sealing the same note
  twice; and
- nullifier-key lookup only through `LocalNullifierKeyStoreV1`, only after a
  spendable envelope authenticates under the exact context.

No genuine cryptographic flaw was found, so the XChaCha20-Poly1305 profile was
not changed.

## Durability and crash boundaries

- **Event received, not persisted:** ingestion is performed on a candidate;
  discarding it leaves the durable file at its original cursor and with no
  note.
- **Note before cursor:** direct delivery before the finalized event is in the
  durable cursor is rejected as `UnexpectedRecoveredNote`.
- **Cursor without required recovered note:** the atomic wallet commit rejects
  the candidate as `MissingRecoveredNote`, leaving cursor and notes unchanged.
- **Wallet committed before witness journal:** reopening the lagging witness
  against the advanced wallet returns `ScanStateMismatch`; retained finalized
  evidence repairs the witness deterministically before normal restart.
- **Cursor replay after restart:** the exact block/page produces no replacement
  ciphertext and no duplicate note.
- **Journal before submission:** simulation and exact signed wire are durable
  before the first send call.
- **RPC response lost:** the signed wire remains durable, but submission and
  final outcome remain unset.
- **Finalized status twice:** identical final evidence is `AlreadyPresent`;
  changed evidence is `OutcomeMismatch` and cannot replace the first outcome.
- **Conflicting quorum:** finalized-versus-confirmed provider responses return
  `ProviderDisagreement` before the journal changes.

## Commands and results

All commands ran from the isolated worktree. Normal tests made no network
connection. Peak RSS values are the `/usr/bin/time -l` command readings;
all measured swap counts were zero.

```text
cargo test --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --no-default-features --features eight-lane-plumbing-v2 \
  --test v7_scanner_durable_restart
PASS: 2 passed, 0 failed; test 0.27 s; real 0.89 s;
      peak RSS 95,617,024 bytes; swap 0

cargo test --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --no-default-features --test v7_note_store_adversarial
PASS: 5 passed, 0 failed; test 0.03 s; real 5.16 s;
      peak RSS 326,221,824 bytes; swap 0

cargo test --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --no-default-features --lib \
  'relayer_finality_join::v7_relayer_finality_replay_tests::lost_submit_response_and_replayed_finality_remain_conservative_and_idempotent' \
  -- --exact
PASS: 1 passed, 0 failed, 109 filtered; test 0.11 s

cargo test --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --no-default-features --features eight-lane-plumbing-v2 --lib
INITIAL: 140 passed, 1 failed because the stale finality-join test expected
         ProviderSetMismatch instead of the earlier StartupReceiptMismatch;
         real 9.00 s; peak RSS 782,073,856 bytes; swap 0
FINAL AFTER TEST FIX: 141 passed, 0 failed; test 0.92 s; real 6.28 s;
                      peak RSS 959,102,976 bytes; swap 0

cargo clippy --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
  --no-default-features --features eight-lane-plumbing-v2 \
  --all-targets --no-deps
PASS: exit 0; real 3.65 s; peak RSS 532,529,152 bytes; swap 0
      Existing dependency/crate warnings remain; no clippy error occurred.

rustfmt --edition 2021 --check \
  crates/aspis-pool-wallet-v1/src/lane_forest_durable_v2.rs \
  crates/aspis-pool-wallet-v1/src/relayer_finality_join.rs \
  crates/aspis-pool-wallet-v1/src/v7_relayer_finality_replay_tests.rs \
  crates/aspis-pool-wallet-v1/tests/v7_note_store_adversarial.rs \
  crates/aspis-pool-wallet-v1/tests/v7_scanner_durable_restart.rs
PASS: exit 0

git diff --check
PASS: exit 0
```

`cargo fmt --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml -- --check`
was also run. It reported pre-existing formatting drift in untouched portions
of `src/lib.rs` and `src/operator_startup.rs`. Those unrelated files were not
bulk-reformatted. The exact changed Rust files pass `rustfmt --check` as shown
above.

## Remaining boundaries

- The V2 eight-lane plumbing is feature-gated, described by its module as
  production-inactive, and is not wired into Pool instruction dispatch. This
  milestone tests its authenticated event/checkpoint model; it does not
  activate V7.
- The V2 lane-forest durable image and encrypted-note storage do not yet have a
  single cross-file transaction coordinator. Exact event replay deliberately
  returns no recovered association, mirroring the V1 duplicate outcome; an
  activating application must atomically couple retained associations/notes to
  its forest state or provide explicit recovery. The tests do not claim that
  missing production orchestration is closed.
- V1 wallet and witness journals remain separate atomic files. Their mismatch
  is detected and repairable from retained finalized evidence, but the
  application still owns commit ordering and recovery policy.
- Exact replay of an already retained V2 append is idempotent. Exact replay of
  a retained checkpoint currently fails closed as
  `EventOutsideFinalizedOrder`; checkpoint replay is not a no-op API.
- RPC providers still assert finalized blockhash, account contents, and loaded
  addresses. Real HTTPS transport, provider honesty, cryptographic ledger or
  account proofs, alerting, retry/backfill policy, and archival availability
  remain outside these offline tests.
- Recipient delivery transport for private-transfer ciphertexts, OS/HSM key
  custody, entropy/CSPRNG integration, backups, rollback pruning policy, and
  filesystem/power-loss qualification remain application responsibilities.
- `lane_forest_client_v2` intentionally stops before the unresolved V2 spend
  builder/verifier CPI path. No proof generation or proof verification was
  exercised or changed here.
- No full repository, SBF, Aeneas, Lean, generated-certificate, or deployment
  gate was run; none was in scope for this focused Rust milestone.

There is no unresolved cryptographic flaw identified in the audited slice.
The cross-store V2 activation/orchestration and external-finality trust
boundaries above remain security boundaries, so this commit is evidence for a
cherry-pickable wallet-security increment, not a complete V7 production
security sign-off.

## Formal and on-chain non-change statement

No file under `AspisFormal/` or `programs/aspis-verifier/` changed. No Pool
program, K1.x file, Lean theorem, verifier implementation, SBF artifact,
cryptographic statement, or proof relation changed.
