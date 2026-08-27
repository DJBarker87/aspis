# V7 non-mathematical ecosystem gap audit

Date: 27 August 2026

Audited source base: `384da5b584d25c095a4c3e6d9e0fe4bc75a7431d`,
plus the read-only one-terminal composition audit at
`cbc97a1999d14366284bb82bd861416068ecebb0` before final commit.

Scope: Rust/client/runtime/release plumbing only. This audit did not modify or
assess Lean mathematics, deploy a program, sign a transaction, or contact a
cluster. A committed file or passing host test is not treated as devnet or
release evidence.

## Result

Most of the off-chain safety kernel exists as concrete Rust rather than a
design sketch: encrypted note delivery and storage, strict finalized block
decoding, two-provider RPC agreement, append-witness maintenance, unsigned
instruction construction, durable relayer admission/execution journals,
external signer isolation, and a fail-closed release startup gate are all
implemented. The principal gap is now integration and release evidence, not
basic data-model plumbing.

The Pool is not mainnet-ready. In particular, the production requirement is
one terminal spend transaction. The committed direct Pool route does not fit
the current compute ceiling, while the measured prepared-settlement route
uses a separately finalized verifier receipt, preparation and settlement. Its
runtime results are valuable component evidence but do not satisfy the
one-terminal-transaction requirement.

## Requirement-by-requirement evidence

| Requirement | Current implementation/evidence | Audit status | What is still required |
| --- | --- | --- | --- |
| Versioned verifier registry | `programs/aspis-registry` implements initialize, schedule, activate, pause/unpause, compatible retirement and irreversible freeze. `crates/aspis-pool-wallet-v1/src/registry_transaction_builder.rs` derives exact PDAs and unsigned governance instructions. `results/registry-v1-runtime-litesvm-20260825/evidence.json` records the full 16-step lifecycle, System-CPI rollback, byte-exact rejected-state preservation and simulation/execution agreement against one 102,648-byte SBF. | Implemented and locally runtime-evidenced. | Two independent clean builds; selected deployment id and loader/upgrade-authority record; real threshold-multisig transaction integration; finalized devnet governance lifecycle. |
| Vault-backed deposits | `programs/aspis-pool/src/{vault,deposit,deposit_transport,processor}.rs` validates the legacy SPL Token mint/accounts, performs `TransferChecked`, verifies source/vault deltas, appends one commitment and emits canonical `ASPD`. The wallet builds `ASDI` and indexes the declared encrypted payload. | Implemented and host-tested; release evidence incomplete. | A committed final-SBF LiteSVM/Agave lifecycle covering initialization, normal deposit, page rollover, real token CPI, rent/account creation and rollback after a successful inner CPI followed by outer failure. Then finalized devnet deposit evidence. |
| Append-only tree and historical roots | `programs/aspis-pool/src/{state,transition,history,anchor}.rs` implements the depth-20 frontier and paged retained roots. `results/pool-v1-prepared-runtime-litesvm-20260827/evidence-historical-anchor-rollover.json` demonstrates membership at sequence 100, 410 intervening appends, live preparation at 510 and ordered roots 511/512 across pages. | Core implemented; populated-tree local runtime evidence exists. | Close the production Rust-to-Aeneas inductive writer invariant used by the optimized non-genesis loader; final runtime evidence for every mutating instruction and page-creation form; finalized devnet history/indexer reconciliation. |
| Atomic private 1-to-2, change and withdrawal | Direct `ASPT`/`ASWD` handlers and prepared `ASPP`/`ASPF` handlers exist. The wallet constructs both transition kinds, locally enforces value/asset conservation and binds recipient/change delivery to finalized `ASTR`. Prepared private rollover settles atomically and rejects replay in LiteSVM. | Semantics/components implemented, production architecture unresolved. | Make proof verification plus current-root append, nullifier and custody fit one terminal transaction. Add final-SBF runtime evidence for private same-page/rollover and withdrawal with real SPL Token CPI, including every late-failure rollback and replay. The current three-stage prepared path is not sufficient. |
| Wallet scanning and encryption | `lib.rs` fixes RFC 9180 HPKE X25519/HKDF-SHA256/ChaCha20-Poly1305 framing; `note_store_crypto.rs` uses XChaCha20-Poly1305 at rest; `durable_state.rs` atomically persists public cursor plus opaque sealed records; `wallet_transition.rs`, `witness_state.rs` and `durable_witness_state.rs` handle ownership, spends, rollback and current paths without serializing spending keys. | Substantial library implementation with focused tests. | A deployable wallet process/UI; protected entropy-to-viewing-key derivation and backup UX; concrete OS/HSM keystore implementation; authenticated recipient/change delivery service; final cross-process crash/recovery and restore evidence. |
| Finalized indexer | `finalized_indexer.rs`, `rpc_json.rs`, `rpc_json_quorum.rs` and `rpc_https_transport.rs` strictly parse v0/legacy blocks, authenticate Pool account layouts and root pages, require exact two-provider agreement, and apply on a clone before durable commit. | Strong library boundary; no production daemon or live evidence. | Durable sequential slot scheduler, retry/backoff and retained-window/backfill policy; an executable service; finalized devnet ingestion of the exact Pool lifecycle; operational provider-disagreement and missed-history alerts. This audit adds authenticated two-provider null-slot evidence so one provider cannot silently omit a block. |
| Relayers | Admission, fee/reserve/rate/queue limits, canonical legacy/v0 message assembly, ALT authentication, simulation journal, external Unix signer protocol, send/status RPC composition and finalized success/failure reconciliation are implemented under `crates/aspis-pool-wallet-v1/src/relayer*.rs` and `operator_execution.rs`. | Strong no-sign/no-send library; service integration absent. | Production daemon, abuse controls, supervised signer service/HSM policy, exact final one-transaction builder route, process-level crash matrix, final-SBF simulation/send/finality lifecycle on devnet. |
| Operator controls | `operator_startup.rs` binds a release manifest to provider agreement, program hashes/authorities, registry state, Pool checkpoint, policy and evidence digests. `docs/pool-v1-operator-runbook.md` defines pause, incident and monitoring expectations. | Pure gate and runbook implemented. | Canonical signed manifest envelope and threshold authenticator implementation; governance transaction templates; executable monitoring/alerting; backup/restore drills; pinned deployment and upgrade-authority evidence. |
| Adversarial testing | V7 verifier host corpus has 4,020 rejected mutations in `results/spend/v7-devnet-20260825-fullc2/v7-adversarial-replay.json`. Pool, wallet and registry contain extensive fail-closed unit tests; registry and prepared settlement runtime evidence include replay/rollback cases. | Good component coverage, not a release corpus. | Position-complete mutation/adversarial corpus for the final integrated one-terminal Pool instruction, all account metas/wires/state pages/token states, CPI-late failures, concurrent deposits/spends, indexer/RPC equivocation, relayer crash points and signer protocol. |
| Reproducible SBF builds | V7 verifier has a profiled SBF and finalized devnet execution. Registry and Pool each have a single pinned SBF in focused evidence. Pool evidence explicitly says it is not a clean-source reproducibility certificate. | Not complete. | Two isolated clean Linux builds per final verifier/Pool/registry source and deployment id, byte-identical hashes, pinned toolchains/logs/source tree, and equality to every simulated/deployed artifact. |
| Finalized devnet lifecycle | `v7-devnet-execution-resume1.json` records finalized Tag-73 verifier execution at 1,257,959 CU and replay rejection. Pool/registry runtime artifacts are LiteSVM only. | Verifier-only devnet evidence. | One finalized end-to-end Pool lifecycle: registry creation/activation, Pool/vault initialization, deposits, retained-root private 1-to-2 spend, withdrawal, nullifier/replay rejection, indexer/wallet recovery, relayer reconciliation, cleanup/refunds and independent RPC reconciliation using exact reproducible binaries. |

## Bounded implementation completed by this audit

Before this change, `result: null` was converted into
`RpcJsonErrorV1::SkippedBlock` while decoding the first provider, so a caller
could not obtain constructor-sealed evidence that both pinned providers agreed
on the null response for the exact requested finalized slot.

`agree_finalized_get_block_outcome_v1` now returns either:

- `AgreedFinalizedSlotPlanV1::Block`, retaining the existing exact semantic
  equality requirement; or
- `AgreedFinalizedSlotPlanV1::Null`, only after both providers return null
  for the identical provider-ordered request bytes.

A null/non-null split is `ProviderDisagreement`; malformed non-null responses
remain attributed to their provider. The skipped result binds provider set,
startup receipt, checkpoint, request id, slot and exact request digest. The
existing block-only API retains its old skipped-slot error behavior for
compatibility. `ExactRelayerHttpsRpcV1::agreed_finalized_slot_plan_v1` exposes
the new sealed outcome over the already-pinned HTTPS transport.

This closes authentication of null-slot responses. It does not by itself prove
whether a null was a skipped slot or unavailable history. Persisting and
operating the retry/classification policy and sequential backfill scheduler
remains a separate application task.

## Ordered remaining ecosystem work

1. Resolve and measure the final one-terminal Pool transaction architecture;
   all builders, relayer policy and lifecycle evidence must target that route.
2. Complete Pool runtime coverage with real SPL Token custody for initialize,
   deposit, private rollover and withdrawal, including CPI-late rollback.
3. Build the operator processes around the existing libraries: durable
   sequential indexer, wallet/key-store adapter, relayer daemon, supervised
   signer, manifest authenticator and monitoring.
4. Produce the integrated adversarial/crash/concurrency corpus against the
   exact final SBF binaries.
5. Produce two-build reproducibility certificates for verifier, Pool and
   registry.
6. Run and archive the complete finalized devnet lifecycle and independent
   reconciliation. No mainnet action is authorized by this audit.
