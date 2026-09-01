# V7 wallet finalized Pool terminal source — 2026-08-31

## Scope

- Branch: `research/v7-wallet-runtime-handoff-20260831`
- Parent milestone: `ff690a7152615eecad4e859871bb39528e477350`
- Final revision: the commit containing this report; the exact SHA is in the
  external handoff.
- V2 remains default-off.
- No Pool, Registry, verifier, proof relation, transcript, cryptographic
  statement, on-chain wire, Lean, Aeneas, deployment, signature or network
  state was changed.

## Result

The wallet no longer needs a hypothetical on-chain append log to construct a
terminal intent. `derive_finalized_pair_forest_terminal_event_v2` derives the
canonical ASL2 event from the literal deployed path:

1. an externally authenticated finalized block and exact transaction
   signature;
2. a successful last top-level invocation of the configured Pool program;
3. the exact 320-byte canonical `ASQ8` instruction;
4. transaction-global return data owned by that same Pool program and decoding
   as the exact 792-byte canonical `ASR8` result;
5. a finalized, context-fresh, Pool-owned, non-executable canonical root-page
   PDA containing the ASR8 after-root at its exact sequence;
6. the current ASL2 lane state, which independently recomputes the output-pair
   leaf, append root and complete frontier from the public commitments.

The derivation binds the Pool/deployment/asset identity, transition kind,
nullifier, routed lane, master, selected-lane PDA, output commitments,
withdrawal destination/amount, after-index, root and every frontier node. The
event identity is exactly `(block point, transaction signature, top-level
instruction index, output ordinal)`. Transfers create ordinals zero and one;
withdrawals create ordinal zero.

The terminal must be the last top-level instruction because Solana return data
is transaction-global and a later program could overwrite it. A later append
in the same finalized block does not invalidate the evidence: the root page is
checked at the ASR8 sequence, not merely at its latest entry.

`ActivatedWalletRuntimeV2::apply_finalized_pool_terminal_journal_v2` composes
this source derivation with the prior exact ASRJ finalized-success capability
and the authoritative ASL2 prepare/recovery path. It therefore provides the
local runtime chain:

```text
finalized ASQ8 + Pool-owned ASR8 + finalized root page
    -> canonical Pool output event and transaction identity
    -> exact ASRJ point/signature/provider capability
    -> ASL2 event/note/spend/lane commit
```

## ASF8 collision removed

`ASF8` remains byte-for-byte the 1,880-byte cryptographic semantic statement in
`aspis-statement`. The wallet-only compact normalized scanner record now uses
the distinct `ASFE` magic. It is explicitly not an on-chain event and the
production runtime never accepts it from program logs. This is a wallet ABI
correction only; the cryptographic ASF8 wire and all ASQ8/ASR8 bytes are
unchanged.

## Fail-closed and recovery coverage

Focused tests cover:

- exact transaction signature and instruction/output identity;
- confirmed/non-finalized input;
- failed transaction;
- zero signature;
- wrong Pool program and wrong return-data owner;
- a non-final ASQ8 instruction whose return data could be overwritten;
- malformed or mutated ASR8;
- wrong root-page owner/PDA/history root;
- exact retained-event replay;
- conflicting same-slot finalized fork and wrong finalized parent;
- ASRJ unknown request, wrong signature and wrong provider;
- no ASL2 mutation on source or journal failure;
- lost response after monotonic commit, restart recovery and exact idempotent
  replay;
- rejection of a second ASRJ request attempting to relabel the same event.

The populated migration/runtime test now uses a real ASQ8/ASR8-derived private
transfer rather than a synthetic deposit event for its ASRJ -> ASL2 handoff.

## Remaining production boundaries

1. **Owned TxV1 RPC decoder/provider adapter.** The new typed source boundary
   is strict, but the existing finalized `rpc_json` block decoder is the legacy
   1,232-byte/v0 path. A production 4 KiB TxV1 decoder must populate these
   fields from two-provider finalized block/account responses, enforce exact
   transaction order and retain provider receipts.
2. **Same-block total order in ASL2.** `DepositEventIdV1` does not contain the
   transaction index. The current coordinator orders multiple events at one
   block point by encoded event identity, which is not the ledger transaction
   order. The scanner can process the real order, and same-lane roots prevent a
   false append, but a valid same-block sequence whose signatures sort
   differently may fail closed. Production activation needs a versioned event
   identity/order field or a proved batching rule.
3. **Terminal note delivery.** ASQ8/ASR8 carries no encrypted note payload and
   two 144-byte payloads do not fit beside the 792-byte ASR8 within Solana's
   1,024-byte return-data limit. This source therefore emits public outputs
   with absent payloads. Recipient/change note bindings may enter ASL2 only
   through a separately authenticated carrier and are rechecked against the
   public commitments. The carrier/service is not implemented here.
4. **Provider and finality truth.** The runtime checks exact activated provider,
   startup and finality identities; it does not prove RPC provider honesty,
   ledger correctness or finality.
5. **Prover/relayer service.** Witness construction, proof generation/upload,
   submission, polling and acquisition of ASRJ evidence remain external
   service work.
6. **Key custody.** Viewing/nullifier key generation, hardware protection,
   backup, recovery, rotation and compromise response remain external.
7. **Production monotonic backend.** ASL2 still requires an independently
   rollback-resistant, production-qualified monotonic provider. The reference
   backend used by focused tests cannot activate production mode.

The first two items are hard production activation work. The latter service and
custody boundaries require operational implementations and review rather than
changes to the cryptographic relation.

## Focused replay

All commands ran locally; no NUC or network was used.

```text
cargo test --features eight-lane-plumbing-v2 \
  lane_forest_rpc_v2::tests::deployed_terminal_source -- --nocapture

cargo test --features eight-lane-plumbing-v2 --lib \
  lane_forest_rpc_v2::tests::compact_scanner_event_abi_round_trips_all_variants_and_rejects_drift \
  -- --exact

cargo test --features wallet-v2-reference-tests \
  populated_handoff_is_one_way_recoverable_and_activation_stays_explicit \
  -- --nocapture
```

The source suite passed 2/2 tests, the ASFE collision test passed 1/1, and the
populated ASRJ -> ASL2 runtime test passed 1/1 including restart/replay. Only
focused consumers were run.
