# V7 wallet finalized 4 KiB TxV1 RPC ingestion — 2026-08-31

## Scope and classification

- Branch: `research/v7-wallet-runtime-handoff-20260831`
- Frozen parent: `a1ffb6dc24b1a39fdd08aa8d0c1c217c9b508779`
- Final revision: the commit containing this report; its exact SHA is in the
  external handoff.
- Classification: **owned TxV1 decode, finalized quorum and same-block order
  closed; external transport/ciphertext/monotonic/key services remain**.
- V2 remains default-off behind `eight-lane-plumbing-v2` and the existing
  activation permit.

This milestone changes only the local wallet crate and this report. It does
not change the Pool, Registry or verifier programs, cryptographic relation,
ASQ8/ASF8/ASR8 wire, transaction builder, Lean/Aeneas sources, deployment,
signature or public network state.

## Owned finalized decoder

`tx_v1_finalized_rpc_v2` owns the bytes from request construction through the
constructor-sealed agreed block consumed by the wallet runtime.

The block request is exactly:

- JSON-RPC `getBlock` at one bound slot and nonzero request ID;
- `commitment: "finalized"`;
- `encoding: "base64"`;
- `transactionDetails: "full"`;
- `maxSupportedTransactionVersion: 1`;
- `rewards: false`.

Both pinned providers must receive byte-identical canonical request JSON in
the activated provider order. Each response is independently parsed with a
64 MiB cap. The decoder preserves every entry in the RPC `transactions` array
and decodes canonical Solana legacy, V0 and V1 transaction wires with the
pinned 4.2.4 `wincode` implementation. Legacy/V0 wires remain capped at 1,232
bytes; V1 wires are capped at 4,096 bytes. Deserialization, SDK sanitization
and byte-exact reserialization must all succeed. Zero or duplicate primary
signatures, trailing bytes, malformed base64, unsupported/mismatched versions
and over-limit wires fail closed.

Only a literal V1 transaction may produce a Pool terminal. Its Pool ASQ8 must
be canonical and the last top-level instruction. A successful transaction
must have canonical Pool-owned ASR8 return data within Solana's 1,024-byte
return-data limit. Failed transactions do not emit finalized-success events.
The focused fixture is an actual 1,834-byte serialized V1 transaction, so the
test exercises a wire that the legacy 1,232-byte decoder cannot accept.

Provider agreement is over the canonical consumed block, transaction order,
wire, signature, success state, return data and derived terminals, rather than
raw JSON whitespace. Any consumed semantic disagreement fails. The request,
provider set, startup receipt and decoded terminal each receive domain-separated
SHA-256 bindings.

## Finalized root-page quorum

For each terminal, the agreed block constructs the exact finalized
`getAccountInfo` request for the canonical selected-lane root-history PDA. It
binds:

- the Pool program, master and selected lane PDA;
- ASR8 output lane, next sequence and after-root;
- the canonical history page number and address;
- `minContextSlot` equal to the finalized block slot;
- the same provider set and startup receipt as the block.

Each provider response is independently checked for finalized context,
Pool ownership, non-executable status, exact account size, canonical page
header, lane linkage and the exact immutable root entry. Providers may observe
different later append-only entries in the same page; those unrelated suffix
bytes are not incorrectly required to be identical.

Only the constructor-sealed agreed block plus the constructor-sealed agreed
root entry can create a `FinalizedPairForestTerminalObservationV2`. The
activated runtime also rechecks the block's provider-set and startup-receipt
digests against its permit policy before entering the existing
ASQ8/ASR8-derived event -> exact ASRJ -> ASL2 path.

## Stable identity and exact ledger order

The stable event ID remains:

```text
(finalized slot + block hash, transaction signature,
 top-level instruction index, output ordinal)
```

The transaction signature is an identity, not an ordering key. The exact
transaction-array index is retained separately as `FinalizedLedgerPositionV2`.
It is committed inside a canonical 16-byte `ASO2` nested envelope around the
existing event bytes. The existing ASL2 content digest, transaction chain and
checksum therefore cover it and preserve it across restart without changing
the outer ASL2 version. Frozen pre-ASO2 images remain readable under their old
signature-order replay convention, while mixing old and ordered streams in
one block fails closed.

For a new block, runtime progress must start with the first decoded successful
Pool terminal. Within that block it may advance only to the immediately next
terminal. An already consumed ordinal may be retried; the existing event ID and
ASL2 content digest admit only the exact idempotent replay and reject a
substitution. Skipping directly to a later terminal, reversing terminals,
using an unknown prior position or relying on signature byte order fails.

## Adversarial coverage

Focused tests cover:

- two genuine 1,834-byte V1 terminals whose signature-byte order is the
  reverse of finalized ledger order;
- JSON whitespace differences with identical canonical semantics;
- provider transaction reorder disagreement;
- duplicate primary signatures;
- malformed base64, trailing transaction bytes and a 4,097-byte wire;
- JSON/wire version mismatch and a non-finalized request substitution;
- first/next/replay progress and skipped/unknown terminal order;
- stale root context, wrong root owner and a mutated target root entry;
- canonical durable ASO2 round-trip and reserved-byte rejection;
- frozen legacy-ASL2 compatibility and ordered/legacy same-block separation;
- the existing populated activated runtime's ASQ8/ASR8 -> ASRJ -> ASL2
  commit, crash recovery and idempotent replay path.

All focused commands ran locally and offline with zero swaps:

| Command | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| `cargo test --features eight-lane-plumbing-v2 --lib tx_v1_finalized_rpc_v2::tests -- --nocapture` | 3 passed | 5.27 s | 875,986,944 B |
| `cargo test --features eight-lane-plumbing-v2 --lib finalized_ledger_position_is_canonical_durable_and_not_signature_order -- --nocapture` | 1 passed | 0.17 s | 94,994,432 B |
| `cargo test --features eight-lane-plumbing-v2,wallet-v2-reference-tests --test v7_populated_wallet_migration populated_handoff_is_one_way_recoverable_and_activation_stays_explicit -- --nocapture` | 1 passed | 6.23 s | 772,521,984 B |
| `cargo clippy --features eight-lane-plumbing-v2 --lib --message-format short` | exit 0; pre-existing warnings only | 2.74 s | 530,104,320 B |
| changed-file `rustfmt --edition 2021 --config skip_children=true ...` | exit 0 | <1 s | not measured |
| `git diff --check` | exit 0 | <1 s | not measured |

Toolchain: `rustc 1.93.0 (254b59607 2026-01-19)`, `cargo 1.93.0
(083ac5135 2025-12-15)`. No job approached the local 8 GiB boundary.

## Remaining production boundaries

1. **Ciphertext delivery.** ASR8 is 792 bytes. Adding two 144-byte encrypted
   note payloads would already make 1,080 bytes before framing, above Solana's
   1,024-byte return-data limit. The terminal source therefore cannot invent
   ciphertext and creates no note from public bytes. Production still needs a
   separately authenticated carrier keyed to the exact stable event ID and
   public commitments, with replay, withholding and substitution handling.
2. **Rollback-independent monotonic storage.** ASL2's prepared-next protocol
   and runtime qualification interface are implemented, but no repository
   backend supplies production-grade authenticated durable CAS, namespace
   isolation and rollback independence. Production activation remains
   impossible without that service and its qualification path.
3. **Key service and custody.** Viewing/spending/nullifier key generation,
   hardware or remote protection, authorization, backup, recovery, rotation,
   revocation and compromise response remain external operational work.
4. **RPC transport/provider operation.** This module owns exact request and
   response bytes and quorum semantics, not HTTPS/TLS credential pinning,
   endpoint availability, provider qualification or proof that both providers
   tell the truth. The activated provider/startup/finality policy must be
   provisioned and operated independently.
5. **Relayer/prover operation.** The runtime binds the agreed block to the
   existing exact finalized ASRJ record. Production proof generation, upload,
   submission, polling and acquisition of that journal capability remain
   service integration work.

The two hard code gaps recorded by the preceding terminal-source milestone—an
owned 4 KiB TxV1 decoder and durable exact same-block ordering—are closed by
this change. That does not make V2 production-enabled; the service and custody
boundaries above deliberately keep the activation gate closed.

## Files changed

- `crates/aspis-pool-wallet-v1/src/tx_v1_finalized_rpc_v2.rs`
- `crates/aspis-pool-wallet-v1/src/lane_forest_rpc_v2.rs`
- `crates/aspis-pool-wallet-v1/src/lane_forest_wallet_txn_v2.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_v2_runtime.rs`
- `crates/aspis-pool-wallet-v1/src/lib.rs`
- `crates/aspis-pool-wallet-v1/tests/v7_populated_wallet_migration.rs`
- `docs/research/v7-wallet-finalized-txv1-rpc-20260831.md`
