# V7 wallet TxV1 ciphertext carrier — 2026-09-01

## Scope and result

- Branch: `research/v7-wallet-runtime-handoff-20260831`
- Frozen parent: `a7955cb893dc96d0ed6ae70e2362ca09e3052692`
- Final revision: the commit containing this report; its exact SHA is in the
  external handoff.
- Classification: **signed carrier, finalized ingestion and local note
  recovery closed; external transport, key-custody and monotonic services
  remain**.
- V2 remains default-off behind `eight-lane-plumbing-v2` and the existing
  activation permit.

This milestone changes only the local wallet crate and this report. It does
not change the Pool, Registry or verifier programs, Tag-73 proof relation,
ASQ8/ASF8/ASR8 schemas, Lean/Aeneas sources, deployment or network state.

ASR8 is 792 bytes and Solana return data is capped at 1,024 bytes. Two 144-byte
encrypted note envelopes would require 1,080 bytes before any binding or
framing, so they cannot be safely added to ASR8. The wallet now places a
fixed 496-byte `ASC8` envelope in an immediately preceding SPL Noop
instruction. The exact 320-byte ASQ8 remains the final top-level instruction,
and ASR8 remains byte-for-byte unchanged.

## Canonical `ASC8` envelope

| Offset | Bytes | Field |
|---:|---:|---|
| 0 | 4 | `ASC8` magic |
| 4 | 1 | version = 1 |
| 5 | 1 | transition kind |
| 6 | 1 | recipient/change presence mask |
| 7 | 1 | canonical digest encoding |
| 8 | 2 | carrier instruction ordinal, little-endian |
| 10 | 2 | terminal instruction ordinal, little-endian |
| 12 | 4 | zero reserved |
| 16 | 32 | Pool identity |
| 48 | 32 | attempt identity |
| 80 | 32 | proof-account identity |
| 112 | 32 | SHA-256 of the exact canonical ASQ8 |
| 144 | 32 | recipient commitment, or zero for withdrawal |
| 176 | 32 | change commitment |
| 208 | 144 | recipient HPKE envelope, or zero for withdrawal |
| 352 | 144 | change HPKE envelope |

The attempt and proof-account identities must be equal for the current Tag-73
lifecycle. Private transfers require both ciphertexts; withdrawals require
only change and require the recipient fields to be zero. Decoding requires the
exact length, version, transition, presence mask, reserved bytes, canonical
field digests and canonical encrypted-note envelope headers. It then
re-encodes the value and requires byte equality.

The carrier invokes the immutable SPL Noop program with exactly one readonly
wallet/proof-authority signer. The reviewed builder compiles exactly:

```text
instruction 0: ASC8 carrier
instruction 1: ASQ8 Pool terminal (last)
```

The carrier can know these two instruction ordinals before signing. Its final
block transaction-array index cannot be known before landing, so that index is
independently obtained from the finalized two-provider block, preserved by the
sealed RPC object and committed into ASL2's stable event position.

The signed-transaction validator decodes, sanitizes and byte-exactly
re-encodes the TxV1 transaction, reconstructs the complete reviewed message,
requires equality, and verifies every required Ed25519 signature. A distinct
relayer may supply the fee payer, but it cannot change the carrier, ASQ8,
account list, instruction order, fee payer, blockhash or resource configuration
after the wallet/proof authority signs.

## Exact serialized packet sizes

The real serialized TxV1 packets use a distinct wallet/proof authority and
relayer fee payer:

| Operation | History shape | Bytes | Headroom to 4,096 |
|---|---|---:|---:|
| private transfer | same-page | 1,440 | 2,656 |
| private transfer | rollover | 1,473 | 2,623 |
| withdrawal | same-page | 1,605 | 2,491 |
| withdrawal | rollover | 1,638 | 2,458 |

Every shape remains below the 3,500-byte review threshold as well as the
4,096-byte TxV1 ceiling.

## Finalized ingestion and non-blocking failure semantics

The two-provider finalized decoder verifies all required signatures over the
full canonical TxV1 wire, preserves exact block transaction order, and binds a
valid carrier to the adjacent ASQ8, proof account, Pool, transition and public
output commitments. Provider agreement covers the complete signed block and
derived carrier status.

Ciphertext delivery is deliberately separated from authenticated Pool state:

- canonical ASQ8, Pool-owned ASR8 and the finalized root page determine the
  proved lane transition whether or not delivery metadata is usable;
- a verified carrier is the only path that may create a local note;
- a missing, malformed, context-mismatched or commitment-mismatched carrier is
  retained as `Unrecoverable` delivery metadata, while the finalized lane
  transition still enters ASRJ and ASL2;
- recipient AEAD decryption uses the exact public note context, and plaintext
  is accepted only when recomputing the exact public note commitment;
- a local nullifier key match produces a spendable note; otherwise a valid
  recipient recovery is view-only;
- each recovered note is sealed for the local note store before its binding is
  included in the same ASL2 transaction as the event and lane update.

This split is fail closed without creating a global scanner denial of service.
A sender can omit or corrupt delivery metadata and thereby deny the recipient
recovery of that output; it cannot alter the commitments, spend Pool funds,
create a false local note, invalidate an otherwise finalized Pool transition,
or prevent unrelated wallets/transactions in the block from advancing.

The production-owned runtime path is now:

```text
signed finalized TxV1 from two providers
    -> exact block order + adjacent ASC8/ASQ8 + Pool-owned ASR8
    -> independently agreed finalized root-page entry
    -> canonical Pool lane transition
    -> optional HPKE/AEAD recovery + recomputed commitment
    -> exact ASRJ finalized-success capability
    -> one authoritative ASL2 event/note/spend/lane transaction
```

The older method that accepts caller-provided note bindings remains only as a
compatibility/reference-fixture seam. Production finalized TxV1 ingestion uses
the constructor-sealed agreed-block method and derives notes itself.

## Focused adversarial coverage

Tests cover:

- fixed-length canonical encode/decode and terminal binding;
- truncation, trailing bytes, reserved bytes and invalid presence masks;
- exact four-shape TxV1 packet sizes;
- authority-signature validation and mutation after signing;
- two-provider finalized agreement and exact transaction order;
- provider disagreement, non-finalized data, malformed/version-mismatched
  transactions, duplicate/conflicting order and invalid signatures;
- carrier omission, reordering, truncation, trailing bytes, wrong ASQ8
  context, wrong commitment and relayer mutation;
- a block containing one bad carrier followed by a valid unrelated carrier:
  both authenticated Pool terminals remain in ledger order, the first is
  unrecoverable and the second remains recoverable;
- separate recipient/change viewing keys, exact AEAD context and recomputed
  commitment equality;
- ciphertext swapping and sender omission: no false note is created and the
  proved after-lane image is unchanged;
- existing ASRJ -> ASL2 crash recovery, exact idempotent replay and conflict
  rejection through the populated wallet fixture.

All focused commands ran locally and offline. No NUC, deployment, signing
service or public RPC was used. The largest observed local build/test peak was
1,169,637,376 bytes RSS; swap remained zero.

```text
cargo test --features eight-lane-plumbing-v2 --lib \
  tx_v1_ciphertext_carrier_v2::tests -- --nocapture

cargo test --features eight-lane-plumbing-v2 --lib \
  tx_v1_finalized_rpc_v2::tests -- --nocapture

cargo test --features eight-lane-plumbing-v2 --lib \
  carrier_aead_recovers_each_wallet_without_allowing_bad_delivery_to_stall_state \
  -- --nocapture

cargo test --features eight-lane-plumbing-v2,wallet-v2-reference-tests \
  --test v7_populated_wallet_migration \
  populated_handoff_is_one_way_recoverable_and_activation_stays_explicit \
  -- --nocapture
```

## Remaining production boundaries

1. **Provider transport and independence.** Exact request/response/quorum
   semantics are owned, but HTTPS/TLS pinning, credentials, endpoint
   availability and operational independence of the two providers remain
   deployment services.
2. **Relayer/prover operation.** Production witness construction, proof
   generation/upload, partial-signature exchange, submission, polling and
   finality recovery are not supplied by this local library milestone.
3. **Signer and key custody.** Wallet/proof-authority signing, viewing,
   nullifier and note-store keys still need hardware or remote protection,
   authorization, backup, rotation, revocation and compromise procedures.
4. **Rollback-independent monotonic storage.** ASL2's protocol is implemented,
   but activation still requires a production-qualified durable CAS provider
   with namespace isolation and rollback independence.
5. **Ciphertext resend/recovery UX.** A sender can always withhold a valid
   ciphertext even though the public commitment lands. An authenticated
   out-of-band resend/recovery channel and user-visible unrecoverable-output
   handling remain product work; this is delivery denial, not a cryptographic
   integrity failure.
6. **Cluster activation evidence.** The exact packet sizes are built locally,
   but the full carrier lifecycle still needs the planned finalized devnet
   execution after the 4 KiB TxV1 feature is active.

These boundaries keep production activation default-off. None requires a
change to the Tag-73 cryptography or the frozen ASQ8/ASF8/ASR8 schemas.

## Files changed

- `crates/aspis-pool-wallet-v1/Cargo.toml`
- `crates/aspis-pool-wallet-v1/Cargo.lock`
- `crates/aspis-pool-wallet-v1/src/tx_v1_ciphertext_carrier_v2.rs`
- `crates/aspis-pool-wallet-v1/src/lane_forest_transaction_v1.rs`
- `crates/aspis-pool-wallet-v1/src/tx_v1_finalized_rpc_v2.rs`
- `crates/aspis-pool-wallet-v1/src/lane_forest_rpc_v2.rs`
- `crates/aspis-pool-wallet-v1/src/wallet_v2_runtime.rs`
- `crates/aspis-pool-wallet-v1/src/lib.rs`
- `crates/aspis-pool-wallet-v1/tests/v7_populated_wallet_migration.rs`
- `docs/research/v7-wallet-txv1-ciphertext-carrier-20260901.md`
