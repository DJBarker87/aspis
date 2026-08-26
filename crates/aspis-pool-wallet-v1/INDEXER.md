# Pool V1 finalized indexer contract

`rpc_json` and `finalized_indexer` form the strict boundary between Solana
JSON-RPC data and the durable Pool wallet scan state. They authenticate every
successful top-level `ASIN`/`ASDI`/`ASPT`/`ASWD`/`ASPP`/`ASPF`/`ASPX`
invocation in transaction order. Append receipts are reconstructed from the
canonical instruction/accounts and authenticated root-history pages. Because
Solana return data is transaction-global, Pool-owned return data is only an
additional byte-exact check on the final Pool setter; a later non-Pool program
may overwrite it. The crate emits and strictly parses the exact requests below
but does not open a network connection. A client sends those bytes and passes
the bounded response bytes back to `plan_finalized_get_block_json_v1` and
`ingest_finalized_rpc_json_plan_v1`.

## Required RPC requests

Construct `FinalizedGetBlockRequestV1` for each non-skipped slot. Its encoder
emits exactly:

```json
getBlock(SLOT, {
  "commitment": "finalized",
  "encoding": "json",
  "transactionDetails": "full",
  "maxSupportedTransactionVersion": 0,
  "rewards": false
})
```

The owned decoder preserves `blockhash`, `previousBlockhash`, `parentSlot`,
transaction order, `version`, every base58 signature, static
`message.accountKeys`, `meta.loadedAddresses`, every top-level compiled
instruction, `meta.err`, and `meta.returnData`. Map `meta.err == null` to
`succeeded = true`; no other success heuristic is accepted. A version-0
message must carry `loadedAddresses`, even when both arrays are empty. The
resolver uses Solana's exact index order:

```text
static account keys || loaded writable || loaded readonly
```

Compiled-instruction data and keys/signatures are strict, bounded base58.
Return data accepts only literal `base58` or `base64`; both are strictly and
size-bounded decoded (base64 is padded RFC 4648). Unknown transaction
versions, out-of-u8 indices, out-of-range indices,
duplicate primary signatures, malformed encodings and oversized values stop
the complete block before cursor mutation.

`plan_finalized_get_block_json_v1` runs the complete read-only transport pass.
It yields sorted unique page bindings after deriving every root-page PDA with
the deployed Pool program and exactly:

```text
[b"aspis-pool-root-page-v1", pool_address, page_number.to_le_bytes()]
```

`FinalizedRootPagesRequestV1::encode_json_v1` then emits one exact request:

```json
getMultipleAccounts(PAGE_ADDRESSES, {
  "commitment": "finalized",
  "encoding": "base64",
  "minContextSlot": SLOT
})
```

`ingest_finalized_rpc_json_plan_v1` associates each response value with its
requested page number and address before constructing the borrowed root views.
It rejects response-ID/version drift, unknown/duplicate fields, missing/null
accounts, wrong account length and a request object that differs from the
original plan. Ingestion repeats the strict block transport pass so block data
cannot be substituted between planning and application.
The layer requires one shared response context at or after the Pool block slot,
the pinned page address, the pinned Pool program as owner,
`executable == false`, the exact 8,256-byte canonical ASPR V1 page, matching
Pool/page metadata, and the exact receipt root at its sequence. Missing,
duplicate and unrelated page snapshots fail closed.

A later finalized page snapshot may authenticate an earlier retained sequence
because the deployed page transition is append-only: existing slots never
change and unused slots must remain canonical zeroes. That property must be
preserved by the production Pool entrypoint and upgrade policy.

## Block application and reorg behavior

All wire decoding, per-instruction account/PDA matching, optional final
Pool-return-data matching, and root-page checks run before scan mutation.
Every reconstructed append root is authenticated individually; for a 1-to-2
transfer both the intermediate and final roots come from history, with an
observed final `ASTR`, when available, required to match exactly. Application
then occurs on a clone:

- an exact replay of the retained head requires the same ordered append-output IDs;
- a direct child advances normally, including skipped-slot parent linkage;
- a new block whose parent is retained rolls back to that exact point, returns
  all invalidated event IDs, and applies the replacement block;
- a replay of an older retained point is rejected as stale; and
- a fork whose parent precedes the durable anchor is rejected for backfill.

Any error drops the working clone (including any recovered note openings) and
leaves the caller's `ScanStateV1` unchanged. On success,
`DurableWalletStateV1::commit_finalized_ingest_v1` verifies the exact
old/candidate/rollback relation, requires sealed records for recovered notes,
marks locally authenticated nullifiers spent, removes rollback IDs and commits
the public scan image plus opaque note state with an atomic fsync/rename. The
returned public historical-root and transition evidence can additionally be
archived by an operator that needs evidence beyond the retained rollback
window. Neither this layer nor the scan-state image accepts or serializes a
spending/nullifier secret. Ownership is promoted only through the local
owner-key lookup interface.

## Remaining production boundaries

- HTTP/TLS transport, retry/backfill policy, null/skipped-slot scheduling and
  the truth of the RPC provider's finalized response remain in the client.
  JSON shape, duplicate fields, request IDs and the commitment requested on
  the wire are enforced by `rpc_json`.
- RPC blockhash/finality and `meta.loadedAddresses` are provider assertions.
  Multi-provider quorum, local address-lookup-table resolution, or a verified
  ledger/light client is required when a single RPC operator is outside the
  trust model.
- Transaction builders and RPC ingestion use the pinned Solana SDK to derive
  exact PDAs. Every supplied `RootPageAddressBindingV1` is independently
  re-derived from the pinned program id, Pool and page number before any RPC
  account data is trusted. There is no default program ID.
- The pinned deployed program rejects inner invocation using the instructions
  sysvar, so every successful Pool mutation is visible in the top-level
  message instruction sequence consumed here.
- The only accepted successful Pool wires are frozen `ASIN`, `ASDI`, `ASPT`,
  `ASWD`, `ASPP`, `ASPF` and `ASPX`; unknown versions/instructions stop the
  complete block. `ASIN`, `ASPP` and `ASPX` are non-appending reconciliation
  events. Deposit payloads are scanned in-band; private-transfer/change
  ciphertext delivery is an external channel bound to the finalized `ASTR`
  leaf context.
- The crate supplies fsync/atomic wallet and relayer state images. Selection
  and key management for the opaque note encryption-at-rest scheme, backups,
  rollback pruning, backfill, missed-slot scheduling, monitoring and
  disagreement alerts remain application responsibilities.
- Transaction signing/submission, per-origin relayer abuse controls, recipient
  delivery transport and proof generation remain application responsibilities.
  The durable relayer layer already persists global queue/inflight/rate/fee and
  reserve admission state. No secret key enters this indexer.
- The deployed root-history entrypoint, owner/address initialization and
  append-only upgrade invariant must be audited end to end. An RPC account
  snapshot is authenticated against those pins but is not a cryptographic
  account proof by itself.
