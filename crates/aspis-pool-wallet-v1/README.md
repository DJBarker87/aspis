# Aspis Pool V1 wallet envelope slice

This isolated host crate closes a narrow P6 slice: a canonical,
recipient-encrypted note-opening payload, exact deposit-record ingestion,
strict owned finalized JSON-RPC mapping, and crash-safe wallet/indexer and
relayer state with explicit rollback.
It is intentionally not registered in the root workspace while the Pool work
tree is shared and dirty.

## Fixed cryptographic suite

The crate uses RFC 9180 HPKE base mode only:

- KEM `0x0020`: DHKEM(X25519, HKDF-SHA256)
- KDF `0x0001`: HKDF-SHA256
- AEAD `0x0003`: ChaCha20-Poly1305
- application `info`:
  `aspis:pool-v1:note-envelope:hpke-base:x25519-hkdf-sha256:chacha20poly1305:v1`

The implementation delegates the complete KEM/KDF/AEAD construction to the
pinned `hpke = 0.14.0` crate. It defines framing and protocol binding only; it
does not implement a custom cryptographic primitive.

## Canonical images

Every encrypted payload is exactly 144 bytes, below the Pool deposit boundary
of 512 opaque bytes:

```text
0..4      magic ASNE
4         envelope version 1
5         flags 0 (HPKE base mode)
6..8      RFC KEM id 0x0020, big-endian
8..10     RFC KDF id 0x0001, big-endian
10..12    RFC AEAD id 0x0003, big-endian
12..14    ciphertext length 96, big-endian
14..16    zero reserved
16..48    32-byte HPKE encapsulated key
48..144   80-byte plaintext plus 16-byte AEAD tag
```

The encrypted 80-byte plaintext is:

```text
0..4      magic ASPN
4         plaintext version 1
5         canonical digest encoding version 1
6..8      zero reserved
8..40     owner-key digest (eight canonical LE M31 limbs)
40..44    private value u32 LE, strictly below VALUE_LIMIT
44..48    canonical asset id u32 LE
48..80    note salt (eight canonical LE M31 limbs)
```

HPKE authenticates a fixed 144-byte AAD image containing `ASNC` version 1,
the exact 32-byte `POOL_V1_FORMAT_BINDING`, Pool address, deployment domain,
leaf index and public note commitment. The scanner returns a note only after
recomputing that exact frozen Pool commitment. A sender knows the recipient's
public owner key; the nullifier/spending key is never accepted by an encryption
or serialization API. A decrypted opening is view-only until
`note_matches_spending_key_v1` matches its owner key to a nullifier/spending key
held in the wallet's local key store.

## Exact deposit record and scan state

The wallet/indexer record is exactly:

```text
0..224    canonical Pool V1 DepositReceiptV1
224..N    receipt-declared opaque encrypted-note payload
```

`N` must be exactly `224 + encrypted_note_payload_bytes` and at most 736;
truncation and trailing bytes fail closed. The cursor checks the configured
Pool, asset mint and vault, then requires `leaf_index == next_leaf_index` and
`root_sequence == leaf_index + 1`. Every valid receipt advances the global
leaf cursor, including payloads for another recipient and malformed opaque
payloads, so an arbitrary depositor cannot stall scanning. A recovered note is
returned only after HPKE context authentication, commitment recomputation,
receipt amount matching and configured asset-id matching.

`ScanStateV1` links each externally-finalized `(slot, blockhash)` to its exact
parent and deduplicates the stable tuple `(slot, blockhash, transaction
signature, instruction index, event index)`. Replaying identical record bytes
is idempotent; reusing an id for different bytes fails closed. Explicit
rollback to a retained common ancestor restores the pre-fork leaf/root cursor
and returns every removed event id for transactional invalidation in the note
store. `prune_finalized_history_through_v1` moves the durable anchor forward
after external persistence, bounding the retained rollback window while every
finalized Solana block is tracked.

The canonical durable image is:

```text
0..344      ASWS/version/config/anchor/head/cursor/counts/SHA-256 checksum
344..       128-byte finalized-block checkpoints
...         212-byte processed-event public metadata/fingerprints
```

The decoder strictly checks image length/version/reserved bytes/checksum,
canonical digests, parent linkage, checkpoint snapshots, unique event ids,
contiguous leaf indices, head and final root. The checksum detects accidental
corruption; it is not a MAC and does not make hostile storage trustworthy.
The image contains no viewing key, owner key, note opening, ciphertext,
nullifier key or spending key. `LocalOwnerKeyStoreV1` receives only the public
owner-key digest; a match promotes the recovered opening from `ViewOnly` to
`Spendable` while the corresponding secret stays inside the local key store.
`classify_local_note_ownership_v1` can repeat that promotion for a securely
stored view-only opening after a later key import, without replaying an event.

## Deposit instruction and RPC return-data transport

The Pool library transport now freezes one complete canonical deposit
instruction image:

```text
0..4      magic ASDI
4         instruction version 1
5         flags 0
6..8      encrypted payload length u16 LE
8..40     owner-key digest (eight canonical LE M31 limbs)
40..44    amount u32 LE
44..48    zero reserved
48..80    note salt (eight canonical LE M31 limbs)
80..N     exact opaque encrypted-note payload
```

On success, the Pool transport calls Solana `set_return_data` with exactly the
canonical `224-byte DepositReceiptV1 || declared payload`. The call occurs only
after the vault-backed deposit kernel and return-record encoding succeed.
Solana return data is transaction-global and identifies only its most recent
setter, so `rpc_adapter` accepts a transaction only when all of these hold:

- `meta.err` is null;
- the deployment-pinned Pool program is the only top-level Pool invocation;
- that Pool deposit is the final top-level instruction and its entire ASDI V1
  image is canonical (unknown versions, reserved bits, truncation and trailing
  bytes fail closed);
- `meta.returnData.programId` is the same pinned Pool program;
- the decoded receipt/payload consumes all return bytes and exactly matches the
  instruction amount, payload and recomputed note commitment; and
- the receipt Pool, mint and vault equal the configured scan identity, whose
  Pool and vault are independently re-derived from the pinned program and mint.

`finalized_indexer` consumes an exact RPC-shaped block view and closes the
binary/chain/root checks around all four frozen Pool instructions. It strictly
decodes bounded base58 instruction/key/signature fields, strict bounded base58
or padded base64 return data, and padded base64 account data; resolves
version-0 keys as static, loaded writable, loaded readonly; checks every
compiled index; requires an explicitly asserted finalized block; and links the
exact blockhash, previous blockhash and `parentSlot`. A failed Pool transaction
never emits a scan event even when RPC reports return data.

Successful `ASIN` is accepted only with its exact `ASIR` identity/PDA receipt.
Successful `ASPT`/`ASWD` requires an exact `ASTR` matching the instruction's
Pool, domain, asset, nullifier, commitments/destination, amount and leaf
sequence. The private transfer's otherwise-unreported intermediate root is
read from authenticated history at the first output sequence. For every
successful append, the layer additionally requires a single-context finalized
root-account batch at or after the block slot. It re-derives each page PDA from
the pinned program, Pool and page number, then checks Pool-program ownership,
non-executable status, the complete canonical ASPR V1 account image and every
exact appended root/sequence. A read-only planning pass returns the sorted
unique page numbers for this second RPC request; ingestion repeats transport
authentication before using the response. Root evidence is returned beside
the note outcome. Block application occurs on a clone, so decoding,
authentication, leaf-order or note scan failure leaves the original cursor
unchanged. A retained-parent fork returns the precise event IDs that external
storage must invalidate; current block replay requires the same ordered
append-output IDs.

`rpc_json` owns the JSON boundary above that borrowed view. It emits the exact
`getBlock` and `getMultipleAccounts` request bodies, pins nonzero response IDs
and JSON-RPC 2.0, enforces response-size bounds and rejects unknown or duplicate
fields. It preserves the complete version-0 address-table lookup description
and verifies that `meta.loadedAddresses` has exactly the writable/readonly
cardinality implied by those lookups before invoking the indexer. The root-page
response is associated with the exact planned PDA order and `minContextSlot`;
missing/null accounts, wrong account space and a request/response plan mismatch
fail before scan-state mutation. A skipped/null block is returned explicitly
for the scheduler to retry or record as skipped.

## Unsigned builders, local spends and relaying

`transaction_builder` reuses the program crate's frozen encoders and Solana
SDK address functions to construct exact unsigned `ASIN`, `ASDI`, `ASPT` and
`ASWD` instructions. It derives every Pool/history/nullifier/vault/registry
PDA from an explicitly pinned program id, selects the rollover layout from the
supplied current root sequence, freezes privilege/order bits and rejects all
account aliases. Its inverse validator rebuilds an untrusted instruction and
requires byte-for-byte account/data equality.

`wallet_transition` explicitly matches a recovered input owner key to a local
nullifier/spending key, derives only the public nullifier in zeroized
temporaries, enforces local value/asset conservation, and prepares recipient
and change openings plus the exact public statements. No spending/nullifier
secret is retained, formatted, encrypted or serialized. Transition-note HPKE
delivery is reconciled only after an authenticated finalized `ASTR` supplies
the actual leaf index. Finalized transition evidence carries the authenticated
public nullifier and output IDs so a note store can atomically mark the input
spent and reverse that update by rollback ID.

`relayer` is a permissionless, no-sign/no-send operator boundary. It
revalidates an unsigned instruction against the pinned deployment/current root
sequence and binds its deterministic request id to the finalized observation
slot and SHA-256 of the exact authenticated Pool-state image. Its pure
admission gate fails closed on emergency pause, stale/future snapshots,
disabled instruction kinds, a mismatched operator payer, signer mismatch,
queue or inflight saturation, a global slot-window rate limit, excessive fee
estimates and insufficient post-fee reserve.

`durable_state` supplies that production storage layer. `DurableWalletStateV1`
holds the canonical public scan image and only caller-encrypted, opaque note
records. Its commit proves that the candidate is exactly one finalized block
beyond the prior state (or one replacement beyond the returned rollback
ancestor), that reported output/root-evidence IDs exactly cover the new block,
and that every recovered `ViewOnly`/`Spendable` outcome has a matching sealed
record. Reorg commits delete removed note IDs and reverse spent markers whose
authenticated transition output disappeared. Marking a local input spent also
requires a `LocalSpendAuthenticatorV1` implementation to match the finalized
public nullifier without exposing a spending key to this crate.

`DurableRelayerStateV1` persists the policy hash, slot-window counter, full
canonical request/snapshot/instruction, admission record and queued/inflight
status. Restart re-runs the frozen instruction validator and request-ID
derivation for every entry. Exact duplicate enqueue is idempotent; policy
drift, malformed lifecycle transitions, queue/inflight/rate/fee/reserve limits
and corrupt images fail closed before mutation.

Both stores take a per-image OS exclusive lock, reject symlink/non-regular or
group/world-readable state files on Unix, bound the complete image, write a
mode-0600 same-directory temporary file, `fsync` it, atomically rename it and
`fsync` the parent directory. Their domain-separated SHA-256 checksums detect
accidental corruption but are not MACs; the state directory remains an
operator-controlled trust boundary. Signer custody, HTTP transport and
transaction submission remain outside this crate.

See [INDEXER.md](INDEXER.md) for the exact RPC request contract, field mapping,
rollback behavior and production trust boundaries.

## Deliberate integration boundary

This crate does not change the Tag-73 proof relation or wire or parse proof
payloads. The Pool crate supplies a native entrypoint and success-only return
data, but deliberately declares no program id. Production release tooling must
select one deployment id, build/pin it consistently, deploy reviewed bytes and
configure that exact id in `DepositRpcBindingV1`; there is no permissive
default.

The remaining production integration must also:

- send the exact `rpc_json` request bytes over a hardened HTTP/TLS client and
  feed each response back with its request object; schedule null/skipped slots,
  retries and backfill without omitting or reordering transactions;
- decide whether one RPC provider is trusted or verify finality, block contents
  and v0 address-table resolution through multiple providers or a ledger/light
  client;
- fetch every required root-page snapshot at finalized commitment; ingestion
  independently re-derives each supplied page binding from the exact deployed
  program id, Pool and page number before trusting its address or contents;
- preserve top-level-only invocation or extend authentication to inner
  instructions before allowing any Pool transition through CPI;
- choose and implement the authenticated at-rest note cipher represented by
  `note_cipher_id`, protect/rotate its key, implement the local nullifier
  authenticator, and archive returned public root/transition evidence if the
  operator requires a longer audit trail than the rollback window;
- provide retry, missed-history/backfill, multi-RPC disagreement, retained
  rollback-window sizing, monitoring and backup policy;
- derive the 32-byte viewing-key IKM from protected wallet entropy with explicit
  domain separation, use a CSPRNG for encryption, back up keys and zeroize
  caller-owned secret copies;
- integrate the approved proof generator/profile/release, hardware/remote
  signer custody, per-origin abuse controls and transaction
  submission/confirmation reconciliation (the library already persists and
  enforces the public global fee/reserve/queue/inflight/rate-window gate);
- execute exact builder output under LiteSVM/Agave against the final SBF and
  pinned deployment id, including CPI rollback, account locks, ALT/v0 message
  sizing, return-data behavior, rent and compute-unit evidence.

HPKE base mode provides recipient confidentiality and context integrity, not
sender authentication. A decrypted view without a local owner-key match is
unspendable by construction.

Run only this focused slice with:

```bash
NO_DNA=1 CARGO_BUILD_JOBS=2 \
  cargo test --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml --lib
```
