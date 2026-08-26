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
setter. The narrow compatibility `rpc_adapter` therefore accepts a transaction
only when all of these hold:

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

`finalized_indexer` is the production block path. It consumes an exact
RPC-shaped block view and closes the binary/chain/root checks around all seven
frozen Pool instructions (`ASIN`, `ASDI`, `ASPT`, `ASWD`, `ASPP`, `ASPF`,
`ASPX`). It processes every successful top-level Pool instruction in
transaction order, reconstructs append results from canonical instruction and
account data, and treats final Pool-owned return data only as a byte-exact
consistency check. A trailing non-Pool program may overwrite return data
without hiding a Pool mutation. It strictly
decodes bounded base58 instruction/key/signature fields, strict bounded base58
or padded base64 return data, and padded base64 account data; resolves
version-0 keys as static, loaded writable, loaded readonly; checks every
compiled index; requires an explicitly asserted finalized block; and links the
exact blockhash, previous blockhash and `parentSlot`. A failed Pool transaction
never emits a scan event even when RPC reports return data.

Successful `ASIN` is accepted only with its exact identity and PDA layout.
Successful `ASPT`/`ASWD`/`ASPF` results are reconstructed from the canonical
statement and exact account layout; `ASPP` and `ASPX` expose non-appending plan
reconciliation evidence. Every output root, including a private transfer's
intermediate root, is read from authenticated history. If the final Pool
setter's `ASIR`, `ASPD`, `ASTR` or `ASPX` bytes remain in `meta.returnData`,
they must equal the reconstructed result. For every successful append, the
layer additionally requires a single-context finalized root-account batch at
or after the block slot. It re-derives each page PDA from
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
SDK address functions to construct exact unsigned `ASIN`, `ASDI`, `ASPT`,
`ASWD`, `ASPP`, `ASPF` and `ASPX` instructions. It derives every
Pool/history/nullifier/vault/registry/prepared-plan
PDA from an explicitly pinned program id, selects the rollover layout from the
supplied current root sequence, freezes privilege/order bits and rejects all
account aliases. Its inverse validator rebuilds an untrusted instruction and
requires byte-for-byte account/data equality. `ASPF`/`ASPX` validation also
requires the public plan authority, source sequence, verifier profile/release,
receipt and core/shard identity authenticated from finalized `ASPP`; those
values are never inferred from the request. `ASPX` remains valid when the Pool
has advanced beyond the plan's source sequence, matching its authority-only,
state-independent cancellation semantics.

`verifier_transaction_builder` supplies the missing native proof-authorization
path without accepting any signer material. It validates an exact Tag-73 proof
length/frontier shape, computes the proof-body digest, encodes the canonical
600-byte transfer or withdrawal `ASVQ`, derives its verifier-owned receipt PDA,
and builds the exact proof create/init/960-byte upload, Tag-74 receipt init,
proof seal, Tag-75 receipt finalization, read-only verification and proof/receipt
close instructions. The finalized receipt address is carried directly into a
`PreparedSettlementRouteAccountsV1`; a relayer cannot substitute it when the
Pool `ASPP`/`ASPF` builders are used.

`registry_transaction_builder` likewise constructs no transaction or
signature. It derives the canonical registry and entry PDAs and freezes the
account order and privileges for initialization, scheduling, activation,
pause/unpause, release retirement and irreversible freeze. The native helper
pins the shared Tag-73 profile, release and statement version; the generic
release-rotation path rejects zero bindings, aliases, same-release retirement
and cross-profile replacement before exposing an instruction to a multisig.

`wallet_transition` explicitly matches a recovered input owner key to a local
nullifier/spending key, derives only the public nullifier in zeroized
temporaries, enforces local value/asset conservation, and prepares recipient
and change openings plus the exact public statements. No spending/nullifier
secret is retained, formatted, encrypted or serialized. Transition-note HPKE
delivery is reconciled only after an authenticated finalized `ASTR` supplies
the actual leaf index. Finalized transition evidence carries the authenticated
public nullifier and output IDs so a note store can atomically mark the input
spent and reverse that update by rollback ID.

`witness_state` maintains current authentication paths for locally owned notes
without trusting an indexer or retaining the complete tree. For an old index
`i` and new append index `n`, it updates exactly the sibling at
`msb(i XOR n)` from the canonical carry/padding computation, then recomputes
every tracked path to the authenticated root before committing. New owned
leaves receive their exact insertion path from the pre-append frontier;
recovered paths supplied by an indexer are accepted only if they recompute to
the complete authenticated current root. Root/index/sequence mismatches leave
the tree and all paths unchanged, and callers can clone a complete witness
snapshot before starting a proof attempt.

`relayer` is a permissionless, no-sign/no-send operator boundary. It
revalidates an unsigned instruction against the pinned deployment/current root
sequence and binds its deterministic request id to the finalized observation
slot and SHA-256 of the exact authenticated Pool-state image. Its pure
admission gate fails closed on emergency pause, stale/future snapshots,
disabled instruction kinds, a mismatched operator payer, signer mismatch,
queue or inflight saturation, a global slot-window rate limit, excessive fee
estimates and insufficient post-fee reserve.
`ASPF` and `ASPX` have distinct opt-in policy switches. Their deterministic
requests bind and durably retain the finalized public `ASPP` validation
context, so restart repeats the same exact validator without retaining proof
or signing material.

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
The same atomic image carries an ordered, checksummed public plan-lifecycle
journal. Finalized `ASPP` inserts the authenticated plan, while `ASPF` or
`ASPX` removes the matching authority/core/shard identity. A retained fork
removes orphaned lifecycle events and therefore restores a plan whose closure
was rolled back. Pruning folds old events into an anchor snapshot, keeping
active-plan state correct without extending the frozen `ASWS` scan-state ABI.

`DurableRelayerStateV1` persists the policy hash, slot-window counter, full
canonical request/snapshot/instruction, admission record and queued/inflight
status. Restart re-runs the frozen instruction validator and request-ID
derivation for every entry. Exact duplicate enqueue is idempotent; policy
drift, malformed lifecycle transitions, queue/inflight/rate/fee/reserve limits
and corrupt images fail closed before mutation.

`note_store_crypto` supplies the concrete authenticated-at-rest layer used by
the durable wallet. Each sealed opening is exactly 128 bytes:

```text
0..4      magic ASNS
4         version 1
5         flags 0
6         XChaCha20-Poly1305 algorithm id 1
7         zero reserved
8..32     random 24-byte nonce
32..128   canonical 80-byte ASPN opening plus 16-byte authentication tag
```

The associated data binds the cipher/key-generation identifier, complete
108-byte finalized event identity and `ViewOnly`/`Spendable` access class.
Consequently a sealed note cannot be copied to another event or promoted to a
spendable record by editing the checksummed public image. Keys and decrypted
openings are zeroized on drop. `EncryptedLocalSpendAuthenticatorV1` opens only
a spendable note under that exact context, requests a zeroizing nullifier-key
copy from an HSM/OS-keystore boundary keyed by the public owner digest, and
recomputes the finalized public nullifier. Neither the at-rest key nor a
nullifier key is serialized by this crate. The caller supplies the CSPRNG and
protects and backs up the uniformly random at-rest key.
`rotate_wallet_note_store_key_v1` authenticates every old record, prepares
every replacement, and atomically advances all ciphertexts and the durable
key-generation identifier in one fsync/rename commit; any wrong key, malformed
record or incomplete replacement leaves the wallet image unchanged.

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
- retain and audit the Pool program's instructions-sysvar guard that rejects
  inner invocation, keeping every successful mutation visible to this
  top-level instruction scanner;
- protect and back up the authenticated note-store keys represented by
  `note_cipher_id`, implement the HSM/OS-keystore lookup behind
  `LocalNullifierKeyStoreV1`, and archive returned public root/transition
  evidence if the operator requires a longer audit trail than the rollback
  window;
- provide retry, missed-history/backfill, multi-RPC disagreement, retained
  rollback-window sizing, monitoring and backup policy;
- derive the 32-byte viewing-key IKM from protected wallet entropy with explicit
  domain separation, use a CSPRNG for encryption, back up keys and zeroize
  caller-owned secret copies;
- feed an accepted proof from the approved prover into the pinned native
  authorization builder, integrate hardware/remote signer custody, per-origin
  abuse controls and transaction submission/confirmation reconciliation (the
  library owns no signer and already persists and enforces the public global
  fee/reserve/queue/inflight/rate-window gate);
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
