# Pool V1 pure-kernel boundary

This directory freezes the Pool V1 hash/tree/history primitives and implements
the pure append-only Merkle/root-history kernel plus the P2 deposit receipt
format. It does not reinterpret the 80-byte `AtomicPoolStateV2`, alter Tag 73
or V7 proof cryptography, access Solana accounts, invoke token CPI, or
implement spend/withdrawal.
For release isolation, `aspis_statement::pool_v1` is compiled on hosts and on
SBF only when the opt-in `pool-v1-kernel` feature is enabled. The separate
`aspis-pool` crate enables it; frozen verifier builds do not.

## Frozen primitive bindings

- Note leaf: existing spendable note commitment, format 2.
- Nullifier: existing spend nullifier derivation, format 1.
- Internal node: existing `merkle_node_compress_v3`, tree-hash version 3.
- Digest: eight canonical little-endian M31 limbs, 32 bytes, encoding 1.
- Tree: binary depth 20, capacity 1,048,576 leaves.
- Empty leaf: zero digest. Empty roots are derived recursively with the same
  v3 parent hash; they are not independent constants.
- Root history: sequence zero is the empty root; leaf `i` creates sequence
  `i + 1`; 256 roots per page.

`POOL_V1_FORMAT_BINDING` pins these choices. Any incompatible change requires
a new format/version rather than a reinterpretation of Pool V1 bytes.

## Exact component account images

| Component | Bytes | Image |
| --- | ---: | --- |
| Pool identity | 144 | `ASPI`, v1, pool, mint, token program, canonical asset id, deployment domain |
| Verifier policy | 104 | `ASPP`, v1, flags, registry program/authority, stable policy binding |
| Verifier registry | 128 | `ASRG`, v1, Pool, authority/policy, generation, activation delay |
| Verifier entry | 192 | `ASRE`, v1, Pool, verifier/profile/release, statement version and active interval |
| Deposit receipt | 224 | `ASPD`, v1, Pool/mint/source/vault, exact u32 amount, payload length, commitment/index/root |
| Historical-anchor envelope | 208 | `ASPA`, v1, transition kind, Pool/domain, sequence/root/nullifier, verifier profile/release |
| Consumed-nullifier marker | 208 | `ASNM`, v1, transition kind, Pool/domain/nullifier, retained sequence/root, verifier profile/release |
| Verifier-dispatch request | 384 + L (385..1,024) | `ASVQ`, v1, 384-byte binding prefix plus exact profile statement payload |
| Verifier success result | 384 | `ASVS`, v1, exact success code and byte-identical binding prefix, without payload |
| Incremental tree | 688 | `ASPT`, v1/depth/hash/encoding, next index, root, 20 frontier digests |
| Root-history page | 8,256 | 64-byte `ASPR` v1 header and 256 canonical roots |

Reserved bytes must be zero. Unused root-history slots must be zero digests.
An inactive tree-frontier slot at level `h` must equal recursive empty root
`E_h`; it is live if and only if bit `h` of `next_leaf_index` is one.

The future root-page PDA descriptor is exactly:

```text
[b"aspis-pool-root-page-v1", pool[32], page_number.to_le_bytes()]
```

The owning Pool program id remains a program-integration choice and is not
part of this Solana-independent kernel.

## Append and terminal-state boundary

`append_one` performs the standard binary carry: clear consecutive live low
slots, hash each stored left subtree with the right-hand carry, and write only
the first carry-stop slot. `append_two` checks capacity for both leaves before
the first transition, so a one-slot remainder fails without exposing a state
that callers could persist.

At `next_leaf_index == 2^20`, the final carry is the depth-20 root and all 20
stored frontier slots are inactive. The 688-byte image has no level-20 witness,
so it cannot independently reconstruct that terminal root. Program integration
must create the full state only via the final atomic append and, on reload,
authenticate and compare it with retained root sequence 1,048,576 at page 4096,
slot 0. `validate_terminal_root_against_history` provides the digest check; it
does not authenticate the future Solana account.

The never-deployed format revision one embedded a single verifier release.
Revision two replaces it with `VerifierPolicyV1`; the `ASPP` policy magic,
Pool format revision and enclosing state-account version all differ, so draft
revision-one bytes fail closed rather than being silently reinterpreted.

Registry accounts are canonically addressed under the policy's registry
program:

```text
[b"aspis-verifier-registry-v1", pool]
[b"aspis-verifier-entry-v1", pool, profile_binding, release_binding]
```

An entry authorizes only one exact verifier/profile/release and statement
version during its active slot interval. It never authorizes a raw tree write.
Policy flag bit 0 requires an immutable registry and zero authority. Registry
flag bits 0/1 mean paused/immutable; all other bits fail. Entry statuses are
0 pending, 1 active, 2 paused and 3 retired. `u64::MAX` is the sole encoding
for no retirement slot; a finite retirement slot must be strictly after
activation and is exclusive at authorization time. Mutable registries require
a nonzero authority and every registry pins a nonzero activation delay.

The P2 receipt has a fixed 224-byte encoding and is paired with at most 512
opaque encrypted-note bytes, for a maximum 736-byte return/event record. It
requires a nonzero amount below the existing 30-bit `VALUE_LIMIT`, canonical
commitment/root digests and `root_sequence = leaf_index + 1`. Payload length is
framed in the receipt; payload content is deliberately not an input to the
frozen note commitment.

The P3a historical-anchor envelope has an exact 208-byte encoding:

```text
0..4      magic ASPA
4         envelope version 1
5         transition kind: 1 private transfer, 2 withdrawal
6         digest encoding version 1
7         zero reserved
8..40     Pool address
40..72    deployment domain
72..80    anchor root sequence u64 LE
80..112   canonical anchor root digest
112..144  canonical nullifier digest
144..176  verifier profile binding
176..208  verifier release binding
```

Deposit is intentionally not a transition kind because it consumes no private
input. Unknown kinds, zero Pool/domain/profile/release bindings, sequences
above the depth-20 terminal sequence and noncanonical digests fail closed.
Output commitments, fee and withdrawal data belong to separately versioned
transition bodies; they are not silently added to this common envelope.

The P3b occupied nullifier-marker account is also exactly 208 bytes, but uses
distinct `ASNM` magic so it cannot be confused with the statement envelope:

```text
0..4      magic ASNM
4         marker version 1
5         transition kind: 1 private transfer, 2 withdrawal
6         digest encoding version 1
7         zero reserved
8..40     Pool address
40..72    deployment domain
72..104   canonical nullifier digest
104..112  retained anchor sequence u64 LE
112..144  canonical retained anchor root
144..176  verifier profile binding
176..208  verifier release binding
```

Its sole PDA seed schedule is:

```text
[b"aspis-pool-nullifier-v1", pool, canonical_nullifier_encoding[32]]
```

The marker is an exact field copy of the accepted common anchor envelope. A
program-owned all-zero 208-byte account is an unconsumed preparation state,
not a valid marker image. A data-empty System-owned PDA is the other fresh
form handled by the later program/CPI layer.

The P3d verifier request is a fixed 384-byte binding prefix followed by the
complete canonical profile-specific statement payload. The success result is
exactly the 384-byte prefix and does not repeat the payload. Both images share
the following header-independent binding at offsets 16..384:

```text
16..48    selected verifier program
48..80    verifier profile binding
80..112   verifier release binding
112..144  Pool address
144..176  deployment domain
176..184  retained anchor sequence u64 LE
184..216  canonical retained anchor root
216..248  canonical nullifier
248..280  profile-specific complete statement digest
280..312  domain-separated SHA-256 of exact 208-byte ASPA envelope
312..344  proof-account key
344..376  raw SHA-256 of the declared proof body
376..380  declared proof-body length u32 LE
380..384  exact statement-payload length L u32 LE
```

The 16-byte request header is `ASVQ || contract-v1 || statement-v1 || kind ||
SHA256-v1 || verify-code-u32 || statement-digest-v1 || zero[3]`; the result
replaces `ASVQ` with `ASVS` and the verify code with exact success code
`0x41530001`. `ASVQ` must have exact total length `384 + L`, with
`1 <= L <= 640`; zero, mismatch, trailing bytes and larger requests fail
closed. Thus the largest accepted request is 1,024 bytes. `ASVS` echoes both L
and the statement digest but remains exactly 384 bytes.

The Pool derives the statement digest itself; there is no separately supplied
digest input. Its frozen preimage is:

```text
SHA256(
  "aspis/pool-v1/profile-statement-payload-digest/v1" ||
  statement-digest-version-u8 || statement-version-u8 ||
  selected-profile[32] || selected-release[32] || L-u32-le || payload[L]
)
```

Encoding and decoding recompute that digest from the exact payload. The result
repeats every other binding field, the digest and L. Therefore one result
cannot authenticate two distinct payloads unless the approved SHA-256
collision boundary occurs; hash injectivity is not assumed. The proof digest
excludes the frozen 40-byte `ASPU || length || zeroed-upload-authority`
header.

Payload parsing and semantics are dispatched by the registry-selected profile
and release. This common contract deliberately does not identify the current
same-path Tag-73 statement bytes with the future Pool historical-anchor
profile, and a future 1-to-2 relation requires its own profile/release and
canonical payload definition.

`ASVS` is selected as Solana return data. Its exact 384-byte length is below
the 1,024-byte runtime ceiling. The separate `aspis-pool` P3e source now clears
the Pool return-data buffer, performs one selected read-only CPI, snapshots
return data on the immediately following operation, and checks both the
returning program id and all 384 bytes. The 1,024-byte `ASVQ` ceiling is a deliberately
conservative contract cap; current Solana CPI instruction data permits more,
but an outer transaction still has a 1,232-byte packet budget. A profile near
the 640-byte payload cap therefore cannot be assumed to fit inline after
accounts/signatures and may need account-backed sourcing. This module does not
invoke a verifier or call return-data syscalls.

## Intended program integration

A new Pool V1 instruction/account layer should decode these components after
checking owner, PDA, exact length, magic, version, and reserved bytes. The
separate `aspis-pool` crate now composes the frozen note hash with one exact
legacy SPL Token transfer and one append, but still has no entrypoint. Existing
atomic-v2 and Tag-73 paths remain separate and frozen.

The Lean modules under `AspisFormal/Pool` prove the format arithmetic, generic
carry count/full-boundary behavior, chronological leaf ordering, recursive
empty-root construction, and history indexing. The incremental-tree proof uses
a non-circular block witness: every live level-h slot is the perfect root of
its exact chronological `2^h`-leaf block. From that witness it proves genesis,
one-append invariant preservation and exact padded-root correctness, old-leaf
prefix preservation, sequential two-append correctness, and the terminal
full-tree root. It intentionally leaves one named source boundary: instantiate
the abstract parent operation with production Poseidon-v3 and establish the
Rust codec/source refinement. `Pool/DepositV1.lean` additionally proves that a
successful deposit appends exactly one deterministic note and root while
adding the same public amount to vault and ghost unspent value, preserves vault
conservation, ignores opaque payload content and fails closed in the abstract
unsuccessful-transfer branch. Token CPI and runtime rollback remain explicit
source/runtime boundaries. `Pool/HistoricalAnchorV1.lean` proves that exact
sequence/root retention and old-leaf prefix membership survive arbitrary later
root/leaf appends, and that an already valid membership predicate at the old
root remains a valid historical authorization premise. Concrete Poseidon-v3
history persistence and the Rust/account codec remain named source-refinement
boundaries. `Pool/NullifierMarkerV1.lean` separately proves fail-closed
planning and `fresh_nullifier_consumed_once` for both admitted fresh account
forms. It requires no PDA-injectivity assumption: any occupied marker blocks a
second use. System CPI, rent, locking/rollback and Rust byte refinement remain
explicit boundaries. `Pool/VerifierDispatchV1.lean` proves the request-size
cap, the fixed result-size cap, exact selected-program/code/binding equality,
and that one result accepted for two distinct exact payloads implies the
explicit approved-hash collision event and equal payload lengths. It derives
substitution rejection only under the named no-collision premise. The P3e
extension proves the abstract exact clear/invoke/capture order, that a missing
callee result cannot reuse stale data, and that every runtime outcome leaves
the abstract Pool state unchanged. SHA-256 collision resistance/source
refinement, profile-specific canonical parsing, loader semantics, Solana CPI/
return-data semantics, selected-verifier implementation and final atomic
composition remain explicit boundaries.
