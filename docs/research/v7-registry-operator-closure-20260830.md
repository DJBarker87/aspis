# V7 registry/operator closure and deployment-identity gate

Date: 2026-08-30

Status: current V1 registry/operator semantics and selected-verifier result
binding are source-tested and kernel-checked. ProgramData, upgrade-authority
and executable-code identity are a hard mainnet activation blocker.

## Current exact on-chain guarantee

The registry program has seven canonical operations:

| Operation | Exact account shape | Successful mutation |
| --- | --- | --- |
| initialize | registry, authority, payer, System | creates one canonical registry, generation 0 |
| schedule | registry, fresh entry, authority, payer, System | creates a pending exact program/profile/release/version entry and increments generation |
| pause/unpause | registry, authority | changes only global pause state and generation |
| activate | registry, entry, authority | changes pending to active after its slot and increments generation |
| retire | registry, retiring, read-only replacement, authority | retires one active release only in favour of an active same-pool/policy/profile/version, different-release replacement |
| freeze | registry, authority | sets immutable, zeroes authority and increments generation |

Every mutation authenticates exact account count and uniqueness. Authority is
an exact read-only signer; registry/entry accounts are canonical program-owned
PDAs with exact codecs. Initialize/schedule authenticate a system-owned
writable signer payer and the exact read-only executable native System
Program. Generation arithmetic and activation delay arithmetic are checked.
The two-account commits obtain both mutable borrows before changing either
image; runtime CPI failure relies on normal Solana transaction rollback.

The Pool then authenticates exactly one active entry under its policy and
current slot. It binds the selected verifier program, profile, release and
statement version. The verifier account must be the selected key, executable,
read-only, nonsigner and owned by legacy BPF, upgradeable BPF or loader-v4. The
proof must be read-only/nonsigner and owned by that verifier. The Pool clears
return data before CPI and accepts only the selected program's exact 792-byte
canonical ASR8 result with the expected semantics before any Pool write.

The new focused adversarial tests cover spoofed payer/System shapes,
cross-policy and malformed entries, all three supported loaders, wrong
program/loader/privileges, CPI failure, missing return, wrong return program,
wrong length and malformed ASR8. Rejected paths preserve every supplied byte
image in the focused tests.

## What V1 does not prove

The 32-byte release binding is SHA-256 of the protocol/profile inventory
preimage in `tag73_pair_forest_profile.rs`. It is not the SBF executable hash.

Neither registry scheduling nor Pool dispatch receives an upgradeable-loader
ProgramData account. Therefore neither path proves:

- the Program account points to a particular ProgramData account;
- the ProgramData upgrade authority is absent or equals an approved key;
- the currently deployed executable bytes hash to the release artifact;
- the executable stayed unchanged between registry scheduling and spending.

Registry freeze is not program freeze. A frozen V1 registry can still select a
program whose upgrade authority changes its code. External release manifests
and startup checks are valuable operational evidence, but they are not an
on-chain cryptographic guarantee. For the intended mainnet standard this is a
hard blocker, superseding the earlier description of an on-chain ProgramData
check as optional defence in depth.

Lean makes this boundary executable:

```text
current_v1_selection_is_independent_of_programdata_code_hash_and_authority
```

Changing arbitrary ProgramData address, code hash, authority or immutability
evidence cannot change the translated V1 decision because none is an input.

## Smallest safe V2 closure

The production profile should accept only permanently immutable verifier
deployments. Allowing a live upgrade authority would permit code replacement
under an already-active entry; merely rechecking that the authority key is the
same does not bind code.

### Account-list changes

Add a new `ScheduleProfileV2` operation with seven accounts:

```text
[registry_v2, fresh_entry_v2, authority, payer, System,
 verifier_program, deployment_metadata]
```

For upgradeable BPF, `deployment_metadata` is the ProgramData account derived
from the Program account. The registry must parse both loader states, require
the exact pointer, require `upgrade_authority_address = None`, isolate the
canonical executable payload after the 45-byte ProgramData header, hash it and
compare it with the instruction's expected hash. Legacy BPF is already
immutable and hashes the Program account data. Loader-v4 needs its own tagged
state parser and an equivalent permanent-immutability check; it must not reuse
upgradeable-loader offsets.

Under this immutable-only rule, the one-terminal Pool account list does not
need another ProgramData meta on every spend. The registry-owned V2 entry is a
one-time certificate over a deployment which the loader can no longer mutate.
Pool dispatch must reject V1 entries for the hardened production policy and
require the V2 immutable-deployment flag. A defence-in-depth terminal
ProgramData meta is possible, but without rehashing the code it adds no code
identity and is not the minimal closure.

### Exact V2 entry image

Use a new magic/version and seed; never reinterpret 192 V1 bytes as V2. A
320-byte fixed image is sufficient:

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | magic, version, status, statement version, deployment mode |
| 8 | 32 | Pool |
| 40 | 32 | verifier Program |
| 72 | 32 | profile binding |
| 104 | 32 | release binding |
| 136 | 32 | loader Program |
| 168 | 32 | deployment metadata / ProgramData address |
| 200 | 32 | executable payload SHA-256 |
| 232 | 32 | expected upgrade authority; all zero for production immutable mode |
| 264 | 8 | activation slot |
| 272 | 8 | retirement slot |
| 280 | 32 | policy binding |
| 312 | 8 | flags and zero reserved bytes |

This is exactly 128 bytes larger than V1. `ScheduleProfileV2` adds the expected
32-byte executable hash to the instruction, taking its fixed data from 128 to
160 bytes. Entry PDA seeds should use `aspis-verifier-entry-v2`; a V2 registry
seed/version is required when migrating an already-frozen V1 registry.

### Builder and compatibility changes

Operator builders must derive the loader-specific metadata address, add the
verifier and metadata accounts, calculate the canonical payload hash and build
the V2 instruction. Pool transaction builders keep the existing verifier meta
and select a V2 registry/entry pair; no proof, ASQ8, ASF8, ASR8 or cryptographic
statement byte changes are needed.

V1 decoders and PDAs remain frozen for archival replay. A mutable pre-release
registry may schedule V2 beside V1, wait the activation delay, switch the Pool
policy to V2-only and retire V1. An immutable V1 registry cannot be upgraded;
it needs a new V2 registry PDA and the Pool's governed policy migration. There
must be no fallback from a malformed/missing V2 entry to V1.

### CU and TxV1 impact

These are estimates, not measurements:

- An upgradeable Tag-73 ProgramData account is about 1.2 MB. The pinned Agave
  cost model records SHA-256 base cost 85 CU and byte cost 1 CU, so one full
  payload hash is roughly 1.15–1.20M CU before registry parsing and account
  creation. It may fit a one-time 1.4M-CU schedule transaction, but the margin
  is tight and must be measured.
- If that one-shot schedule does not fit, first remove the upgrade authority,
  then build a permissionless chunked attestation PDA over the now-immutable
  ProgramData. Each transaction hashes the next fixed chunk and advances a
  domain-separated rolling commitment; `ScheduleProfileV2` accepts only the
  finalized attestation. This adds setup transactions, not spend transactions.
- The terminal path only decodes 128 additional entry bytes and checks fixed
  fields. Expected incremental cost is low single-digit kCU; treat that as a
  static estimate until the combined SBF path is measured.
- With address-table lookups, the two new schedule accounts add only account
  indices plus the 32 instruction bytes. Without lookup tables they add up to
  64 static-key bytes plus compiled indices, for an estimated schedule-packet
  increase of about 98–102 bytes. This is far below 4,096 bytes.
- The one-terminal private-transfer/withdrawal TxV1 sizes do not grow in the
  immutable-only design. The larger entry is account data, not packet data.

## Activation decision

Current V1 operator and selected-result semantics are green. Mainnet
activation remains blocked until V2 (or an equivalently strong immutable
deployment certificate) is implemented, source-bridged, measured and included
in the finalized devnet lifecycle.
