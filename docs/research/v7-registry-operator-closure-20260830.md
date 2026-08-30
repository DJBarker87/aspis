# V7 registry/operator closure and deployment-identity gate

Date: 2026-08-30

Status: V1 registry/operator semantics remain frozen and source/kernel checked.
The isolated Registry V2 runtime now adds immutable loader-v3 deployment
certificates for both the Registry program and every selected verifier, and
the Pool/Tag-73 registry readers fail closed onto the V2 account family when
the immutable-deployment policy bit is set. Focused Rust tests are green. SBF
measurement, operator-builder integration, refreshed Rust-to-Lean/Aeneas
source closure and finalized devnet evidence remain activation gates.

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

## What V1 still does not prove

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
hard blocker for any Pool policy which does not require Registry V2.

Lean makes this boundary executable:

```text
current_v1_selection_is_independent_of_programdata_code_hash_and_authority
```

Changing arbitrary ProgramData address, code hash, authority or immutability
evidence cannot change the translated V1 decision because none is an input.

## Implemented immutable-deployment V2

The production profile accepts only permanently immutable loader-v3
deployments. Allowing a live upgrade authority would permit code replacement
under an already-active entry; merely rechecking that the authority key is the
same would not bind code.

### Account-list changes

`InitializeV2` has six exact accounts:

```text
[registry_v2, authority, payer, System,
 registry_program, registry_programdata]
```

Before creating or writing the registry PDA, it authenticates the executing
Registry Program account as read-only, executable and loader-v3-owned; parses
its exact 36-byte `Program` state; derives and checks the linked ProgramData
PDA; parses the 45-byte ProgramData metadata; requires
`upgrade_authority_address = None`; hashes every byte of the loader-visible
executable payload; and compares that digest with the 32-byte expected
Registry executable hash supplied by the V2 initialization instruction. The
stored 256-byte registry image is therefore a certificate over the exact
immutable Registry deployment, not merely a self-reported program address.

Every subsequent V2 operator mutation rederives the Registry ProgramData PDA
from the executing program and loader-v3 ID. Entry mutations likewise require
the stored loader-v3 ID, the ProgramData PDA derived from the stored verifier
Program, and a zero expected upgrade authority. A corrupted deployment
certificate therefore fails before any registry or entry byte is changed.

`ScheduleProfileV2` has seven exact accounts:

```text
[registry_v2, fresh_entry_v2, authority, payer, System,
 verifier_program, deployment_metadata]
```

`deployment_metadata` is the ProgramData account derived from the Program
account. The implemented route applies the same exact loader state, PDA,
finalized-authority and executable-payload hash checks and compares the result
with the expected hash in the fixed V2 schedule instruction. V2 deliberately
rejects legacy BPF and loader-v4 rather than pretending their state layouts
share loader-v3 semantics.

Under this immutable-only rule, the one-terminal Pool account list does not
need another ProgramData meta on every spend. The registry-owned V2 entry is a
one-time certificate over a deployment which the loader can no longer mutate.
Pool dispatch rejects V1 entries for a policy carrying the new
`IMMUTABLE_DEPLOYMENT` flag and derives only V2 registry/entry PDAs. It checks
the stored Registry and verifier ProgramData PDAs against the loader-v3
derivation, requires a frozen/unpaused Registry, an active exact release, a
zero expected upgrade authority, and narrows the selected executable account
owner to loader-v3. The Tag-73 registry-only reader performs the same V2
selection. A defence-in-depth terminal
ProgramData meta is possible, but without rehashing the code it adds no code
identity and is not the minimal closure.

The terminal account list remains exactly `[registry, entry]`; proof,
ASQ8/ASF8/ASR8 and cryptographic relation bytes are unchanged.

### Exact V2 registry image

The new registry seed is `aspis-verifier-registry-v2`; V1 bytes are never
reinterpreted.

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 8 | magic, version, flags, immutable-loader-v3 mode, reserved |
| 8 | 32 | Pool |
| 40 | 32 | authority; zero after freeze |
| 72 | 32 | policy binding |
| 104 | 8 | generation |
| 112 | 8 | minimum activation delay |
| 120 | 32 | Registry Program |
| 152 | 32 | loader-v3 Program |
| 184 | 32 | Registry ProgramData PDA |
| 216 | 32 | exact Registry executable-payload SHA-256 |
| 248 | 8 | zero reserved bytes |

### Exact V2 entry image

The entry uses a new magic/version and `aspis-verifier-entry-v2` seed; 192-byte
V1 entries are never reinterpreted. Its fixed image is 320 bytes:

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

This is exactly 128 bytes larger than V1. `InitializeV2` is 112 bytes, adding
the expected Registry executable hash to the 80-byte V1 shape.
`ScheduleProfileV2` is 160 bytes, adding the expected verifier executable hash
to the 128-byte V1 shape.

### Builder and compatibility changes

The low-level Rust codecs and PDA derivations are implemented. The production
operator builder must still derive both ProgramData addresses, hash the exact
post-45-byte account payloads, add the two init-only or schedule-only accounts,
and emit the fixed V2 instructions. Pool transaction builders keep the
existing terminal account count and merely select a V2 registry/entry pair;
no proof, ASQ8, ASF8, ASR8 or cryptographic statement byte changes are needed.

V1 decoders and PDAs remain frozen for archival replay. A mutable pre-release
registry may schedule V2 beside V1, wait the activation delay, switch the Pool
policy to V2-only and retire V1. An immutable V1 registry cannot be upgraded;
it needs a new V2 registry PDA and the Pool's governed policy migration. There
must be no fallback from a malformed/missing V2 entry to V1.

### CU and TxV1 impact

These remain static estimates, not SBF measurements:

- An upgradeable Tag-73 ProgramData account is about 1.2 MB. Agave 4.2 charges
  SHA-256 base cost 85 CU plus `max(mem_op_base_cost, byte_cost * len / 2)` for
  one slice, with byte cost 1. The hash syscall itself is therefore roughly
  0.58–0.60M CU for a 1.15–1.20 MB payload, before account parsing and PDA
  creation. That should fit a one-time 1.4M-CU schedule transaction, but the
  complete instruction must still be measured.
- If that one-shot schedule does not fit, first remove the upgrade authority,
  then build a permissionless chunked attestation PDA over the now-immutable
  ProgramData. Each transaction hashes the next fixed chunk and advances a
  domain-separated rolling commitment; `ScheduleProfileV2` accepts only the
  finalized attestation. This adds setup transactions, not spend transactions.
- The terminal path only decodes 128 additional entry bytes and checks fixed
  fields. Expected incremental cost is low single-digit kCU; treat that as a
  static estimate until the combined SBF path is measured.
- With address-table lookups, the two init/schedule-only accounts add only
  account indices plus the 32 instruction bytes. Without lookup tables they
  add up to 64 static-key bytes plus compiled indices, for an estimated packet
  increase of about 98–102 bytes. This is far below 4,096 bytes.
- The one-terminal private-transfer/withdrawal TxV1 sizes do not grow in the
  immutable-only design. The larger entry is account data, not packet data.

## Activation decision

The runtime V2 deployment certificate and terminal V2 selection are now
implemented and locally green. Mainnet activation remains blocked on:

1. production operator/builder integration and exact TxV1 packet evidence;
2. reproducible SBF builds plus measured V2 initialize/schedule/terminal CU;
3. refreshed Rust-to-Charon/Aeneas-to-Lean source bridges for V2 parsing,
   deployment authentication and caller selection;
4. finalized devnet initialization, schedule, activation/freeze, successful
   spend, adversarial mutation and rollback receipts.

Until those gates are frozen, the hardened policy bit stays default-off and
V1 remains available only for archival/backward-compatible replay.
