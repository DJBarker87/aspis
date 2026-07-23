# Aspis V5 Tag 67 — frozen mainnet candidate

This bundle pins the exact V5 verifier prepared for Tag-67 mainnet
deployment. It brings the production SBF, clean-source byte-parity record,
selector proofs, accepted-input compute envelope, formal entry points,
assumptions ledger, and finalized devnet rehearsal into one offline-verifiable
release object.

The candidate is source-reproducible, formal-closure backed, and comfortably
inside Solana's transaction limit:

| Item | Frozen value |
| --- | --- |
| SBF SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |
| SBF size | 1,258,496 bytes |
| Clean-source commit | `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` |
| Accepted-input CU ceiling | 1,353,616 CU |
| Headroom below 1.4M | 46,384 CU |
| ProgramData allocation minimum | 1,258,496 bytes |
| Recommended fresh allocation | 1,300,000 bytes |

A clean manifest-default build from the public source commit reproduced the
frozen SBF byte for byte. The provenance record binds 77 source identities and
91 toolchain identities. The CU policy covers all three selectors, both
marker modes, and the maximum topology accepted by the frozen grammar.

This is the exact-deployment handoff for V5. It is separate from the earlier
Tag-65 q18/g37 mainnet result and does not claim that a V5 mainnet transaction
has already occurred.

## Devnet rehearsal

`evidence/devnet-execution.json` records the finalized execution of this exact
SBF through the atomic Tag-67 path. It binds the deployed program, pool, sealed
proof account, canonical nullifier, finalized transaction, landed compute
units, retained proof bytes, and rejected duplicate-spend replay.

The atomic verify-and-apply transaction
[`38mNKeMm…WtEuLC`](https://explorer.solana.com/tx/38mNKeMmRf9Ttqmde8jZqCMq8F1piHhCEqGYVYrSHEggTu21C93wWAEhoDkZ2qJHeTX7j3qCmibNNmZ6awWtEuLC?cluster=devnet)
finalized at slot `478299357` and consumed `1,335,952` CU.

| Devnet account | Address |
| --- | --- |
| Program | `EZYH9FFDGj9gSacmDhvYBqPAzcSm9cfURwuz1CtzQRFS` |
| Pool | `5HtT94qnUNU1gfWsjGm7786hwi15Ky4qEByuRc5Qzmt` |
| Sealed proof | `Er5ocNK2QHDxRL2pahqvXGE91ku39T9Q5pFJHgkfQ6DX` |
| Nullifier marker | `F4wakJYuP18URA1HnwJZjW3GjY91jWDWwWRnbp9hCQAH` |

The rehearsal proof and public statement are retained under `proof/devnet/`.
`manifest.json` binds their identities to the execution record.

## What is in the bundle

- `program/aspis_verifier_v5_tag67.so` — the 1,258,496-byte frozen SBF.
- `provenance/build-provenance.json` — the sanitized 77-source and
  91-toolchain build inventory.
- `provenance/source-parity-attestation.json` — the clean public-source
  rebuild and byte-parity record.
- `proof/selector-{0,1,2}/` — the three retained selector fixtures and public
  statements.
- `proof/devnet/` — the exact proof and statement used in the finalized
  devnet rehearsal.
- `evidence/accepted-topology-cu-policy.json` — the derivation of the
  1,353,616-CU accepted-input ceiling.
- `evidence/selector-*-marker-*.json` — repeated selector and marker-mode
  runtime measurements.
- `evidence/devnet-execution.json` — finalized atomic execution and replay
  evidence.
- `formal/ENTRYPOINTS.md` — the combined capstone, Component-C public-output,
  and Tag-67 verifier theorem entry points with pinned source hashes.
- `ASSUMPTIONS.md` — one compact ledger for the cryptographic, translation,
  compiler, and runtime boundaries.
- `manifest.json` and `SHA256SUMS` — object-level sizes and hashes.
- `verify.sh` — the offline bundle verifier.

## Verify

From this directory:

```bash
./verify.sh
```

The verifier requires Bash, `jq`, and either `sha256sum` or `shasum`. It uses
no network access and no Solana toolchain. It checks every checksum and
manifest object, the exact SBF identity, all four V5 proof containers,
clean-source parity, the accepted-input CU ceiling, finalized devnet state
transition and replay rejection, and the absence of signing material or local
operator paths.

A successful run ends with:

```text
PASS: Aspis V5 Tag-67 frozen-candidate bundle verified offline
```

## Formal closure

The combined Lean 4.32 capstone joins:

- Component A source correspondence at the frozen schedule, with runtime
  GoodA and GoodB recomputation on every selected branch;
- Component B maintained correspondence;
- Component C's extracted evaluator, four runtime rounds, finalization,
  packer, and exact public output; and
- Tag-67 wire parsing, digest predicate, and all six ordered work checks.

The Tag-67 implementation boundary is one explicit hash-application equation
over `DOM_GRIND || nonce_le64`. Parser, projection, predicate, six-step
execution, and Component-C public output are inside the theorem conclusions.
The audited capstones use only
`{propext, Classical.choice, Quot.sound}`.

The theorem names, source locations, source hashes, and replay entry points
are collected in [`formal/ENTRYPOINTS.md`](formal/ENTRYPOINTS.md). The
remaining trusted boundaries are stated once in
[`ASSUMPTIONS.md`](ASSUMPTIONS.md).
