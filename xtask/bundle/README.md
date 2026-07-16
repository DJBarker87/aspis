# aspis-spend q18/g37 mainnet-beta release v1

This is a self-contained, offline-verifiable bundle for the finalized
aspis-spend q18/g37 mainnet-beta execution. It contains the exact proof and
public statement that were verified on-chain, the byte-for-byte SBF verifier
that ran, the machine-checked release certificate and its three supporting
theorem artifacts, the finalized execution and cleanup evidence, and the
publication paper. `manifest.json` and `SHA256SUMS` pin every byte, and
`verify.sh` checks the whole bundle without a network connection.

## The finalized transaction

The single atomic transaction that verifies the finalized proof and commits
the nullifier marker plus pool-state mutation is
`3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv`.
It finalized at slot `433219840` and consumed `1,344,003` compute units. View
it with the cluster-pinned
[Solana Explorer](https://explorer.solana.com/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet-beta)
or
[Solscan](https://solscan.io/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet)
links.

Deployed program: `GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3`. Pool
account: `3ZRYarQZcWJQgzNwLo1Eo7PDmier3rbW41L8ccAddCvb`. Nullifier account
committed by the transaction: `CFJ5fYPSi4Qn6okBCZS3tXFMw7Lsz4Jy9vEAAGU5kfSU`.
Deployment domain: `ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f`.

## Contents

- `proof/spend-q18-g37.bin` — the finalized 65,407-byte proof
  (`ASP0` container), sha256
  `32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529`.
- `proof/statement.json` — the witness-independent public statement.
- `program/aspis_verifier.so` — the deployed 924,344-byte SBF verifier
  (ELF), sha256
  `e289faf85fe4773880794d5d4356461bb9cb94077b68711f99348efe19707d7e`.
- `certificates/release.json` — the release certificate. It reports
  `released=true` with all release gates green.
- `certificates/spend_d_after_g_soundness_epro.json`,
  `certificates/spend_complete_good_product.json`,
  `certificates/spend_computational_hvzk_closure.json` — the three
  proof-independent theorem artifacts referenced by the certificate.
- `evidence/mainnet-execution.json` — the finalized executor record for the
  verify-and-apply transaction and its lifecycle.
- `evidence/mainnet-cleanup.json` — the finalized ProgramData cleanup and
  refund receipt.
- `evidence/spend_mainnet_sbf_and_instruction_reconstruction.json` — the
  byte-level reconstruction of the deployed SBF from the buffer's archival
  loader-write history, cross-checked between two independent RPC endpoints.
- `evidence/spend_mainnet_independent_rpc_reconciliation.json` — the
  deterministic two-endpoint reconciliation of the deployment, verification,
  and ProgramData-close records, and the cluster disambiguation.
- `tools/reconstruct_spend_mainnet_sbf.py` — the stdlib-only archival
  reproducer that regenerates both files from live RPC.
- `paper/aspis-spend.pdf` — the publication paper.
- `manifest.json` — object-by-object byte length and sha256, plus the pinned
  on-chain identities.
- `SHA256SUMS` — checksums for every file in the bundle.
- `verify.sh` — the offline verifier.

## Verify

From this directory:

```bash
./verify.sh
```

It requires only Bash, `jq`, and either `sha256sum` or `shasum`. It uses no
network access and no Solana toolchain. It checks every file against
`SHA256SUMS`, checks every `manifest.json` object's byte length and sha256,
asserts the proof `ASP0` header and the SBF ELF magic, asserts the
certificate reports `released=true` with all gates green, asserts the
evidence's finalized signature, slot, and compute units are the values above,
and scans the bundle for secret-key material, leaked local paths, and
explorer links that fail to pin a cluster. It prints `PASS` and exits 0 only
when every check agrees, and exits nonzero with a `FAIL` line otherwise.

## Note on the evidence files

`evidence/mainnet-execution.json` and `evidence/mainnet-cleanup.json` are the
immutable executor records, copied verbatim. They retain the operator's
absolute artifact paths exactly as recorded at generation time; those strings
are non-secret and are pinned by `SHA256SUMS` and `manifest.json`. No signing
key, funding record, or serialized signed-transaction bytes are included. The
deployed SBF is retained byte-for-byte and may contain non-secret compiler
and toolchain source-path strings.
