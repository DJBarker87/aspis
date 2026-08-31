# V7 Registry V2 operational release bundle

Status: **NO GO — not a deployable mainnet release candidate**.

This directory binds the green, signed Registry V2 one-transaction lifecycle
to its exact source, binaries, Tag-73 profile, statements, proofs and public
devnet feature preflight. It is an operational handoff, not authorization to
deploy.

The local result is strong: two isolated Linux builds produced byte-identical
Pool, verifier and Registry SBFs; four honest TxV1 transactions finalized below
1.3M CU; seven adversarial transactions finalized as failures with exact
protected-account rollback. No real funds or public cluster were used.

The measured binaries cannot yet be promoted. The Pool and Registry IDs are
audit constants, the verifier pins those IDs, and the tested verifier ID is a
historical V5 identity whose ProgramData was closed. Production identities and
their custody have not been selected. Changing those identities changes the
verifier binary and statement/proof bindings, so the affected formal, build,
runtime and public-devnet evidence must be regenerated.

Public devnet is independently blocked: the TxV1/4KiB feature account was
absent at finalized slot 491,160,606 on 31 August 2026. The gate fails closed
and no public lifecycle was attempted.

## Contents

- `manifest.json` — machine-readable source, binary, profile, runtime,
  authority, operations and blocker inventory.
- `statement-inventory.json` — exact ASQ8, reconstructed ASF8, ASR8, proof
  account, candidate and proof-body hashes for the four honest cases.
- `runbook.md` — staged deployment, immutability, Registry V2 and rollback
  ceremony. Every write command is disabled by prerequisites in this bundle.
- `verify.sh` — offline, read-only verification of the frozen objects and
  evidence. It intentionally finishes with `releaseDecision=NO_GO`.

The human-readable readiness report is
[`docs/research/v7-registry-v2-mainnet-readiness-20260901.md`](../../docs/research/v7-registry-v2-mainnet-readiness-20260901.md).

## Read-only replay

From the repository root:

```sh
release/v7-registry-v2-mainnet-rc1/verify.sh
```

This does not build, sign, submit, deploy, contact an RPC, or rerun the
eleven-case lifecycle. A full rebuild/runtime replay is required only after a
release-affecting source, identity, binary, profile, statement or proof change.

## Promotion rule

Do not rename this bundle `GO`, use its SBFs for custody, or execute its write
templates. Promotion requires every P0 blocker in `manifest.json` to be closed,
the manifest regenerated against the exact production identities, and a new
explicit human mainnet authorization after the irreversible authority/freeze
ceremony has been reviewed.
