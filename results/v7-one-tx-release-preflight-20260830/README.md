# V7 release-evidence preflight results — 2026-08-30

These are the checks actually executed while preparing the release-evidence
rail:

- `input-audit.json`: atomic-marker source `da77d5f5`, program feature aliases,
  toolchain inventory and the deterministic eleven-case fixture all match the
  frozen preflight manifest; the Pool SBF and fresh combined CU are explicitly
  null/pending rather than inherited from the superseded Pool source;
- `public-devnet-capability.json`: a signer-free, read-only finalized devnet
  probe found TxV1 RPC decoding support but no feature account or activation
  slot, so the public-devnet rail stopped before simulation.

The public-devnet observation predates the marker-source advance and is retained
only as an exact signer-free capability observation; no new public probe was
needed to freeze local fixtures. No Linux SBF build or Agave 4.2+ suite is
represented here. The local machine is Darwin arm64 and the available local
validator is below 4.2. The complete eleven-case template is now checked in,
but deliberately lacks a Pool SBF binding until a capped dual Linux build from
`da77d5f5` succeeds. These are recorded as open gates rather than replaced with
LiteSVM measurements or component sums.
