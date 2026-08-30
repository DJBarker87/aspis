# V7 release-evidence preflight results — 2026-08-30

These are the checks actually executed while preparing the release-evidence
rail:

- `input-audit.json`: the exact source, program feature aliases, toolchain
  inventory, fixtures and current-source LiteSVM worst-case evidence all match
  the frozen preflight manifest;
- `public-devnet-capability.json`: a signer-free, read-only finalized devnet
  probe found TxV1 RPC decoding support but no feature account or activation
  slot, so the public-devnet rail stopped before simulation.

No Linux SBF build or Agave 4.2+ suite is represented here. The local machine
is Darwin arm64, the available local validator is below 4.2, and the complete
eleven-case bundle is not checked in. Those are recorded as open gates rather
than replaced with LiteSVM measurements or component sums.
