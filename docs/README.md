# Documentation

Start with the [paper source](../paper/aspis-spend/) and the repository
[README](../README.md). Current documents:

- [mainnet demonstration](mainnet-demo.md) — the finalized mainnet-beta
  execution, lifecycle signatures, and cost
- [code map](code-map.md) — concept-to-file navigation and the naming
  conventions
- [novelty re-scan, 2026-07-13](novelty-rescan-2026-07-13.md) — dated
  public-evidence search for the claim shape; machine-readable companion
  alongside it
- [design history](design-history.md) — what the default branch keeps and
  where the research archive tags live

The release has executed. Its evidence and certificates are frozen in the
offline-verifiable bundle at
[`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/);
run its
[`verify.sh`](../release/aspis-spend-q18-g37-mainnet-v1/verify.sh) to check
every byte, the release-certificate gates, and the finalized on-chain
signature, slot, and compute units offline. The complete relation and account
model are specified in the paper.
