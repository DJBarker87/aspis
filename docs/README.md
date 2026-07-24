# Documentation

Start with the repository [README](../README.md). It presents Aspis as one
connected evidence chain:

- Lean proofs check substantial parts of the private-spend mathematics.
- Charon and Aeneas bring selected production Rust into Lean, where bridge
  proofs connect it to the maintained models.
- Pinned source and build tools reproduce the exact compiled Solana program.
- Finalized chain records show what the program actually executed.

V5 currently completes this chain through a finalized devnet transaction. Its
mainnet transaction is pending. The earlier q18/g37 release is the existing
finalized mainnet feasibility result.

## Start here

- [README](../README.md): the result, evidence chain, formal coverage, and
  reproduction entry points
- [how Aspis works](how-it-works.md): the private-spend proof, proof-account
  upload, and all-or-nothing state update
- [how Aspis is formally checked](formal-verification.md): the mathematical
  proof layer, the Rust-to-Lean connection, and the exact current scope
- [formal proof status](../AspisFormal/README.md): the detailed Lean theorem
  table
- [Rust-to-Lean proof status](../aeneas-verif/README.md): exact Charon/Aeneas
  coverage and the remaining transcript-hash boundary
- [code map](code-map.md): concept-to-file navigation and production entry
  points
- [security assumptions](assumptions-ledger.md): the cryptographic,
  translation, compiler, and runtime trust boundary
- [paper source](../paper/aspis-spend/): the complete construction and
  security argument

## Chain evidence and history

- [q18/g37 mainnet demonstration](mainnet-demo.md): finalized mainnet-beta
  execution, lifecycle signatures, and compute use
- [V5 release preflight](../release/preflight/v5-production-freeze.md):
  current candidate identity, formal evidence, reproducible build, and
  finalized devnet record
- [novelty re-scan, 2026-07-13](novelty-rescan-2026-07-13.md): dated
  public-evidence search for the claim shape; machine-readable companion
  alongside it
- [design history](design-history.md): what the default branch keeps and
  where the research archive tags live

The q18/g37 release evidence and certificates are frozen in the
offline-verifiable bundle at
[`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/);
run its
[`verify.sh`](../release/aspis-spend-q18-g37-mainnet-v1/verify.sh) to check
every byte, the release-certificate gates, and the finalized on-chain
signature, slot, and compute units offline. The complete relation and account
model are specified in the paper.
