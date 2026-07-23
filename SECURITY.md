# Security

Please report vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact.

The supported research surface is the current `main` branch. Public issue
reports are appropriate for non-sensitive correctness or reproducibility
problems.

## Review status

The repository contains formal proofs, source-authentic Aeneas correspondence,
independent rank checkers, hostile-path tests, binary provenance, and
reproducible chain evidence. It has not yet received an external security
audit or a published coverage-guided fuzz campaign.

The current trust boundary is kept in
[`docs/assumptions-ledger.md`](docs/assumptions-ledger.md).

For a Solana review, start with the Tag-67 dispatch and atomic transition in
`programs/aspis-verifier/src/{dispatch,v5_full_transaction}.rs`, then the
accepted-input compute analysis in
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).
The two best cryptographic review targets are:

1. The complete affine-image reconstruction and hybrid argument behind the
   hiding floors. `tools/verify_hiding_ranks.py` independently reproduces the
   eight rank claims; the mapping from the complete execution view to that
   linear model remains the cryptographic proof obligation described in the
   paper.
2. The custom Poseidon2-M31 commitments and two-to-one Merkle compression in
   `crates/aspis-statement/src/poseidon2.rs`. Constants, domain separation, and
   wrapper outputs are pinned by CI and known-answer tests; their cryptographic
   security remains an explicit primitive assumption.

The historical q18/g37 review is
[`docs/reviews/prepublication-security-review.md`](docs/reviews/prepublication-security-review.md).
The current V5 release gate is
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).
