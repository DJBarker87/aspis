# Security

Please report vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact.

The supported research surface is the current `main` branch. Public issue
reports are appropriate for non-sensitive correctness or reproducibility
problems.

## External-review status

No external security audit and no coverage-guided fuzz campaign have been
performed on this release. The internal review of record is
`docs/reviews/prepublication-security-review.md`.

Two conditional premises are load-bearing and most need independent review:

1. The complete affine-image rank/coverage reconstruction behind the hiding
   floors, currently self-attested by the release-time GoodSpend checker with
   no independent verifier (`paper/aspis-spend/sections/hiding.tex`).
2. The custom Poseidon2 two-to-one compression `merkle_node_compress_v3` used
   for note and tree binding, whose domain separation is by call-site
   convention (`crates/aspis-statement/src/poseidon2.rs`).
