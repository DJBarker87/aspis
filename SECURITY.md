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
2. The custom Poseidon2 constructions used for note and tree binding
   (`crates/aspis-statement/src/poseidon2.rs`). Each semantic hash is
   separated by a distinct domain constant injected into the sponge capacity,
   or, for the fixed-arity node compression, added into the last state limb:
   owner-key derivation `0x4153_0001`, nullifier `0x4153_0002`, note / leaf /
   spendable-output commitment `0x4153_0003`, the retired v2 node sponge
   `0x4153_0005`, and the deployed `merkle_node_compress_v3` two-to-one node
   compression `0x4153_1005`. Separation is a property of the injected
   bytes, not of call-site convention, and is verified by cross-domain
   non-equality KATs (each domain yields a distinct digest on a shared input)
   plus per-wrapper regression KATs that pin the exact output bytes. The
   residual risk is not present under-separation but future misuse: the
   generic domain-parameterized entry point was public, so a new call site
   could hash under an unintended domain. It is now `pub(crate)` and external
   callers are routed through typed, single-domain wrappers
   (`hash_owner_key`, `hash_nullifier`, `hash_note_commitment`,
   `hash_merkle_node_sponge`, `merkle_node_compress_v3`), which narrows but
   does not eliminate that class of error.
