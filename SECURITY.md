# Security

Please report vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact.

The supported research surface is the current `main` branch. Public issue
reports are appropriate for non-sensitive correctness or reproducibility
problems.

## Security evidence

Aspis combines several forms of evidence:

- Lean proofs check substantial parts of the mathematical construction and
  the concrete calculations used by the release.
- Charon, Aeneas, and additional Lean proofs connect selected production Rust
  to the maintained mathematical models.
- Automated tests exercise the transaction, rejected proofs, and malicious
  account and state arrangements. The latest bounded
  [pre-mainnet property-test run](results/fuzz/v5-pre-mainnet-proptest-20260724.md)
  records 122,880 generated cases plus the targeted Tag-67 and state-mutation
  tests.
- The recorded source and pinned tools reproduce the exact compiled Solana
  program.
- Release records preserve the finalized q18/g37 mainnet result and the
  current V5 devnet and runtime evidence.
- Independent rank checkers reproduce the eight hiding-rank claims.

The project has not yet received an external security audit or published a
coverage-guided fuzzing campaign.

The assumptions and unproved links are listed on the
[`assumptions page`](docs/assumptions-ledger.md).

For a Solana review, start with the Tag-67 dispatch and all-or-nothing state
update in
`programs/aspis-verifier/src/{dispatch,v5_full_transaction}.rs`, then the
mainnet CU policy and runtime analysis in
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).

## Most valuable areas for outside review

1. The cryptographic assumptions used by the proof system, especially the
   complete affine-image reconstruction and hybrid argument behind the hiding
   floors. `tools/verify_hiding_ranks.py` independently reproduces the eight
   rank claims; the mapping from the complete execution view to that linear
   model remains the cryptographic proof obligation described in the paper.
   The custom Poseidon2-M31 commitments and Merkle compression in
   `crates/aspis-statement/src/poseidon2.rs` are another focused primitive
   review target.
2. The exact transcript-hash function-call boundary between production Rust
   and its Lean model, recorded in
   the [`assumptions page`](docs/assumptions-ledger.md).
3. Production Rust outside the current Charon/Aeneas coverage.
4. Solana account validation, proof-account handling, and the ordered state
   update.
5. Runtime pricing and compute sensitivity for the frozen V5 program.

Poseidon2 constants, domain separation, and wrapper outputs are pinned by CI
and known-answer tests. Its cryptographic security remains an explicit
primitive assumption.

The historical q18/g37 review is
[`docs/reviews/prepublication-security-review.md`](docs/reviews/prepublication-security-review.md).
The current V5 release gate is
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).
