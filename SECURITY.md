# Security

Please report vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact.

The supported research surface is the current `main` branch. Public issue
reports are appropriate for non-sensitive correctness or reproducibility
problems.

## How to read the security case

Aspis does not claim one universal end-to-end proof from cryptographic
assumptions through a finalized Solana transaction. Its assurance comes from
four complementary layers:

1. Lean checks the maintained mathematical construction and concrete release
   calculations, subject to the named cryptographic interfaces.
2. Charon/Aeneas bridge proofs connect selected production V5 Rust paths to
   those models.
3. Reproducible-build records connect the reviewed source and pinned tools to
   the exact deployed SBF.
4. Rejection tests, property tests, runtime replays, exact-wire simulation,
   and finalized chain receipts test the operational boundaries.

Each layer answers a different question; evidence in one layer does not erase
an assumption at the boundary to the next.

The selected production-Rust theorem covers Component-A matrix execution to
maintained GoodA for the release schedule; the generated Component-B
sampler/evaluator/C2 layout to its maintained ten-round terminal; Component
C's actual four rounds, finish, packer, and deployed public rows; Tag-67 magic,
LE64 reads, projection, digest predicate, and six ordered work checks; and
their combined public output and verifier at that schedule. The runtime
verifier recomputes GoodA and GoodB for every selected branch, but a universal
all-schedule source theorem for Component A remains open.

The only retained Tag-67 transcript function-call equation is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

It is a concrete function-pointer boundary that the pinned Aeneas translation
cannot cross, not a generic assumption that Rust equals Lean. Once that
equation and the successful generated reads/guards are supplied, the exact
projection, leading-zero predicate, six ordered checks, Component-C public
output, and A/B/C composition are theorem conclusions.

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
- Release records preserve the finalized q18/g37 and V5 mainnet results, as
  well as the V5 devnet and runtime evidence.
- The [V5 mainnet record](docs/v5-mainnet-demo.md) binds the exact proof,
  statement, program, canonical nullifier bump 255, exact-wire simulation,
  landed compute use, and finalized cleanup/refund transactions.
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

The highest-value external work is to attack the boundaries between the four
layers, rather than merely rerunning already-green checks:

1. The cryptographic reduction from the complete execution view to the
   affine/linear hiding model, applicability of the cited PCS/BCS and
   Fiat–Shamir results, and the extractor or simulation-extractability premise
   used by theft resistance. `tools/verify_hiding_ranks.py` independently
   reproduces the eight rank claims, but does not discharge that reduction.
2. The custom Poseidon2-M31 primitive used for commitments, nullifiers, and
   Merkle compression, including its cryptographic security and universal
   all-input Rust equality. Constants and known-answer executions are pinned;
   those checks are not a primitive-security proof.
3. The exact transcript-hash function-call equation above, also recorded on
   the [`assumptions page`](docs/assumptions-ledger.md).
4. Production Rust outside the selected Charon/Aeneas paths, especially the
   still-open universal Component-A source theorem and a complete joint
   serializer theorem.
5. Solana account validation and aliasing, proof-account and marker state
   mutation, ordered all-or-nothing updates, refund and cleanup behavior, and
   the host executor's signer and recovery dependency surface.
6. Runtime repricing and compute sensitivity for the frozen V5 program on
   future Solana runtime families.

Poseidon2 constants, domain separation, and wrapper outputs are pinned by CI
and known-answer tests. Its cryptographic security remains an explicit
primitive assumption.

The historical q18/g37 review is
[`docs/reviews/prepublication-security-review.md`](docs/reviews/prepublication-security-review.md).
The current V5 release gate is
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).
The finalized V5 execution and pinned refund accounting are
[`docs/v5-mainnet-demo.md`](docs/v5-mainnet-demo.md).
