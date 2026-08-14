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

The selected production-Rust theorems cover Component-A matrix execution to
maintained GoodA for the release schedule; selected Component-B
sampler/evaluator/C2 behavior; a packaged Component-C public run; and Tag-67
magic, LE64 reads, projection, digest predicate, and six ordered work checks.
The final Lean theorem combines those results by assuming that the relevant
Rust calls return successfully, their inputs have the required lengths and
field encodings, and several intermediate Rust values equal the corresponding
Lean values. It does not prove that every accepted production proof meets all
of those assumptions or implies the complete spend relation. The runtime verifier recomputes GoodA and
GoodB for every selected branch, but a universal all-schedule source theorem
for Component A remains open.

The sole retained function-call equation in the **Tag-67 work-verifier
subtheorem** is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

It is a concrete function-pointer boundary that the pinned Aeneas translation
cannot cross, not a generic assumption that Rust equals Lean. Once that
equation and the successful generated reads/guards are supplied, the exact
projection, leading-zero predicate, and six ordered Tag-67 checks are theorem
conclusions. The Component B/C proofs and the final combined theorem still
assume that the relevant Rust calls return successfully, that inputs have the
required lengths and encodings, and that specified intermediate values match
the Lean model.

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
  statement, program, observed nullifier bump 255, exact-wire simulation,
  landed compute use, and finalized cleanup/refund transactions.
- `programs/aspis-verifier/tests/v5_mainnet_release_proof.rs` reruns the exact
  archived proof and statement through the released verifier callback and
  confirms that changing any public field causes rejection.
- The [full payer RPC archive](release/aspis-v5-tag67-mainnet-rpc-archive-v1/)
  reconstructs that proof from 79 finalized uploads and the exact SBF from
  1,466 finalized loader writes, then compares both with the released files.
- Independent rank checkers reproduce the eight hiding-rank claims.

The current mathematical review found no concrete forgery or broken finite
calculation. It also confirms that V5 soundness, deployed hiding, and theft
resistance still assume that the listed failure cases cover every false proof,
the cited papers apply to this exact protocol, selected Rust values match the
Lean model, extraction works as assumed, and the hash functions have the
required security. See the
[dated mathematical review](docs/reviews/mathematical-status-20260814.md).

`V5AcceptedSpendRelation.lean` proves that a successfully extracted V5 trace
with the checked arithmetic, Poseidon2, Merkle, and public-input equations
satisfies the complete spend relation. The still-open high-priority step is
deriving that trace from arbitrary deployed acceptance, with a concrete bound
on the polynomial-commitment, FRI, Fiat--Shamir, collision, and decoding
failure events.

`V5DeployedFalseAcceptance.lean` now states one conditional probability step
without hiding that gap: it takes three parameterized failure predicates,
proves their union bound, and derives a work-normalized `2^-100` bound and
ordinary `min(1, T / 2^100)` bound if callers prove that the predicates are
the actual deployed selector failures and supply the extraction, Poseidon2,
width, round, transcript, commitment, Fiat--Shamir, and branch-security
premises, within the theorem's range `1 <= T <= 2^128`.
`V5FixedVictimTheftGame.lean` separately classifies a fixed-victim attack into
eight mathematical and chain-level failures for the attack event defined in
the Lean model. Neither file supplies the still-missing deployed connection or
extraction theorem, or numerical Poseidon2, PDA, and runtime bounds.

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

1. Whether the listed failure cases cover every way a false proof could be
   accepted; whether the cited coding and Fiat--Shamir theorems apply to this
   exact protocol; whether the separate grinding hashes justify the claimed
   work factors; and whether the full Rust execution really has the hiding
   behavior described by the simpler mathematical model. The calculators and
   rank checks do not prove these links.
2. The custom Poseidon2-M31 primitive used for commitments, nullifiers, and
   Merkle compression, including its cryptographic security and universal
   all-input Rust equality. Constants and known-answer executions are pinned;
   those checks are not a primitive-security proof. `TheftResistance.lean`
   and `V5TheftResistance.lean` use fixed-target second-preimage events.
   `ApplicationMerkleBinding.lean` proves that a different leaf at the
   victim's exact tree position and root exposes a node-hash collision.
   `V5FixedVictimTheftGame.lean` separates extraction failure, credential
   recovery, nullifier collision, note-opening collision, Merkle collision,
   PDA aliasing, runtime/state failure, and invalid victim setup, and proves
   their eight-term union bound. The extractor receives a complete prover
   execution record, not public proof bytes alone. The deployed connection,
   extraction after observed proofs, target sampling, and concrete Poseidon2,
   PDA, and runtime bounds remain outside the proof.
3. The assumptions that the Component-B/C Rust calls return successfully,
   their inputs have the required lengths and field encodings, their folded
   values, coefficients, challenges, serialized bytes, and transcript match
   the Lean model, plus the remaining Tag-67 hash-call equation.
4. Production Rust outside the selected Charon/Aeneas paths, especially the
   still-open universal Component-A source theorem, a complete joint serializer
   theorem, and a proof that ordinary acceptance supplies the facts currently
   passed into the selected component theorems as assumptions.
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
