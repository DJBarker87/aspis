# Security

Report sensitive vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact. Public issues are appropriate for
non-sensitive correctness or reproducibility findings.

The supported research surface is the current `main` branch and the frozen V5
release artifacts named below.

## Security result

Aspis V5 has an end-to-end Lean proof of its selected accepting verifier
callback. From any successful call to the translated deployed path, the
theorem derives
the exact parse, Fiat-Shamir challenges, six work checks, 18 distinct queries,
five authenticated opening sections, four FRI folds, final polynomial, 76
decoded claims, 58-field relation tail, and both terminal accumulators. The
clean Lean 4.32 replay passed on 24 August 2026 over 331 tracked modules.

Lean separately proves a finite false-acceptance decomposition and the release
arithmetic. The checked work-normalized protocol subtotal is at most
`0.7 * 2^-100`. A total external budget of at most `0.3 * 2^-100` yields the
conditional `2^-100` endpoint. The dominant raw term after completing the
37-bit grind is about 70--71 bits and is reported separately.

The completed theorem covers the selected accepted proof-checker callback.
The security interpretation uses named interfaces for published decoding and
Fiat-Shamir results, SHA-256 and Poseidon2 security, extraction, translation,
compilation, and Solana runtime behavior. The remaining formal composition
work connects Rust public-statement fields to the abstract theft game and
lifts the deterministic accepted-call result into the work-normalized
probability experiment. See the [assumptions ledger](docs/assumptions-ledger.md).

## Evidence layers

| Layer | Security evidence |
| --- | --- |
| Mathematical construction | Lean proofs of the spend relation, circle domains, four-fold FRI argument, query sampler, failure ledger, hiding reductions, theft reductions, and marker-state model |
| Selected deployed verifier | Charon/Aeneas translations and bridge proofs composed into the accepted-call theorem |
| Compiled program | Pinned clean build inputs reproduce the exact 1,258,496-byte SBF |
| Runtime behavior | Rejection tests, 122,880 bounded property-test cases, runtime replays, exact signed-wire simulation, and finalized receipts |
| Historical identity | Full RPC archive reconstructs the 75,358-byte proof and deployed SBF from finalized transaction history |

The main publication theorem is
`AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator`.
The exact proof map and replay command are in
[formal verification](docs/formal-verification.md).

## Primitive security

SHA-256 is used for the transcript, proof-of-work checks, and authenticated
opening trees. Lean specifies the byte framing and records collision,
target-preimage, callback-divergence, and random-oracle events separately.

Poseidon2 over Mersenne31 is used for owner, note, nullifier, and relation
hashing with width 16, `alpha = 5`, 8 full rounds, and 14 partial rounds.
Constants, round execution, and typed wrappers are pinned and tested. Recent
algebraic cryptanalysis improves attacks on Poseidon2 but reports no break of
the Aspis tuple; because no dedicated concrete advantage is published for
that exact tuple, the release keeps its collision and target-preimage bounds
symbolic.

## Theft and state

The fixed-victim proof separates eight cases: extractor failure, credential
recovery, a second nullifier preimage, a second note opening, a Merkle
collision at the victim's position, marker-address behavior, runtime/state
failure, and invalid setup. `ApplicationMerkleBinding.lean` reduces a changed
leaf at the same position and root to a node-hash collision.

`V5NullifierMarkerReplay.lean` proves that a marker address cannot be consumed
successfully twice in the maintained sequential state model, including the
case where two distinct nullifiers derive the same address. The deployed
interpretation uses Solana's recorded locking, rollback, address-derivation,
and persistence behavior.

## Release identities

- Program: `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`
- SBF SHA-256:
  `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`
- Finalized V5 transaction:
  `EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE`
- Finalized slot: `435019536`
- Landed compute: `1,334,452` CU

The exact archived proof passes the released verifier callback. Mutating any
of its nine public fields causes rejection. The proof, statement, state
transition, cleanup, and refunds are preserved in the
[V5 mainnet bundle](release/aspis-v5-tag67-mainnet-v1/). The
[full payer RPC archive](release/aspis-v5-tag67-mainnet-rpc-archive-v1/)
reconstructs the closed proof and program accounts offline.

## Highest-value review targets

1. Applicability of the cited circle-decoding and BCS Fiat-Shamir results to
   the exact V5 schedule.
2. Dedicated cryptanalysis of the Poseidon2-M31 parameter tuple and typed
   hash modes.
3. The field-by-field Rust public-statement bridge and the
   deterministic-to-probability composition.
4. The pinned Charon/Aeneas translation and clean accepted-path replay.
5. Deployed Rust surrounding the selected proof-checker callback, especially
   account parsing, writable-state checks, marker creation, and refund paths.
6. Rust/LLVM/SBF source-to-binary correspondence.
7. Solana account locking, rollback, persistent marker state, and runtime
   repricing.

For Solana review, begin with
`programs/aspis-verifier/src/{dispatch,v5_full_transaction}.rs` and the
[V5 release preflight](release/preflight/v5-production-freeze.md). For the
formal path, begin with the [15-stop source map](docs/v5-accepted-source-map.md).
