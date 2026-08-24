# Security

Please report vulnerabilities through GitHub's private security-advisory
workflow for this repository. Include the affected commit, a minimal
reproducer, and the expected impact.

The supported research surface is the current `main` branch. Public issue
reports are appropriate for non-sensitive correctness or reproducibility
problems.

## How to read the security case

Aspis separates four kinds of evidence rather than presenting them as one
unqualified proof of Solana itself:

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

The current accepted-path proof chain starts with one successful translated call
to the released proof checker. From that same call it derives the parse,
transcript challenges, six work checks, 18 distinct queries, five
authenticated opening sections, FRI checks, final polynomial, exact decoded
claim table, initial relation value, and decoded four-round relation tail.
These values cannot be chosen from different runs. The accepted general
accumulator's four initial components, eight additions, twelve-component
schedule, fold traversal, terminal weights, and dot implementation are derived
from that execution. The compact constructor, four folds, final assembly, and
dot are derived internally as well. Once the final clean replay is green, one
successful selected translated verifier call therefore yields the maintained
accepted-path security-event conclusion without a caller-supplied accumulator
equality.

This is deliberately narrower than verification of the whole program. The
surrounding account wrapper, compiler, Solana runtime, and persistent state
transition retain their own stated boundaries. SHA-256 and Poseidon2
implementation and security properties, the cited decoding and Fiat--Shamir
results, and the numerical bounds assigned to external failure events are
also explicit assumptions rather than Lean conclusions.

## Security evidence

Aspis combines several forms of evidence:

- Lean proofs check substantial parts of the mathematical construction and
  the concrete calculations used by the release.
- Charon, Aeneas, and additional Lean proofs connect selected production Rust
  to the maintained mathematical models.
- Automated tests exercise the transaction, rejected proofs, and malicious
  account and state arrangements. The latest bounded
  [pre-mainnet property-test run](results/fuzz/v5-pre-mainnet-proptest-20260724.md)
  records 122,880 generated cases plus the targeted V5-verifier and state-mutation
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
calculation. The earlier batching argument has been repaired: the proof now
handles a challenge-dependent decoder family without multiplying by the
240-candidate list cap, and it follows one initial candidate through all four
folds. Lean also checks the exact released circle-code parameters and the side
conditions needed by the cited decoding result.

The dominant raw batching event is about 71 bits after a grind has completed.
Charging the attacker for the released 37-bit grind gives a checked core below
`0.7 * 2^-100`. The release target is therefore 100 bits of work-normalized
attack cost, not 128 bits and not a raw `2^-100` probability per completed
proof. The remaining external events must together fit the reserved
`0.3 * 2^-100` budget.

The final deterministic theorem connects the selected accepted proof-checker
path to the maintained security-event conclusion, subject to a clean replay.
Its main and compact accumulator equalities are proved inside the theorem.
What remains outside that source theorem is `EntryTerminalBoundary`, the
SHA-256 callback and primitive security, Poseidon2 security, released FRI
tables, published decoding/PCS/FRI/Fiat--Shamir applicability, fresh prover
randomness, extraction, translation and compilation, the surrounding Solana
account/state code and runtime, and concrete probability bounds for the named
external events. Consequently the repository reports a checked 100-bit
work-normalized **protocol subtotal**, not an unconditional 100-bit deployed
theft-resistance number. See the [formal-verification overview](docs/formal-verification.md)
and [dated mathematical review](docs/reviews/mathematical-status-20260814.md).

`V5AcceptedSpendRelation.lean` proves that the extracted arithmetic,
Poseidon2, Merkle, and public-input equations imply the complete spend
relation. The accepted-path chain supplies the verifier-side parse,
transcript, opening, FRI, claims, initial relation value, and relation tail
from one translated execution. The final theorem derives both the main and
compact accumulator equalities and uses them to reach the maintained
accepted-path security-event conclusion; its clean replay is the publication
gate.
`V5FixedVictimTheftGame.lean` separately classifies a fixed-victim attack into
eight mathematical and chain-level failures for the attack event defined in
the Lean model. These results do not prove that an extractor recovers a valid
witness from every observed accepted proof, or supply numerical Poseidon2 and
runtime bounds. The marker-state model proves that two sequential successful
marker writes cannot share an address. Connecting the surrounding Rust and
Solana state transition to that model, and using it to remove the PDA-alias
case from the theft game, remains open.

The project has not yet received an external security audit or published a
coverage-guided fuzzing campaign.

The assumptions and unproved links are listed on the
[`assumptions page`](docs/assumptions-ledger.md).

For a Solana review, start with the V5 dispatch and all-or-nothing state
update in
`programs/aspis-verifier/src/{dispatch,v5_full_transaction}.rs`, then the
mainnet CU policy and runtime analysis in
[`release/preflight/v5-production-freeze.md`](release/preflight/v5-production-freeze.md).

## Most valuable areas for outside review

The highest-value external work is to attack the boundaries between the four
layers, rather than merely rerunning already-green checks:

1. Whether the listed failure cases cover every way a false proof could be
   accepted, and whether the cited coding and Fiat--Shamir results apply with
   the exact hypotheses recorded by the release. Lean checks the released
   field, code dimensions, distances, degree limits, query schedule, and
   finite arithmetic; an outside review should challenge the imported
   cryptographic theorems and the probability assigned to every external
   event.
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
   their eight-term union bound. `V5NullifierMarkerReplay.lean` then shows that
   two sequential successful marker consumptions cannot share an address. The
   extractor receives a complete prover execution record, not public proof
   bytes alone. The deployed connection, extraction after observed proofs,
   target sampling, concrete Poseidon2 bounds, PDA-alias game reduction, and
   exact Rust/Solana state behavior remain outside the proof.
3. The trusted boundary around Charon, Aeneas, Lean, the Rust/LLVM/SBF
   toolchain, and the production SHA-256 callback. These tools and primitive
   semantics are pinned and replayed, not themselves proved by the final
   theorem.
4. Production Rust outside the selected accepted proof-checker path,
   especially the outer account parser, atomic state wrapper, serializers,
   and paths not exercised by the released spend.
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
