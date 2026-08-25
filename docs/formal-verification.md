# End-to-end formal verification of the deployed verifier

Aspis has a completed end-to-end formal proof for the deployed successful
proof-checker path. The theorem begins with any successful call to the Rust
verifier after functional translation by Charon and Aeneas. It follows the
values from that single execution through parsing, Fiat-Shamir,
authentication, the four-round low-degree test, the full algebraic relation,
and both final accumulators, then derives the security classification in Lean.

This formal result accompanies, to our knowledge at the 24 August 2026 search
cutoff, the first publicly evidenced Solana mainnet transaction to directly
verify a transparent, computationally hiding private-spend proof and
atomically record its nullifier and new pool state within the transaction
compute limit.

The final clean replay passed on 24 August 2026. It resolved and built all 331
tracked Lean modules in the dependency closure under Lean 4.32 and pinned
Aeneas revision `b59d5188c082f704a418c7cb4e52ad69328002d1`.

## The publication theorem

The exact declaration and source location are listed in the
[artifact guide](../paper/aspis-formalization/ARTIFACT.md). In mathematical
form, a successful translated verifier call, together with the explicit
SHA-256, encoder, and published-decoding premises, constructs:

1. a single accepted execution snapshot;
2. the exact general-accumulator weight schedule; and
3. the maintained security classification for the authenticated FRI and
   relation execution represented by that snapshot.

The caller supplies neither accumulator equality. Both are proved inside the
theorem from the accepted execution. The security argument consumes the
independently authenticated low-degree and relation evidence, including the
values read before the final helper returns.

## What is followed end to end

Every item below is derived from the same successful translated execution:

| Runtime stage | Checked connection |
| --- | --- |
| Entry and parse | Exact proof body, live statement, statement digest, fixed-body slices, and accepted result |
| Fiat-Shamir | Typed transcript events, byte framing, sampled field elements, and challenge order |
| Work | Batch, four fold, and final work records with their six ordered checks |
| Query selection | Exact 18 distinct positions produced by the bounded sampler |
| Authentication | Five ordered Merkle opening sections, complete byte consumption, and the returned values |
| FRI | Authenticated-value consumption, coordinate calculations, four folds, and final four-coefficient polynomial |
| Claim preparation | 76 decoded point claims, four prepared claims, and the initial relation value |
| Relation | Complete 58-field tail and four accepted relation rounds |
| General accumulator | Four initial components, eight tensor additions, all twelve terminal weights, and the final dot product |
| Compact accumulator | Constructor, four fold cases, final scatter/assembly, and four-term dot product |
| Composition | One accepted snapshot yields the maintained accepted-path security-event conclusion |

The [accepted V5 source map](v5-accepted-source-map.md) reduces this path to
15 review stops. The detailed generated-source inventory is in
[`aeneas-verif/README.md`](../aeneas-verif/README.md).

## Verification methodology

The proof follows the verifier's data flow rather than proving isolated helper
functions and joining them by hand-written equalities:

1. **Model the received data.** Lean definitions specify the proof bytes,
   statement, transcript events, five authenticated opening trees, FRI
   schedule, relation, and state transition.
2. **Prove release-specific mathematics.** The maintained project proves the
   field and circle-domain facts, coherent four-fold candidate chain,
   challenge-dependent nineteen-lane reduction, distinct-query calculation,
   relation reductions, hiding lemmas, theft reductions, and finite security
   ledger.
3. **Translate focused deployed Rust.** Charon records LLBC snapshots and
   Aeneas produces Lean definitions for the selected verifier functions.
4. **Bridge producers to consumers.** Each theorem connects values returned by
   one translated stage to the exact values consumed by the next stage.
5. **Compose one accepted execution.** The aggregate theorem constructs every
   witness from a single successful callback, including both accumulators.
6. **Audit replay and foundations.** The replay resolves only tracked sources,
   rejects proof escapes, builds in a clean directory, and checks the theorem's
   axiom report.

This same-execution discipline prevents mixing a valid transcript from one run
with openings, claims, or accumulator values from another.

## Mathematical layer

[`AspisFormal/`](../AspisFormal/) contains the maintained Lean 4 development.
Its publication results include:

- the complete one-input/one-output private-spend relation after extraction,
  including ownership, value conservation, asset and fee binding, note and
  nullifier derivation, and both Merkle paths;
- exact M31 circle domains and the four released encoders;
- a coherent initial candidate list of size at most 240 carried through all
  four FRI folds;
- the width-19 challenge-dependent batching argument;
- uniform sampling of 18 distinct positions from at most 64 draws;
- fixed-victim and observed-history theft reductions;
- the sequential non-overwritable nullifier-marker model;
- component-level hiding and retry-controller results; and
- the exact work-normalized release arithmetic.

Published circle-decoding and Fiat-Shamir theorems enter through explicit
interfaces whose release-specific field, distance, degree, transcript, and
query hypotheses are checked in Lean.

## Security statement

Lean defines one finite failure ledger and proves the pointwise classification
and union-bound arithmetic used by the release. The work-normalized protocol
subtotal satisfies

```text
B_protocol <= 0.7 * 2^-100.
```

The conditional composition theorem proves

```text
B_external <= 0.3 * 2^-100
--------------------------------
B_total    <=       2^-100.
```

The external budget names the published decoding/Fiat-Shamir applicability,
SHA-256 and Poseidon2 security, extraction, credential, translation,
compilation, and runtime events. The dominant raw term after the 37-bit grind
has already been completed is about 70--71 bits, so the paper publishes both
the raw and work-normalized interpretations.

The accepted-call theorem and the probability theorem are currently separate
formal results. A final probabilistic composition would place successful
translated calls in the work-normalized causal law and lift the deterministic
classification to event inclusion. The Rust entry path already checks the
live statement against its digest; a second composition theorem would identify
those Rust fields one by one with the abstract public statement used by the
false-acceptance and theft games. These are the two open composition tasks
that constrain the deployed-security wording.

## Cryptographic and platform interfaces

The formal result uses the following named interfaces:

| Interface | Role | Repository evidence |
| --- | --- | --- |
| Solana SHA-256 callback | Hashes the exact byte lists specified by the transcript and Merkle models | Byte-framing proofs, known-answer tests, generated callback boundary |
| SHA-256 security / random-oracle model | Transcript, authentication, and Fiat-Shamir arguments | Domain schedule, event ledger, cited BCS result |
| Poseidon2-M31 security | Note, nullifier, and relation hashes | Pinned constants, all-round Lean model, Rust KATs, `Poseidon2Faithful` interface |
| Published circle decoding | Converts the checked distance/agreement hypotheses into the list-decoding conclusion | Exact release-domain and encoder theorems |
| Charon, Aeneas, Lean | Translation and proof checking | Pinned revisions, patches, manifests, clean replay |
| Rust/LLVM/SBF toolchain | Source-to-program identity | Pinned clean build and byte-parity record |
| Solana runtime | Locks, rollback, PDA/CPI behavior, and persistent state | Runtime replay, exact-wire simulation, finalized account receipts |

Recent Poseidon2 algebraic cryptanalysis improves attack estimates but reports
no break of the Aspis parameters. Because no paper gives a dedicated concrete
advantage for M31, width 16, `alpha = 5`, 8 full and 14 partial rounds, the
release keeps primitive security symbolic instead of assigning an unsupported
number. See the [assumptions ledger](assumptions-ledger.md) for the full
interface definitions.

## From proof to deployed bytes

Two reproducibility records connect the formal source review to the historical
execution:

1. The [V5 preflight](../release/preflight/v5-production-freeze.md) reproduces
   the 1,258,496-byte SBF with SHA-256
   `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
2. The [V5 mainnet bundle](../release/aspis-v5-tag67-mainnet-v1/) binds that
   program to the 75,358-byte proof, statement, finalized transaction,
   1,334,452-CU result, state transition, and cleanup receipts.

The [full payer RPC archive](../release/aspis-v5-tag67-mainnet-rpc-archive-v1/)
reconstructs the proof and program from finalized transaction history after
their accounts were closed.

## Reproduce the evidence

### Mathematical proofs

```sh
cd AspisFormal
lake exe cache get
lake build
```

### End-to-end accepted-path proof

```sh
aeneas-verif/scripts/replay-accepted-path-lean432.sh
```

### Frozen SBF

```sh
./release/aspis-v5-tag67-frozen-candidate-v1/verify.sh
```

### Finalized execution archive

```sh
./release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 tools/check_release_facts.py
python3 release/aspis-v5-tag67-mainnet-rpc-archive-v1/verify.py
```

The finalized V5 verification transaction is
[`EJviPgF...R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).
