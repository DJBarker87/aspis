# V7 / Pool V1 K1.1 knowledge-extraction audit

Date: 25 August 2026

Repository revision inspected: `d4c5115059026bbe55faec9f0657ecfb4e6e23c3`

Deployed protocol in scope: compact one-fold V7, production Tag 73

Roadmap gate: Pool V1 Track K1, Stage K1.1

## Executive verdict

**Finding — K1 is not closed.** The repository has a conditional V7
argument-*soundness* endpoint, but no cited theorem is presently instantiated
as an end-to-end argument of knowledge for the exact deployed Tag-73
transcript. In particular, BCS 2016 does not supply the deterministic
one-recorded-run extractor represented by the existing Lean
`KnowledgeExtractor` structure.

**Finding — the published theorem's extractor is black-box and may restart.**
BCS 2016 defines a probabilistic polynomial-time extractor with oracle access
to the malicious prover. It may restart the prover with the same randomness and
auxiliary input while choosing random-oracle answers. Its Theorem 7.1 preserves
proof of knowledge only when the underlying IOP already has *restricted
state-restoration proof of knowledge*. The compiler does not manufacture that
interactive knowledge property from ordinary soundness.

**Finding — a straight-line sub-extractor remains plausible, but is a new V7
proof.** BCS Lemma 3.2 gives Valiant's ordinary-Merkle query-graph extractor.
That component reads the oracle query graph and reconstructs a committed list,
up to missing-query/guess/collision events. V7 instead uses two typed binary
trees, shared leaf salts, domain-separated variable-length preimages, and
208-bit prefixes of a 256-bit SHA-256 oracle. A V7 adapter and its exact raw
failure bound are not in the current formalization.

**Finding — the current decoder interfaces are existential, not algorithmic.**
The V7/V6 `PublishedInitialWidth29CurveDecodability` and
`PublishedOneFoldCurveDecodability` predicates prove existence of component
messages and selected challenge sets. They do not expose a decoder, its finite
output list, completeness, or runtime. S-two Theorem 7 states an appropriate
deterministic Guruswami–Sudan algorithm, but it has not been instantiated for
the exact Aspis M31 domains and serialization.

**Blocker — uncapped custody/theft resistance.** Until the query-graph,
algorithmic-decoder, candidate-chain, trace-to-witness, and observed-proof
simulation-extraction steps are closed, V7 cannot support an unconditional or
numerically complete theft-resistance claim for a high-value pool. The
roadmap's experimental/TVL-capped launch policy remains appropriate.

A new typed boundary was added at
`AspisFormal/AspisFormal/Pool/KnowledgeExtractorInterface.lean`. It records the
published black-box/restart theorem shape, the exact classical error formulas,
an algorithmic list-decoder interface, a separate one-log Merkle extractor, and
the unproved V7 applicability obligations. It asserts none of those
obligations.

## Scope and method

This was a source-to-source applicability audit, not a new cryptographic proof.
It compared:

- the exact production Rust transcript and 208-bit Merkle implementation;
- the current V7/V6 Lean security interfaces and theft reductions;
- the cited primary literature; and
- the Pool V1 roadmap's ten K1.1 questions.

Only a focused compile of the new Lean file was run. No full Lean regression,
NUC job, deployment, mainnet action, or commit was performed.

### Primary sources pinned for this audit

| Source | Exact item used | PDF SHA-256 |
|---|---|---|
| [Ben-Sasson, Chiesa, Spooner, *Interactive Oracle Proofs*](https://eprint.iacr.org/2016/116.pdf) | 10 February 2016 ePrint; Lemma 3.2, Definition 5.1, Theorem 7.1, Section 7.3 | `a2dc9bd042665081664287281b9bcf64735be2c818ce9207cce57cc43939fa2f` |
| [Chiesa, Manohar, Spooner, *Succinct Arguments in the Quantum Random Oracle Model*](https://eprint.iacr.org/2019/834.pdf) | 14 January 2020 revision; Definitions 8.3–8.5, Theorem 8.6 | `c3258e2faa339bdc441403d73aba9fee7d03687121c3369ef007ccce71cd2b41` |
| [Block et al., *Fiat–Shamir Security of FRI and Related SNARKs*](https://eprint.iacr.org/2023/1071.pdf) | 15 February 2024 revision; Definitions 3.13–3.14, Theorems 3.15 and 5.11 | `bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947` |
| [Carmon et al., *S-two Whitepaper*](https://eprint.iacr.org/2026/532.pdf) | 24 March 2026 revision; Theorems 7, 15, 21, 22; Remark 23 | `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f` |
| [Ganesh et al., *Fiat-Shamir Bulletproofs are Non-Malleable (in the ROM)*](https://eprint.iacr.org/2023/147.pdf) | 10 October 2024 full version; Definitions 2.8 and 3.1–3.3, Lemmas 3.1–3.2 | `73aa86a400d3724a38eac4d30aedd1f8e0909d6af8456ea7bfd269d0c5b5031f` |
| [Fiat and Shamir, *How to Prove Yourself*](https://doi.org/10.1007/3-540-47721-7_12) | CRYPTO 1986/1987 transform | n/a |

The Ganesh et al. 2024 full version explicitly supersedes its EUROCRYPT 2022
AGM result. It is included as a possible K1.6 route, not as an existing V7
theorem.

## Exact deployed V7 transcript that a theorem must cover

The production entry point is Tag 73 in
`programs/aspis-verifier/src/v7_transaction.rs`. It binds the program ID,
compiled release binding, statement digest, and proof-account key as the
attempt ID, verifies the complete proof, and only then applies the atomic state
transition.

The Fiat–Shamir order is implemented primarily in
`crates/aspis-core/src/v6_transcript.rs` and is not equivalent merely to a list
of independent uniform challenges:

1. Absorb V7 profile, circle basis, deployment `(program ID, release binding)`,
   statement digest, and the hiding precommit/attempt identity.
2. Absorb the 208-bit C1 root and deterministic public root salt; draw
   `lambda` and `chi`.
3. Absorb the 208-bit C2 root and deterministic public root salt; draw the
   zero-check batching challenges. **C2 is challenge-dependent**, because it is
   committed after `lambda` and `chi`.
4. Absorb the semantic initial claim, draw `eta`, then consume ten degree-27
   semantic sumcheck messages and challenges.
5. Absorb the three rows of point claims.
6. Check and absorb the 35-bit batch-work nonce; draw nonzero `gamma`.
7. Absorb the inactive claim; draw nonzero `kappa`.
8. For each of two OOD samples, draw a circle point, absorb its claimed value,
   then draw its mixing challenge.
9. Absorb relation round zero, check and absorb the 31-bit fold-work nonce,
   then draw `alpha[0]`.
10. Absorb the complete `final256` vector and check/absorb the 34-bit final-work
    nonce.
11. Derive the **first** of at most 64 candidate q16 schedules whose binary
    Merkle frontier has at most 203 nodes. The selected queries are sampled
    without replacement from `2^18`; this is a conditioned/rejection-derived
    schedule, not one unconstrained uniform q16 draw.
12. Draw the nonzero query-batch challenge, authenticate both C1 and C2
    openings, fold the opened fibres, and absorb the derived query claim.
13. Consume relation rounds one through three and check the final dot-product
    terminal.

The C1/C2 commitments use
`crates/aspis-core/src/v7_merkle208.rs`: node digests are the first 26 bytes of
`SHA-256(0x11 || left26 || right26)`. Leaves are typed and salted; the same
32-byte private salt is carried by the paired C1/C2 query record. Thus the
Merkle oracle effectively exposes 208-bit outputs while transcript challenges
use the full 256-bit SHA-256 output.

**Inference.** The generic BCS syntax can represent a second oracle message
sent after prior public coins, so challenge-dependent C2 is not inherently
incompatible with BCS. It becomes covered only after the exact sequence above
is defined as an interactive IOP and its round-by-round/state-restoration
*knowledge* property is proved. That mapping does not currently exist.

## Answers to the ten K1.1 questions

### 1. Argument of knowledge or soundness only?

**BCS 2016:** Both notions exist, but separately. Theorem 7.1 preserves proof
of knowledge only from an underlying *restricted state-restoration proof of
knowledge* premise. State-restoration soundness alone yields only soundness.

**CMS 2019:** Theorem 8.6(2) is an argument-of-knowledge theorem in the QROM,
conditional on round-by-round knowledge (Definition 8.5). It is not obtained
from round-by-round soundness.

**Block et al. 2023:** Theorem 3.15 has both adaptive soundness and adaptive
knowledge clauses. The knowledge clause assumes a round-by-round knowledge
extractor as in Definition 3.13. Theorem 5.11 supplies that property for the
paper's exact FRI/Batched-FRI Algorithm 1, not for Aspis's complete spend IOP.

**S-two:** Theorem 15 calls its exact Protocol 1 round-by-round
knowledge-sound; Theorem 21 does so for its batch-evaluation protocol. Theorem
22 then states a BCS knowledge-soundness bound, but the whitepaper says the
formal treatment is postponed.

**Fiat–Shamir 1987:** The original transform is not a multi-round IOP
argument-of-knowledge theorem and cannot discharge this gate.

**V7 finding:** `V7ConditionalCompleteSecurity.lean` proves conditional
false-acceptance arithmetic only. Its `ClassicalFSCompiler` bounds
`coreAdvantage`; it has no witness extractor or extraction probability.

### 2. Straight-line, rewinding, or algebraic extractor?

**BCS 2016:** The *end-to-end PoK extractor is classical black-box with
restart/state restoration*. Section 2.3 permits restarting the malicious prover
with the same randomness and auxiliary input while choosing oracle answers;
Section 7.3 constructs a state-restoring prover and invokes its extractor.

BCS Lemma 3.2's Valiant Merkle component is query-graph/straight-line after the
oracle run. This does not make the complete witness extractor straight-line.

**CMS 2019:** Theorem 8.6 uses a quantum black-box/compressed-oracle extractor.
It is neither a one-classical-log extractor nor an algebraic-group extractor.

**Block et al. 2023:** Definition 3.13's *interactive RBR extractor* is
algorithmic from `(index, statement, partial transcript, next prover message)`.
The classical compiled BCS extractor is still the BCS black-box extractor.

**Ganesh et al. 2024:** Its FS-EXT extractor uses black-box rewinding to build a
tree of transcripts and runs in expected polynomial time. The current full
version removes the AGM requirement; the older 2022 proceedings citation in
the V5 paper does not reflect that improvement.

**V7 finding:** `TheftResistance.lean` lines 82–95 and 263–273 type both
extractors as total deterministic maps with pointwise success on every
accepting execution. That is strictly stronger and operationally different
from the cited theorems.

### 3. What is the extractor input?

**BCS 2016:** Instance `x`, unary query/output-security bounds, and black-box
oracle access to the malicious prover. The extractor does not receive the
prover's code, random tape, or auxiliary input; it controls oracle answers and
may restart the same hidden tape.

**Ganesh et al. 2024 / AFK shape:** The FS-EXT experiment explicitly carries
the first-run statement, proof, adversary random tape token, and random-oracle
query history, while the extractor additionally has oracle access to the
prover's next-message function. Query history alone is not the interface.

**Block RBR extractor:** `(index, x, partialTranscript, nextMessage)` and an
actual polynomial-time algorithm.

**V7 gap:** A public proof account plus transcript log is insufficient to
instantiate the cited end-to-end BCS extractor. A separately proved V7 Merkle
query-graph extractor could use one log to recover committed words, but witness
selection still needs the RBR/candidate-chain argument.

### 4. Merkle commitments in the programmable ROM?

**BCS finding:** Yes, for its ordinary binary λ-bit Merkle construction.
Valiant extraction reconstructs the committed list consistently with accepted
openings except for collision/guessed-answer events. Lemma 3.2's exact failure
term is

```text
(Q^2 + 1) / 2^lambda.
```

Theorem 7.1's whole compiler charges

```text
3 (Q^2 + 1) / 2^lambda.
```

**V7 blocker:** No current proof adapts that query graph to both typed V7
trees, 208-bit truncation, their domain separation, paired/shared salts, and
the shared 256-bit SHA-256 oracle. S-two Remark 23 explicitly says its
mixed-domain Merkle adaptation is not formally proved; it is not a substitute
for the V7 adapter.

### 5. Challenge-dependent second-stage commitments?

**Finding:** Generic public-coin IOP/BCS sequencing permits a prover oracle
message after previous public coins. Therefore C2-after-`lambda,chi` is not a
generic impossibility.

**Blocker:** Neither S-two Protocol 1 nor Block et al.'s FRI Algorithm 1 is the
V7 semantic/C1/C2 transcript. V7 must prove an RBR knowledge state function and
extractor at the exact C2 boundary, including the dependence of all complete C2
fibres on `lambda` and `chi`. Existing Lean `Width29CurveDecodable` only states
an existential correlated-agreement implication; it is not that extractor.

### 6. Grinding?

**S-two finding:** The paragraph following Theorem 22 models a grinding salt as
part of the preceding prover message and says state restoration permits it by
default. This is a stated applicability claim, not a separate formal theorem;
the same section says formal treatment is postponed.

**V7 blocker:** V7 has three positioned work nonces (35/31/34 bits), and each
filters a different subsequent challenge/schedule. The final stage also
precedes a first-success, cap-203 conditioned query schedule. The exact
state-restoration/RBR experiment must include all of these freedoms and prove
the raw knowledge-error reduction. Dividing a soundness expression by adversary
work does not produce an extraction-failure probability.

### 7. Adaptive statements?

**BCS 2016 finding:** Its basic PoK definition and Theorem 7.1 quantify for
each fixed instance `x`; they do not directly state a multi-theorem experiment
where the final statement is selected after simulated proofs.

**CMS 2019 finding:** Definition 8.5 is also stated for each `x` and partial
transcript.

**Block et al. nuance:** Theorem 3.15 labels its resulting errors adaptive, and
supports indexed/holographic relations, while Definition 3.14 is written for
each `x`. This is useful for adversarial instance selection in its model but is
not, without a reduction, the Pool theft game after a history of proofs and
state changes.

**Ganesh et al. 2024 finding:** Definition 2.8 explicitly lets the adversary
output `(x,T)` after oracle access; its simulation-extractability definition
also permits adaptive statements and simulation queries. This is the better
K1.6 framework if its premises can be proved for V7.

### 8. After observed or simulated proofs?

**Finding:** Ordinary BCS proof of knowledge plus zero knowledge does not by
itself imply simulation extractability. The current `SimExtractor` and
`ExtractAfterObservation` Lean interfaces assume the desired output map; they
do not prove its existence, efficiency, or error.

**Promising primary route:** Ganesh et al. 2024 Lemma 3.2 proves that FS-EXT
plus FS weak unique response (FS-WUR), with a canonical programmable-ROM NIZK
simulator, yields FS-SIM-EXT. Its concrete generic error is

```text
kappa_hat(lambda, q_RO, q_sim)
  = q_sim * Adv_FS-WUR + kappa(lambda, q_RO).
```

Lemma 3.1 bounds FS-WUR from SR-WUR with an additional
`(q_RO + 1) / |Ch_min|`. The simulation-extraction definition includes a
polynomial extraction loss and expected-polynomial-time black-box access.

**V7 blockers for this route:** no exact canonical transcript simulator, no
proof of its programming/abort probability, no exact V7 FS-EXT theorem, and no
SR-WUR/FS-WUR proof for the heterogeneous V7 challenge schedule. The current
computational hiding factorization is not automatically perfect HVZK or the
canonical simulator required by this theorem.

### 9. Exact extraction error?

The applicable formulas must be kept distinct:

| Result | Raw classical knowledge error stated by the result |
|---|---|
| BCS 2016 Theorem 7.1 | `epsilon_sr(x,Q) + 3(Q^2+1) 2^-lambda` |
| Block et al. 2023 Theorem 3.15 | `Q * epsilon_rbr-k(x) + 3(Q^2+1) 2^-kappa` |
| S-two Theorem 22 claim | `(Q+R) * max_i epsilon_i + 3(Q^2+1) 2^-lambda` |
| CMS 2019 Theorem 8.6, QROM | extraction probability `Omega(mu - Q^2*kappa - Q^3/2^lambda)`; hidden constants, so not an exact V7 numerical bound |
| Ganesh et al. 2024 Lemma 3.2 | `q_sim * Adv_FS-WUR + kappa(lambda,q_RO)`, subject to its polynomial extraction loss |

**Finding:** V7's current `bcsError` ledger is a work-normalized
false-acceptance calculation. `ClassicalFSCompiler.compiledBound` says only
`coreAdvantage <= bcsError(...)`. It is not an extraction theorem.

**Finding:** `HashAndImplementationInterfaces.digestCollisionBound <= 2^-104`
is a generic birthday-strength reserve. A knowledge extractor needs a raw,
query-indexed event bound. Because V7 Merkle nodes expose 208 bits while
Fiat–Shamir challenges expose 256 bits, one undifferentiated `lambda=256`
compiler term is not justified. The exact two-tree/truncation composition must
be derived; this audit deliberately does not invent its constants.

### 10. Which list decoder must be algorithmic?

**Finding:** At minimum, both reconstructed V7 received-word stages need an
algorithm:

1. the initial width-29 / `2^20` circle-code batch; and
2. the one-fold final-code / `2^18` stage.

The decoder must return a finite list, include every word within the exact
agreement threshold, respect the proved list-size cap, and run in polynomial
time in the public parameters.

**Primary support:** S-two Theorem 7 states that deterministic
Guruswami–Sudan decoding outputs all close circle-code words below the Johnson
radius in fewer than `O(|D|^4)` field operations. This supplies the right kind
of algorithmic theorem.

**Blocker:** Aspis still needs the exact M31 circle-to-univariate conversion,
multiplicity/threshold instantiation, executable representation, output-list
completeness, and a bridge from decoded messages through one *consistent*
candidate chain to the spend trace. Block et al. Theorem 5.11 merely has its RBR
extractor read the first FRI oracle as a close word; it does not decode an Aspis
spend witness.

## Citation and manuscript audit

1. **Finding — CMS is named but not bibliographically pinned.** Neither
   `paper/aspis-formalization/references.bib` nor
   `paper/aspis-spend/references.bib` contains Chiesa–Manohar–Spooner,
   ePrint 2019/834, even though project prose and interfaces refer to
   “BCS/CMS”. Add the exact 14 January 2020 revision or its final publication.

2. **Finding — the V5 straight-line claim is unsupported as written.**
   `paper/aspis-spend/sections/soundness.tex` Lemma
   `lem:generic-extraction` and Theorem `thm:argument-of-knowledge` attribute a
   no-rewinding, query-transcript-only witness extractor to BCS. BCS supports a
   straight-line Valiant *Merkle-list* extraction component, but its complete
   PoK theorem invokes a black-box restricted state-restoration extractor. The
   manuscript must either narrow that lemma to the Merkle component and prove
   the subsequent algorithmic RBR extractor, or state the actual black-box
   theorem.

3. **Finding — S-two's status must remain explicit.** Theorem 22 is a stated
   bound whose formal treatment is postponed, and Remark 23 leaves its special
   Merkle adaptation unproved. It is useful guidance, not a complete V7
   instantiation.

4. **Finding — update the simulation-extraction source.** The V5 paper cites
   the 2022 Ganesh et al. AGM proceedings result and correctly says it does not
   apply. The 10 October 2024 full version at ePrint 2023/147 supersedes that
   result with a programmable-ROM generic chain. Cite both history and the
   superseding version. The new result is promising but still conditional on
   exact V7 FS-EXT, canonical simulation, and WUR proofs.

5. **Finding — Fiat–Shamir 1987 is background only.** It should not be cited
   as the security theorem for the many-round, Merkle-compiled V7 protocol.

## Lean-interface audit

### Existing interfaces

- `TheftResistance.lean::KnowledgeExtractor` is a deterministic total map
  `Statement -> Execution -> Witness` with pointwise validity for every
  accepting execution. It contains no adversary, query bound, black-box access,
  restart semantics, probability space, efficiency, or knowledge error.
- `TheftResistance.lean::SimExtractor` has the same pointwise shape and leaves
  history, simulator programming, freshness, query counts, and failure
  probability inside an opaque `AcceptsSim` predicate.
- `V5AdaptiveObservedTheftGame.lean::ExtractAfterObservation` adds a public
  history argument but remains a deterministic convenience function rather
  than a simulation-extractability experiment.
- `V7ConditionalCompleteSecurity.lean` explicitly proves soundness only.
- `V6PublishedTheoremInterfaces.lean` and its correlated-agreement predicates
  are existential mathematical properties, not algorithmic decoders.

### New interface

`Pool/KnowledgeExtractorInterface.lean` adds:

- explicit extractor access modes (`oneRecordedRun`, classical black-box
  restart, quantum black-box, algebraic model);
- exact BCS 2016, Block et al. classical RBR, and S-two claimed error
  expressions;
- an algorithmic round-by-round knowledge interface;
- an algorithmic finite-list decoder interface;
- a fixed-statement classical BCS AoK guarantee with probabilistic extraction
  rather than pointwise success;
- a separate V7 Merkle query-graph result with explicit failure categories;
- a programmable-ROM observed-proof simulation-extractability boundary; and
- uninhabited V7 and V7-observed-proof obligation structures.

The theorem `bcsExtractor_is_not_typed_as_one_recorded_run` records the
operational distinction forced by the BCS theorem shape.

## Required closure sequence

### K1.2 — exact 208-bit Merkle query graph

Define the two typed tree grammars and an extractor over the adversary's
SHA-256 query database. Prove that each accepted root reconstructs one complete
received word or emits a concrete missing-query, guessed-prefix, or
truncated-collision event. Derive the raw bound as a function of total SHA-256
queries, with the two trees and domain tags included.

The exact deployed grammar and required combined two-tree theorem are frozen
in `docs/v7-k1.2-merkle-query-graph-spec.md`.

### K1.3 — executable circle-code decoders

Instantiate S-two Theorem 7 for the exact `2^20` width-29 and `2^18` final
domains. Expose finite output lists, completeness, list caps, and runtime. An
existential `CurveDecodable` predicate is insufficient.

### K1.4 — one candidate chain

Use the exact C1/C2 commitments, challenges, OOD values, fold equations,
conditioned q16 checks, and final coefficients to select one consistent chain.
Do not choose unrelated existential candidates at successive layers.

### K1.5 — trace to spend witness

Implement and prove a deterministic `AcceptedTrace -> SpendWitness` decoder for
the exact Pool deposit/transfer/withdraw relation, then bridge it to accepted
production Rust/Aeneas traces.

### K1.6 — observed/simulated proofs

Instantiate the Ganesh et al. 2024 programmable-ROM chain or another exact
theorem. Prove the V7 canonical simulator and programming-abort bound,
FS-EXT, FS/SR-WUR, statement/attempt/proof-account freshness, and the combined
raw error. Do not infer this from hiding or ordinary AoK.

## Release decision

**Finding:** V7's deterministic verifier, soundness arithmetic, and atomic
state-transition work are valuable and independent of this audit.

**Blocker:** They do not close theft resistance for an uncapped custody pool.
Until K1 or a replacement K2 compiler theorem is fully instantiated, preserve
the roadmap controls: experimental labeling, capped TVL/per-note value,
prominent extractor risk disclosure, monitoring, and no immutable high-value
custody.

**Inference:** A defensible path exists without changing the deployed
cryptography: build the V7-specific Merkle query graph, instantiate the
algorithmic S-two decoder, and supply the RBR/candidate/trace chain. The
observed-proof upgrade then has a modern ROM framework. The audit does not yet
establish that the resulting losses fit the desired numerical custody target.
