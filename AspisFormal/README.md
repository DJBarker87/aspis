# Lean proofs of the Aspis construction

This directory contains the mathematical proof layer for Aspis. Lean checks
substantial parts of the private-spend relation, the concrete security
calculations used by the release, group and hiding results, fixed Poseidon2
executions, and the Lean models for current V5 verifier components.

Aspis also has a second proof layer that connects selected production Rust to
these models through Charon, Aeneas, and Lean bridge proofs. The accessible
overview is
[`docs/formal-verification.md`](../docs/formal-verification.md); the exact
Rust-to-model coverage is recorded in
[`aeneas-verif/README.md`](../aeneas-verif/README.md).

The detailed table below states what is proved, what uses a named assumption,
and what remains outside the current release theorem. Older module comments and
archived reports record the state at the time they were written.

## How the proof layers fit together

The maintained Lean project answers mathematical questions: it proves the
relations and concrete release calculations stated below, relative to explicit
cryptographic interfaces where noted. The Charon/Aeneas project answers a
different implementation question: selected production V5 Rust paths agree
with those Lean models. Reproducible-build evidence then identifies the exact
SBF, while tests, runtime replay, exact-wire simulation, and finalized chain
receipts exercise the deployed system.

These are complementary assurance layers, not one theorem that universally
proves the cryptography, every Rust path, compilation, and Solana execution at
once. In particular, the Rust bridge covers Component A at the selected
release schedule, generated Component B through its ten-round terminal,
Component C's four rounds through deployed public output, the V5 work wire and
six ordered work checks, and their selected-schedule composition. The runtime
verifier recomputes GoodA and GoodB for every selected branch, but the universal
all-schedule Component-A source theorem remains open.

The best independent-review targets are therefore the missing links: the reduction
from the full execution view to the maintained hiding model and applicability
of the cited PCS/Fiat–Shamir results; the custom Poseidon2-M31 primitive and
universal Rust correspondence; the one transcript hash-call equation shown
below; production Rust and serialization outside the selected extraction; and
Solana account/state, refund, and runtime-pricing behavior. The complete
boundary ledger is
[`docs/assumptions-ledger.md`](../docs/assumptions-ledger.md).

## Build the proofs

```sh
cd AspisFormal
lake exe cache get
lake build
```

CI runs the same project in
[`lean.yml`](../.github/workflows/lean.yml). Parameter and constant bindings
back to Rust are checked by
[`param-binding.yml`](../.github/workflows/param-binding.yml) and
[`poseidon-binding.yml`](../.github/workflows/poseidon-binding.yml).

The audited integration theorems depend only on
`{propext, Classical.choice, Quot.sound}`, Lean/mathlib's standard logical
base. The project contains no `sorry`, custom axiom, `native_decide`, or
compiled-evaluation shortcut. Poseidon2 known-answer theorems use kernel
`decide` on pinned round transitions.

## Two artefacts

- **q18/g37, tag 65** is the construction executed on mainnet-beta on
  2026-07-16. Its formal layer checks the relation, finite security arithmetic,
  hiding lemmas, and selected implementation bindings. Its immutable evidence
  is in
  [`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/).
- **V5** is the later release line (wire tag 67). Its exact frozen SBF finalized the
  atomic path on devnet on 2026-07-23 at 1,335,952 CU and subsequently
  finalized the mainnet-beta V5 state transition at slot 435019536 at
  1,334,452 CU. Its maintained mathematics lives here, and pinned
  Charon/Aeneas extraction plus the final Rust-to-model composition live in
  [`aeneas-verif/`](../aeneas-verif/). The frozen inputs remain in the
  [`V5 candidate bundle`](../release/aspis-v5-tag67-frozen-candidate-v1/);
  the subsequent chain outcome and cleanup are in the
  [`V5 mainnet record`](../release/aspis-v5-tag67-mainnet-v1/).

The later V5 proof does not retroactively relabel the tag-65 transaction.

## q18/g37 theorem status

| Result | Principal module | Status |
| --- | --- | --- |
| Integer value conservation without field wraparound | `ValueConservation.lean` | **PROVED** |
| Range, balance, and asset clauses from constraint residuals | `ArithmetizationCore.lean` | **PROVED** |
| Maintained spend relation from arithmetic plus Poseidon2/Merkle clauses | `ArithmetizationCore.lean`, `HashMerkleModel.lean` | **PROVED from an explicit `HashMerkleWitness`, relative to `Poseidon2Faithful`; deriving that witness from complete deployed-verifier acceptance is outside this theorem** |
| Manifest-bound Johnson/MCA regime and agreement cap | `SoundnessParams.lean` | **PROVED** |
| Complete finite-event calculation and conservative `≤ 2⁻¹⁰⁴` floor | `SoundnessLedger.lean` | **PROVED** |
| Work-normalized `≤ 2⁻¹⁰⁰` endpoint | `SoundnessWorkNormalizedEndpoint.lean` | **PROVED relative to the cited BCS error formula** |
| Circle generator order, same-x criterion, and fibre-root distinctness | `CircleGroupOrder.lean`, `CircleFibreRoots.lean` | **PROVED** |
| Distribution-level masking and concrete circle-matrix hiding | `CoreHidingPMF.lean`, `MaskingHiding.lean`, `AspisViewBinding.lean` | **PROVED for the stated model** |
| Poseidon2 permutation, node, owner, note, and nullifier known-answer bindings | `Poseidon2Kat.lean` | **PROVED on the pinned vectors** |
| Wrong-secret and same-fixed-leaf/different-opening events reduce to extractor failure or target second-preimage events | `TheftResistance.lean`, `V5TheftResistance.lean` | **PROVED, including exact V5 relation instantiations. The old impossible global-injectivity premise has been removed. The extractor input is a complete execution record, not public proof bytes alone. The fuller V5 fixed-victim game is recorded in the V5 table below** |

## V5 mathematical model status

| Result | Principal modules | Status |
| --- | --- | --- |
| Component-A rank, schedule, and deployed terminal applicability | `V5AtomicComponentA.lean`, `V5ComponentARankCompletion.lean`, `V5ComponentADeployedTerminalApplicability.lean` | **PROVED** |
| Component-B triangular hiding, spend-difference coverage, terminal-functional algebra, and transcript-order logic | `V5ComponentBTriangularHiding.lean`, `V5ComponentBSpendDifferenceCoverage.lean`, `V5SumcheckCommitment.lean`, `V5SumcheckTranscriptBinding.lean` | **PROVED for the Lean model; opening uniqueness, hash security, Rust absorb/challenge correspondence, and the deployed PCS link remain interfaces** |
| Component-C sampler, pivot encoder, QM31 tower/codec, residual projection, and four-fold runtime | `V5ComponentCSamplerKernel.lean`, `V5ComponentCEncoderCorrespondence.lean`, `V5ComponentCExactTowerDeployment.lean`, `V5ComponentCPreCProjection.lean`, `V5ComponentCConcreteFoldLinearity.lean` | **PROVED** |
| Component-C direct conditional hiding and deployment composition | `V5ComponentCDirectHiding.lean`, `V5ComponentCDeploymentLedger.lean`, `V5ConditionalHidingCapstoneV3.lean` | **CONDITIONAL MODEL RESULT relative to the named entropy, sampler, projection, transcript, PCS, serialization, compiler, and hash interfaces; this final model theorem is not a deployed V5 zero-knowledge theorem** |
| Good-gate verifier relation and functional batching | `V5SelectedGoodVerifierRelation.lean`, `V5FunctionalBatching.lean`, `V5GoodGateDotBatching.lean` | **PROVED** |
| Exact 17-attempt retry control and nonce/work authentication | `V5ProductionCap17RetryControl.lean`, `V5NonceWorkAuthentication.lean` | **PROVED** |
| Ideal bounded q18 sampler and fixed bad-set probability | `V5BoundedQuerySamplerUniformity.lean`, `V5WithoutReplacementQuerySoundness.lean` | **PROVED FOR THE FINITE UNIFORM EXPERIMENT. Conditioned on obtaining 18 distinct positions within 64 independent uniform draws, Lean proves that every ordered schedule is equally likely and that the fixed-bad-set probability is the exact descending-factorial ratio. It also proves the unconditioned upper bound when draw exhaustion rejects. For a bad set of at most 6,082 of 131,072 positions, a separate joint-event premise with a 32-bit work factor gives `2^-111`. The SHA/Rust sampling correspondence, the FRI bad-set theorem, and the joint work argument remain external** |
| Relation finite-field count | `V5RelationSumcheckSoundness.lean` | **PROVED FOR THE STATED FINITE SETS. A wrong degree-six boundary claim has at most six matching challenges. For one fixed candidate, false data can cancel through the two sequential mixes on at most a `2 / |K|` fraction of mix pairs. Over all twelve mix-and-alpha challenges, with later rounds allowed to depend on completed earlier rounds, the modeled fixed-candidate repair event has mass at most `32 / |K|`** |
| Exact candidate and verifier-weight folds | `V5FriRelationCandidateBridge.lean` | **PROVED. The natural candidate fold and the verifier's dual weight fold give the same dot product after each arity-four round. The boundary and evaluation discrepancies used in the finite count are derived from the exact round algebra. For any supplied fixed family of `L` candidate strategies, the union of their counted events has ideal uniform mass at most `32 * L / |K|`** |
| Accepted candidate-relative false claim enters the counted event | `V5Tag67RelationListInclusion.lean` | **PROVED FOR THE EXPLICIT CANDIDATE EXECUTION. If all four relation boundary checks and the final dot-product check accept, one candidate's folds reach the published final coefficients, and an initial or out-of-domain claim is false for that candidate, then the twelve relation challenges lie in that candidate's counted event. For a fixed family of at most 240 candidates, the union is at most `32 * 240 / |K|`** |
| V5 list-cap arithmetic | `V5FriListCap.lean` | **PROVED FOR THE FOUR STATED LIST EXPRESSIONS. The Guruswami--Sudan multiplicities are `10`, `10`, `9`, and `6`, and all four resulting numeric bounds are strictly below 240. Applying the Guruswami--Sudan theorem to the actual V5 encoders remains external** |
| Ideal FRI acceptance supplies one matching initial-list member, or an explicit FRI failure | `V5FriCoherentCandidateExtraction.lean` | **PROVED AS A DETERMINISTIC INCLUSION. Ideal q18 acceptance either hits one of six named failures, or one member of a single initial decoder list of at most 240 reaches the published final coefficients through the exact four folds. There is no independent list choice at each round. The cited decoding theorem remains external; its released parameters and encoder side conditions are audited separately** |
| A false no-witness statement makes every list member have a scalar mismatch, or an explicit candidate/trace failure | `V5Tag67CandidateTraceExtraction.lean` | **PROVED AS A DETERMINISTIC INCLUSION. The six named failures are the four-claim batch equation, a four-claim batch collision, 19-lane recombination, public-field binding, arithmetic residuals, and hash/Merkle residuals. Production C1/C2 authentication and extraction of the 19 lanes, plus probability bounds for these failures, remain external** |
| Modeled relation success gives every shared relation check | `V5Tag67ModeledRelationAcceptanceBridge.lean` | **PROVED FOR THE PURE MODEL. Modeled success is equivalent to the four boundary checks and final dot-product check and therefore implies relation acceptance for every initial-list member. Connecting successful Rust callback execution to this model remains external** |
| Accepted-false inclusion | `V5Tag67AcceptedFalseInclusion.lean` | **PROVED AS AN EXPLICIT FIVE-WAY SPLIT. This older split is refined by the projected raw-accounting and width-nineteen candidate-family modules below; do not read its four broad branches as the current final gap list** |
| Exact released width-nineteen theorem application | `V5Width19S2ApplicabilityAudit.lean`, `V5Width19CorrelatedAgreement.lean` | **PROVED FOR THE RELEASED PARAMETERS, CONDITIONAL ON THE CITED DECODING RESULT. Lean checks the exact field, code, distance, threshold, list parameters, degree, and nonzero challenge denominator. The paper itself remains an external premise** |
| Corrected candidate-family event and accounting | `V5Width19CandidateEventBridge.lean`, `V5ProjectedAcceptedFalseRawAccounting.lean`, `V5HundredBitSecurityMargin.lean` | **PROVED FOR THE MODEL AND NAMED CONNECTIONS. The dominant completed-grind batching event is about 71 raw bits. Charging for the 37-bit grind gives a checked core below `0.7 * 2^-100`; external bounded events must fit `0.3 * 2^-100`. Five production-code connections remain** |
| Conservative full-list arithmetic | `V5ConservativeRelationListEndpoint.lean` | **ARITHMETIC CHECK ONLY. Replacing the old relation entry by `32 * 240 / |K|`, Lean checks that the conservative expression remains at most `2^-100`. It keeps the width-29 batch term and `R ≤ 32`, conservative relative to V5 width 19 and `R = 30`, and has only about 0.015 bits of margin. This bounds only the repair-event branch; it does not bound the other four branches, prove Fiat--Shamir or callback correspondence, or establish deployed security. Any further factor requires a new calculation** |
| Extracted V5 arithmetic, Poseidon and Merkle rows imply the complete spend relation | `V5AcceptedSpendRelation.lean` | **PROVED for the deterministic step after extraction, relative to `Poseidon2Faithful`. The proof does not yet derive those rows from arbitrary acceptance by the deployed V5 verifier or bound the probability that extraction fails** |
| Work-normalized V5 endpoint | `V5ImplementedWorkNormalizedEndpoint.lean`, `V5WorkNormalizedApplicabilityRepair.lean` | **CONDITIONAL COMPOSITION. Lean proves the width-19/degree-18 `F*` arithmetic, six-event accounting, exact post-`m0` `R = 30`, and the final implication. The deterministic accepted-false inclusion is now proved separately, but this endpoint still needs bounds for its four unfinished branches: raw Rust relation-model correspondence, raw-to-ideal FRI and Merkle binding, the six FRI failures, and the six candidate/trace failures. Virtual-oracle/code membership, separate-output grinding, transcript correspondence, authenticated-round semantics, PCS/Merkle, Fiat--Shamir, and cited MCA/BCS/CMS applicability also remain external** |
| Explicit V5 false-acceptance composition | `V5DeployedFalseAcceptance.lean` | **PROVED AS A CONDITIONAL STATEMENT. Lean defines the false-acceptance event, takes three parameterized failure predicates, proves their union bound, and derives a work-normalized bound of `2^-100` and an ordinary bound of `min(1, T / 2^100)` for `1 <= T <= 2^128`. A separate source-extracted result gates a caller-supplied predicate family by parsed selector zero, one, or two. The family's real cryptographic meaning, the full callback/run connection, acceptance-to-trace extraction, Poseidon2 faithfulness, the width/round/transcript/commitment assumptions, and the three branch-security bounds remain explicit premises** |
| Private-note Merkle binding and fixed-victim theft game | `ApplicationMerkleBinding.lean`, `V5FixedVictimTheftGame.lean` | **PROVED AS AN EVENT CLASSIFICATION. A different leaf at the victim's exact position and root exposes a concrete node-hash collision. For the attack event defined in Lean, the game separates extraction failure, credential recovery, nullifier collision, note-opening collision, Merkle collision, PDA aliasing, runtime/state failure, and invalid victim setup, and proves the eight-term union bound. Connecting every real deployed attack to that event and supplying numerical cryptographic bounds remain external** |
| Nullifier-marker replay prevention | `V5NullifierMarkerReplay.lean` | **PROVED FOR THE EXPLICIT STATE MODEL. Equal nullifiers derive the same marker address. After a successful marker write, the same nullifier is rejected, and a different nullifier resolving to the same address is also rejected rather than overwriting the marker. Replay prevention therefore does not require PDA injectivity inside this model. The result has not yet been connected to the fixed-victim theft game, which still lists PDA aliasing. The relevant branch is unchanged between the recorded deployed source and current Rust except for the current bump-255 precheck, but that comparison is manual. Machine-checked Rust correspondence and Solana account locking, rollback, and finalized marker persistence remain external** |

## V5 production Rust connection

The principal integration theorem is
`FormalClosureStream1.current_source_combined_capstone` in
[`CurrentSourceABCapstone.lean`](../aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean).

| Implementation path | Theorem | Status |
| --- | --- | --- |
| Source-extracted Component-A matrix execution to maintained GoodA at the selected release schedule | `FormalClosureStream1.component_a_actual_matches_maintained` | **PROVED FOR THE RELEASE SCHEDULE** |
| Generated Component-B sampler/evaluator/C2 layout to maintained ten-round terminal | `FormalClosureStream1.component_b_actual_matches_maintained` | **PROVED under the theorem's successful-call, input-length, and field-encoding premises** |
| Actual four Component-C rounds, finish, packer, and deployed public rows | `generated_public_run_output_matches_deployed` | **PROVED for a `GeneratedPublicRun`, whose fields include successful-call, valid-input, and folded-word/coefficient/challenge execution-to-model equalities** |
| V5 instruction magic byte, LE64 reads, projection, digest predicate, and six ordered work checks | `AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure` | **PROVED subject to one hash-call equation** |
| Combined A/B/C public output and current V5 verifier at that schedule | `FormalClosureStream1.current_source_combined_capstone` | **PROVED as a package of the selected component results under their successful-call, valid-input, Component-C execution/model, and V5 hash-call hypotheses; it is not `arbitrary verifier acceptance → complete spend relation`** |

The remaining equation in the **V5 work-verifier subtheorem** is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

It is the concrete function-pointer call boundary, not a generic
“Rust matches Lean” premise. It is not the only important assumption in the
complete A/B/C composition: in particular, `GeneratedPublicRun` carries
explicit Component-C execution/model equalities, and the final integration theorem
does not prove that ordinary production-verifier acceptance constructs every
component hypothesis or implies the maintained spend relation.

## Status of older open items

Several older modules and archived reports intentionally say that work remains.
Here is the current status of the items most likely to be encountered:

| Older open item | Current status |
| --- | --- |
| Component-A universal 48×48 conversion table | **NOT REQUIRED BY THE FINAL V5 PATH.** The production-Rust proof covers the reachable even-kernel conversion and twelve GoodA shifts used by the release schedule. The unrelated Component-B width-64 table is proved by `AspisV5Row256Aeneas.generatedRow256Conversion64_exact`. |
| Component-C stored-OOD identity and public output | **PROVED FOR THE STATED GENERATED RUN.** `generated_public_run_output_matches_deployed` covers the stored OOD pair, four rounds, finish, and packed output under its explicit run hypotheses. |
| Discrete q18 availability and a universal Rust proof for GoodA | **THE RUNTIME CHECK IS PROVED; THE UNIVERSAL RUST PROOF IS OPEN.** The verifier recomputes GoodA/GoodB for every selected branch and rejects failure; the 17-attempt host fails closed if it finds no good schedule. The production-Rust theorem currently proves the selected release schedule, not every possible schedule. A universal source theorem would additionally need the generic circle-query kernel, terminal-minor construction, and fraction-free determinant loop invariants. Availability is a liveness question, not an acceptance gap. |
| Complete serialization proof for all proof bytes | **OPEN.** The final path proves the Component-B layout, Component-C public vector/packer, and V5 work-byte layout separately; it does not prove one serializer theorem for the complete cryptographic view. |
| V5 relation check, PCS, and Fiat--Shamir soundness | **THE DETERMINISTIC INCLUSION IS PROVED; DEPLOYED PROBABILITY BOUNDS ARE OPEN.** The four new inclusion modules prove that ideal FRI acceptance supplies one member of one initial list through the exact four folds unless one of six named FRI failures occurs; a false no-witness statement makes every list member have a scalar mismatch unless one of six named candidate/trace failures occurs; pure modeled relation success supplies the shared checks; and these facts place a raw accepted false execution in one of those failures or the bounded single-list repair event. The raw relation-model and raw FRI-model failures are also explicit. Only the repair branch has the `32 * 240 / |K|` bound. Rust callback correspondence, Merkle binding, S-two applicability and fold-reduction probabilities, the actual list theorem, C1/C2-to-19-lane extraction, Fiat--Shamir/work, primitive-security, PCS/BCS, and runtime bounds remain external. S-two Theorem 21 proves a different quotient-based protocol. |
| Universal all-input Rust Poseidon2 equality | **OPEN.** Constants and known-answer executions are pinned; `Poseidon2Faithful` remains the named all-input interface used by the relation theorem. |

The runtime enforces the GoodA/GoodB predicate on every selected branch. The
production-Rust Component-A theorem is specialized to the release schedule;
the production-Rust B, C, public-output, work-byte, and ordered-verifier
theorems have the broader scopes stated above. Published PCS/Fiat–Shamir
results and primitive security are the external cryptographic inputs.

## Assumptions and replay

The complete one-page boundary is
[`docs/assumptions-ledger.md`](../docs/assumptions-ledger.md).

For the maintained project:

```sh
cd AspisFormal
lake exe cache get
lake build
```

For the retained production-Rust integration theorems:

```sh
aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh
aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh
```

The integration replay requires the authenticated dependency caches described
in the
[`aeneas-verif` replay notes](../aeneas-verif/README.md#replaying-the-final-integration).
