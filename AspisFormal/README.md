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
with those Lean models. That implementation proof is complete through the
exact initial relation value and decoded relation tail. The complete general
dot product and individual compact-accumulator calculations are proved. The
compact state composition and outer theorem remain. Reproducible-build evidence
then identifies the exact SBF, while tests, runtime replay, exact-wire
simulation, and finalized chain receipts exercise the deployed system.

These are complementary assurance layers, not one theorem that proves the
cryptographic primitives, compiler, every Rust path, and Solana at once. The
accepted-path work starts with one successful translated call to the released
proof checker and derives its parse, transcript, work, queries, authenticated
openings, FRI calculations, final polynomial, claim table, initial relation
value, and relation tail from that same execution. It also joins the complete
general dot product, but does not yet join the compact state evolution to the
outer theorem.

The best independent-review targets are the cited PCS/Fiat--Shamir and
circle-decoding results; the custom Poseidon2-M31 primitive; the SHA-256
callback and primitive-security boundary; production Rust outside the
selected accepting proof-checker path; and Solana account, state, refund, and
runtime behavior. The complete boundary ledger is
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
- **V5** is the later release line. Its exact frozen SBF finalized the
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
| A false no-witness statement makes every list member have a scalar mismatch, or an explicit candidate/trace failure | `V5Tag67CandidateTraceExtraction.lean` | **PROVED AS A DETERMINISTIC INCLUSION. The six named failures are the four-claim batch equation, a four-claim batch collision, 19-lane recombination, public-field binding, arithmetic residuals, and hash/Merkle residuals. The source work supplies the production opening, relation inputs, and general final dot; the compact state composition and outer theorem remain, while probability bounds for the named failures remain external** |
| Modeled relation success gives every shared relation check | `V5Tag67ModeledRelationAcceptanceBridge.lean` | **PROVED FOR THE PURE MODEL. Modeled success is equivalent to the four boundary checks and final dot-product check and therefore implies relation acceptance for every initial-list member. Connecting the selected successful Rust callback to this complete relation call still requires the compact state composition and outer accepted-call theorem** |
| Accepted-false inclusion | `V5Tag67AcceptedFalseInclusion.lean` | **PROVED AS AN EXPLICIT FIVE-WAY SPLIT. This older split is refined by the projected raw-accounting and width-nineteen candidate-family modules below; do not read its four broad branches as the current final gap list** |
| Exact released width-nineteen theorem application | `V5Width19S2ApplicabilityAudit.lean`, `V5Width19CorrelatedAgreement.lean` | **PROVED FOR THE RELEASED PARAMETERS, CONDITIONAL ON THE CITED DECODING RESULT. Lean checks the exact field, code, distance, threshold, list parameters, degree, and nonzero challenge denominator. The paper itself remains an external premise** |
| Corrected candidate-family event and accounting | `V5Width19CandidateEventBridge.lean`, `V5ProjectedAcceptedFalseRawAccounting.lean`, `V5HundredBitSecurityMargin.lean` | **PROVED FOR THE MODEL AND NAMED CONNECTIONS. The dominant completed-grind batching event is about 71 raw bits. Charging for the 37-bit grind gives a checked core below `0.7 * 2^-100`; external bounded events must fit `0.3 * 2^-100`. The selected accepted proof-checker path is connected separately; primitive, literature, compiler, and runtime bounds remain external** |
| Conservative full-list arithmetic | `V5ConservativeRelationListEndpoint.lean` | **ARITHMETIC CHECK ONLY. Replacing the old relation entry by `32 * 240 / |K|`, Lean checks that the conservative expression remains at most `2^-100`. It keeps the width-29 batch term and `R ≤ 32`, conservative relative to V5 width 19 and `R = 30`, and has only about 0.015 bits of margin. This bounds only the repair-event branch; it does not bound the other four branches, prove Fiat--Shamir or callback correspondence, or establish deployed security. Any further factor requires a new calculation** |
| Extracted V5 arithmetic, Poseidon and Merkle rows imply the complete spend relation | `V5AcceptedSpendRelation.lean` | **PROVED for the deterministic step after extraction, relative to `Poseidon2Faithful`. The proof does not yet derive those rows from arbitrary acceptance by the deployed V5 verifier or bound the probability that extraction fails** |
| Work-normalized V5 endpoint | `V5ImplementedWorkNormalizedEndpoint.lean`, `V5WorkNormalizedApplicabilityRepair.lean` | **CONDITIONAL COMPOSITION. Lean proves the width-19/degree-18 arithmetic, six-event accounting, exact post-`m0` `R = 30`, and the final implication. The selected accepted source path discharges the deterministic transcript, opening, FRI, claim-table, initial-value, relation-tail, and general-dot links; its compact state composition and outer theorem remain open. Virtual-oracle/code membership, work reduction, PCS/Merkle security, Fiat--Shamir, published decoding applicability, and numerical primitive bounds remain external** |
| Explicit V5 false-acceptance composition | `V5DeployedFalseAcceptance.lean` | **PROVED AS A CONDITIONAL STATEMENT. Lean defines the false-acceptance event, proves its union bound, and derives a work-normalized bound of `2^-100` and an ordinary bound of `min(1, T / 2^100)` for `1 <= T <= 2^128`. The current accepted-path work supplies all selected-verifier deterministic evidence except the compact state composition and outer accepted-call theorem. Poseidon2 faithfulness, extraction, published cryptographic results, and external event bounds remain explicit inputs** |
| Private-note Merkle binding and fixed-victim theft game | `ApplicationMerkleBinding.lean`, `V5FixedVictimTheftGame.lean` | **PROVED AS AN EVENT CLASSIFICATION. A different leaf at the victim's exact position and root exposes a concrete node-hash collision. For the attack event defined in Lean, the game separates extraction failure, credential recovery, nullifier collision, note-opening collision, Merkle collision, PDA aliasing, runtime/state failure, and invalid victim setup, and proves the eight-term union bound. Connecting every real deployed attack to that event and supplying numerical cryptographic bounds remain external** |
| Nullifier-marker replay prevention | `V5NullifierMarkerReplay.lean` | **PROVED FOR THE EXPLICIT STATE MODEL. Equal nullifiers derive the same marker address. After a successful marker write, the same nullifier is rejected, and a different nullifier resolving to the same address is also rejected rather than overwriting the marker. Replay prevention therefore does not require PDA injectivity inside this model. The result has not yet been connected to the fixed-victim theft game, which still lists PDA aliasing. The relevant branch is unchanged between the recorded deployed source and current Rust except for the current bump-255 precheck, but that comparison is manual. Machine-checked Rust correspondence and Solana account locking, rollback, and finalized marker persistence remain external** |

## V5 production Rust connection

The primary production proof effort is now the accepted-path result under
[`v5-result-aware-source-link-20260821/`](../aeneas-verif/v5-result-aware-source-link-20260821/).
The checked chain starts from one successful translated call to
`verify_mode9_composite_with_live_statement` and constructs the parse,
transcript, work, query, authenticated-opening, FRI, and relation evidence
used by the maintained security event. It is complete through the exact
decoded claim table, initial relation value, and 58-field relation tail. The
complete general dot product and individual compact-accumulator calculations
are proved. The compact state composition and final outer theorem remain open
as of August 24, 2026.

The former Component A/B/C integration theorem remains as a historical staged
result. The accepted-path chain is stronger for the released verifier where
completed because its intermediate values are derived from one execution
instead of being supplied as separate equality hypotheses.

The proof still assumes that Solana's SHA-256 call returns SHA-256 of exactly
the bytes passed to it. Charon, Aeneas, Lean, the Rust/SBF compiler, Solana,
SHA-256 and Poseidon2 security, and the cited decoding and Fiat--Shamir results
are not proved by the source theorem.

## Status of older open items

Several older modules and archived reports intentionally say that work remains.
Here is the current status of the items most likely to be encountered:

| Older open item | Current status |
| --- | --- |
| Component-A universal 48×48 conversion table | **NOT REQUIRED BY THE FINAL V5 PATH.** The production-Rust proof covers the reachable even-kernel conversion and twelve GoodA shifts used by the release schedule. The unrelated Component-B width-64 table is proved by `AspisV5Row256Aeneas.generatedRow256Conversion64_exact`. |
| Component-C stored-OOD identity and public output | **PROVED FOR THE STATED GENERATED RUN.** `generated_public_run_output_matches_deployed` covers the stored OOD pair, four rounds, finish, and packed output under its explicit run hypotheses. |
| Discrete q18 availability and a universal Rust proof for GoodA | **THE RUNTIME CHECK IS PROVED; THE UNIVERSAL RUST PROOF IS OPEN.** The verifier recomputes GoodA/GoodB for every selected branch and rejects failure; the 17-attempt host fails closed if it finds no good schedule. The production-Rust theorem currently proves the selected release schedule, not every possible schedule. A universal source theorem would additionally need the generic circle-query kernel, terminal-minor construction, and fraction-free determinant loop invariants. Availability is a liveness question, not an acceptance gap. |
| Complete serialization proof for all proof bytes | **OPEN.** The final path proves the Component-B layout, Component-C public vector/packer, and V5 work-byte layout separately; it does not prove one serializer theorem for the complete cryptographic view. |
| V5 relation check, PCS, and Fiat--Shamir soundness | **THE MATHEMATICAL MODEL INCLUSION IS PROVED; THE SELECTED SOURCE CONNECTION IS COMPLETE THROUGH THE INITIAL RELATION VALUE AND 58-FIELD TAIL, THE GENERAL DOT PRODUCT IS COMPLETE, AND THE COMPACT COMPONENT CALCULATIONS ARE PROVED.** The compact state composition and final outer theorem remain open. Published decoding/PCS/Fiat--Shamir results, SHA-256 and Poseidon2 security, extraction, compiler, and runtime bounds also remain external. |
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

For the production-Rust accepted path, use the Lean 4.32 replay recorded under
[`v5-result-aware-source-link-20260821/`](../aeneas-verif/v5-result-aware-source-link-20260821/).
The replay uses the pinned Aeneas environment described in
[`aeneas-verif/README.md`](../aeneas-verif/README.md).
