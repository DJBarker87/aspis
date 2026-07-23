# AspisFormal

`AspisFormal` is the maintained Lean 4 proof layer for Aspis. This file is the
canonical proof-status ledger for the repository as of the current `main`
branch. Older module comments and archived reports record the state at the time
they were written; they do not override this ledger.

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

The audited capstones depend only on
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
- **V5, tag 67** is the frozen mainnet candidate. The exact SBF finalized the
  atomic Tag-67 path on devnet on 2026-07-23 at 1,335,952 CU. Its maintained
  mathematics lives here; pinned Charon/Aeneas extraction and the final
  Rust-to-model composition live in
  [`aeneas-verif/`](../aeneas-verif/), and the execution record lives in the
  [`V5 candidate bundle`](../release/aspis-v5-tag67-frozen-candidate-v1/).

The later V5 proof does not retroactively relabel the tag-65 transaction.

## q18/g37 ledger

| Result | Principal module | Status |
| --- | --- | --- |
| Integer value conservation without field wraparound | `ValueConservation.lean` | **PROVED** |
| Range, balance, and asset clauses from constraint residuals | `ArithmetizationCore.lean` | **PROVED** |
| Complete maintained spend relation from Poseidon2/Merkle clauses | `HashMerkleModel.lean` | **PROVED relative to `Poseidon2Faithful`** |
| Manifest-bound Johnson/MCA regime and agreement cap | `SoundnessParams.lean` | **PROVED** |
| Complete finite event ledger and conservative `≤ 2⁻¹⁰⁴` floor | `SoundnessLedger.lean` | **PROVED** |
| Work-normalized `≤ 2⁻¹⁰⁰` endpoint | `SoundnessWorkNormalizedEndpoint.lean` | **PROVED relative to the cited BCS error formula** |
| Circle generator order, same-x criterion, and fibre-root distinctness | `CircleGroupOrder.lean`, `CircleFibreRoots.lean` | **PROVED** |
| Distribution-level masking and concrete circle-matrix hiding | `CoreHidingPMF.lean`, `MaskingHiding.lean`, `AspisViewBinding.lean` | **PROVED for the stated model** |
| Poseidon2 permutation, node, owner, note, and nullifier known-answer bindings | `Poseidon2Kat.lean` | **PROVED on the pinned vectors** |
| Extractor plus nullifier binding implies theft resistance | `TheftResistance.lean` | **PROVED as a connective; extractor and simulation-extractability are cited inputs** |

## V5 maintained-model ledger

| Result | Principal modules | Status |
| --- | --- | --- |
| Component-A rank, schedule, and deployed terminal applicability | `V5AtomicComponentA.lean`, `V5ComponentARankCompletion.lean`, `V5ComponentADeployedTerminalApplicability.lean` | **PROVED** |
| Component-B triangular hiding, spend-difference coverage, commitment, and transcript binding | `V5ComponentBTriangularHiding.lean`, `V5ComponentBSpendDifferenceCoverage.lean`, `V5SumcheckCommitment.lean`, `V5SumcheckTranscriptBinding.lean` | **PROVED for the maintained model** |
| Component-C sampler, pivot encoder, exact QM31 tower/codec, residual projection, and four-fold runtime | `V5ComponentCSamplerKernel.lean`, `V5ComponentCEncoderCorrespondence.lean`, `V5ComponentCExactTowerDeployment.lean`, `V5ComponentCPreCProjection.lean`, `V5ComponentCConcreteFoldLinearity.lean` | **PROVED** |
| Component-C direct conditional hiding and deployment composition | `V5ComponentCDirectHiding.lean`, `V5ComponentCDeploymentLedger.lean`, `V5ConditionalHidingCapstoneV3.lean` | **PROVED relative to the named entropy, transcript, PCS, serialization, and hash interfaces** |
| Selected-good verifier relation and functional batching | `V5SelectedGoodVerifierRelation.lean`, `V5FunctionalBatching.lean`, `V5GoodGateDotBatching.lean` | **PROVED** |
| Exact 17-attempt retry control and nonce/work authentication | `V5ProductionCap17RetryControl.lean`, `V5NonceWorkAuthentication.lean` | **PROVED** |
| Work-normalized V5 endpoint | `V5ImplementedWorkNormalizedEndpoint.lean`, `V5WorkNormalizedApplicabilityRepair.lean` | **PROVED under the cited cryptographic endpoint formula** |

## V5 source-authentic closure

The final integration theorem is
`FormalClosureStream1.current_source_combined_capstone` in
[`CurrentSourceABCapstone.lean`](../aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean).

| Runtime seam | Closing theorem | Status |
| --- | --- | --- |
| Source-extracted Component-A matrix execution to maintained GoodA at the frozen concrete schedule | `FormalClosureStream1.component_a_actual_matches_maintained` | **CLOSED FOR THE FROZEN SCHEDULE** |
| Generated Component-B sampler/evaluator/C2 layout to maintained ten-round terminal | `FormalClosureStream1.component_b_actual_matches_maintained` | **CLOSED** |
| Actual four Component-C rounds, finish, packer, and deployed public rows | `generated_public_run_output_matches_deployed` | **CLOSED** |
| Tag-67 magic, LE64 reads, exact projection, digest predicate, and six ordered work checks | `AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure` | **CLOSED subject to one exact hash-call equation** |
| Combined A/B/C public output and Tag-67 verifier at that schedule | `FormalClosureStream1.current_source_combined_capstone` | **CLOSED under the same equation** |

That remaining equation is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

It is the concrete function-pointer call boundary, not a generic
“Rust matches Lean” premise.

## Disposition of the older obligation list

Several older modules and archived reports intentionally say that work remains.
Here is the current disposition of the items most likely to be encountered:

| Older obligation | Current disposition |
| --- | --- |
| Component-A universal 48×48 conversion table | **SUPERSEDED FOR THE FINAL V5 ROUTE**. The source-authentic route proves the reachable even-kernel conversion and twelve GoodA shifts used by the frozen schedule. The unrelated Component-B width-64 table is closed by `AspisV5Row256Aeneas.generatedRow256Conversion64_exact`. |
| Component-C stored-OOD identity and public output | **CLOSED BY** `generated_public_run_output_matches_deployed`; the stored OOD pair, four rounds, finish, and packed output are in the theorem chain. |
| Discrete q18 availability and universal executable GoodA correspondence | **RUNTIME ENFORCEMENT CLOSED; UNIVERSAL SOURCE CORRESPONDENCE STILL OPEN**. The verifier recomputes GoodA/GoodB for every selected branch and rejects failure; the 17-attempt host fails closed if it finds no good schedule. The source-authentic theorem currently proves the concrete frozen schedule, not every possible schedule. A universal source theorem would additionally need the generic circle-query kernel, terminal-minor construction, and fraction-free determinant loop invariants. Availability is a liveness question, not a fail-closed acceptance gap. |
| Comprehensive all-proof-bytes serialization faithfulness | **STILL OPEN**. The final route closes the Component-B layout, Component-C public vector/packer, and Tag-67 work wire separately; it does not claim one universal serializer theorem for the complete joint cryptographic view. |
| Adaptive sumcheck/PCS/Fiat–Shamir security from first principles | **STILL OPEN AS AN INTERNAL REPROOF**. The release uses the cited PCS/BCS and Fiat–Shamir results with an explicit parameter mapping. |
| Universal all-input Rust Poseidon2 equality | **STILL OPEN**. Constants and known-answer executions are pinned; `Poseidon2Faithful` remains the named all-input interface used by the relation theorem. |

The runtime enforces the GoodA/GoodB predicate on every selected branch. The
source-authentic Component-A theorem is specialized to the frozen schedule;
the source-authentic B, C, public-output, work-wire, and ordered-verifier
closures have the broader scopes stated above. Published PCS/Fiat–Shamir
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

For the pinned source-authentic capstones:

```sh
aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh
aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh
```
