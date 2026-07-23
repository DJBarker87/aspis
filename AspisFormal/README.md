# AspisFormal

`AspisFormal` is the maintained Lean 4 proof layer for Aspis. It kernel-checks
the finite algebra, parameter arithmetic, hiding constructions, relation
closure, and security-capstone plumbing used by the released q18/g37
construction and the current V5 candidate.

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

Every audited theorem depends only on
`{propext, Classical.choice, Quot.sound}`, Lean/mathlib's standard logical
base. The project contains no `sorry`, custom axiom, `native_decide`, or
compiled-evaluation shortcut. Poseidon2 known-answer theorems use kernel
`decide` on pinned round transitions.

## Two artefacts, one maintained model

The formal tree covers two related but distinct artefacts:

- **q18/g37, tag 65:** the construction executed on mainnet-beta on
  2026-07-16. Its formal layer checks the relation, finite security arithmetic,
  hiding lemmas, and selected implementation bindings. The immutable execution
  evidence is in
  [`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/).
- **V5, tag 67:** the current production-default candidate. Its maintained
  mathematics lives here; pinned Charon/Aeneas extraction and the final
  Rust-to-model composition live in
  [`aeneas-verif/`](../aeneas-verif/).

The repository does not use the later V5 proofs to relabel the earlier
mainnet transaction.

## q18/g37 proof status

| Result | Principal module | Status |
| --- | --- | --- |
| Integer value conservation without field wraparound | `ValueConservation.lean` | Proved |
| Range, balance, and asset clauses from constraint residuals | `ArithmetizationCore.lean` | Proved |
| Complete maintained spend relation from Poseidon2/Merkle clauses | `HashMerkleModel.lean` | Proved relative to `Poseidon2Faithful` |
| Manifest-bound Johnson/MCA regime and agreement cap | `SoundnessParams.lean` | Proved |
| Complete finite event ledger and conservative `≤ 2⁻¹⁰⁴` floor | `SoundnessLedger.lean` | Proved |
| Work-normalized `≤ 2⁻¹⁰⁰` endpoint | `SoundnessWorkNormalizedEndpoint.lean` | Proved relative to the cited BCS error formula |
| Circle generator order and same-x criterion | `CircleGroupOrder.lean` | Proved by kernel evaluation and induction |
| Fibre-root distinctness | `CircleFibreRoots.lean` | Proved using the group-order result |
| Distribution-level masking and concrete circle-matrix hiding | `CoreHidingPMF.lean`, `MaskingHiding.lean`, `AspisViewBinding.lean` | Proved for the stated model |
| Poseidon2 permutation, node, owner, note, and nullifier KATs | `Poseidon2Kat.lean` | Proved on the pinned vectors |
| Extractor plus nullifier binding implies theft resistance | `TheftResistance.lean` | Proved as a connective; extractor and simulation-extractability remain cited inputs |

## V5 proof status

| Result | Principal modules | Status |
| --- | --- | --- |
| Component-A rank, schedule, and deployed terminal applicability | `V5AtomicComponentA.lean`, `V5ComponentARankCompletion.lean`, `V5ComponentADeployedTerminalApplicability.lean` | Proved |
| Component-B triangular hiding, spend-difference coverage, commitment and transcript binding | `V5ComponentBTriangularHiding.lean`, `V5ComponentBSpendDifferenceCoverage.lean`, `V5SumcheckCommitment.lean`, `V5SumcheckTranscriptBinding.lean` | Proved for the maintained model |
| Component-C sampler, pivot encoder, exact QM31 tower/codec, residual projection, and four-fold linear runtime | `V5ComponentCSamplerKernel.lean`, `V5ComponentCEncoderCorrespondence.lean`, `V5ComponentCExactTowerDeployment.lean`, `V5ComponentCPreCProjection.lean`, `V5ComponentCConcreteFoldLinearity.lean` | Proved |
| Component-C direct conditional hiding and deployment composition | `V5ComponentCDirectHiding.lean`, `V5ComponentCDeploymentLedger.lean`, `V5ConditionalHidingCapstoneV3.lean` | Proved relative to the named entropy, transcript, PCS, serialization, and hash interfaces |
| Selected-good verifier relation and functional batching | `V5SelectedGoodVerifierRelation.lean`, `V5FunctionalBatching.lean`, `V5GoodGateDotBatching.lean` | Proved |
| Exact 17-attempt production retry control and nonce/work authentication | `V5ProductionCap17RetryControl.lean`, `V5NonceWorkAuthentication.lean` | Proved |
| Work-normalized production endpoint | `V5ImplementedWorkNormalizedEndpoint.lean`, `V5WorkNormalizedApplicabilityRepair.lean` | Proved under the cited cryptographic endpoint formula |

The final source-authentic composition is
`FormalClosureStream1.current_source_combined_capstone` in
[`aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`](../aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean).
It joins maintained A and B, the actual-current C operational and public-output
closures, and the Tag-67 wire/work-verifier theorem.

## Boundary ledger

The formal development deliberately names the interfaces it imports:

1. Published Johnson/MCA/PCS, Fiat–Shamir, extractor, and
   simulation-extractability results are cited rather than reconstructed.
2. Hash collision resistance and random-oracle modelling are cryptographic
   assumptions, not consequences of Lean.
3. The final Tag-67 Rust correspondence retains one exact function-pointer
   boundary:

   ```text
   actualTranscriptGrindingDigest state nonce
     = rustHash state ((3 : Byte) :: nonceLEBytes nonce)
   ```

4. Lean, mathlib, the Rust/Solana toolchain, Charon/Aeneas, and the hardware
   executing them remain in the trusted computing base.

These are the edges of the result. Parser layout, wire projection, the digest
predicate, Component-C public output, six-step work-verifier order, retry
control, and the maintained A/B/C composition are inside the checked closure.
