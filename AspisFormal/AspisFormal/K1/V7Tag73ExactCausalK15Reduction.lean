import AspisFormal.K1.V7Tag73ExactOperationalK15Stage
import AspisFormal.K1.V7Tag73BatchedQuerySourceBridge
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14
import AspisFormal.Pool.V7K15FixedFamilyCausalCover

/-!
# Exact causal reduction of the operational Tag-73 K1.5 failure

The concrete K1.5 classifier retains the predecessor facts needed by its last
gamma/point-claim branch.  This module consumes those facts.  For one exact
operational material value and one restoration-wide selected-chain family, a
K1.5 failure has only three outcomes:

* the restored family already contains a point-compatible K1.4 certificate;
* one of the fixed-family K1.5 events holds; or
* the sampled gamma belongs to the single constrained restoration set.

Downstream code first checks for a point-compatible K1.4 certificate; when
none exists, the third branch is the precise finite event bounded by the
published correlated-decoding cap.  No local post-selected component tuple
is counted.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73ExactCausalK15Reduction

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7CorrelatedPointClaimExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7PointClaimBatchBinding
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29ConstrainedFunctionalExtraction
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Small generic wrapper used to keep the very large operational dependent
type out of the restored-family theorem's elaboration path. -/
theorem accepted_branch_mem_constrained_residual_kernel_friendly
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (fields : FixedFieldView QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (gamma kappa : QM31Exact)
    (available : family.available gamma)
    {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (combinedExact : extraction.combined = family.selected gamma)
    (gammaNonzero : gamma ≠ 0)
    (aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa)
    (noKappaCollision :
      ¬ KappaPointRowCollision fields extraction point kappa) :
    gamma ∈ acceptedRestoredPointConstrainedGammaSet decoder words point
      fields.pointClaim family := by
    classical
    have everyRowZero :=
      every_row_gamma_discrepancy_zero_of_aggregate_exact fields extraction
        point kappa aggregateExact noKappaCollision
    have responseAt := family.responseAt gamma available
    have selectedValid := selected_chain_yields_valid_width29_response decoder
      words gamma disclosedFinal schedule extraction.combined
      extraction.combinedSelected
    have acceptedSupportEqRestored :=
      accepted_restored_support_eq_restored_of_available decoder words family
        gamma available
    have restoredSupportEqSelected :=
      restoredWidth29Strategy_support_eq_selected decoder
        (extractedWidth29InitialWords words) (family.selected gamma)
        family.response gamma responseAt
    have acceptedSupportEqSelected :
        (acceptedRestoredWidth29Strategy decoder words family).support gamma =
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords words) extraction.combined).support
              gamma := by
      rw [acceptedSupportEqRestored, restoredSupportEqSelected, ← combinedExact]
    have acceptedValid : Width29ValidResponse exactInitialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (acceptedRestoredWidth29Strategy decoder words family) gamma := by
      constructor
      · rw [acceptedSupportEqSelected]
        exact selectedValid.1
      · intro index member
        have selectedMember : index ∈
            (selectedCandidateStrategy decoder
              (extractedWidth29InitialWords words) extraction.combined).support
                gamma := by
          rw [← acceptedSupportEqSelected]
          exact member
        have selectedAgreement := selectedValid.2 index selectedMember
        change width29CurveValue (extractedWidth29InitialWords words) gamma index =
          exactInitialEncoder (family.response gamma) index
        rw [responseAt, ← combinedExact, ← initialEncoderExact]
        exact selectedAgreement
    have functionalConstraint : Width29FunctionalConstraint
        (pointFunctional point) fields.pointClaim
        (acceptedRestoredWidth29Strategy decoder words family) gamma := by
      intro row
      have rowZero : rowGammaDiscrepancy fields extraction point row = 0 :=
        congrFun everyRowZero row
      have rowBatchExact :=
        (rowGammaDiscrepancy_eq_zero_iff fields extraction point row).mp rowZero
      calc
        pointFunctional point row
            ((acceptedRestoredWidth29Strategy decoder words family).candidate gamma) =
            pointFunctional point row (family.response gamma) := by rfl
        _ = pointFunctional point row (family.selected gamma).1 := by
          rw [responseAt]
        _ = pointFunctional point row extraction.combined.1 := by
          rw [combinedExact]
        _ = pointFunctional point row
            (batchInitialMessages extraction.components gamma) := by
          rw [CoherentTraceExtraction.combined_eq_batchInitialMessages extraction
            initialEncoderExact]
        _ = width29Batch
            (fun lane => componentPointClaim extraction point row lane) gamma :=
          pointFunctional_batchInitialMessages point row extraction.components gamma
        _ = width29Batch (fields.pointClaim row) gamma := rowBatchExact.symm
    unfold acceptedRestoredPointConstrainedGammaSet
    rw [mem_width29GoodChallenges_iff]
    refine ⟨gammaNonzero, ?_⟩
    constructor
    · simpa [constrainedWidth29Strategy, functionalConstraint] using
        acceptedValid.1
    · intro index member
      have acceptedMember : index ∈
          (acceptedRestoredWidth29Strategy decoder words family).support gamma := by
        simpa [constrainedWidth29Strategy, functionalConstraint] using member
      simpa [constrainedWidth29Strategy, functionalConstraint] using
        acceptedValid.2 index acceptedMember

/-- Exact deterministic causal reduction for the literal operational K1.5
failure.  The only family-facing premises are availability and selected-chain
identity at the actual gamma, plus the pre-challenge semantic plan family used
by the already proved fixed-family root inventory. -/
theorem exact_operational_k15_failure_reduces_to_restored_or_fixed
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k13 : ExactK13Certificate decoder input k12}
    {k14 : ExactK14Certificate decoder decoderBinding input k12}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (material : ExactTag73OperationalK15Material input k12 k14 basis rc
      poseidon)
    (family : RestoredSelectedChainFamily decoder k12.words)
    (familyAvailable : family.available (exactK13ParsedProof input).gamma)
    (familySelected : family.selected (exactK13ParsedProof input).gamma =
      k14.extraction.combined)
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords k12.words) →
        FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords k12.words) →
        AdaptiveDegree27MessagePlan QM31Exact)
    (terminalExact : ∀ member : k14.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords k12.words),
      terminal (extractedFixedWidth29Candidate k14.extraction member) =
        extractedFixedTerminalPlan basis rc fixedInstance.statement
          k14.extraction (exactOperationalChallenge input .lambda)
          (exactOperationalChallenge input .chi) material.data.helper)
    (sumcheckCausal : ∀ member : k14.extraction.components ∈
        fixedWidth29TupleList decoder
          (extractedWidth29InitialWords k12.words),
      WireUsesAdaptiveDegree27Plan
        (acceptedProductionWireOfCompact
          (operationalFixedFields material.data.decoded)
          (operationalAcceptedRun input material.data.decoded
            material.data.fixedDecode)
          (operationalCompactEvidence input material.data.decoded
            material.data.fixedDecode))
        material.exactHonest
        (sumcheck (extractedFixedWidth29Candidate k14.extraction member)))
    (failure : ExactTag73OperationalK15Failure material) :
    HasAcceptedRestoredPointCompatibleK14 decoder k12.words
        (operationalAcceptedRun input material.data.decoded
          material.data.fixedDecode).point
        (operationalFixedFields material.data.decoded).pointClaim family ∨
      FixedFamilyK15Failure terminal sumcheck
          (operationalFixedFields material.data.decoded) k14.extraction
          (fun coordinate => exactOperationalChallenge input
            (.zerocheckPoint coordinate))
          (operationalAcceptedRun input material.data.decoded
            material.data.fixedDecode).point
          (exactOperationalChallenge input .lambda)
          (exactOperationalChallenge input .chi)
          (exactOperationalChallenge input .theta)
          (exactOperationalChallenge input .mu)
          (exactOperationalChallenge input .kappa) material.data.execution ∨
        (exactK13ParsedProof input).gamma ∈
          acceptedRestoredPointConstrainedGammaSet decoder k12.words
            (operationalAcceptedRun input material.data.decoded
              material.data.fixedDecode).point
            (operationalFixedFields material.data.decoded).pointClaim family := by
  classical
  let fields := operationalFixedFields material.data.decoded
  let transcript := operationalAcceptedRun input material.data.decoded
    material.data.fixedDecode
  let compact := operationalCompactEvidence input material.data.decoded
    material.data.fixedDecode
  have fixedMember : k14.extraction.components ∈
      fixedWidth29TupleList decoder
        (extractedWidth29InitialWords k12.words) :=
    coherentTraceExtraction_components_mem_fixedWidth29TupleList
      material.source.initialEncoderEq k14.extraction
  rcases failure.evidence with ⟨kind, holds, predecessorClear⟩
  apply failureKind_elim_causal
    basis rc fixedInstance.statement fields transcript compact k14.extraction
    (exactOperationalChallenge input .lambda)
    (exactOperationalChallenge input .chi)
    (exactOperationalChallenge input .theta)
    (fun coordinate => exactOperationalChallenge input
      (.zerocheckPoint coordinate))
    (exactOperationalChallenge input .mu) material.data.helper
    material.data.mask material.exactHonest
    (exactOperationalChallenge input .kappa) material.data.execution fixedMember
    terminal sumcheck (terminalExact fixedMember) (sumcheckCausal fixedMember)
    kind
  · intro fixed
    exact Or.inr (Or.inl fixed)
  · intro kindIsGamma _gammaCollision
    obtain ⟨noOodEvent, noAlphaEvent, noKappaEvent⟩ :=
      predecessorClear kindIsGamma
    have noOod :
        ¬ material.data.execution.discrepancyTrace.MixCancellation 0 := by
      change ¬ material.data.execution.discrepancyTrace.MixCancellation 0 at noOodEvent
      exact noOodEvent
    have noAlpha : ∀ round : Fin 4,
        ¬ material.data.execution.discrepancyTrace.AlphaRepair round := by
      intro round repair
      apply noAlphaEvent
      exact ⟨round, repair⟩
    have noKappa : ¬ KappaPointRowCollision fields k14.extraction
        transcript.point (exactOperationalChallenge input .kappa) := by
      change ¬ KappaPointRowCollision fields k14.extraction transcript.point
        (exactOperationalChallenge input .kappa) at noKappaEvent
      exact noKappaEvent
    have positive := positive_relation_facts_of_exact_source_bindings
      material.source.sourceBinding material.source.finalSource
      material.source.querySource.toOperationalSourceBinding
      (material.authenticatedQueryValuesExact k13)
      material.data.terminalSource
    have aggregateExact :
        claimedPointBatch fields (exactK13ParsedProof input).gamma
            (exactOperationalChallenge input .kappa) =
          extractedPointBatch k14.extraction transcript.point
            (exactOperationalChallenge input .kappa) := by
      exact (relation_and_point_aggregate_exact_outside_relation_collisions
        material.data.masks fields k14.extraction transcript.point
        (exactOperationalChallenge input .kappa) material.data.execution
        material.source.initialEncoderEq
        material.source.finalSource.initialValuesExact
        material.source.executionInitialWeights
        material.source.executionInitialClaim material.source.inactiveExact
        positive.1 positive.2.1 positive.2.2 noOod noAlpha).2.2.2
    right
    right
    · classical
      have everyRowZero :=
        every_row_gamma_discrepancy_zero_of_aggregate_exact fields
          k14.extraction transcript.point
          (exactOperationalChallenge input .kappa) aggregateExact noKappa
      have responseAt := family.responseAt (exactK13ParsedProof input).gamma
        familyAvailable
      have selectedValid := selected_chain_yields_valid_width29_response decoder
        k12.words (exactK13ParsedProof input).gamma
        (exactK13ParsedProof input).disclosedFinal
        (exactK13ParsedProof input).schedule k14.extraction.combined
        k14.extraction.combinedSelected
      have acceptedSupportEqRestored :=
        accepted_restored_support_eq_restored_of_available decoder k12.words
          family (exactK13ParsedProof input).gamma familyAvailable
      have restoredSupportEqSelected :=
        restoredWidth29Strategy_support_eq_selected decoder
          (extractedWidth29InitialWords k12.words)
          (family.selected (exactK13ParsedProof input).gamma) family.response
          (exactK13ParsedProof input).gamma responseAt
      have acceptedSupportEqSelected :
          (acceptedRestoredWidth29Strategy decoder k12.words family).support
              (exactK13ParsedProof input).gamma =
            (selectedCandidateStrategy decoder
              (extractedWidth29InitialWords k12.words)
              k14.extraction.combined).support
                (exactK13ParsedProof input).gamma := by
        rw [acceptedSupportEqRestored, restoredSupportEqSelected,
          ← familySelected.symm]
      have acceptedValid : Width29ValidResponse exactInitialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
          (extractedWidth29InitialWords k12.words)
          (acceptedRestoredWidth29Strategy decoder k12.words family)
          (exactK13ParsedProof input).gamma := by
        constructor
        · rw [acceptedSupportEqSelected]
          exact selectedValid.1
        · intro index member
          have selectedMember : index ∈
              (selectedCandidateStrategy decoder
                (extractedWidth29InitialWords k12.words)
                k14.extraction.combined).support
                  (exactK13ParsedProof input).gamma := by
            rw [← acceptedSupportEqSelected]
            exact member
          have selectedAgreement := selectedValid.2 index selectedMember
          change width29CurveValue (extractedWidth29InitialWords k12.words)
              (exactK13ParsedProof input).gamma index =
            exactInitialEncoder
              (family.response (exactK13ParsedProof input).gamma) index
          rw [responseAt, familySelected,
            ← material.source.initialEncoderEq]
          exact selectedAgreement
      have functionalConstraint : Width29FunctionalConstraint
          (pointFunctional
            (operationalAcceptedRun input material.data.decoded
              material.data.fixedDecode).point)
          (operationalFixedFields material.data.decoded).pointClaim
          (acceptedRestoredWidth29Strategy decoder k12.words family)
          (exactK13ParsedProof input).gamma := by
        intro row
        have rowZero : rowGammaDiscrepancy fields k14.extraction
            transcript.point row = 0 := congrFun everyRowZero row
        have rowBatchExact :=
          (rowGammaDiscrepancy_eq_zero_iff fields k14.extraction
            transcript.point row).mp rowZero
        calc
          pointFunctional transcript.point row
              ((acceptedRestoredWidth29Strategy decoder k12.words family).candidate
                (exactK13ParsedProof input).gamma) =
              pointFunctional transcript.point row
                (family.response (exactK13ParsedProof input).gamma) := by rfl
          _ = pointFunctional transcript.point row
              (family.selected (exactK13ParsedProof input).gamma).1 := by
            rw [responseAt]
          _ = pointFunctional transcript.point row k14.extraction.combined.1 := by
            rw [familySelected]
          _ = pointFunctional transcript.point row
              (batchInitialMessages k14.extraction.components
                (exactK13ParsedProof input).gamma) := by
            rw [CoherentTraceExtraction.combined_eq_batchInitialMessages
              k14.extraction material.source.initialEncoderEq]
          _ = width29Batch
              (fun lane => componentPointClaim k14.extraction transcript.point
                row lane) (exactK13ParsedProof input).gamma :=
            pointFunctional_batchInitialMessages transcript.point row
              k14.extraction.components (exactK13ParsedProof input).gamma
          _ = width29Batch (fields.pointClaim row)
              (exactK13ParsedProof input).gamma := rowBatchExact.symm
      unfold acceptedRestoredPointConstrainedGammaSet
      rw [mem_width29GoodChallenges_iff]
      refine ⟨exact_parsed_gamma_ne_zero material.source.sourceBinding, ?_⟩
      constructor
      · simpa [constrainedWidth29Strategy, functionalConstraint] using
          acceptedValid.1
      · intro index member
        have acceptedMember : index ∈
            (acceptedRestoredWidth29Strategy decoder k12.words family).support
              (exactK13ParsedProof input).gamma := by
          simpa [constrainedWidth29Strategy, functionalConstraint] using member
        simpa [constrainedWidth29Strategy, functionalConstraint] using
          acceptedValid.2 index acceptedMember
  · exact holds

#print axioms exact_operational_k15_failure_reduces_to_restored_or_fixed
#print axioms accepted_branch_mem_constrained_residual_kernel_friendly

end

end AspisK1.V7Tag73ExactCausalK15Reduction
