import AspisFormal.Pool.V7K15FailureRootInventory

/-!
# Deterministic fixed-family cover for the complete V7 K1.5 ledger

The accepted-spend capstone returns thirteen precise failure branches.  Their
local root counts are not by themselves a sound probability argument because
the decoded trace is selected after some of the challenges.  This file proves
the missing deterministic classification for one accepted trace:

* the four semantic branches enter the width-29 family fixed before `theta`;
* the three copy branches enter the C1 family fixed before `lambda` and `chi`;
* the gamma point-lane branch is impossible under the strengthened K1.4
  all-87-point-claims certificate; and
* the five remaining branches retain their literal, non-postselected form.

This is a deterministic theorem.  Random-oracle sampling and probability
composition remain separate, explicit layers.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisPool.V7K15FixedFamilyCausalCover

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyLogUpCollisionBounds
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7K15FailureRootInventory
open AspisPool.V7K15FailureProbabilityComposition
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Width29ComponentExtraction
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV5SumcheckTranscriptBinding
open AspisSumcheckMasking
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-- An active pole is in the fixed-source chi bad set.  Keeping this generic
lemma opaque prevents the dependent concrete registry from being unfolded by
later classification proofs. -/
theorem activePole_mem_fixedSourceChiBad
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact producerValue
      consumerValue)
    (lambda chi : QM31Exact)
    (pole : DeployedCopyActivePole source lambda chi) :
    chi ∈ copyChiPoleSet source lambda ∪
      copyChiNonPoleCollisionSet source lambda := by
  rw [Finset.mem_union]
  apply Or.inl
  simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and,
    producerCompressedMultiset, consumerCompressedMultiset,
    Multiset.mem_map, Finset.mem_val]
  rcases pole with ⟨link, equal⟩ | ⟨link, equal⟩
  · exact Or.inl ⟨link, equal.symm⟩
  · exact Or.inr ⟨link, equal.symm⟩

/-- Every fixed-source rational collision is in the same chi bad set: at a
pole it is charged to the pole branch; away from poles it is a Wronskian
collision. -/
theorem copyChiCollision_mem_fixedSourceChiBad
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact producerValue
      consumerValue)
    (lambda chi : QM31Exact)
    (collision : CopyChiCollision source lambda chi) :
    chi ∈ copyChiPoleSet source lambda ∪
      copyChiNonPoleCollisionSet source lambda := by
  rw [Finset.mem_union]
  by_cases pole : DeployedCopyActivePole source lambda chi
  · apply Or.inl
    simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and,
      producerCompressedMultiset, consumerCompressedMultiset,
      Multiset.mem_map, Finset.mem_val]
    rcases pole with ⟨link, equal⟩ | ⟨link, equal⟩
    · exact Or.inl ⟨link, equal.symm⟩
    · exact Or.inr ⟨link, equal.symm⟩
  · apply Or.inr
    simp only [copyChiNonPoleCollisionSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨collision, ?_, ?_⟩
    · intro member
      apply pole
      left
      simp only [producerCompressedMultiset, Multiset.mem_map,
        Finset.mem_val, Finset.mem_univ, true_and] at member
      rcases member with ⟨link, equal⟩
      exact ⟨link, equal.symm⟩
    · intro member
      apply pole
      right
      simp only [consumerCompressedMultiset, Multiset.mem_map,
        Finset.mem_val, Finset.mem_univ, true_and] at member
      rcases member with ⟨link, equal⟩
      exact ⟨link, equal.symm⟩

/-- A witnessed C1-family tuple-compression failure is membership in the
literal family union used by the probability experiment. -/
theorem packedSourceFamilyTupleCompressionWitness_mem_familyLambdaBad
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource)
    (lambda : QM31Exact)
    (failure : ∃ candidate : Candidate,
      CopyTupleCompressionCollision
        (source candidate).registry lambda) :
    lambda ∈ familyLambdaBad source := by
  classical
  rcases failure with ⟨candidate, collision⟩
  unfold familyLambdaBad
  rw [Finset.mem_biUnion]
  refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
  simpa only [packedLambdaBad, copyLambdaCollisionSet, Finset.mem_filter,
    Finset.mem_univ, true_and] using collision

/-- A witnessed C1-family pole or rational collision is membership in the
literal conditional chi-family union. -/
theorem packedSourceFamilyChiWitness_mem_familyChiBad
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (source : Candidate → PackedDeployedCopySource)
    (lambda chi : QM31Exact)
    (failure : ∃ candidate : Candidate,
      DeployedCopyActivePole
          (source candidate).registry lambda chi ∨
        CopyChiCollision
          (source candidate).registry lambda chi) :
    chi ∈ familyChiBad source lambda := by
  classical
  rcases failure with ⟨candidate, pole | collision⟩
  · unfold familyChiBad
    rw [Finset.mem_biUnion]
    refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
    unfold packedChiBad
    rw [Finset.mem_union]
    apply Or.inl
    simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and,
      producerCompressedMultiset, consumerCompressedMultiset,
      Multiset.mem_map, Finset.mem_val]
    rcases pole with ⟨link, equal⟩ | ⟨link, equal⟩
    · exact Or.inl ⟨link, equal.symm⟩
    · exact Or.inr ⟨link, equal.symm⟩
  · unfold familyChiBad
    rw [Finset.mem_biUnion]
    refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
    unfold packedChiBad
    rw [Finset.mem_union]
    by_cases pole : DeployedCopyActivePole (source candidate).registry
        lambda chi
    · apply Or.inl
      simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and,
        producerCompressedMultiset, consumerCompressedMultiset,
        Multiset.mem_map, Finset.mem_val]
      rcases pole with ⟨link, equal⟩ | ⟨link, equal⟩
      · exact Or.inl ⟨link, equal.symm⟩
      · exact Or.inr ⟨link, equal.symm⟩
    · apply Or.inr
      simp only [copyChiNonPoleCollisionSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨collision, ?_, ?_⟩
      · intro member
        apply pole
        left
        simp only [producerCompressedMultiset, Multiset.mem_map,
          Finset.mem_val, Finset.mem_univ, true_and] at member
        rcases member with ⟨link, equal⟩
        exact ⟨link, equal.symm⟩
      · intro member
        apply pole
        right
        simp only [consumerCompressedMultiset, Multiset.mem_map,
          Finset.mem_val, Finset.mem_univ, true_and] at member
        rcases member with ⟨link, equal⟩
        exact ⟨link, equal.symm⟩

/-- Every coherent extraction belongs to the fixed pre-`gamma` tuple family
once the decoder encoder is identified with the exact deployed encoder. -/
theorem coherentTraceExtraction_components_mem_fixedWidth29TupleList
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words) := by
  have valid := selected_chain_yields_valid_width29_response decoder words
    gamma disclosedFinal schedule extraction.combined
      extraction.combinedSelected
  have shared :
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) extraction.combined).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) extraction.components := by
    simpa only [initialEncoderExact] using extraction.sharedSupport
  exact mem_fixedWidth29TupleList_of_shared_support decoder
    (extractedWidth29InitialWords words) extraction.components
    ((selectedCandidateStrategy decoder
      (extractedWidth29InitialWords words) extraction.combined).support gamma)
    valid.1 shared extraction.everyComponentDecoded

/-- The fixed-family candidate represented by one accepted extraction. -/
def extractedFixedWidth29Candidate
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (member : extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words)) :
    FixedWidth29TupleCandidate decoder (extractedWidth29InitialWords words) :=
  ⟨extraction.components, member⟩

/-- The literal fixed terminal plan of the accepted extracted trace. -/
noncomputable def extractedFixedTerminalPlan
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact) : FixedTerminalAlgebraPlan QM31Exact where
  basis := basis
  constraintRows := extractedConstraintRows statement extraction
    (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
    (deployedCompiledCopyLane
      (concreteDeployedCopyRegistryProjection extraction) lambda chi helper)
  helper := helper

/-- The causal normal form of a K1.5 failure.  Its constructor costs are,
respectively, 30,500, 292,800, 73,100, 1, 1, 2, 24 and 2 roots in the final
ledger. -/
inductive FixedFamilyK15Failure
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (zerocheckPoint point : Fin 10 → QM31Exact)
    (lambda chi theta mu kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact) : Prop where
  | semantic : FixedWidth29SemanticFailure decoder
      (extractedWidth29InitialWords words) terminal sumcheck theta
        zerocheckPoint point mu →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | copyLambda : (∃ candidate : FixedC1TupleCandidate decoder
      (c1Received words),
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder (c1Received words) candidate).registry
        lambda) →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | copyChi : (∃ candidate : FixedC1TupleCandidate decoder
      (c1Received words),
      DeployedCopyActivePole
          (fixedC1CopySourceFamily decoder
            (c1Received words) candidate).registry lambda chi ∨
        CopyChiCollision
          (fixedC1CopySourceFamily decoder
            (c1Received words) candidate).registry lambda chi) →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | muZero : mu = 0 →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | inactiveChi : DeployedCopyInactiveSlotCollision chi →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | oodMix : execution.discrepancyTrace.MixCancellation 0 →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | relationAlpha : (∃ round : Fin 4,
      execution.discrepancyTrace.AlphaRepair round) →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution
  | kappaPointRow : KappaPointRowCollision fields extraction point kappa →
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint point
        lambda chi theta mu kappa execution

/-- Grouping the thirteen canonical branches into the eight constructors
above preserves the exact corrected `396430` numerator. -/
theorem groupedFixedFamilyRootCap_eq_inventory :
    30500 + 292800 + 73100 + 1 + 1 + 2 + 24 + 2 =
      (orderedFailureKinds.map fixedFamilyCausalRootCap).sum := by
  rw [fixedFamilyCausalRootCap_sum_eq_396430]

set_option linter.constructorNameAsVariable false in
theorem failureKind_elim_causal
    {Result : Prop}
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    (statement : V5PublicStatement)
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (fixedMember : extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words))
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact)
    (terminalExact : terminal
      (extractedFixedWidth29Candidate extraction fixedMember) =
        extractedFixedTerminalPlan basis rc statement extraction lambda chi helper)
    (sumcheckCausal : WireUsesAdaptiveDegree27Plan
      (acceptedProductionWireOfCompact fields transcript compact) honest
      (sumcheck (extractedFixedWidth29Candidate extraction fixedMember)))
    (kind : FailureKind)
    (fixedCover :
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint
        transcript.point lambda chi theta mu kappa execution → Result)
    (gammaCover : kind = .gammaPointLane →
      GammaPointLaneCollision fields extraction transcript.point → Result)
    (holds : failureEvent basis rc statement fields transcript compact extraction
      lambda chi theta zerocheckPoint mu helper mask honest kappa execution kind) :
    Result := by
  classical
  let selected := extractedFixedWidth29Candidate extraction fixedMember
  have selectedTerminalExact : terminal selected =
      extractedFixedTerminalPlan basis rc statement extraction lambda chi
        helper := by
    simpa only [selected] using terminalExact
  have semanticSource : SelectedFixedWidth29SemanticSource decoder
      (extractedWidth29InitialWords words) terminal sumcheck selected
      (acceptedProductionWireOfCompact fields transcript compact) honest :=
    selectedFixedWidth29SemanticSourceOfCausal decoder
      (extractedWidth29InitialWords words) terminal sumcheck selected
      (acceptedProductionWireOfCompact fields transcript compact) honest
      (by simpa only [selected] using sumcheckCausal)
  have c1Member : projectWidth29ToC1 extraction.components ∈
      fixedC1TupleList decoder (c1Received words) :=
    width29_member_projects_to_fixedC1TupleList decoder words
      extraction.components fixedMember
  let c1Candidate : FixedC1TupleCandidate decoder (c1Received words) :=
    ⟨projectWidth29ToC1 extraction.components, c1Member⟩
  have c1SourceExact :
      fixedC1CopySourceFamily decoder (c1Received words) c1Candidate =
        packedCopySourceOfExtraction extraction := by
    simpa only [c1Candidate, fixedC1CopySourceFamily] using
      packedCopySourceOfC1Tuple_project_extraction extraction
  cases kind with
  | tenRoundRepair =>
      change TenRoundRepair
        (acceptedProductionWireOfCompact fields transcript compact) honest
        at holds
      have covered := selected_semantic_failure_mem_fixedWidth29_family decoder
        (extractedWidth29InitialWords words) terminal sumcheck selected
        (acceptedProductionWireOfCompact fields transcript compact) honest
        semanticSource theta zerocheckPoint mu (Or.inl holds)
      exact fixedCover (FixedFamilyK15Failure.semantic covered)
  | helperCancellation =>
      change HelperCancellation basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta zerocheckPoint mu helper at holds
      have algebraFailure : FixedTerminalAlgebraFailure (terminal selected)
          theta zerocheckPoint mu := by
        rw [selectedTerminalExact]
        exact Or.inl holds
      have covered := selected_semantic_failure_mem_fixedWidth29_family decoder
        (extractedWidth29InitialWords words) terminal sumcheck selected
        (acceptedProductionWireOfCompact fields transcript compact) honest
        semanticSource theta zerocheckPoint mu (Or.inr algebraFailure)
      exact fixedCover (FixedFamilyK15Failure.semantic covered)
  | zerocheckEvaluation =>
      change ZerocheckEvaluationCollision basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta zerocheckPoint at holds
      have algebraFailure : FixedTerminalAlgebraFailure (terminal selected)
          theta zerocheckPoint mu := by
        rw [selectedTerminalExact]
        exact Or.inr (Or.inl holds)
      have covered := selected_semantic_failure_mem_fixedWidth29_family decoder
        (extractedWidth29InitialWords words) terminal sumcheck selected
        (acceptedProductionWireOfCompact fields transcript compact) honest
        semanticSource theta zerocheckPoint mu (Or.inr algebraFailure)
      exact fixedCover (FixedFamilyK15Failure.semantic covered)
  | thetaLane =>
      change ThetaLaneCollision basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta at holds
      have algebraFailure : FixedTerminalAlgebraFailure (terminal selected)
          theta zerocheckPoint mu := by
        rw [selectedTerminalExact]
        exact Or.inr (Or.inr holds)
      have covered := selected_semantic_failure_mem_fixedWidth29_family decoder
        (extractedWidth29InitialWords words) terminal sumcheck selected
        (acceptedProductionWireOfCompact fields transcript compact) honest
        semanticSource theta zerocheckPoint mu (Or.inr algebraFailure)
      exact fixedCover (FixedFamilyK15Failure.semantic covered)
  | muZero =>
      change mu = 0 at holds
      exact fixedCover (FixedFamilyK15Failure.muZero holds)
  | inactiveChi =>
      change DeployedCopyInactiveSlotCollision chi at holds
      exact fixedCover (FixedFamilyK15Failure.inactiveChi holds)
  | activePole =>
      change DeployedCopyActivePole
        (concreteDeployedCopyRegistryProjection extraction) lambda chi at holds
      apply fixedCover
      apply FixedFamilyK15Failure.copyChi
      refine ⟨c1Candidate, Or.inl ?_⟩
      rw [c1SourceExact]
      exact holds
  | copyChi =>
      change CopyChiCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda chi at holds
      apply fixedCover
      apply FixedFamilyK15Failure.copyChi
      refine ⟨c1Candidate, Or.inr ?_⟩
      rw [c1SourceExact]
      exact holds
  | tupleCompression =>
      change CopyTupleCompressionCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda at holds
      apply fixedCover
      apply FixedFamilyK15Failure.copyLambda
      refine ⟨c1Candidate, ?_⟩
      rw [c1SourceExact]
      exact holds
  | oodMix =>
      change execution.discrepancyTrace.MixCancellation 0 at holds
      exact fixedCover (FixedFamilyK15Failure.oodMix holds)
  | relationAlpha =>
      change (∃ round : Fin 4,
        execution.discrepancyTrace.AlphaRepair round) at holds
      exact fixedCover (FixedFamilyK15Failure.relationAlpha holds)
  | kappaPointRow =>
      change KappaPointRowCollision fields extraction transcript.point kappa
        at holds
      exact fixedCover (FixedFamilyK15Failure.kappaPointRow holds)
  | gammaPointLane =>
      change GammaPointLaneCollision fields extraction transcript.point at holds
      exact gammaCover rfl holds

/-- Without strengthening K1.4, the deterministic ledger has exactly one
residual branch: a nonzero point-claim discrepancy killed by `gamma`.  Every
other branch is already in the fixed causal family counted below. -/
theorem failureEvidence_implies_gammaPointLane_or_fixedFamilyK15Failure
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    (statement : V5PublicStatement)
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (fixedMember : extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words))
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact)
    (terminalExact : terminal
      (extractedFixedWidth29Candidate extraction fixedMember) =
        extractedFixedTerminalPlan basis rc statement extraction lambda chi helper)
    (sumcheckCausal : WireUsesAdaptiveDegree27Plan
      (acceptedProductionWireOfCompact fields transcript compact) honest
      (sumcheck (extractedFixedWidth29Candidate extraction fixedMember)))
    (failure : FailureEvidence
      (failureEvent basis rc statement fields transcript compact extraction
        lambda chi theta zerocheckPoint mu helper mask honest kappa execution)) :
    GammaPointLaneCollision fields extraction transcript.point ∨
      FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint
        transcript.point lambda chi theta mu kappa execution := by
  classical
  rcases failure with ⟨kind, holds⟩
  exact failureKind_elim_causal
    basis rc statement fields transcript compact extraction lambda chi theta
    zerocheckPoint mu helper mask honest kappa execution fixedMember
    terminal sumcheck terminalExact sumcheckCausal kind Or.inr
    (fun _ collision => Or.inl collision) holds

/-- The strengthened K1.4 all-claims certificate eliminates the sole residual
gamma branch and recovers the fixed-family-only result used by the existing
capstone. -/
theorem failureEvidence_implies_fixedFamilyK15Failure
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    (statement : V5PublicStatement)
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (fixedMember : extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words))
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact)
    (terminalExact : terminal
      (extractedFixedWidth29Candidate extraction fixedMember) =
        extractedFixedTerminalPlan basis rc statement extraction lambda chi helper)
    (sumcheckCausal : WireUsesAdaptiveDegree27Plan
      (acceptedProductionWireOfCompact fields transcript compact) honest
      (sumcheck (extractedFixedWidth29Candidate extraction fixedMember)))
    (allPointClaimsExact : ∀ row lane,
      fields.pointClaim row lane =
        componentPointClaim extraction transcript.point row lane)
    (failure : FailureEvidence
      (failureEvent basis rc statement fields transcript compact extraction
        lambda chi theta zerocheckPoint mu helper mask honest kappa execution)) :
    FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint
      transcript.point lambda chi theta mu kappa execution := by
  rcases failure with ⟨kind, holds⟩
  exact failureKind_elim_causal
    basis rc statement fields transcript compact extraction lambda chi theta
    zerocheckPoint mu helper mask honest kappa execution fixedMember
    terminal sumcheck terminalExact sumcheckCausal kind
    (fun fixed => fixed)
    (fun _ collision => False.elim
      ((gamma_point_lane_collision_impossible_of_all_claims_exact fields
        extraction transcript.point allPointClaimsExact) collision)) holds

#print axioms extractedFixedWidth29Candidate
#print axioms coherentTraceExtraction_components_mem_fixedWidth29TupleList
#print axioms extractedFixedTerminalPlan
#print axioms activePole_mem_fixedSourceChiBad
#print axioms copyChiCollision_mem_fixedSourceChiBad
#print axioms packedSourceFamilyTupleCompressionWitness_mem_familyLambdaBad
#print axioms packedSourceFamilyChiWitness_mem_familyChiBad
#print axioms groupedFixedFamilyRootCap_eq_inventory
#print axioms failureKind_elim_causal
#print axioms
  failureEvidence_implies_gammaPointLane_or_fixedFamilyK15Failure
#print axioms failureEvidence_implies_fixedFamilyK15Failure

end AspisPool.V7K15FixedFamilyCausalCover
