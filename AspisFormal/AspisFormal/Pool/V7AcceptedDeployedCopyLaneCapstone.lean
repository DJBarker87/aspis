import AspisFormal.Pool.V7AcceptedSemanticRelationComposition
import AspisFormal.Pool.V7Tag73InactiveHelperAggregate

/-!
# Accepted Tag-73 deployed-copy capstone

This integration leaf specializes the accepted K1.5 semantic composition to
the exact 183-link deployed copy evaluator.  It reuses the accepted unmasked
sum equation to derive the helper zero-sum when `mu != 0`, turns the accepted
local copy rows into the deployed rational balance, and obtains every
`RequiredTraceAliases` field outside the explicitly named denominator and
LogUp challenge failures.

In particular, the older standalone `BalanceOutputCellAlias` premise is not
carried into the final capstone: it is derived from the deployed copy lane
before the existing arithmetic/public-field closure theorem is invoked.

The source-generated registry certificate remains an adjacent Aeneas leaf.
It checks that the concrete endpoint/tag/pattern table used here is the one at
the pinned deployed Rust source; it does not replace the remaining aggregate
helper or sampled-challenge premises below.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace AspisPool.V7AcceptedDeployedCopyLaneCapstone

open Module
open AspisFormal.ArithmetizationCore
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7SelectedSemanticPointClaims
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisPool.V7Width29ComponentExtraction
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5ConstraintLaneBatching
open AspisV5FriRelationCandidateBridge
open AspisV5ProductionPublicResidualBinding
open AspisV5SumcheckTranscriptBinding
open AspisV5TowerPackedResidualExtraction
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-! ## The accepted source equation also fixes the helper sum -/

/-- The unmasked sum equation used inside semantic row extraction, exposed in
the exact source-table form needed by the deployed helper bridge.  This is a
consequence of the authenticated mask initial claim, terminal opening, and
absence of a ten-round repair; it does not assume any residual is zero. -/
theorem extracted_unmasked_sum_zero_of_compact_acceptance
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction poseidonRows
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              poseidonRows
              (deployedCompiledCopyLane
                (concreteDeployedCopyRegistryProjection extraction)
                lambda chi helper)
              theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (noRepair : ¬ TenRoundRepair
      (acceptedProductionWireOfCompact fields transcript compact) honest) :
    tableSum
      (extractedUnmaskedSemanticTable basis statement extraction poseidonRows
        (deployedCompiledCopyLane
          (concreteDeployedCopyRegistryProjection extraction)
          lambda chi helper)
        theta zerocheckPoint mu helper) = 0 := by
  let real := extractedUnmaskedSemanticTable basis statement extraction
    poseidonRows
    (deployedCompiledCopyLane
      (concreteDeployedCopyRegistryProjection extraction) lambda chi helper)
    theta zerocheckPoint mu helper
  let wire := acceptedProductionWireOfCompact fields transcript compact
  have boundary : ExtractedMaskedSumcheckBoundary transcript.eta real mask := by
    apply accepted_wire_implies_extracted_masked_boundary wire transcript.eta
      real mask
    exact {
      etaMatches := rfl
      honest := honest
      maskInitialAuthenticated := by
        simpa [wire, acceptedProductionWireOfCompact] using maskInitialExact
      terminalAuthenticated := by
        simpa [wire, acceptedProductionWireOfCompact] using terminalOpeningExact
      outsideRepair := noRepair
    }
  exact unmasked_sum_zero_of_extracted_boundary transcript.eta real mask boundary

/-! ## Integrated consequence -/

/-- Accepted semantic/relation closure specialized to the exact deployed copy
lane, together with the helper boundary, global rational balance, and all five
raw trace aliases supplied by that lane. -/
structure AcceptedDeployedCopyLaneConsequence
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact) : Prop where
  semanticRelation : AcceptedSemanticRelationConsequence statement masks fields
    extraction point kappa execution poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper)
  helperSumZero : tableSum helper = 0
  rationalBalance : copyRationalBalance
    (concreteDeployedCopyRegistryProjection extraction) lambda chi = 0
  aliases : RequiredTraceAliases
    (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction))

/-- Integration from an already-obtained semantic/relation consequence.  The
only additional hypotheses are the exact helper and sampled-challenge
boundaries used by the deployed rational and multiset arguments. -/
theorem accepted_deployed_copy_lane_consequence_of_semantic_relation
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact)
    (accepted : AcceptedSemanticRelationConsequence statement masks fields
      extraction point kappa execution poseidonRows
        (deployedCompiledCopyLane
          (concreteDeployedCopyRegistryProjection extraction)
          lambda chi helper))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (helperSumZero : tableSum helper = 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    AcceptedDeployedCopyLaneConsequence statement masks fields extraction
      point kappa execution poseidonRows lambda chi helper := by
  have balance := copyRationalBalance_zero_of_accepted_copy_rows_aggregate
    statement extraction poseidonRows lambda chi helper accepted.rows
    helperSumZero inactiveSumZero chiNonzero noPole
  have aliases := requiredTraceAliases_of_accepted_copy_rows_aggregate
    statement extraction poseidonRows lambda chi helper accepted.rows
    helperSumZero inactiveSumZero chiNonzero noPole noChiCollision
    noCompressionCollision
  exact {
    semanticRelation := accepted
    helperSumZero := helperSumZero
    rationalBalance := balance
    aliases := aliases
  }

/-- Full accepted K1.5 capstone for the deployed copy lane.  Relative to
`accepted_semantic_relation_consequence`, this theorem hard-codes the exact
copy evaluator and discharges the former `BalanceOutputCellAlias` and helper
zero-sum inputs.  The aggregate inactive-helper zero-sum, `mu != 0`,
denominator exclusions, and the two sampled LogUp collision exclusions remain
explicit.  No inactive helper cell is required to be pointwise zero. -/
theorem accepted_semantic_relation_deployed_copy_lane_consequence
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction poseidonRows
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              poseidonRows
              (deployedCompiledCopyLane
                (concreteDeployedCopyRegistryProjection extraction)
                lambda chi helper)
              theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (noRepair : ¬ TenRoundRepair
      (acceptedProductionWireOfCompact fields transcript compact) honest)
    (noHelper : ¬ HelperCancellation basis
      (extractedConstraintRows statement extraction poseidonRows
        (deployedCompiledCopyLane
          (concreteDeployedCopyRegistryProjection extraction)
          lambda chi helper))
      theta zerocheckPoint mu helper)
    (noZerocheck : ¬ ZerocheckEvaluationCollision basis
      (extractedConstraintRows statement extraction poseidonRows
        (deployedCompiledCopyLane
          (concreteDeployedCopyRegistryProjection extraction)
          lambda chi helper))
      theta zerocheckPoint)
    (noTheta : ¬ ThetaLaneCollision basis
      (extractedConstraintRows statement extraction poseidonRows
        (deployedCompiledCopyLane
          (concreteDeployedCopyRegistryProjection extraction)
          lambda chi helper))
      theta)
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (muNonzero : mu ≠ 0)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda)
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialValues : execution.initialValues = extraction.combined.1)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks transcript.point kappa)
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod fields gamma kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (relationTerminal : execution.RelationTerminalAccepts)
    (noOodCancellation : ¬ execution.discrepancyTrace.MixCancellation 0)
    (noAlphaRepair : ∀ round : Fin 4,
      ¬ execution.discrepancyTrace.AlphaRepair round)
    (noKappaCollision : ¬ KappaPointRowCollision fields extraction
      transcript.point kappa)
    (noGammaCollision : ¬ GammaPointLaneCollision fields extraction
      transcript.point) :
    AcceptedDeployedCopyLaneConsequence statement masks fields extraction
      transcript.point kappa execution poseidonRows lambda chi helper := by
  let source := concreteDeployedCopyRegistryProjection extraction
  let copyLane := deployedCompiledCopyLane source lambda chi helper
  have rows : ExtractedConstraintRowsVanish statement extraction poseidonRows
      copyLane :=
    constraint_rows_vanish_of_compact_acceptance basis statement extraction
      fields transcript compact poseidonRows copyLane theta zerocheckPoint mu
      helper mask honest maskInitialExact terminalOpeningExact noRepair noHelper
      noZerocheck noTheta
  have unmaskedSumZero : tableSum
      (sourceUnmaskedZerocheckTable basis
        (extractedConstraintRows statement extraction poseidonRows copyLane)
        theta zerocheckPoint mu helper) = 0 := by
    have exactSourceSum :=
      extracted_unmasked_sum_zero_of_compact_acceptance basis statement
        extraction fields transcript compact poseidonRows lambda chi theta
        zerocheckPoint mu helper mask honest maskInitialExact
        terminalOpeningExact noRepair
    simpa [extractedUnmaskedSemanticTable, source, copyLane] using exactSourceSum
  have helperSumZero : tableSum helper = 0 :=
    helper_sum_zero_of_unmasked_sum basis statement extraction poseidonRows
      copyLane theta zerocheckPoint mu helper rows unmaskedSumZero muNonzero
  have aliases : RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) :=
    requiredTraceAliases_of_accepted_copy_rows_aggregate statement extraction
      poseidonRows lambda chi helper (by simpa [source, copyLane] using rows)
      helperSumZero inactiveSumZero chiNonzero noPole noChiCollision
      noCompressionCollision
  have balanceAlias : BalanceOutputCellAlias
      (extractedPhysicalTrace extraction) :=
    (balanceOutputCellAlias_iff_raw_alias
      (extractedPhysicalTrace extraction)).2 aliases.balanceOutputValue
  have semanticRelation := accepted_semantic_relation_consequence basis statement
    masks fields transcript compact extraction poseidonRows copyLane theta
    zerocheckPoint mu helper mask honest maskInitialExact terminalOpeningExact
    noRepair noHelper noZerocheck noTheta balanceAlias kappa execution
    initialEncoderEq executionInitialValues executionInitialWeights
    executionInitialClaim inactiveExact finalMatches queryExact relationTerminal
    noOodCancellation noAlphaRepair noKappaCollision noGammaCollision
  have balance := copyRationalBalance_zero_of_accepted_copy_rows_aggregate
    statement extraction poseidonRows lambda chi helper
      (by simpa [source, copyLane] using rows)
      helperSumZero inactiveSumZero chiNonzero noPole
  exact {
    semanticRelation := by simpa [source, copyLane] using semanticRelation
    helperSumZero := helperSumZero
    rationalBalance := balance
    aliases := aliases
  }

/-! ## Collision-explicit boundary -/

/-- Without assuming sampled-challenge exclusions, the exact accepted local
rows and helper boundary give a five-way conclusion: one of the two
denominator failures, one of the two LogUp collision events, or all required
trace aliases. -/
theorem required_trace_aliases_or_deployed_copy_failure
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact)
    (acceptedRows : ExtractedConstraintRowsVanish statement extraction
      poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (helperSumZero : tableSum helper = 0) :
    DeployedCopyInactiveSlotCollision chi ∨
      DeployedCopyActivePole
        (concreteDeployedCopyRegistryProjection extraction) lambda chi ∨
      CopyChiCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda chi ∨
      CopyTupleCompressionCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda ∨
      RequiredTraceAliases
        (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  classical
  by_cases chiZero : DeployedCopyInactiveSlotCollision chi
  · exact Or.inl chiZero
  · by_cases pole : DeployedCopyActivePole
        (concreteDeployedCopyRegistryProjection extraction) lambda chi
    · exact Or.inr (Or.inl pole)
    · by_cases chiCollision : CopyChiCollision
          (concreteDeployedCopyRegistryProjection extraction) lambda chi
      · exact Or.inr (Or.inr (Or.inl chiCollision))
      · by_cases compressionCollision : CopyTupleCompressionCollision
            (concreteDeployedCopyRegistryProjection extraction) lambda
        · exact Or.inr (Or.inr (Or.inr (Or.inl compressionCollision)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (requiredTraceAliases_of_accepted_copy_rows_aggregate statement
              extraction poseidonRows lambda chi helper acceptedRows
              helperSumZero inactiveSumZero chiZero pole chiCollision
              compressionCollision))))

/-! ## Audit -/

#print axioms extracted_unmasked_sum_zero_of_compact_acceptance
#print axioms accepted_deployed_copy_lane_consequence_of_semantic_relation
#print axioms accepted_semantic_relation_deployed_copy_lane_consequence
#print axioms required_trace_aliases_or_deployed_copy_failure

end AspisPool.V7AcceptedDeployedCopyLaneCapstone
