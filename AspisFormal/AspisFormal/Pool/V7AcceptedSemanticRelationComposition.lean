import AspisFormal.Pool.V7AtomicSemanticRowsFromTrace
import AspisFormal.Pool.V7CompactSemanticBinding
import AspisFormal.Pool.V7InactiveClaimBinding
import AspisFormal.Pool.V7RelationCandidateBinding

/-!
# Accepted Tag-73 semantic/relation composition

This leaf composes the exact K1.5 facts already proved for Tag 73.

On the semantic side, the compact ten-round wire is connected to the literal
Boolean oracle built from the extracted physical trace.  Outside the three
sumcheck authentication/repair conditions and the three existing constraint
batching collisions, every one of the 25 Boolean-row lanes is zero.  The
Poseidon rows and compiled copy/LogUp lane are supplied as independent source
functions; they are never defined to be zero.  Their vanishing is a conclusion
of the same lane-extraction theorem.  No Poseidon hash equation or copy-alias
semantics is inferred from that vanishing.

On the relation side, `extractedInitialRelationWeights` is the literal
inactive-mask plus three-point MLE covector.  Its dot product with the selected
gamma-batched candidate is proved equal to the extracted inactive-plus-point
claim.  Consequently three small source equalities--initial values, weights,
and claim--let the existing four-round theorem authenticate the initial
relation claim and then all 87 serialized point claims.  The separately
carried inactive claim remains one exact scalar equality, because it shares
coefficient one with point row zero and cannot be separated by random
batching.

The final capstone states both conclusions together.  It does not introduce a
blanket faithfulness predicate, an assumed residual, an arbitrary choice, or a
zero-valued stand-in for Poseidon/copy.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace AspisPool.V7AcceptedSemanticRelationComposition

open Module
open AspisFormal.ArithmetizationCore
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7SelectedSemanticPointClaims
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7Width29ComponentExtraction
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV5ProductionPublicResidualBinding
open AspisV5SumcheckTranscriptBinding
open AspisV5TowerPackedResidualExtraction
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-! ## The exact trace and semantic Boolean oracle -/

/-- The physical M31 trace is the first sixteen columns of the one coherent
width-29 component tuple. -/
def extractedPhysicalTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : PhysicalTrace :=
  semanticTrace extraction.components

/-- The complete 25-lane Boolean constraint row.  Poseidon and compiled copy
are parameters, while the 20 semantic lanes are the exact 77-position model
of `atomic_semantic_packed_impl`. -/
def extractedConstraintRows
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (compiledCopyLane : Fin 1024 → QM31Exact) :
    Fin 1024 → ConstraintRowResiduals (F := F) (K := QM31Exact) :=
  constraintRowsWithAtomicSemantic (terminalSpendFields statement)
    (extractedPhysicalTrace extraction) poseidonRows compiledCopyLane

/-- Literal unmasked Boolean oracle evaluated by the semantic sumcheck model. -/
noncomputable def extractedUnmaskedSemanticTable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (compiledCopyLane : Fin 1024 → QM31Exact)
    (theta : QM31Exact) (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact) (helper : Fin 1024 → QM31Exact) :
    Fin 1024 → QM31Exact :=
  sourceUnmaskedZerocheckTable basis
    (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
    theta zerocheckPoint mu helper

/-- Exact row-level conclusion of the compact semantic argument.  Poseidon
and copy are kept separate from the 77 semantic positions. -/
structure ExtractedConstraintRowsVanish
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (compiledCopyLane : Fin 1024 → QM31Exact) : Prop where
  poseidon : ∀ row group slot, poseidonRows row group slot = 0
  semantic : AtomicSemanticRowsVanish (terminalSpendFields statement)
    (extractedPhysicalTrace extraction)
  copy : ∀ row, compiledCopyLane row = 0

/-- Compact Tag-73 acceptance, two concrete authenticated scalar equalities,
and exclusion of the four already named algebraic repair families imply that
all 25 lane residuals vanish on every Boolean trace row.

`maskInitialExact` is exactly the fixed-mask initial opening.  The second
equality is exactly the fixed terminal opening.  These are the irreducible
claim equalities at this layer; neither assumes a constraint residual is zero.
-/
theorem constraint_rows_vanish_of_compact_acceptance
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
    (compiledCopyLane : Fin 1024 → QM31Exact)
    (theta : QM31Exact) (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction poseidonRows
          compiledCopyLane theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              poseidonRows compiledCopyLane theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (noRepair : ¬ TenRoundRepair
      (acceptedProductionWireOfCompact fields transcript compact) honest)
    (noHelper : ¬ HelperCancellation basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta zerocheckPoint mu helper)
    (noZerocheck : ¬ ZerocheckEvaluationCollision basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta zerocheckPoint)
    (noTheta : ¬ ThetaLaneCollision basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta) :
    ExtractedConstraintRowsVanish statement extraction poseidonRows
      compiledCopyLane := by
  let rows := extractedConstraintRows statement extraction poseidonRows
    compiledCopyLane
  let real := extractedUnmaskedSemanticTable basis statement extraction
    poseidonRows compiledCopyLane theta zerocheckPoint mu helper
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
  have realSumZero : tableSum real = 0 :=
    unmasked_sum_zero_of_extracted_boundary transcript.eta real mask boundary
  have mleZero : constraintMLE basis rows theta zerocheckPoint = 0 :=
    constraintMLE_zero_outside_helper_cancellation basis rows theta
      zerocheckPoint mu helper (by
        simpa [real, extractedUnmaskedSemanticTable, rows] using realSumZero)
      (by simpa [rows] using noHelper)
  have tableZero : thetaConstraintTable basis rows theta = 0 :=
    thetaConstraintTable_zero_outside_zerocheck_collision basis rows
      theta zerocheckPoint mleZero (by simpa [rows] using noZerocheck)
  have polynomialZero : ∀ row,
      rowConstraintPolynomial basis rows row = 0 :=
    row_polynomials_zero_outside_theta_collision basis rows theta
      tableZero (by simpa [rows] using noTheta)
  have laneZero : ∀ row,
      (∀ group slot, (rows row).poseidon group slot = 0) ∧
        (∀ group slot, (rows row).semantic group slot = 0) ∧
        (rows row).copy = 0 := by
    intro row
    exact all_row_residuals_zero_of_theta_polynomial_zero basis (rows row)
      (polynomialZero row)
  refine {
    poseidon := ?_
    semantic := ?_
    copy := ?_
  }
  · intro row group slot
    exact (laneZero row).1 group slot
  · intro row group slot
    exact (laneZero row).2.1 group slot
  · intro row
    exact (laneZero row).2.2

/-! ## Exact initial relation covector -/

/-- The candidate-side initial relation covector: the binary inactive mask
plus the three statement-point MLE covectors with coefficients
`1, kappa, kappa^2`. -/
noncomputable def extractedInitialRelationWeights
    {K : Type*} [Field K]
    (masks : InactiveMasks) (point : Fin 10 → K)
    (kappa : K) : Fin 1024 → K :=
  fun row => inactiveWeight masks row +
    ∑ which : Fin 3,
      pointScale kappa which * mleRowWeight (statementPoint point which) row

/-- Field-generic coefficient-level width-29 message batch.  Keeping the
linearity proof abstract avoids reducing the concrete QM31 tower. -/
def width29MessageBatch
    {K : Type*} [Field K]
    (components : Fin 29 → Fin 1024 → K) (gamma : K) : Fin 1024 → K :=
  fun row => width29Batch (fun lane => components lane row) gamma

/-- MLE evaluation commutes with a coefficient-level width-29 gamma batch. -/
theorem multilinearEvalValue_width29MessageBatch
    {K : Type*} [Field K]
    (components : Fin 29 → Fin 1024 → K)
    (gamma : K) (point : Fin 10 → K) :
    multilinearEvalValue point (width29MessageBatch components gamma) =
      width29Batch
        (fun lane => multilinearEvalValue point (components lane)) gamma := by
  classical
  unfold multilinearEvalValue width29MessageBatch width29Batch
  calc
    (∑ row : Fin 1024,
        mleRowWeight point row *
          ∑ lane : Fin 29, components lane row * gamma ^ lane.val) =
        ∑ row : Fin 1024, ∑ lane : Fin 29,
          mleRowWeight point row *
            (components lane row * gamma ^ lane.val) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
    _ = ∑ lane : Fin 29, ∑ row : Fin 1024,
        mleRowWeight point row *
          (components lane row * gamma ^ lane.val) := by
      rw [Finset.sum_comm]
    _ = ∑ lane : Fin 29,
        (∑ row : Fin 1024,
          mleRowWeight point row * components lane row) * gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring

/-- Concrete Tag-73 spelling of the generic MLE batching identity. -/
theorem multilinearEvalValue_batchInitialMessages
    (components : Width29InitialMessages QM31Exact)
    (gamma : QM31Exact) (point : Fin 10 → QM31Exact) :
    multilinearEvalValue point (batchInitialMessages components gamma) =
      width29Batch
        (fun lane => multilinearEvalValue point (components lane)) gamma := by
  change multilinearEvalValue point (width29MessageBatch components gamma) = _
  exact multilinearEvalValue_width29MessageBatch components gamma point

@[simp] theorem batchInitialMessages_eq_width29MessageBatch
    (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact) :
    batchInitialMessages components gamma =
      width29MessageBatch components gamma := by
  rfl

/-- The exact inactive-plus-three-point covector evaluates to the inactive
functional plus the three scaled MLEs of the same candidate. -/
theorem candidateClaim_extractedInitialRelationWeights
    {K : Type*} [Field K]
    (masks : InactiveMasks) (values : Fin 1024 → K)
    (point : Fin 10 → K) (kappa : K) :
    candidateClaim (extractedInitialRelationWeights masks point kappa) values =
      inactiveClaim masks values +
        ∑ which : Fin 3, pointScale kappa which *
          multilinearEvalValue (statementPoint point which) values := by
  classical
  unfold candidateClaim extractedInitialRelationWeights inactiveClaim
    multilinearEvalValue
  calc
    (∑ row : Fin 1024, values row *
        (inactiveWeight masks row +
          ∑ which : Fin 3,
            pointScale kappa which *
              mleRowWeight (statementPoint point which) row)) =
        (∑ row : Fin 1024, inactiveWeight masks row * values row) +
          ∑ row : Fin 1024, ∑ which : Fin 3,
            values row * (pointScale kappa which *
              mleRowWeight (statementPoint point which) row) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro row _
      ring

    _ = (∑ row : Fin 1024, inactiveWeight masks row * values row) +
        ∑ which : Fin 3, ∑ row : Fin 1024,
          values row * (pointScale kappa which *
            mleRowWeight (statementPoint point which) row) := by
      rw [Finset.sum_comm]
    _ = (∑ row : Fin 1024, inactiveWeight masks row * values row) +
        ∑ which : Fin 3, pointScale kappa which *
          ∑ row : Fin 1024,
            mleRowWeight (statementPoint point which) row * values row := by
      congr 1
      apply Finset.sum_congr rfl
      intro which _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      ring

/-- The exact initial covector evaluated on a field-generic width-29 message
batch.  Proving this over an abstract field keeps the concrete QM31
instantiation computationally small. -/
theorem candidateClaim_extractedInitialRelationWeights_width29MessageBatch
    {K : Type*} [Field K]
    (masks : InactiveMasks) (components : Fin 29 → Fin 1024 → K)
    (gamma : K) (point : Fin 10 → K) (kappa : K) :
    candidateClaim (extractedInitialRelationWeights masks point kappa)
        (width29MessageBatch components gamma) =
      inactiveClaim masks (width29MessageBatch components gamma) +
        ∑ which : Fin 3, pointScale kappa which *
          width29Batch
            (fun lane => multilinearEvalValue
              (statementPoint point which) (components lane)) gamma := by
  rw [candidateClaim_extractedInitialRelationWeights]
  apply congrArg (fun pointBatch =>
    inactiveClaim masks (width29MessageBatch components gamma) + pointBatch)
  apply Finset.sum_congr rfl
  intro which _
  rw [multilinearEvalValue_width29MessageBatch]

/-- The exact initial relation covector evaluated on the selected combined
candidate is the extracted inactive claim plus the two-level point batch. -/
theorem candidateClaim_extractedInitialRelationWeights_eq_extractedRelation
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder) :
    candidateClaim (extractedInitialRelationWeights masks point kappa)
        extraction.combined.1 =
      extractedRelationClaimBeforeOod masks extraction point kappa := by
  have combinedEq :=
    CoherentTraceExtraction.combined_eq_batchInitialMessages extraction
      initialEncoderEq
  have exactCovector := candidateClaim_extractedInitialRelationWeights
    masks extraction.combined.1 point kappa
  rw [combinedEq] at exactCovector
  simp_rw [multilinearEvalValue_batchInitialMessages] at exactCovector
  unfold extractedRelationClaimBeforeOod extractedPointBatch componentPointClaim
  rw [combinedEq]
  exact exactCovector

/-! ## Four-round relation and all point claims -/

/-- Exact deterministic output of the relation composition. -/
structure ExtractedRelationClaimsExact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact) : Prop where
  initialRelation : relationClaimBeforeOod fields gamma kappa =
    extractedRelationClaimBeforeOod masks extraction point kappa
  firstOod : execution.firstOodClaim =
    candidateClaim execution.firstOodWeights execution.initialValues
  secondOod : execution.secondOodClaim execution.firstMix =
    candidateClaim (execution.secondOodWeights execution.firstMix)
      execution.initialValues
  pointClaims : ∀ row lane,
    fields.pointClaim row lane = componentPointClaim extraction point row lane
  semanticPointClaims : ∀ row : Fin 3, ∀ lane : Fin 16,
    fields.pointClaim row (c1LaneIndex (semanticColumnIndex lane)) =
      selectedSemanticPointClaim extraction point row lane

/-- The four-round relation theorem plus the literal initial relation covector
authenticates the initial/OOD claims and all 87 serialized point claims.

The three `executionInitial*` equalities are individual source projections.
`inactiveExact` is the one independently authenticated scalar which random
batching cannot separate from point row zero.  Query injection and final-fold
matching retain their exact, already defined equality predicates.
-/
theorem relation_and_point_aggregate_exact_outside_relation_collisions
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialValues : execution.initialValues = extraction.combined.1)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks point kappa)
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod fields gamma kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (terminal : execution.RelationTerminalAccepts)
    (noOodCancellation : ¬ execution.discrepancyTrace.MixCancellation 0)
    (noAlphaRepair : ∀ round : Fin 4,
      ¬ execution.discrepancyTrace.AlphaRepair round) :
    relationClaimBeforeOod fields gamma kappa =
        extractedRelationClaimBeforeOod masks extraction point kappa ∧
      execution.firstOodClaim =
        candidateClaim execution.firstOodWeights execution.initialValues ∧
      execution.secondOodClaim execution.firstMix =
        candidateClaim (execution.secondOodWeights execution.firstMix)
          execution.initialValues ∧
      claimedPointBatch fields gamma kappa =
        extractedPointBatch extraction point kappa := by
  have relationClaims := execution.initial_and_ood_claims_exact_outside_collisions
    finalMatches queryExact terminal noOodCancellation noAlphaRepair
  have candidateInitial :
      candidateClaim execution.initialWeights execution.initialValues =
        extractedRelationClaimBeforeOod masks extraction point kappa := by
    rw [executionInitialWeights, executionInitialValues]
    exact candidateClaim_extractedInitialRelationWeights_eq_extractedRelation
      masks extraction point kappa initialEncoderEq
  have relationExact : relationClaimBeforeOod fields gamma kappa =
      extractedRelationClaimBeforeOod masks extraction point kappa := by
    calc
      relationClaimBeforeOod fields gamma kappa = execution.initialClaim :=
        executionInitialClaim.symm
      _ = candidateClaim execution.initialWeights execution.initialValues :=
        relationClaims.1
      _ = extractedRelationClaimBeforeOod masks extraction point kappa :=
        candidateInitial
  have aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa :=
    point_aggregate_exact_of_relation_and_inactive_exact masks fields extraction
      point kappa relationExact inactiveExact
  exact ⟨relationExact, relationClaims.2.1, relationClaims.2.2, aggregateExact⟩

theorem relation_and_point_claims_exact_outside_collisions
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialValues : execution.initialValues = extraction.combined.1)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks point kappa)
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod fields gamma kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (terminal : execution.RelationTerminalAccepts)
    (noOodCancellation : ¬ execution.discrepancyTrace.MixCancellation 0)
    (noAlphaRepair : ∀ round : Fin 4,
      ¬ execution.discrepancyTrace.AlphaRepair round)
    (noKappaCollision : ¬ KappaPointRowCollision fields extraction point kappa)
    (noGammaCollision : ¬ GammaPointLaneCollision fields extraction point) :
    ExtractedRelationClaimsExact masks fields extraction point kappa execution := by
  obtain ⟨relationExact, firstOod, secondOod, aggregateExact⟩ :=
    relation_and_point_aggregate_exact_outside_relation_collisions masks fields
      extraction point kappa execution initialEncoderEq executionInitialValues
      executionInitialWeights executionInitialClaim inactiveExact finalMatches
      queryExact terminal noOodCancellation noAlphaRepair
  have everyPoint := all_point_claims_exact_outside_collisions fields extraction
    point kappa aggregateExact noKappaCollision noGammaCollision
  have everySemantic := semantic_point_claims_exact_outside_collisions fields
    extraction point kappa aggregateExact noKappaCollision noGammaCollision
  exact {
    initialRelation := relationExact
    firstOod := firstOod
    secondOod := secondOod
    pointClaims := everyPoint
    semanticPointClaims := everySemantic
  }

/-! ## Joint accepted semantic/relation consequence -/

/-- Strongest deterministic K1.5 composition currently available without
assigning probabilities to Fiat--Shamir challenges or interpreting zero
Poseidon/copy rows as hash/Merkle/copy semantics. -/
structure AcceptedSemanticRelationConsequence
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
    (compiledCopyLane : Fin 1024 → QM31Exact) : Prop where
  rows : ExtractedConstraintRowsVanish statement extraction poseidonRows
    compiledCopyLane
  arithmetic : ExtractedArithmeticResiduals
    (openedColumnsFromTrace (extractedPhysicalTrace extraction)
      (boundedFeeFromStatement statement))
  publicFields : OpenedColumnsMatchStatement statement
    (openedColumnsFromTrace (extractedPhysicalTrace extraction)
      (boundedFeeFromStatement statement))
  relation : ExtractedRelationClaimsExact masks fields extraction point kappa
    execution

/-- Joint capstone.  The semantic and relation inputs remain field-by-field;
the only compiled-copy semantic needed for arithmetic/public closure is the
single balance alias `(864,12) = (866,11)`. -/
theorem accepted_semantic_relation_consequence
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
    (compiledCopyLane : Fin 1024 → QM31Exact)
    (theta : QM31Exact) (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction poseidonRows
          compiledCopyLane theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              poseidonRows compiledCopyLane theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (noRepair : ¬ TenRoundRepair
      (acceptedProductionWireOfCompact fields transcript compact) honest)
    (noHelper : ¬ HelperCancellation basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta zerocheckPoint mu helper)
    (noZerocheck : ¬ ZerocheckEvaluationCollision basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta zerocheckPoint)
    (noTheta : ¬ ThetaLaneCollision basis
      (extractedConstraintRows statement extraction poseidonRows compiledCopyLane)
      theta)
    (balanceAlias : BalanceOutputCellAlias (extractedPhysicalTrace extraction))
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
    AcceptedSemanticRelationConsequence statement masks fields extraction
      transcript.point kappa execution poseidonRows compiledCopyLane := by
  have rows := constraint_rows_vanish_of_compact_acceptance basis statement
    extraction fields transcript compact poseidonRows compiledCopyLane theta
    zerocheckPoint mu helper mask honest maskInitialExact terminalOpeningExact
    noRepair noHelper noZerocheck noTheta
  have arithmetic := arithmetic_residuals_of_atomic_semantic_rows statement
    (extractedPhysicalTrace extraction) balanceAlias rows.semantic
  have publicFields := public_fields_match_of_atomic_semantic_rows statement
    (extractedPhysicalTrace extraction) balanceAlias rows.semantic
  have relation := relation_and_point_claims_exact_outside_collisions masks fields
    extraction transcript.point kappa execution initialEncoderEq
    executionInitialValues executionInitialWeights executionInitialClaim
    inactiveExact finalMatches queryExact relationTerminal noOodCancellation
    noAlphaRepair noKappaCollision noGammaCollision
  exact {
    rows := rows
    arithmetic := arithmetic
    publicFields := publicFields
    relation := relation
  }

/-! ## Audit -/

#print axioms constraint_rows_vanish_of_compact_acceptance
#print axioms multilinearEvalValue_batchInitialMessages
#print axioms candidateClaim_extractedInitialRelationWeights_eq_extractedRelation
#print axioms relation_and_point_aggregate_exact_outside_relation_collisions
#print axioms relation_and_point_claims_exact_outside_collisions
#print axioms accepted_semantic_relation_consequence

end AspisPool.V7AcceptedSemanticRelationComposition
