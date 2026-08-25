import AspisFormal.V6TranscriptRelationGrammar
import AspisFormal.V6FirstCompactSampler
import AspisFormal.V6RelationFold
import AspisFormal.V6QueryBatchSoundness

/-!
# Deterministic obligations of an accepted V6 transcript

This file turns the successful branch of
`verify_v6_transcript_and_relation` into a single mathematical record.  It
does not assume that acceptance is sound.  Instead it says exactly what an
accepted implementation path must have established before the probabilistic
PCS, Fiat--Shamir, Merkle, and Rust-to-Lean arguments may be applied.

The transcript hash, the production terminal callback, and the concrete
`WeightAccumulator` implementation are deliberately supplied as interfaces.
Their source equalities remain separate obligations; the deterministic
composition below does not hide them.
-/

set_option autoImplicit false

namespace AspisV6AcceptedPathObligations

open AspisV6TranscriptRelationGrammar
open AspisV6FirstCompactSampler
open AspisV6RelationFold
open AspisV6QueryBatchSoundness
open AspisV5ComponentCConcreteFoldLinearity

variable {K : Type*} [Field K]

/-! ## Decoding every fixed field -/

def decodedFixedFieldView (decoded : Fin 641 → K) : FixedFieldView K where
  initialClaim := decoded ⟨0, by omega⟩
  semanticSent := fun round sent => decoded (semanticFieldIndex round sent)
  pointClaim := fun row column => decoded (pointClaimFieldIndex row column)
  inactiveClaim := decoded ⟨358, by omega⟩
  oodValue := fun sample => decoded (oodFieldIndex sample)
  relationSent := fun round sent => decoded (relationFieldIndex round sent)
  finalCoefficient := fun coefficient => decoded (finalFieldIndex coefficient)

theorem decoded_view_has_exact_point_claim_layout
    (decoded : Fin 641 → K) (row : Fin 3) (column : Fin 29) :
    (decodedFixedFieldView decoded).pointClaim row column =
      decoded ⟨271 + row.val * 29 + column.val, by omega⟩ := by
  rfl

theorem decoded_view_has_exact_final_layout
    (decoded : Fin 641 → K) (coefficient : Fin 256) :
    (decodedFixedFieldView decoded).finalCoefficient coefficient =
      decoded ⟨385 + coefficient.val, by omega⟩ := by
  rfl

/-! ## Semantic sumcheck and exact three-row statement points -/

def semanticParts (fields : FixedFieldView K) (round : Fin 10) :
    SemanticRoundParts K where
  constant := fields.semanticSent round 0
  higher := fun coefficient =>
    fields.semanticSent round ⟨coefficient.val + 1, by omega⟩

def semanticRunningClaim (fields : FixedFieldView K)
    (challenge : Fin 10 → K) : Nat → K
  | 0 => fields.initialClaim
  | round + 1 =>
      if inRange : round < 10 then
        semanticEvaluate (semanticRunningClaim fields challenge round)
          (semanticParts fields ⟨round, inRange⟩) (challenge ⟨round, inRange⟩)
      else semanticRunningClaim fields challenge round

def semanticTerminalClaim (fields : FixedFieldView K)
    (challenge : Fin 10 → K) : K :=
  semanticRunningClaim fields challenge 10

theorem every_semantic_round_has_running_boundary
    (fields : FixedFieldView K) (challenge : Fin 10 → K)
    (round : Fin 10) :
    semanticBoundaryFromParts
        (reconstructedSemanticLinear
          (semanticRunningClaim fields challenge round.val)
          (semanticParts fields round))
        (semanticParts fields round) =
      semanticRunningClaim fields challenge round.val := by
  exact reconstructed_semantic_linear_has_exact_boundary _ _

def successorCarry (point : Fin 10 → K) (coordinate : Fin 10) : K :=
  ∏ later : Fin 10,
    if coordinate.val < later.val then point later else 1

/-- Algebra computed by the reverse carry loop in `v6_statement_points`. -/
def successorPoint (point : Fin 10 → K) : Fin 10 → K :=
  fun coordinate =>
    let carry := successorCarry point coordinate
    point coordinate + carry - (point coordinate * carry + point coordinate * carry)

def xor12Point (point : Fin 10 → K) : Fin 10 → K :=
  fun coordinate =>
    if coordinate.val = 7 ∨ coordinate.val = 6 then 1 - point coordinate
    else point coordinate

def statementPoint (point : Fin 10 → K) : Fin 3 → Fin 10 → K :=
  ![point, successorPoint point, xor12Point point]

theorem exact_three_statement_points (point : Fin 10 → K) :
    statementPoint point 0 = point ∧
      statementPoint point 1 = successorPoint point ∧
      statementPoint point 2 = xor12Point point := by
  simp [statementPoint]

def terminalProjection (claims : Fin 3 → Fin 29 → K) :
    Fin 3 → Fin 28 → K :=
  fun row column => claims row ⟨column.val, by omega⟩

theorem terminal_projection_excludes_d_and_nothing_else
    (claims : Fin 3 → Fin 29 → K) :
    (∀ row column,
      terminalProjection claims row column =
        claims row ⟨column.val, by omega⟩) ∧
      ∀ row : Fin 3,
        ¬ terminalUsesPointClaim (row, (⟨28, by omega⟩ : Fin 29)) := by
  constructor
  · intros
    rfl
  · intro row
    exact (terminal_excludes_exactly_d_lane row).1

structure SemanticCallbackView (K : Type*) where
  lambda : K
  chi : K
  theta : K
  zerocheckPoint : Fin 10 → K
  mu : K
  eta : K
  point : Fin 10 → K
  terminalClaim : K
  /-- The source callback receives exactly columns zero through twenty-seven.
  Column twenty-eight is used later by the relation but is not visible here. -/
  pointClaims : Fin 3 → Fin 28 → K

/-! ## Width-29 batching and four-round relation -/

def gammaCombinedPointClaim (fields : FixedFieldView K) (gamma : K)
    (row : Fin 3) : K :=
  ∑ column : Fin 29, fields.pointClaim row column * gamma ^ column.val

def pointScale (kappa : K) : Fin 3 → K :=
  ![(1 : K), kappa, kappa ^ 2]

def relationClaimBeforeOod (fields : FixedFieldView K)
    (gamma kappa : K) : K :=
  fields.inactiveClaim + ∑ row : Fin 3,
    pointScale kappa row * gammaCombinedPointClaim fields gamma row

def relationClaimAfterOod (fields : FixedFieldView K)
    (gamma kappa : K) (mix : Fin 2 → K) : K :=
  relationClaimBeforeOod fields gamma kappa +
    ∑ sample : Fin 2, mix sample * fields.oodValue sample

def relationParts (fields : FixedFieldView K) (round : Fin 4) :
    RelationRoundParts K where
  c0 := fields.relationSent round 0
  c1 := fields.relationSent round 1
  c2 := fields.relationSent round 2
  c3 := fields.relationSent round 3
  c5 := fields.relationSent round 4
  c6 := fields.relationSent round 5

def relationRunningClaim (fields : FixedFieldView K)
    (gamma kappa quarter : K) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) : Nat → K
  | 0 => relationClaimAfterOod fields gamma kappa oodMix
  | round + 1 =>
      if inRange : round < 4 then
        relationEvaluate quarter
          (relationRunningClaim fields gamma kappa quarter oodMix alpha round)
          (relationParts fields ⟨round, inRange⟩) (alpha ⟨round, inRange⟩)
      else relationRunningClaim fields gamma kappa quarter oodMix alpha round

def relationTerminalClaim (fields : FixedFieldView K)
    (gamma kappa quarter : K) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) : K :=
  relationRunningClaim fields gamma kappa quarter oodMix alpha 4

/-- Incoming claim after the sole committed `1024 -> 256` fold. -/
def relationClaimAfterFirstRound (fields : FixedFieldView K)
    (gamma kappa quarter : K) (oodMix : Fin 2 → K)
    (alpha0 : K) : K :=
  relationEvaluate quarter (relationClaimAfterOod fields gamma kappa oodMix)
    (relationParts fields 0) alpha0

def queryBatchClaim (authenticatedFoldedValues : Fin 16 → K)
    (rho : K) : K :=
  ∑ ordinal : Fin 16,
    rho ^ ordinal.val * authenticatedFoldedValues ordinal

theorem queryBatchClaim_difference_is_exact_residual
    (expected authenticated : Fin 16 → K) (rho : K) :
    queryBatchClaim expected rho - queryBatchClaim authenticated rho =
      queryBatchResidual expected authenticated rho := by
  simp only [queryBatchClaim, queryBatchResidual, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ordinal _
  ring

theorem equal_queryBatchClaims_imply_zero_residual
    (expected authenticated : Fin 16 → K) (rho : K)
    (equalClaims : queryBatchClaim expected rho =
      queryBatchClaim authenticated rho) :
    queryBatchResidual expected authenticated rho = 0 := by
  rw [← queryBatchClaim_difference_is_exact_residual]
  exact sub_eq_zero.mpr equalClaims

/-- The query claim is installed after round zero. Rounds one through three
then reduce the augmented log-eight weight accumulator and the disclosed
256-vector together. -/
def relationTailRunningClaim (fields : FixedFieldView K)
    (gamma kappa quarter : K) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) (installedQueryClaim : K) : Nat → K
  | 0 => relationClaimAfterFirstRound fields gamma kappa quarter oodMix (alpha 0) +
      installedQueryClaim
  | tailRound + 1 =>
      if inRange : tailRound < 3 then
        let round : Fin 4 := ⟨tailRound + 1, by omega⟩
        relationEvaluate quarter
          (relationTailRunningClaim fields gamma kappa quarter oodMix alpha
            installedQueryClaim tailRound)
          (relationParts fields round) (alpha round)
      else relationTailRunningClaim fields gamma kappa quarter oodMix alpha
        installedQueryClaim tailRound

def relationTerminalClaimWithQueryBatch (fields : FixedFieldView K)
    (gamma kappa quarter : K) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) (authenticatedFoldedValues : Fin 16 → K)
    (rho : K) : K :=
  relationTailRunningClaim fields gamma kappa quarter oodMix alpha
    (queryBatchClaim authenticatedFoldedValues rho) 3

theorem reconstructed_relation_message_has_arbitrary_incoming_boundary
    (quarter incomingClaim : K) (parts : RelationRoundParts K)
    (quarterExact : quarter * 4 = (1 : K)) :
    relationBoundaryFromParts
        (reconstructedRelationQuartic quarter incomingClaim parts) parts =
      incomingClaim := by
  exact reconstructed_relation_quartic_has_exact_boundary
    quarter incomingClaim parts quarterExact

theorem every_relation_round_has_running_boundary
    (fields : FixedFieldView K) (gamma kappa quarter : K)
    (oodMix : Fin 2 → K) (alpha : Fin 4 → K)
    (quarterExact : quarter * 4 = (1 : K)) (round : Fin 4) :
    relationBoundaryFromParts
        (reconstructedRelationQuartic quarter
          (relationRunningClaim fields gamma kappa quarter oodMix alpha round.val)
          (relationParts fields round))
        (relationParts fields round) =
      relationRunningClaim fields gamma kappa quarter oodMix alpha round.val := by
  exact reconstructed_relation_quartic_has_exact_boundary
    quarter _ _ quarterExact

/-- The disclosed vector is not folded by `alpha[0]`: that challenge belongs
to the committed circle-to-line fold.  Only `alpha[1..3]` reduce 256 values to
four. -/
def disclosedFinal64 (fields : FixedFieldView K) (alpha : Fin 4 → K) :
    Fin 64 → K :=
  coefficientFoldLayer 64 (alpha 1) fields.finalCoefficient

def disclosedFinal16 (fields : FixedFieldView K) (alpha : Fin 4 → K) :
    Fin 16 → K :=
  coefficientFoldLayer 16 (alpha 2) (disclosedFinal64 fields alpha)

def disclosedFinal4 (fields : FixedFieldView K) (alpha : Fin 4 → K) :
    Fin 4 → K :=
  coefficientFoldLayer 4 (alpha 3) (disclosedFinal16 fields alpha)

theorem disclosed_final_has_exact_reduction_sizes :
    256 / 4 = 64 ∧ 64 / 4 = 16 ∧ 16 / 4 = 4 := by
  norm_num

/-! ## Abstract but ordered weight-accumulator interface -/

abbrev InactiveMasks := Fin 64 → Fin 16 → Bool

structure LinePointDescriptor where
  circleDomainLog : Nat
  lineLayer : Nat
  query : Fin 262144

def v6QueryLinePointDescriptor (query : Fin 262144) : LinePointDescriptor :=
  ⟨20, 1, query⟩

theorem exact_v6_query_line_geometry (query : Fin 262144) :
    (v6QueryLinePointDescriptor query).circleDomainLog = 20 ∧
      (v6QueryLinePointDescriptor query).lineLayer = 1 ∧
      (v6QueryLinePointDescriptor query).query = query := by
  exact ⟨rfl, rfl, rfl⟩

structure WeightOperations (K Weight CirclePoint LinePoint : Type*) where
  emptyLog10 : Weight
  addMultilinear : Weight → K → (Fin 10 → K) → Weight
  addInactiveMasks : Weight → InactiveMasks → Weight
  addCircleTensor : Weight → K → CirclePoint → Weight
  addLineTensor : Weight → K → LinePoint → Weight
  foldArity4 : Weight → K → Weight
  finalWeights : Weight → Fin 4 → K

def weightBeforeOod {Weight CirclePoint LinePoint : Type*}
    (operations : WeightOperations K Weight CirclePoint LinePoint)
    (point : Fin 10 → K) (kappa : K) (masks : InactiveMasks) : Weight :=
  let after0 := operations.addMultilinear operations.emptyLog10
    (pointScale kappa 0) (statementPoint point 0)
  let after1 := operations.addMultilinear after0
    (pointScale kappa 1) (statementPoint point 1)
  let after2 := operations.addMultilinear after1
    (pointScale kappa 2) (statementPoint point 2)
  operations.addInactiveMasks after2 masks

def addQueryBatchWeightTensors {Weight CirclePoint LinePoint : Type*}
    (operations : WeightOperations K Weight CirclePoint LinePoint)
    (linePoint : Fin 16 → LinePoint) (rho : K) : Nat → Weight → Weight
  | 0, initial => initial
  | ordinal + 1, initial =>
      if inRange : ordinal < 16 then
        operations.addLineTensor
          (addQueryBatchWeightTensors operations linePoint rho ordinal initial)
          (rho ^ ordinal) (linePoint ⟨ordinal, inRange⟩)
      else addQueryBatchWeightTensors operations linePoint rho ordinal initial

def finalWeightState {Weight CirclePoint LinePoint : Type*}
    (operations : WeightOperations K Weight CirclePoint LinePoint)
    (point : Fin 10 → K) (kappa : K) (masks : InactiveMasks)
    (oodPoint : Fin 2 → CirclePoint) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) (queryLinePoint : Fin 16 → LinePoint)
    (rho : K) : Weight :=
  let afterOod0 := operations.addCircleTensor
    (weightBeforeOod operations point kappa masks) (oodMix 0) (oodPoint 0)
  let afterOod1 := operations.addCircleTensor afterOod0
    (oodMix 1) (oodPoint 1)
  let afterFold0 := operations.foldArity4 afterOod1 (alpha 0)
  let afterQueryBatch :=
    addQueryBatchWeightTensors operations queryLinePoint rho 16 afterFold0
  let afterFold1 := operations.foldArity4 afterQueryBatch (alpha 1)
  let afterFold2 := operations.foldArity4 afterFold1 (alpha 2)
  operations.foldArity4 afterFold2 (alpha 3)

def finalRelationWeights {Weight CirclePoint LinePoint : Type*}
    (operations : WeightOperations K Weight CirclePoint LinePoint)
    (point : Fin 10 → K) (kappa : K) (masks : InactiveMasks)
    (oodPoint : Fin 2 → CirclePoint) (oodMix : Fin 2 → K)
    (alpha : Fin 4 → K) (queryLinePoint : Fin 16 → LinePoint)
    (rho : K) : Fin 4 → K :=
  operations.finalWeights
    (finalWeightState operations point kappa masks oodPoint oodMix alpha
      queryLinePoint rho)

/-! ## Deterministic first-compact query selection -/

abbrev QuerySchedule := Fin 16 → Fin 262144

def CompactSchedule (frontierNodes : QuerySchedule → Nat)
    (schedule : QuerySchedule) : Prop :=
  frontierNodes schedule ≤ 209

structure CompactSelection
    (candidate : Fin 3 → Fin 8 → QuerySchedule)
    (frontierNodes : QuerySchedule → Nat) where
  selector : Fin 3
  counter : Fin 8
  queries : QuerySchedule
  selectedAtCounter : candidate selector counter = queries
  selectedIsCompact : CompactSchedule frontierNodes queries
  everyEarlierIsNoncompact : ∀ earlier : Fin 8,
    earlier.val < counter.val →
      ¬ CompactSchedule frontierNodes (candidate selector earlier)
  queriesWithoutReplacement : Function.Injective queries
  c1FrontierNodes : Nat
  c2FrontierNodes : Nat
  c1FrontierExact : c1FrontierNodes = frontierNodes queries
  c2FrontierExact : c2FrontierNodes = frontierNodes queries

/-- Exact public input passed to the production one-fold callback. -/
structure QueryFoldView (K : Type*) where
  gamma : K
  alpha0 : K
  queries : QuerySchedule
  selector : Fin 3
  compactCounter : Fin 8
  frontierNodes : Nat

def selectedQueryFoldView
    {candidate : Fin 3 → Fin 8 → QuerySchedule}
    {frontierNodes : QuerySchedule → Nat}
    (selection : CompactSelection candidate frontierNodes)
    (gamma alpha0 : K) : QueryFoldView K where
  gamma := gamma
  alpha0 := alpha0
  queries := selection.queries
  selector := selection.selector
  compactCounter := selection.counter
  frontierNodes := frontierNodes selection.queries

theorem compactSelection_is_firstCompactResult
    {candidate : Fin 3 → Fin 8 → QuerySchedule}
    {frontierNodes : QuerySchedule → Nat}
    (selection : CompactSelection candidate frontierNodes) :
    FirstCompactResult (CompactSchedule frontierNodes)
      (candidate selection.selector) selection.queries := by
  exact ⟨selection.counter, selection.selectedAtCounter,
    selection.selectedIsCompact, selection.everyEarlierIsNoncompact⟩

/-! ## One record for the complete successful deterministic path -/

structure AcceptedPath
    (CanonicalField : K → Prop)
    (TerminalAccepts : SemanticCallbackView K → Prop)
    (WorkAccepts : WorkStage → Prop)
    (Weight CirclePoint LinePoint : Type*)
    (weightOperations : WeightOperations K Weight CirclePoint LinePoint)
    (linePointFromDescriptor : LinePointDescriptor → LinePoint)
    (compiledInactiveMasks : InactiveMasks)
    (candidate : Fin 3 → Fin 8 → QuerySchedule)
    (candidateDecodedWithin64 : Fin 3 → Fin 8 → Prop)
    (QueryFoldAccepts :
      QueryFoldView K → (Fin 16 → K) → (Fin 16 → LinePoint) → Prop)
    (frontierNodes : QuerySchedule → Nat) where
  executionTrace : List ExecutionOperation
  executionTraceExact : executionTrace = acceptedExecutionGrammar
  decoded : Fin 641 → K
  fields : FixedFieldView K
  fieldsExact : fields = decodedFixedFieldView decoded
  everyFieldCanonical : ∀ index, CanonicalField (decoded index)
  fixedPackedLastByte : Fin 256
  fixedPaddingCanonical : CanonicalFixedPadding fixedPackedLastByte

  lambda : K
  chi : K
  theta : K
  zerocheckPoint : Fin 10 → K
  mu : K
  eta : K
  etaNonzero : eta ≠ 0
  semanticChallenge : Fin 10 → K
  terminalAccepted : TerminalAccepts {
    lambda := lambda
    chi := chi
    theta := theta
    zerocheckPoint := zerocheckPoint
    mu := mu
    eta := eta
    point := semanticChallenge
    terminalClaim := semanticTerminalClaim fields semanticChallenge
    pointClaims := terminalProjection fields.pointClaim }

  checkPow : Bool
  checkPowEnabled : checkPow = true
  workAccepted : ∀ stage : WorkStage, WorkAccepts stage
  gamma : K
  gammaNonzero : gamma ≠ 0
  kappa : K
  kappaNonzero : kappa ≠ 0
  alpha : Fin 4 → K
  compactSelection : CompactSelection candidate frontierNodes
  everyAttemptedCandidateDecodedWithinLimit : ∀ counter : Fin 8,
    counter.val ≤ compactSelection.counter.val →
      candidateDecodedWithin64 compactSelection.selector counter
  queryBatchChallenge : K
  queryBatchChallengeNonzero : queryBatchChallenge ≠ 0
  authenticatedFoldedQueryValues : Fin 16 → K
  authenticatedQueryLinePoints : Fin 16 → LinePoint
  queryFoldAccepted : QueryFoldAccepts
    (selectedQueryFoldView compactSelection gamma (alpha 0))
    authenticatedFoldedQueryValues authenticatedQueryLinePoints
  queryFoldOutputFixedByCommitments :
    ∀ (otherValues : Fin 16 → K) (otherLinePoints : Fin 16 → LinePoint),
      QueryFoldAccepts (selectedQueryFoldView compactSelection gamma (alpha 0))
          otherValues otherLinePoints →
        otherValues = authenticatedFoldedQueryValues ∧
          otherLinePoints = authenticatedQueryLinePoints
  authenticatedQueryLinePointsExact : ∀ ordinal : Fin 16,
    authenticatedQueryLinePoints ordinal =
      linePointFromDescriptor
        (v6QueryLinePointDescriptor (compactSelection.queries ordinal))
  absorbedQueryBatchClaim : K
  absorbedQueryBatchClaimExact : absorbedQueryBatchClaim =
    queryBatchClaim authenticatedFoldedQueryValues queryBatchChallenge
  inactiveMasks : InactiveMasks
  inactiveMasksExact : inactiveMasks = compiledInactiveMasks
  oodPoint : Fin 2 → CirclePoint
  oodMix : Fin 2 → K
  quarter : K
  quarterExact : quarter * 4 = (1 : K)
  relationTerminalExact :
    (∑ index : Fin 4,
      disclosedFinal4 fields alpha index *
        finalRelationWeights weightOperations semanticChallenge kappa
          inactiveMasks oodPoint oodMix alpha
          authenticatedQueryLinePoints
          queryBatchChallenge index) =
      relationTerminalClaimWithQueryBatch fields gamma kappa quarter oodMix alpha
        authenticatedFoldedQueryValues queryBatchChallenge

theorem accepted_path_uses_every_fixed_field_once
    {CanonicalField : K → Prop}
    {TerminalAccepts : SemanticCallbackView K → Prop}
    {WorkAccepts : WorkStage → Prop}
    {Weight CirclePoint LinePoint : Type*}
    {weightOperations : WeightOperations K Weight CirclePoint LinePoint}
    {linePointFromDescriptor : LinePointDescriptor → LinePoint}
    {compiledInactiveMasks : InactiveMasks}
    {candidate : Fin 3 → Fin 8 → QuerySchedule}
    {candidateDecodedWithin64 : Fin 3 → Fin 8 → Prop}
    {QueryFoldAccepts :
      QueryFoldView K → (Fin 16 → K) → (Fin 16 → LinePoint) → Prop}
    {frontierNodes : QuerySchedule → Nat}
    (_accepted : AcceptedPath CanonicalField TerminalAccepts WorkAccepts
      Weight CirclePoint LinePoint weightOperations linePointFromDescriptor
      compiledInactiveMasks candidate candidateDecodedWithin64 QueryFoldAccepts
      frontierNodes)
    (index : Fin 641) :
    index.val ∈ fixedFieldConsumptionOrder ∧
      fixedFieldConsumptionOrder.count index.val = 1 :=
  every_fixed_field_is_consumed_once index

theorem accepted_path_summary
    {CanonicalField : K → Prop}
    {TerminalAccepts : SemanticCallbackView K → Prop}
    {WorkAccepts : WorkStage → Prop}
    {Weight CirclePoint LinePoint : Type*}
    {weightOperations : WeightOperations K Weight CirclePoint LinePoint}
    {linePointFromDescriptor : LinePointDescriptor → LinePoint}
    {compiledInactiveMasks : InactiveMasks}
    {candidate : Fin 3 → Fin 8 → QuerySchedule}
    {candidateDecodedWithin64 : Fin 3 → Fin 8 → Prop}
    {QueryFoldAccepts :
      QueryFoldView K → (Fin 16 → K) → (Fin 16 → LinePoint) → Prop}
    {frontierNodes : QuerySchedule → Nat}
    (accepted : AcceptedPath CanonicalField TerminalAccepts WorkAccepts
      Weight CirclePoint LinePoint weightOperations linePointFromDescriptor
      compiledInactiveMasks candidate candidateDecodedWithin64 QueryFoldAccepts
      frontierNodes) :
    accepted.executionTrace = acceptedExecutionGrammar ∧
      CanonicalFixedPadding accepted.fixedPackedLastByte ∧
      accepted.inactiveMasks = compiledInactiveMasks ∧
      (∀ stage : WorkStage, WorkAccepts stage) ∧
      accepted.queryBatchChallenge ≠ 0 ∧
      QueryFoldAccepts
        (selectedQueryFoldView accepted.compactSelection accepted.gamma
          (accepted.alpha 0))
        accepted.authenticatedFoldedQueryValues
        accepted.authenticatedQueryLinePoints ∧
      (∀ (otherValues : Fin 16 → K)
          (otherLinePoints : Fin 16 → LinePoint),
        QueryFoldAccepts
            (selectedQueryFoldView accepted.compactSelection accepted.gamma
              (accepted.alpha 0))
            otherValues otherLinePoints →
          otherValues = accepted.authenticatedFoldedQueryValues ∧
            otherLinePoints = accepted.authenticatedQueryLinePoints) ∧
      (∀ ordinal : Fin 16,
        accepted.authenticatedQueryLinePoints ordinal =
          linePointFromDescriptor
            (v6QueryLinePointDescriptor
              (accepted.compactSelection.queries ordinal))) ∧
      accepted.absorbedQueryBatchClaim =
        queryBatchClaim accepted.authenticatedFoldedQueryValues
          accepted.queryBatchChallenge ∧
      FirstCompactResult (CompactSchedule frontierNodes)
        (candidate accepted.compactSelection.selector)
        accepted.compactSelection.queries ∧
      accepted.compactSelection.c1FrontierNodes =
        frontierNodes accepted.compactSelection.queries ∧
      accepted.compactSelection.c2FrontierNodes =
        frontierNodes accepted.compactSelection.queries := by
  exact ⟨accepted.executionTraceExact, accepted.fixedPaddingCanonical,
    accepted.inactiveMasksExact, accepted.workAccepted,
    accepted.queryBatchChallengeNonzero, accepted.queryFoldAccepted,
    accepted.queryFoldOutputFixedByCommitments,
    accepted.authenticatedQueryLinePointsExact,
    accepted.absorbedQueryBatchClaimExact,
    compactSelection_is_firstCompactResult accepted.compactSelection,
    accepted.compactSelection.c1FrontierExact,
    accepted.compactSelection.c2FrontierExact⟩

/-! ## Audit -/

#print axioms decoded_view_has_exact_point_claim_layout
#print axioms every_semantic_round_has_running_boundary
#print axioms exact_three_statement_points
#print axioms terminal_projection_excludes_d_and_nothing_else
#print axioms every_relation_round_has_running_boundary
#print axioms reconstructed_relation_message_has_arbitrary_incoming_boundary
#print axioms queryBatchClaim_difference_is_exact_residual
#print axioms equal_queryBatchClaims_imply_zero_residual
#print axioms exact_v6_query_line_geometry
#print axioms compactSelection_is_firstCompactResult
#print axioms accepted_path_uses_every_fixed_field_once
#print axioms accepted_path_summary

end AspisV6AcceptedPathObligations
