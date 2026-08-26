import AspisFormal.Pool.V7AcceptedSpendK15FailureLedger

/-!
# Deterministic V7 trace-to-witness decoder

K1.5 must recover a witness, rather than conclude only that some witness
exists.  This file defines the concrete decoder.  Each range bit is decoded
to `0` or `1`; the thirty decoded bits determine the input and output natural
values.  The existing accepted-trace capstone then proves the spend relation
for exactly those values.

No cryptographic premise is introduced.  Poseidon implementation
faithfulness remains the same explicit boundary as in the existing relation
capstone.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace AspisPool.V7DeterministicSpendWitness

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7AcceptedSpendRelationCapstone
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7SelectedSemanticPointClaims
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisPool.V7Width29ComponentExtraction
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

/-! ## Choice-free range decoding -/

/-- Decode one constraint-system bit deterministically.  Invalid field values
totalize to zero; accepted bitness proves that this fallback is unreachable. -/
def decodeFieldBit (value : F) : Nat :=
  if value = 1 then 1 else 0

theorem decodeFieldBit_le_one (value : F) : decodeFieldBit value ≤ 1 := by
  unfold decodeFieldBit
  split <;> omega

theorem field_eq_natCast_decodeFieldBit {value : F}
    (bitness : value * (value - 1) = 0) :
    value = (decodeFieldBit value : F) := by
  rcases field_bool bitness with equal | equal
  · subst value
    simp [decodeFieldBit]
  · subst value
    simp [decodeFieldBit]

/-- The ten decoded bits of one range limb. -/
def decodeRangeLimb (witness : RangeWitness) (limb : Fin 3) : Nat :=
  ∑ bit : Fin 10, decodeFieldBit (witness.bit limb bit) * 2 ^ bit.val

/-- The exact thirty-bit little-endian natural value carried by a range
witness. -/
def decodeRangeValue (witness : RangeWitness) : Nat :=
  decodeRangeLimb witness 0 +
    decodeRangeLimb witness 1 * 2 ^ 10 +
    decodeRangeLimb witness 2 * 2 ^ 20

private theorem sum_pow_two_ten :
    (∑ bit : Fin 10, (2 : Nat) ^ bit.val) = 1023 := by
  norm_num [Fin.sum_univ_succ]

theorem decodeRangeLimb_lt
    (witness : RangeWitness) (limb : Fin 3) :
    decodeRangeLimb witness limb < 2 ^ 10 := by
  have bounded : decodeRangeLimb witness limb ≤
      ∑ bit : Fin 10, (2 : Nat) ^ bit.val := by
    unfold decodeRangeLimb
    apply Finset.sum_le_sum
    intro bit _
    calc
      decodeFieldBit (witness.bit limb bit) * 2 ^ bit.val ≤
          1 * 2 ^ bit.val :=
        Nat.mul_le_mul_right _ (decodeFieldBit_le_one _)
      _ = 2 ^ bit.val := one_mul _
  rw [sum_pow_two_ten] at bounded
  omega

theorem range_value_sound_deterministic
    (witness : RangeWitness) (residuals : RangeResiduals witness) :
    decodeRangeValue witness < 2 ^ 30 ∧
      witness.value = (decodeRangeValue witness : F) := by
  have limbCast : ∀ limb,
      witness.limb limb = (decodeRangeLimb witness limb : F) := by
    intro limb
    calc
      witness.limb limb = ∑ bit : Fin 10,
          witness.bit limb bit * (2 : F) ^ bit.val :=
        residuals.limbRecon limb
      _ = ∑ bit : Fin 10,
          (decodeFieldBit (witness.bit limb bit) : F) *
            (2 : F) ^ bit.val := by
        apply Finset.sum_congr rfl
        intro bit _
        exact congrArg (fun value : F => value * (2 : F) ^ bit.val)
          (field_eq_natCast_decodeFieldBit
            (residuals.bitness limb bit))
      _ = (decodeRangeLimb witness limb : F) := by
        unfold decodeRangeLimb
        push_cast
        rfl
  have limbZero := decodeRangeLimb_lt witness 0
  have limbOne := decodeRangeLimb_lt witness 1
  have limbTwo := decodeRangeLimb_lt witness 2
  constructor
  · unfold decodeRangeValue
    omega
  · rw [residuals.valueRecon, Fin.sum_univ_three,
      limbCast 0, limbCast 1, limbCast 2]
    unfold decodeRangeValue
    norm_num

theorem range_balance_sound_deterministic
    (input output : RangeWitness) (fee : Nat)
    (inputResiduals : RangeResiduals input)
    (outputResiduals : RangeResiduals output)
    (feeBound : fee < 2 ^ 30)
    (balance : input.value = output.value + (fee : F)) :
    decodeRangeValue output + fee = decodeRangeValue input := by
  obtain ⟨inputBound, inputExact⟩ :=
    range_value_sound_deterministic input inputResiduals
  obtain ⟨outputBound, outputExact⟩ :=
    range_value_sound_deterministic output outputResiduals
  have fieldEqual :
      ((decodeRangeValue output + fee : Nat) : F) =
        (decodeRangeValue input : F) := by
    calc
      ((decodeRangeValue output + fee : Nat) : F) =
          (decodeRangeValue output : F) + (fee : F) := Nat.cast_add _ _
      _ = output.value + (fee : F) :=
        congrArg (fun value : F => value + (fee : F)) outputExact.symm
      _ = input.value := balance.symm
      _ = (decodeRangeValue input : F) := inputExact
  have fieldOrder : p = 2147483647 := rfl
  have leftBound : decodeRangeValue output + fee < p := by
    rw [fieldOrder]
    omega
  have rightBound : decodeRangeValue input < p := by
    rw [fieldOrder]
    omega
  exact nat_of_field_eq leftBound rightBound fieldEqual

/-! ## Exact decoded witness -/

structure DecodedSpendWitness where
  opened : OpenedColumns
  inputValue : Nat
  outputValue : Nat

/-- The deterministic spend-witness decoder on normalized opened columns. -/
def decodeSpendWitness (opened : OpenedColumns) : DecodedSpendWitness where
  opened := opened
  inputValue := decodeRangeValue opened.rin
  outputValue := decodeRangeValue opened.rout

@[simp] theorem decodeSpendWitness_opened (opened : OpenedColumns) :
    (decodeSpendWitness opened).opened = opened := by
  rfl

@[simp] theorem decodeSpendWitness_inputValue (opened : OpenedColumns) :
    (decodeSpendWitness opened).inputValue = decodeRangeValue opened.rin := by
  rfl

@[simp] theorem decodeSpendWitness_outputValue (opened : OpenedColumns) :
    (decodeSpendWitness opened).outputValue = decodeRangeValue opened.rout := by
  rfl

/-- Deterministic version of `arithmetization_sound`: the relation uses the
values returned by `decodeSpendWitness`, not existentially selected naturals. -/
theorem arithmetization_sound_deterministic
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (opened : OpenedColumns)
    (models : ArithmetizationModels deployedOwner deployedNote
      deployedNullifier deployedNode opened)
    (constraints : ConstraintsSatisfied opened) :
    SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
      opened (decodeSpendWitness opened).inputValue
        (decodeSpendWitness opened).outputValue := by
  have inputSound := range_value_sound_deterministic opened.rin
    constraints.rangeIn
  have outputSound := range_value_sound_deterministic opened.rout
    constraints.rangeOut
  exact {
    owner_key := models.owner constraints
    input_note := models.input_note constraints _ inputSound.2
    nullifier := models.nullifier constraints
    output_note := models.output_note constraints _ outputSound.2
    input_root := models.input_root constraints
    output_root := models.output_root constraints
    asset_equality := constraints.assetIn
    balance := range_balance_sound_deterministic opened.rin opened.rout
      opened.f constraints.rangeIn constraints.rangeOut opened.hf
        constraints.balance
    range_in := inputSound
    range_out := outputSound
  }

/-- A normalized extracted trace validates exactly the choice-free decoded
witness, modulo the maintained Poseidon implementation-faithfulness boundary. -/
theorem extracted_trace_implies_deterministic_spend_relation
    (rc : RoundConstants) (opened : OpenedColumns)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (trace : ExtractedV5Trace rc opened) :
    SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
      opened (decodeSpendWitness opened).inputValue
        (decodeSpendWitness opened).outputValue := by
  exact arithmetization_sound_deterministic opened
    (arithmetization_models_of_faithful rc opened poseidon
      trace.hashAndMerkle.toHashMerkleWitness)
    trace.arithmetic.toConstraintsSatisfied

/-! ## Tag-73 specialization -/

/-- The actual coherent Tag-73 trace deterministically fixes the opened
columns and therefore the complete spend witness data. -/
noncomputable def decodeTag73SpendWitness
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : DecodedSpendWitness :=
  decodeSpendWitness
    (openedColumnsFromTrace (extractedPhysicalTrace extraction)
      (boundedFeeFromStatement statement))

/-- Accepted deployed rows prove the complete spend relation for the literal
output of `decodeTag73SpendWitness`. -/
theorem acceptedDeployedRows_implies_decodedSpendWitnessValid
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact)
    (accepted : AcceptedDeployedCopyLaneConsequence statement masks fields
      extraction point kappa execution
        (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
        lambda chi helper)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    let witness := decodeTag73SpendWitness statement extraction
    OpenedColumnsMatchStatement statement witness.opened ∧
      SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
        witness.opened witness.inputValue witness.outputValue := by
  let opened := openedColumnsFromTrace (extractedPhysicalTrace extraction)
    (boundedFeeFromStatement statement)
  have trace := extractedV5TraceOfAcceptedDeployedRows rc statement masks fields
    extraction point kappa execution lambda chi helper accepted
      noChiCollision noCompressionCollision
  have relation := extracted_trace_implies_deterministic_spend_relation rc
    opened poseidon trace
  exact ⟨accepted.semanticRelation.publicFields, relation⟩

/-! ## Complete deterministic K1.5 endpoint -/

/-- Exact trace-to-witness K1.5 classifier.  Acceptance returns the literal
output of `decodeTag73SpendWitness`, unless one of the thirteen already named
causal failure events holds.  The success branch is no longer an existential
witness selected by a proof. -/
theorem accepted_semantic_relation_implies_decoded_witness_or_k15_failure
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
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
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
              (deployedCompiledCopyLane
                (concreteDeployedCopyRegistryProjection extraction)
                lambda chi helper)
              theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
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
    (relationTerminal : execution.RelationTerminalAccepts) :
    let witness := decodeTag73SpendWitness statement extraction
    (OpenedColumnsMatchStatement statement witness.opened ∧
      SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
        witness.opened witness.inputValue witness.outputValue) ∨
      FailureEvidence (failureEvent basis rc statement fields transcript compact
        extraction lambda chi theta zerocheckPoint mu helper mask honest kappa
        execution) := by
  classical
  let event := failureEvent basis rc statement fields transcript compact
    extraction lambda chi theta zerocheckPoint mu helper mask honest kappa
    execution
  by_cases failed : FailureEvidence event
  · exact Or.inr failed
  · have outside : ∀ kind, ¬ event kind := by
      intro kind holds
      exact failed ⟨kind, holds⟩
    have noRelationAlpha : ∀ round : Fin 4,
        ¬ execution.discrepancyTrace.AlphaRepair round := by
      intro round repair
      exact outside .relationAlpha ⟨round, repair⟩
    have accepted :=
      accepted_semantic_relation_deployed_copy_lane_consequence basis statement
        masks fields transcript compact extraction
        (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
        lambda chi theta zerocheckPoint mu helper mask honest maskInitialExact
        terminalOpeningExact (outside .tenRoundRepair)
        (outside .helperCancellation) (outside .zerocheckEvaluation)
        (outside .thetaLane) inactiveSumZero (outside .muZero)
        (outside .inactiveChi) (outside .activePole) (outside .copyChi)
        (outside .tupleCompression) kappa execution initialEncoderEq
        executionInitialValues executionInitialWeights executionInitialClaim
        inactiveExact finalMatches queryExact relationTerminal
        (outside .oodMix) noRelationAlpha (outside .kappaPointRow)
        (outside .gammaPointLane)
    exact Or.inl
      (acceptedDeployedRows_implies_decodedSpendWitnessValid rc poseidon
        statement masks fields extraction transcript.point kappa execution
        lambda chi helper accepted (outside .copyChi)
        (outside .tupleCompression))

#print axioms field_eq_natCast_decodeFieldBit
#print axioms range_value_sound_deterministic
#print axioms range_balance_sound_deterministic
#print axioms arithmetization_sound_deterministic
#print axioms extracted_trace_implies_deterministic_spend_relation
#print axioms acceptedDeployedRows_implies_decodedSpendWitnessValid
#print axioms
  accepted_semantic_relation_implies_decoded_witness_or_k15_failure

end AspisPool.V7DeterministicSpendWitness
