import AspisFormal.K1.V7Tag73OperationalK15Classifier
import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding

/-!
# Exact source facts for the operational Tag-73 relation execution

The K1.5 theorem consumes three positive relation facts: the selected initial
candidate folds to final256, the installed q16 claim is the exact linear
functional of final256, and the terminal four-value dot comparison succeeds.
This module derives those propositions from smaller data equalities matching
the actual Rust evaluator's intermediate values.

In particular, the source bridge should expose values and equations from the
translated execution; it need not postulate `Final256Matches`,
`QueryInjectionExact` or `RelationTerminalAccepts` directly.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73OperationalRelationSourceFacts

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentADeployedTerminalApplicability
open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV5FriConcreteEncoderApplicability
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6QueryBatchSoundness
open AspisV6TranscriptRelationGrammar
open AspisV7ExactOneFoldDomains

noncomputable section

private theorem qm31ExactTwoNeZero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (2 : M31Exact) =
        algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (0 : M31Exact) := by
    calc
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (2 : M31Exact) =
          (2 : QM31Exact) := map_ofNat _ 2
      _ = 0 := equalZero
      _ = algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (0 : M31Exact) := (map_zero _).symm
  have baseEqual := FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31ExactTwoNeZero⟩

/-! ## Exact final-line q16 covector -/

/-- Coefficient weight of one exact final-line evaluation.  This is the
natural-line basis value at the exact stored log-18 point used by Rust. -/
def exactFinalQueryWeight (query : Fin 262144) (coefficient : Fin 256) :
    QM31Exact :=
  naturalLineValue
    (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
      (storedFirstLineX18 query))
    coefficient.val

/-- The frozen V6-style final256 covector for sixteen ordered evaluations,
with powers `1, rho, ..., rho^15`.  Tag 73 wraps this base covector in one
additional factor of `rho` below. -/
def exactQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact) : Fin 256 → QM31Exact :=
  fun coefficient => ∑ ordinal : Fin 16,
    rho ^ ordinal.val * exactFinalQueryWeight (queries ordinal) coefficient

/-- Expanding the exact final encoder gives its literal natural-line dot
product.  This avoids an artificial coordinate-basis decomposition and is the
same polynomial identity already used by the deployed encoder proof. -/
theorem exactFinalEncoder_eq_candidateClaim
    (coefficients : Fin 256 → QM31Exact) (query : Fin 262144) :
    exactFinalEncoder coefficients query =
      candidateClaim (exactFinalQueryWeight query) coefficients := by
  change
    (naturalCoefficientPolynomial coefficients).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
          (storedFirstLineX18 query)) =
      ∑ coefficient : Fin 256,
        coefficients coefficient *
          naturalLineValue
            (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
              (storedFirstLineX18 query))
            coefficient.val
  rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]

/-- The concrete q16 covector evaluates to the same ordered batch of final
line-code answers used by the verifier callback. -/
theorem candidateClaim_exactQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (coefficients : Fin 256 → QM31Exact) :
    candidateClaim (exactQueryBatchWeights queries rho) coefficients =
      queryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal)) rho := by
  classical
  unfold candidateClaim exactQueryBatchWeights queryBatchClaim
  calc
    (∑ coefficient : Fin 256,
        coefficients coefficient *
          ∑ ordinal : Fin 16,
            rho ^ ordinal.val *
              exactFinalQueryWeight (queries ordinal) coefficient) =
        ∑ coefficient : Fin 256, ∑ ordinal : Fin 16,
          rho ^ ordinal.val *
            (coefficients coefficient *
              exactFinalQueryWeight (queries ordinal) coefficient) := by
      apply Finset.sum_congr rfl
      intro coefficient _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ordinal _
      ring
    _ = ∑ ordinal : Fin 16, ∑ coefficient : Fin 256,
        rho ^ ordinal.val *
          (coefficients coefficient *
            exactFinalQueryWeight (queries ordinal) coefficient) := by
      rw [Finset.sum_comm]
    _ = ∑ ordinal : Fin 16,
        rho ^ ordinal.val *
          exactFinalEncoder coefficients (queries ordinal) := by
      apply Finset.sum_congr rfl
      intro ordinal _
      rw [← Finset.mul_sum]
      exact congrArg (fun value => rho ^ ordinal.val * value)
        (exactFinalEncoder_eq_candidateClaim coefficients
          (queries ordinal)).symm

/-- The repaired Tag-73 covector is exactly one factor of `rho` times the
frozen base covector, hence uses powers `rho, ..., rho^16`. -/
def exactTag73ShiftedQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact) :
    Fin 256 → QM31Exact :=
  fun coefficient => rho * exactQueryBatchWeights queries rho coefficient

/-- The corresponding shifted authenticated scalar. -/
def exactTag73ShiftedQueryBatchClaim
    (values : QueryVector QM31Exact) (rho : QM31Exact) : QM31Exact :=
  rho * queryBatchClaim values rho

theorem candidateClaim_exactTag73ShiftedQueryBatchWeights
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (coefficients : Fin 256 → QM31Exact) :
    candidateClaim (exactTag73ShiftedQueryBatchWeights queries rho)
        coefficients =
      exactTag73ShiftedQueryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal)) rho := by
  classical
  unfold candidateClaim exactTag73ShiftedQueryBatchWeights
    exactTag73ShiftedQueryBatchClaim
  calc
    (∑ coefficient : Fin 256,
        coefficients coefficient *
          (rho * exactQueryBatchWeights queries rho coefficient)) =
        rho * candidateClaim (exactQueryBatchWeights queries rho)
          coefficients := by
      unfold candidateClaim
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coefficient _
      ring
    _ = rho * queryBatchClaim
        (fun ordinal => exactFinalEncoder coefficients (queries ordinal)) rho :=
      congrArg (fun value : QM31Exact => rho * value)
        (candidateClaim_exactQueryBatchWeights queries rho coefficients)

/-! ## Small source-facing equality records -/

/-- Direct fields needed to derive final256 matching from the exact K1.4
chain.  Each field is a plain equality to an evaluator input/output. -/
structure ExactFinal256ExecutionBinding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (decoded : Fin 641 → QM31Exact)
    (execution : CandidateExecution QM31Exact) : Prop where
  initialValuesExact : execution.initialValues = k14.extraction.combined.1
  disclosedFinalExact : execution.disclosedFinal256 =
    (operationalFixedFields decoded).finalCoefficient
  alphaZeroExact : execution.alpha 0 =
    (exactK13ParsedProof input).schedule.alpha

/-- Exact K1.4 fold consistency plus the parser/source equalities proves the
positive final256 fact required by K1.5. -/
theorem final256_matches_of_exact_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k14 : ExactK14Certificate decoder decoderBinding input k12}
    {decoded : Fin 641 → QM31Exact}
    {execution : CandidateExecution QM31Exact}
    (parsed : ExactParsedProofSourceBinding input decoded)
    (source : ExactFinal256ExecutionBinding k14 decoded execution) :
    execution.Final256Matches := by
  unfold CandidateExecution.Final256Matches CandidateExecution.foldedInitial256
  calc
    execution.disclosedFinal256 =
        (operationalFixedFields decoded).finalCoefficient :=
      source.disclosedFinalExact
    _ = (exactK13ParsedProof input).disclosedFinal :=
      parsed.disclosedFinalExact.symm
    _ = coefficientFoldLayer 256
        (exactK13ParsedProof input).schedule.alpha
        k14.extraction.combined.1 := by
      simpa [foldInitial] using k14.extraction.foldsToDisclosedFinal.symm
    _ = coefficientFoldLayer 256 (execution.alpha 0)
        execution.initialValues := by
      rw [source.alphaZeroExact, source.initialValuesExact]

/-- Direct q16 evaluator equalities.  `queryClaimExact` is the value returned
by the authenticated query callback with the repaired shifted powers.  This
record alone does not imply `QueryInjectionExact`: K1.3 must additionally
prove that the authenticated values equal the final-code evaluations. -/
structure ExactQueryInjectionSourceBinding
    (execution : CandidateExecution QM31Exact)
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact)
    (authenticated : QueryVector QM31Exact) : Prop where
  queryWeightsExact : execution.queryWeights =
    exactTag73ShiftedQueryBatchWeights queries rho
  queryClaimExact : execution.queryClaim =
    exactTag73ShiftedQueryBatchClaim authenticated rho

theorem query_injection_exact_of_source_binding
    {execution : CandidateExecution QM31Exact}
    {queries : Fin 16 → Fin 262144} {rho : QM31Exact}
    {authenticated : QueryVector QM31Exact}
    (source : ExactQueryInjectionSourceBinding execution queries rho
      authenticated)
    (authenticatedExact : authenticated = fun ordinal =>
      exactFinalEncoder execution.disclosedFinal256 (queries ordinal)) :
    execution.QueryInjectionExact := by
  unfold CandidateExecution.QueryInjectionExact
  rw [source.queryWeightsExact, source.queryClaimExact,
    candidateClaim_exactTag73ShiftedQueryBatchWeights, authenticatedExact]

/-- Literal terminal values exposed by the accepted relation tail. -/
structure ExactRelationTerminalSourceTrace
    (execution : CandidateExecution QM31Exact) : Type where
  terminalDot : QM31Exact
  runningClaim : QM31Exact
  terminalDotExact : terminalDot =
    candidateClaim execution.weights4 execution.values4
  runningClaimExact : runningClaim = execution.claim4
  acceptedComparison : terminalDot = runningClaim

theorem relation_terminal_accepts_of_source_trace
    {execution : CandidateExecution QM31Exact}
    (source : ExactRelationTerminalSourceTrace execution) :
    execution.RelationTerminalAccepts := by
  unfold CandidateExecution.RelationTerminalAccepts
  rw [← source.terminalDotExact, ← source.runningClaimExact]
  exact source.acceptedComparison

/-- The complete positive relation premise of operational K1.5 follows from
the three small equality bundles exposed by the translated Rust evaluator.
This is the source-facing handoff: no aggregate K1.5 acceptance proposition is
assumed at the Aeneas boundary. -/
theorem positive_relation_facts_of_exact_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k14 : ExactK14Certificate decoder decoderBinding input k12}
    {decoded : Fin 641 → QM31Exact}
    {execution : CandidateExecution QM31Exact}
    {queries : Fin 16 → Fin 262144}
    {rho : QM31Exact}
    {authenticated : QueryVector QM31Exact}
    (parsed : ExactParsedProofSourceBinding input decoded)
    (finalSource : ExactFinal256ExecutionBinding k14 decoded execution)
    (querySource : ExactQueryInjectionSourceBinding execution queries rho
      authenticated)
    (authenticatedExact : authenticated = fun ordinal =>
      exactFinalEncoder execution.disclosedFinal256 (queries ordinal))
    (terminalSource : ExactRelationTerminalSourceTrace execution) :
    execution.Final256Matches ∧
      execution.QueryInjectionExact ∧
      execution.RelationTerminalAccepts := by
  exact ⟨final256_matches_of_exact_source_bindings parsed finalSource,
    query_injection_exact_of_source_binding querySource authenticatedExact,
    relation_terminal_accepts_of_source_trace terminalSource⟩

/-! ## Operational K1.5 with only source-level relation premises -/

/- Source-facing operational K1.5 classifier.  Compared with
`operational_k14_implies_decoded_witness_or_k15_failure`, the aggregate
final256, q16-injection and terminal-acceptance premises have disappeared.
They are derived here from literal evaluator equalities, with the q16
positions and batching challenge fixed to the actual parsed proof and
operational transcript. -/
set_option maxHeartbeats 5000000 in
theorem operational_k14_source_implies_decoded_witness_or_k15_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded)
    (sourceBinding : ExactParsedProofSourceBinding input decoded)
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
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
        (extractedUnmaskedSemanticTable basis statement k14.extraction
          (deployedPoseidonRows rc
            (extractedPhysicalTrace k14.extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection k14.extraction)
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi) helper)
          (exactOperationalChallenge input .theta)
          (fun coordinate => exactOperationalChallenge input
            (.zerocheckPoint coordinate))
          (exactOperationalChallenge input .mu) helper)
        mask)
      (operationalAcceptedRun input decoded fixedDecode).point)
    (maskInitialExact : (operationalFixedFields decoded).initialClaim =
      tableSum mask)
    (terminalOpeningExact :
      semanticTerminalClaim (operationalFixedFields decoded)
          (operationalAcceptedRun input decoded fixedDecode).point =
        claimAtStep
          (tableSum
            (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
              (extractedUnmaskedSemanticTable basis statement k14.extraction
                (deployedPoseidonRows rc
                  (extractedPhysicalTrace k14.extraction))
                (deployedCompiledCopyLane
                  (concreteDeployedCopyRegistryProjection k14.extraction)
                  (exactOperationalChallenge input .lambda)
                  (exactOperationalChallenge input .chi) helper)
                (exactOperationalChallenge input .theta)
                (fun coordinate => exactOperationalChallenge input
                  (.zerocheckPoint coordinate))
                (exactOperationalChallenge input .mu) helper)
              mask))
          honest.messages
          (operationalAcceptedRun input decoded fixedDecode).point
          (Fin.last 10))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks
        (operationalAcceptedRun input decoded fixedDecode).point
        (exactOperationalChallenge input .kappa))
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod (operationalFixedFields decoded)
        (exactK13ParsedProof input).gamma
        (exactOperationalChallenge input .kappa))
    (inactiveExact : (operationalFixedFields decoded).inactiveClaim =
      inactiveClaim masks k14.extraction.combined.1)
    (finalSource : ExactFinal256ExecutionBinding k14 decoded execution)
    (authenticated : QueryVector QM31Exact)
    (querySource : ExactQueryInjectionSourceBinding execution
      (exactK13ParsedProof input).queries
      (exactOperationalChallenge input .queryBatch) authenticated)
    (authenticatedExact : authenticated = fun ordinal =>
      exactFinalEncoder execution.disclosedFinal256
        ((exactK13ParsedProof input).queries ordinal))
    (terminalSource : ExactRelationTerminalSourceTrace execution) :
    ExactParsedProofSourceBinding input decoded ∧
      (let witness := decodeTag73SpendWitness statement k14.extraction
       (OpenedColumnsMatchStatement statement witness.opened ∧
        SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
          witness.opened witness.inputValue witness.outputValue) ∨
        CausalFailureEvidence
          (failureEvent basis rc statement (operationalFixedFields decoded)
            (operationalAcceptedRun input decoded fixedDecode)
            (operationalCompactEvidence input decoded fixedDecode)
            k14.extraction
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi)
            (exactOperationalChallenge input .theta)
            (fun coordinate => exactOperationalChallenge input
              (.zerocheckPoint coordinate))
            (exactOperationalChallenge input .mu) helper mask honest
            (exactOperationalChallenge input .kappa) execution)) := by
  have positive := positive_relation_facts_of_exact_source_bindings
    sourceBinding finalSource querySource authenticatedExact terminalSource
  exact operational_k14_implies_decoded_witness_or_k15_failure input k14 decoded
    fixedDecode sourceBinding basis rc poseidon statement masks helper mask
    honest maskInitialExact terminalOpeningExact inactiveSumZero execution
    initialEncoderEq finalSource.initialValuesExact executionInitialWeights
    executionInitialClaim inactiveExact positive.1 positive.2.1 positive.2.2

#print axioms candidateClaim_exactQueryBatchWeights
#print axioms exactFinalEncoder_eq_candidateClaim
#print axioms final256_matches_of_exact_source_bindings
#print axioms query_injection_exact_of_source_binding
#print axioms relation_terminal_accepts_of_source_trace
#print axioms positive_relation_facts_of_exact_source_bindings
#print axioms operational_k14_source_implies_decoded_witness_or_k15_failure

end

end AspisK1.V7Tag73OperationalRelationSourceFacts
