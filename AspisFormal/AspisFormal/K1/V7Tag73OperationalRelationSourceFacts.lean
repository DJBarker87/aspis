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
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7RelationCandidateBinding
open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV5FriConcreteEncoderApplicability
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
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

/-- The exact final256 covector installed by sixteen ordered q16 evaluations
and the nonzero query-batch challenge. -/
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
by the authenticated query callback; the linear-algebra theorem above turns
it into `QueryInjectionExact`. -/
structure ExactQueryInjectionSourceBinding
    (execution : CandidateExecution QM31Exact)
    (queries : Fin 16 → Fin 262144) (rho : QM31Exact) : Prop where
  queryWeightsExact : execution.queryWeights = exactQueryBatchWeights queries rho
  queryClaimExact : execution.queryClaim =
    queryBatchClaim
      (fun ordinal => exactFinalEncoder execution.disclosedFinal256
        (queries ordinal)) rho

theorem query_injection_exact_of_source_binding
    {execution : CandidateExecution QM31Exact}
    {queries : Fin 16 → Fin 262144} {rho : QM31Exact}
    (source : ExactQueryInjectionSourceBinding execution queries rho) :
    execution.QueryInjectionExact := by
  unfold CandidateExecution.QueryInjectionExact
  rw [source.queryWeightsExact, source.queryClaimExact,
    candidateClaim_exactQueryBatchWeights]

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
    (parsed : ExactParsedProofSourceBinding input decoded)
    (finalSource : ExactFinal256ExecutionBinding k14 decoded execution)
    (querySource : ExactQueryInjectionSourceBinding execution queries rho)
    (terminalSource : ExactRelationTerminalSourceTrace execution) :
    execution.Final256Matches ∧
      execution.QueryInjectionExact ∧
      execution.RelationTerminalAccepts := by
  exact ⟨final256_matches_of_exact_source_bindings parsed finalSource,
    query_injection_exact_of_source_binding querySource,
    relation_terminal_accepts_of_source_trace terminalSource⟩

#print axioms candidateClaim_exactQueryBatchWeights
#print axioms exactFinalEncoder_eq_candidateClaim
#print axioms final256_matches_of_exact_source_bindings
#print axioms query_injection_exact_of_source_binding
#print axioms relation_terminal_accepts_of_source_trace
#print axioms positive_relation_facts_of_exact_source_bindings

end

end AspisK1.V7Tag73OperationalRelationSourceFacts
