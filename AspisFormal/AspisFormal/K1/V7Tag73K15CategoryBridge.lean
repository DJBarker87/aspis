import AspisFormal.K1.V7Tag73K15ExactMeasureLedger
import AspisFormal.Pool.V7K15FixedFamilyCausalCover

/-!
# Deterministic bridge from fixed-family K1.5 failures to measure categories

`FixedFamilyK15Failure` is the proof-producing algebraic classifier.  The
measure ledger deliberately uses a small stable eight-constructor index.
This file proves that the two views are exactly equivalent for every fixed
operational context, so the compiler/source layer cannot omit or silently
relabel a failure branch when constructing its measured events.
-/

set_option autoImplicit false
-- The dependent fixed-family type contains the full width-29/copy registry.
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15CategoryBridge

open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyLogUpCollisionBounds
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Width29ComponentExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

/-- The literal proposition represented by each one of the eight stable
measure-ledger categories. -/
def FixedK15CategoryWitness
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
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
    (execution : CandidateExecution QM31Exact) : FixedK15Category → Prop
  | .semantic => FixedWidth29SemanticFailure decoder
      (extractedWidth29InitialWords words) terminal sumcheck theta
        zerocheckPoint point mu
  | .copyLambda => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received words),
      CopyTupleCompressionCollision
        (fixedC1CopySourceFamily decoder (c1Received words) candidate).registry
        lambda
  | .copyChi => ∃ candidate : FixedC1TupleCandidate decoder
      (c1Received words),
      DeployedCopyActivePole
          (fixedC1CopySourceFamily decoder
            (c1Received words) candidate).registry lambda chi ∨
        CopyChiCollision
          (fixedC1CopySourceFamily decoder
            (c1Received words) candidate).registry lambda chi
  | .muZero => mu = 0
  | .inactiveChi => DeployedCopyInactiveSlotCollision chi
  | .oodMix => execution.discrepancyTrace.MixCancellation 0
  | .relationAlpha => ∃ round : Fin 4,
      execution.discrepancyTrace.AlphaRepair round
  | .kappaPointRow => KappaPointRowCollision fields extraction point kappa

/-- Every proof-producing fixed-family failure has exactly one of the stable
measure-category propositions as a witness. -/
theorem fixedFamilyK15Failure_implies_category
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    {terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact}
    {sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact}
    {fields : FixedFieldView QM31Exact}
    {extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule}
    {zerocheckPoint point : Fin 10 → QM31Exact}
    {lambda chi theta mu kappa : QM31Exact}
    {execution : CandidateExecution QM31Exact}
    (failure : FixedFamilyK15Failure terminal sumcheck fields extraction
      zerocheckPoint point lambda chi theta mu kappa execution) :
    ∃ category, FixedK15CategoryWitness terminal sumcheck fields extraction
      zerocheckPoint point lambda chi theta mu kappa execution category := by
  cases failure with
  | semantic witness => exact ⟨.semantic, witness⟩
  | copyLambda witness => exact ⟨.copyLambda, witness⟩
  | copyChi witness => exact ⟨.copyChi, witness⟩
  | muZero witness => exact ⟨.muZero, witness⟩
  | inactiveChi witness => exact ⟨.inactiveChi, witness⟩
  | oodMix witness => exact ⟨.oodMix, witness⟩
  | relationAlpha witness => exact ⟨.relationAlpha, witness⟩
  | kappaPointRow witness => exact ⟨.kappaPointRow, witness⟩

/-- Conversely, every stable measure-category witness reconstructs the exact
proof-producing fixed-family failure constructor. -/
theorem category_implies_fixedFamilyK15Failure
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    {terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact}
    {sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact}
    {fields : FixedFieldView QM31Exact}
    {extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule}
    {zerocheckPoint point : Fin 10 → QM31Exact}
    {lambda chi theta mu kappa : QM31Exact}
    {execution : CandidateExecution QM31Exact}
    {category : FixedK15Category}
    (witness : FixedK15CategoryWitness terminal sumcheck fields extraction
      zerocheckPoint point lambda chi theta mu kappa execution category) :
    FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint
      point lambda chi theta mu kappa execution := by
  cases category with
  | semantic => exact .semantic witness
  | copyLambda => exact .copyLambda witness
  | copyChi => exact .copyChi witness
  | muZero => exact .muZero witness
  | inactiveChi => exact .inactiveChi witness
  | oodMix => exact .oodMix witness
  | relationAlpha => exact .relationAlpha witness
  | kappaPointRow => exact .kappaPointRow witness

theorem fixedFamilyK15Failure_iff_exists_category
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    {terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact}
    {sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact}
    {fields : FixedFieldView QM31Exact}
    {extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule}
    {zerocheckPoint point : Fin 10 → QM31Exact}
    {lambda chi theta mu kappa : QM31Exact}
    {execution : CandidateExecution QM31Exact} :
    FixedFamilyK15Failure terminal sumcheck fields extraction zerocheckPoint
        point lambda chi theta mu kappa execution ↔
      ∃ category, FixedK15CategoryWitness terminal sumcheck fields extraction
        zerocheckPoint point lambda chi theta mu kappa execution category := by
  constructor
  · exact fixedFamilyK15Failure_implies_category
  · rintro ⟨category, witness⟩
    exact category_implies_fixedFamilyK15Failure witness

#print axioms fixedFamilyK15Failure_implies_category
#print axioms category_implies_fixedFamilyK15Failure
#print axioms fixedFamilyK15Failure_iff_exists_category

end AspisK1.V7Tag73K15CategoryBridge
