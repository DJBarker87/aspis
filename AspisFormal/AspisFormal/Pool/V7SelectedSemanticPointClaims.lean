import AspisFormal.Pool.V7CoherentTraceExtraction
import AspisFormal.V5ComponentADeployedTerminalApplicability

/-!
# Selected V7 semantic point claims

The coherent K1.4 extraction produces sixteen literal M31 semantic columns
inside the selected width-29 QM31 component tuple.  This module defines their
three deployed multilinear evaluations and identifies each one with the
corresponding selected component evaluation.

This is a deterministic mathematical equality.  It does not assume that a
serialized verifier claim equals the selected evaluation; that separate
terminal-binding obligation belongs to the next extraction layer.
-/

set_option autoImplicit false

namespace AspisPool.V7SelectedSemanticPointClaims

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

/-- The concrete MLE claim of one recovered semantic column at one of the
three deployed relation points. -/
noncomputable def selectedSemanticPointClaim
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (which : Fin 3) (lane : Fin 16) :
    QM31Exact :=
  multilinearEvalValue (deployedRelationPoint point which)
    (fun row => embedM31Exact (semanticTrace extraction.components row lane))

/-- Evaluating an extracted semantic column is exactly evaluating its selected
width-29 component message. -/
theorem selectedSemanticPointClaim_eq_componentEvaluation
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (which : Fin 3) (lane : Fin 16) :
    selectedSemanticPointClaim extraction point which lane =
      multilinearEvalValue (deployedRelationPoint point which)
        (extraction.components
          (c1LaneIndex (semanticColumnIndex lane))) := by
  unfold selectedSemanticPointClaim
  apply congrArg (multilinearEvalValue (deployedRelationPoint point which))
  funext row
  exact extraction.semanticTraceExact row lane

#print axioms selectedSemanticPointClaim_eq_componentEvaluation

end AspisPool.V7SelectedSemanticPointClaims
