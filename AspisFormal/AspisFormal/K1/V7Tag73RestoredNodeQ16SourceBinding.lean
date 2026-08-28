import AspisFormal.K1.V7Tag73RestoredK13Events

/-!
# Restored-node q16 source binding

The parser records sixteen query positions while the future-free verifier
records the selected q16 schedule in a literal `.q16Selected` control state.
This module states their exact data equality for one stored restoration node
and transports the K1.3 bad-set result onto that operational transition.

The binding contains no acceptance, probability, or extraction conclusion.
It is the narrow source/alignment fact that the current Rust/Aeneas caller
bridge must construct for every accepted stored node.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RestoredNodeQ16SourceBinding

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Literal operational source fact for the selected q16 branch of one
restored execution. -/
def RestoredNodeQ16SourceBinding
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) : Prop :=
  ∃ (base : Digest256) (counter : Fin 64) (schedule : QuerySchedule)
      (remaining : List FutureFreeSlot) (transition : FutureFreeTransition),
    transition ∈ node.verifierFinalState.transitions ∧
      transition.before.control =
        .q16Selected base counter schedule remaining ∧
      (restoredNodeK12Proof node).queries = schedule.positions

/-- A restored K1.3 q16 failure is now attached to a previously executed,
literal selected-control transition rather than merely to parser bytes. -/
theorem restored_query_failure_is_operational_selected_all_in_bad
    {Statement Payload : Type*}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {node : RestoredK13Node Statement Payload}
    (source : RestoredNodeQ16SourceBinding node)
    (k12 : RestoredNodeK12Certificate node)
    (failure : QueryPhaseFailure (restoredNodeK12Proof node).schedule
      (decoderCodeEncoders decoder)
      (parsedK13Transcript k12.words (restoredNodeK12Proof node))
      (restoredNodeK12Proof node).queries) :
    ∃ (bad : Finset (Fin 262144))
        (base : Digest256) (counter : Fin 64) (schedule : QuerySchedule)
        (remaining : List FutureFreeSlot) (transition : FutureFreeTransition),
      bad.card ≤ 9557 ∧
      transition ∈ node.verifierFinalState.transitions ∧
      transition.before.control = .q16Selected base counter schedule remaining ∧
      AllInBad bad schedule.positions := by
  obtain ⟨bad, badCard, allBad⟩ :=
    restored_query_phase_failure_exposes_q16_bad_set k12 failure
  rcases source with
    ⟨base, counter, schedule, remaining, transition, transitionMember,
      controlExact, queriesExact⟩
  refine ⟨bad, base, counter, schedule, remaining, transition, badCard,
    transitionMember, controlExact, ?_⟩
  simpa [queriesExact] using allBad

#print axioms restored_query_failure_is_operational_selected_all_in_bad

end

end AspisK1.V7Tag73RestoredNodeQ16SourceBinding
