import AspisFormal.K1.V7Tag73RestoredNodeK13Classifier
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events

/-!
# Restoration-wide K1.3 events for Tag-73

The completed K1.6 accumulator contains the accepted root at node zero and
every successful same-tape restoration child thereafter.  K1.3 must therefore
be measured over failures of stored nodes, not only over the proof eventually
returned by the root run.  This module defines that literal event family and
keeps q16 and one-fold failures disjoint at the accounting interface.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RestoredK13Events

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisK1.V7Tag73Q16FirstCompactUniformity

noncomputable section

/-- A q16 consistency failure in any successful execution actually stored by
the exact K1.6 restoration client. -/
def exactTag73RestoredK13QueryEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (node : RestoredK13Node Statement Payload),
    node ∈ (exactRestorationAccumulator input).nodes ∧
      node.verifierFinalState.current.control = .done ∧
      ∃ k12 : RestoredNodeK12Certificate node,
        QueryPhaseFailure (restoredNodeK12Proof node).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript k12.words (restoredNodeK12Proof node))
          (restoredNodeK12Proof node).queries}

/-- A published one-fold reduction failure in any successful execution stored
by the exact K1.6 restoration client. -/
def exactTag73RestoredK13OneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (node : RestoredK13Node Statement Payload),
    node ∈ (exactRestorationAccumulator input).nodes ∧
      node.verifierFinalState.current.control = .done ∧
      ∃ k12 : RestoredNodeK12Certificate node,
        OneFoldReductionFailure (restoredNodeK12Proof node).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript k12.words (restoredNodeK12Proof node))}

/-- The residual K1.3 algebraic event before the joint-batch and later-alpha
checks are added. -/
def exactTag73RestoredK13QueryOrOneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (node : RestoredK13Node Statement Payload),
    node ∈ (exactRestorationAccumulator input).nodes ∧
      node.verifierFinalState.current.control = .done ∧
      ∃ k12 : RestoredNodeK12Certificate node,
        QueryPhaseFailure (restoredNodeK12Proof node).schedule
            (decoderCodeEncoders decoder)
            (parsedK13Transcript k12.words (restoredNodeK12Proof node))
            (restoredNodeK12Proof node).queries ∨
          OneFoldReductionFailure (restoredNodeK12Proof node).schedule
            (decoderCodeEncoders decoder)
            (parsedK13Transcript k12.words (restoredNodeK12Proof node))}

theorem exactTag73RestoredK13QueryOrOneFoldEvent_eq_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    exactTag73RestoredK13QueryOrOneFoldEvent transitionFuel configuration
        projection fixedInstance decoder =
      exactTag73RestoredK13QueryEvent transitionFuel configuration projection
          fixedInstance decoder ∪
        exactTag73RestoredK13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, node, member, accepted, k12, query | oneFold⟩
    · exact Or.inl ⟨input, node, member, accepted, k12, query⟩
    · exact Or.inr ⟨input, node, member, accepted, k12, oneFold⟩
  · rintro (⟨input, node, member, accepted, k12, query⟩ |
      ⟨input, node, member, accepted, k12, oneFold⟩)
    · exact ⟨input, node, member, accepted, k12, Or.inl query⟩
    · exact ⟨input, node, member, accepted, k12, Or.inr oneFold⟩

/-- Pointwise semantic handoff for the restoration-wide q16 event.  It
retains the literal node and accumulator membership needed by the operational
same-tape coupling. -/
theorem restored_query_event_exposes_node_and_capped_bad_set
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (member : sample ∈ exactTag73RestoredK13QueryEvent transitionFuel
      configuration projection fixedInstance decoder) :
    ∃ (input : ExactK12OperationalInput transitionFuel configuration projection
          fixedInstance sample)
        (node : RestoredK13Node Statement Payload)
        (k12 : RestoredNodeK12Certificate node)
        (bad : Finset (Fin 262144)),
      node ∈ (exactRestorationAccumulator input).nodes ∧
        node.verifierFinalState.current.control = .done ∧
        bad.card ≤ 9557 ∧
        AllInBad bad (restoredNodeK12Proof node).queries := by
  rcases member with ⟨input, node, nodeMember, accepted, k12, failure⟩
  obtain ⟨bad, badCard, allBad⟩ :=
    restored_query_phase_failure_exposes_q16_bad_set k12 failure
  exact ⟨input, node, k12, bad, nodeMember, accepted, badCard, allBad⟩

#print axioms exactTag73RestoredK13QueryOrOneFoldEvent_eq_union
#print axioms restored_query_event_exposes_node_and_capped_bad_set

end

end AspisK1.V7Tag73RestoredK13Events
