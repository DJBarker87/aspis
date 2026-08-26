import AspisFormal.K1.V7Tag73ExactConcreteStageAssembly
import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity

/-!
# Concrete K1.3/K1.4 events for the assembled Tag-73 stages

This module removes the generic K1.3 and K1.4 error families from the K1.6
stage package.  Under the exact successful one-fold verifier check and the
proved production initial-encoder identity, an executable K1.3 error is
literally either q16 proximity failure or the published one-fold event.  An
executable K1.4 error is literally the published width-29 correlated-
agreement event.

The events remain separate so the q16 probability theorem and the published
circle-code theorem can be instantiated without double counting.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactConcreteK13K14Events

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The deterministic source fact needed to eliminate `idealRejected` from
the K1.3 classifier.  It is the literal one-fold verifier success condition,
not a proximity-security claim. -/
structure ExactTag73K13SourceObligations
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop where
  idealAccepts :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
      IdealAccepts (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries

/-- Exact K1.3 residual event after deterministic source failures and the
impossible list-cap branch are removed. -/
def exactTag73K13QueryOrOneFoldEvent
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
      (k12 : ExactPrefixK12Certificate input),
    QueryPhaseFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries ∨
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)}

/-- Exact K1.4 residual event exposed directly by its sole classifier error
constructor. -/
def exactTag73K14Width29Event
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
      (k12 : ExactPrefixK12Certificate input)
      (_k13 : ExactK13Certificate decoder input k12),
    Width29DecompositionFailure decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule}

/-! ## Literal selected-schedule q16 target -/

/-- A fixed-run query failure says that the literal cap-203 schedule selected
by the operational transcript lies entirely in one exact consistency set of
size at most 9,557.  No probability or work normalization appears here. -/
theorem query_phase_failure_is_literal_selected_all_in_bad
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    AllInBad
      (consistencySet (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12))
      (exactOperationalTape input).search.selectedSchedule.positions := by
  intro ordinal
  have accepted := accepted_queries_mem_consistencySet
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    (exactK13Transcript input k12) (exactK13ParsedProof input).queries
    failure.1 ordinal
  rw [source.selectedQueriesExact] at accepted
  exact accepted

/-- Exact witness consumed by the forthcoming same-tape q16 coupling: one
pre-q16 consistency set, its deployed cardinality cap, and the actual selected
schedule landing wholly inside it. -/
theorem query_phase_failure_exposes_literal_q16_bad_set
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    ∃ bad : Finset (Fin 262144),
      bad.card ≤ 9557 ∧
        AllInBad bad
          (exactOperationalTape input).search.selectedSchedule.positions := by
  exact ⟨consistencySet (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12), failure.2,
    query_phase_failure_is_literal_selected_all_in_bad source failure⟩

theorem assembled_k13_error_subset_query_or_onefold
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    k13CircleListDecodeErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K13QueryOrOneFoldEvent transitionFuel configuration projection
        fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, k12, error⟩
  exact ⟨input, k12,
    exact_k13_error_reduces_to_query_or_onefold initialEncoderExact
      (source.idealAccepts sample input k12) error.some⟩

theorem assembled_k14_error_subset_width29
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding) :
    k14CoherentChainErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K14Width29Event transitionFuel configuration projection
        fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, k12, k13, error⟩
  exact ⟨input, k12, k13,
    exact_k14_error_is_width29_failure error.some⟩

/-- Combined deterministic cover retained only for final union accounting;
the two branches remain individually available for their different bounds. -/
theorem assembled_k13_k14_error_subset_exact_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    k13CircleListDecodeErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15) ∪
        k14CoherentChainErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K13QueryOrOneFoldEvent transitionFuel configuration projection
          fixedInstance decoder ∪
        exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder := by
  intro sample member
  rcases member with k13Error | k14Error
  · exact Or.inl (assembled_k13_error_subset_query_or_onefold transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 initialEncoderExact source k13Error)
  · exact Or.inr (assembled_k14_error_subset_width29 transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 k14Error)

#print axioms assembled_k13_error_subset_query_or_onefold
#print axioms assembled_k14_error_subset_width29
#print axioms assembled_k13_k14_error_subset_exact_union
#print axioms query_phase_failure_is_literal_selected_all_in_bad
#print axioms query_phase_failure_exposes_literal_q16_bad_set

end

end AspisK1.V7Tag73ExactConcreteK13K14Events
