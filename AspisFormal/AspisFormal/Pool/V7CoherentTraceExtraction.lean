import AspisFormal.Pool.V7CandidateChainExtraction
import AspisFormal.Pool.V7C1SubfieldRecovery

/-!
# One coherent V7 candidate chain and semantic trace

The Merkle query-graph extractor reconstructs twenty-nine separate received
words.  The one-fold decoder, however, first selects one candidate for their
`gamma`-batched word whose natural coefficient fold is the disclosed final
vector.  This module joins those two facts without attempting to invert the
batched word.

For the selected combined candidate we build its literal agreement strategy
against the twenty-nine reconstructed lanes.  The only circle-code boundary
is then `HasMatchingWidth29Decomposition`.  Outside that named failure, the
algorithmic component selector returns one tuple on the same support and the
C1 projection theorem recovers one M31 semantic trace from its first sixteen
components.

This is the deterministic K1.4 composition.  It does not yet prove that the
semantic terminal accepts that trace or turn the trace into a spend witness;
those are K1.5 obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7CoherentTraceExtraction

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6Width29CorrelatedAgreement

abbrev ExactSchedule := OneFoldSchedule M31Exact QM31Exact
abbrev ExactCandidatePair := CandidatePair QM31Exact

/-- Use the exact encoders carried by one algorithmic decoder package in the
one-fold model.  This prevents the component and one-fold stages from silently
using different code definitions. -/
def decoderCodeEncoders (decoder : ExactDecoderInstantiation QM31Exact) :
    CodeEncoders QM31Exact where
  initial := decoder.initialEncoder
  final := decoder.finalEncoder

/-- The exact ideal one-fold transcript reconstructed from both complete
Merkle words.  Its initial word is definitionally the deployed width-29
pointwise gamma batch; it is not an independently supplied vector. -/
def extractedIdealTranscript
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact) :
    IdealTranscript QM31Exact where
  initial := batchInitialWords (extractedWidth29InitialWords words) gamma
  disclosedFinal := disclosedFinal

/-- Agreement support for one already-selected combined candidate.  The
candidate is fixed while the challenge varies; this is the exact response
strategy consumed by the width-29 correlated theorem. -/
noncomputable def selectedCandidateStrategy
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (selected : ExactCandidatePair) :
    Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact) := by
  classical
  exact {
    candidate := fun _ => selected.1
    support := fun challenge => Finset.univ.filter fun index =>
      width29CurveValue lanes challenge index =
        decoder.initialEncoder selected.1 index
  }

@[simp] theorem selectedCandidateStrategy_candidate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (selected : ExactCandidatePair) (challenge : QM31Exact) :
    (selectedCandidateStrategy decoder lanes selected).candidate challenge =
      selected.1 := by
  rfl

theorem selectedCandidateStrategy_support_card
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (selected : ExactCandidatePair) (gamma : QM31Exact) :
    ((selectedCandidateStrategy decoder lanes selected).support gamma).card =
      agreementCount (batchInitialWords lanes gamma)
        (decoder.initialEncoder selected.1) := by
  rfl

/-- Membership of the selected combined candidate in the exact initial
decoder list gives a valid width-29 response on precisely its full agreement
support. -/
theorem selected_chain_yields_valid_width29_response
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule) (selected : ExactCandidatePair)
    (selectedEq :
      selectCandidateChain
          (decoder.decodeBoth
            (extractedIdealTranscript words gamma disclosedFinal).initial
            (foldedReceived schedule
              (extractedIdealTranscript words gamma disclosedFinal)))
          schedule disclosedFinal = some selected) :
    Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)
      gamma := by
  let transcript := extractedIdealTranscript words gamma disclosedFinal
  let lists := decoder.decodeBoth transcript.initial
    (foldedReceived schedule transcript)
  have exactChain := selectedCandidateChain_is_exact
    lists schedule disclosedFinal selected (by simpa [lists, transcript] using selectedEq)
  have close := decoder.initialSound transcript.initial selected.1 exactChain.1
  constructor
  · rw [selectedCandidateStrategy_support_card]
    change 38229 < agreementCount transcript.initial
      (decoder.initialEncoder selected.1)
    change 38230 ≤ agreementCount transcript.initial
      (decoder.initialEncoder selected.1) at close
    omega
  · intro index indexInSupport
    simpa only [selectedCandidateStrategy, Finset.mem_filter,
      Finset.mem_univ, true_and] using indexInSupport

/-- Everything deterministically recovered at K1.4: one fold-consistent
combined candidate, one matching twenty-nine-component tuple on one common
support, and one literal M31 semantic trace. -/
structure CoherentTraceExtraction
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule) where
  combined : ExactCandidatePair
  combinedSelected :
    selectCandidateChain
        (decoder.decodeBoth
          (extractedIdealTranscript words gamma disclosedFinal).initial
          (foldedReceived schedule
            (extractedIdealTranscript words gamma disclosedFinal)))
        schedule disclosedFinal = some combined
  components : Width29InitialMessages QM31Exact
  everyComponentDecoded : ∀ lane,
    components lane ∈
      decoder.initialDecode ((extractedWidth29InitialWords words) lane)
  sharedSupport :
    (selectedCandidateStrategy decoder
      (extractedWidth29InitialWords words) combined).support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder
        (extractedWidth29InitialWords words) components
  combinedOnCurve :
    Width29CandidateOnCurve decoder.initialEncoder
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) combined)
      components gamma
  c1ComponentsAreBase : ∀ column : Fin 26,
    projectMessage (components (c1LaneIndex column)) =
      components (c1LaneIndex column)
  foldsToDisclosedFinal :
    foldInitial schedule combined.1 = disclosedFinal

/-- The extracted semantic table is an exact field embedding of the first
sixteen selected C1 messages. -/
theorem CoherentTraceExtraction.semanticTraceExact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (row : Fin 1024) (lane : Fin 16) :
    embedM31Exact (semanticTrace extraction.components row lane) =
      extraction.components
        (c1LaneIndex (semanticColumnIndex lane)) row := by
  exact semanticTrace_embeds_to_selected extraction.components
    extraction.c1ComponentsAreBase row lane

/-- The only new failure branch at this deterministic composition layer: the
selected fold-consistent combined candidate did not receive the matching
twenty-nine-component decomposition supplied by the published theorem. -/
def Width29DecompositionFailure
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule) : Prop :=
  ∃ selected,
    selectCandidateChain
        (decoder.decodeBoth
          (extractedIdealTranscript words gamma disclosedFinal).initial
          (foldedReceived schedule
            (extractedIdealTranscript words gamma disclosedFinal)))
        schedule disclosedFinal = some selected ∧
      ¬ HasMatchingWidth29Decomposition decoder.initialEncoder
        (extractedWidth29InitialWords words)
        (selectedCandidateStrategy decoder
          (extractedWidth29InitialWords words) selected)
        gamma

/-- A selected chain plus the published matching-decomposition conclusion
constructs the complete coherent K1.4 output. -/
theorem selected_chain_and_matching_components_extract_coherent_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule) (selected : ExactCandidatePair)
    (selectedEq :
      selectCandidateChain
          (decoder.decodeBoth
            (extractedIdealTranscript words gamma disclosedFinal).initial
            (foldedReceived schedule
              (extractedIdealTranscript words gamma disclosedFinal)))
          schedule disclosedFinal = some selected)
    (components : Width29InitialMessages QM31Exact)
    (everyDecoded : ∀ lane,
      components lane ∈
        decoder.initialDecode ((extractedWidth29InitialWords words) lane))
    (shared :
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected).support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder
        (extractedWidth29InitialWords words) components)
    (onCurve : Width29CandidateOnCurve decoder.initialEncoder
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)
      components gamma) :
    ∃ extraction : CoherentTraceExtraction decoder binding words gamma
        disclosedFinal schedule,
      extraction.combined = selected ∧ extraction.components = components := by
  have valid := selected_chain_yields_valid_width29_response decoder words
    gamma disclosedFinal schedule selected selectedEq
  have base := extracted_c1_components_are_base decoder binding words
    (selectedCandidateStrategy decoder
      (extractedWidth29InitialWords words) selected)
    gamma components valid shared
  have exactChain := selectedCandidateChain_is_exact
    (decoder.decodeBoth
      (extractedIdealTranscript words gamma disclosedFinal).initial
      (foldedReceived schedule
        (extractedIdealTranscript words gamma disclosedFinal)))
    schedule disclosedFinal selected selectedEq
  let extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule := {
    combined := selected
    combinedSelected := selectedEq
    components := components
    everyComponentDecoded := everyDecoded
    sharedSupport := shared
    combinedOnCurve := onCurve
    c1ComponentsAreBase := base
    foldsToDisclosedFinal := exactChain.2.2.1.trans exactChain.2.2.2
  }
  exact ⟨extraction, rfl, rfl⟩

/-- A selected chain plus the published matching-decomposition conclusion
constructs the complete coherent K1.4 output. -/
theorem selected_chain_extracts_coherent_trace
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule) (selected : ExactCandidatePair)
    (selectedEq :
      selectCandidateChain
          (decoder.decodeBoth
            (extractedIdealTranscript words gamma disclosedFinal).initial
            (foldedReceived schedule
              (extractedIdealTranscript words gamma disclosedFinal)))
          schedule disclosedFinal = some selected)
    (matching : HasMatchingWidth29Decomposition decoder.initialEncoder
      (extractedWidth29InitialWords words)
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)
      gamma) :
    ∃ extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule,
      extraction.combined = selected := by
  have valid := selected_chain_yields_valid_width29_response decoder words
    gamma disclosedFinal schedule selected selectedEq
  obtain ⟨components, _componentsEq, everyDecoded, shared, onCurve⟩ :=
    matching_decomposition_selects_exact_components decoder
      (extractedWidth29InitialWords words)
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)
      gamma valid matching
  obtain ⟨extraction, combinedExact, _componentsExact⟩ :=
    selected_chain_and_matching_components_extract_coherent_trace decoder
      binding words gamma disclosedFinal schedule selected selectedEq components
      everyDecoded shared onCurve
  exact ⟨extraction, combinedExact⟩

/-- Ideal one-fold acceptance deterministically yields one coherent trace or
the single explicit width-29 decomposition failure.  Query, fold and list-cap
failures remain the already named premises of the one-fold theorem. -/
theorem accepted_onefold_extracts_coherent_trace_or_width29_failure
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144)
    (accepts : IdealAccepts schedule (decoderCodeEncoders decoder)
      (extractedIdealTranscript words gamma disclosedFinal) queries)
    (notQueryFailure : ¬ QueryPhaseFailure schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript words gamma disclosedFinal) queries)
    (notFoldFailure : ¬ OneFoldReductionFailure schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript words gamma disclosedFinal))
    (notListCapFailure : ¬ InitialListCapFailure
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript words gamma disclosedFinal)) :
    (∃ extraction : CoherentTraceExtraction decoder binding words gamma
        disclosedFinal schedule, True) ∨
      Width29DecompositionFailure decoder words gamma disclosedFinal schedule := by
  obtain ⟨selected, selectedEq, _⟩ :=
    accepted_selects_one_consistent_chain schedule (decoderCodeEncoders decoder)
      (extractedIdealTranscript words gamma disclosedFinal) queries decoder
      rfl rfl accepts notQueryFailure notFoldFailure notListCapFailure
  by_cases matching : HasMatchingWidth29Decomposition decoder.initialEncoder
      (extractedWidth29InitialWords words)
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)
      gamma
  · left
    obtain ⟨extraction, _⟩ := selected_chain_extracts_coherent_trace decoder
      binding words gamma disclosedFinal schedule selected selectedEq matching
    exact ⟨extraction, trivial⟩
  · right
    exact ⟨selected, selectedEq, matching⟩

#print axioms selected_chain_yields_valid_width29_response
#print axioms CoherentTraceExtraction.semanticTraceExact
#print axioms selected_chain_and_matching_components_extract_coherent_trace
#print axioms selected_chain_extracts_coherent_trace
#print axioms accepted_onefold_extracts_coherent_trace_or_width29_failure

end AspisPool.V7CoherentTraceExtraction
