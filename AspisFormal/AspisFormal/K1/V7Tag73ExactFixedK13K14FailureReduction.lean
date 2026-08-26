import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
import AspisFormal.Pool.V7C1ConcreteProjectionBinding

/-!
# Exact fixed Tag-73 K1.3/K1.4 failure reduction

This module removes the deterministic/non-cryptographic branches from the
fixed-run K1.3/K1.4 classifiers.  Once production acceptance supplies the
literal ideal one-fold checks and the decoder uses the exact initial encoder,
the only remaining branches are:

* the conditioned q16 query miss;
* the published one-fold reduction failure; or
* the published width-29 matching-decomposition failure.

In particular the initial list-cap branch is impossible from the proved exact
encoder overlap bound; it is not charged as an extra probability event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedK13K14FailureReduction

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

theorem exact_k13_initial_encoder_overlap_cap
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder) :
    InitialEncoderOverlapCap (exactK13Encoders decoder) := by
  have binding := initialProjectionBinding_of_initialEncoder_eq decoder
    initialEncoderExact
  intro left right different
  exact binding.overlapCap left right different

theorem exact_k13_initial_list_cap_failure_impossible
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    ¬ InitialListCapFailure (exactK13Encoders decoder)
      (exactK13Transcript input k12) := by
  exact initial_list_cap_failure_impossible_of_overlap
    (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exact_k13_initial_encoder_overlap_cap decoder initialEncoderExact)

/-- Under the actual ideal acceptance check and the exact encoder identity,
an executable K1.3 error is only a q16 miss or the published one-fold event. -/
theorem exact_k13_error_reduces_to_query_or_onefold
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
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries)
    (error : ExactK13Error decoder input k12) :
    QueryPhaseFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries ∨
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12) := by
  cases error with
  | idealRejected rejected => exact False.elim (rejected accepts)
  | queryPhaseFailure failure => exact Or.inl failure
  | oneFoldReductionFailure failure => exact Or.inr failure
  | initialListCapFailure failure =>
      exact False.elim
        ((exact_k13_initial_list_cap_failure_impossible decoder
          initialEncoderExact input k12) failure)

/-- K1.4 has exactly one right branch, with no residual aggregate event. -/
theorem exact_k14_error_is_width29_failure
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
    (error : ExactK14Error decoder input k12) :
    Width29DecompositionFailure decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule := by
  cases error with
  | width29 failure => exact failure

/-- Complete deterministic K1.3/K1.4 reduction.  The second disjunct is the
precise permitted circle-code boundary; q16 remains separate. -/
theorem exact_k13_k14_error_reduces_to_query_or_circle
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
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries)
    (error : ExactK13Error decoder input k12 ⊕
      ExactK14Error decoder input k12) :
    QueryPhaseFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries ∨
      (OneFoldReductionFailure (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder) (exactK13Transcript input k12) ∨
        Width29DecompositionFailure decoder k12.words
          (exactK13ParsedProof input).gamma
          (exactK13ParsedProof input).disclosedFinal
          (exactK13ParsedProof input).schedule) := by
  cases error with
  | inl k13 =>
      rcases exact_k13_error_reduces_to_query_or_onefold
          initialEncoderExact accepts k13 with query | fold
      · exact Or.inl query
      · exact Or.inr (Or.inl fold)
  | inr k14 =>
      exact Or.inr (Or.inr (exact_k14_error_is_width29_failure k14))

/-! ## Pointwise width-29 published-theorem target -/

/-- A concrete K1.4 failure at nonzero `gamma` is a valid-but-unmatched
response for the exact selected candidate strategy. -/
theorem exact_k14_failure_mem_width29_bad_challenges
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
    (gammaNonzero : (exactK13ParsedProof input).gamma ≠ 0)
    (failure : Width29DecompositionFailure decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule) :
    ∃ selected,
      selectCandidateChain
          (decoder.decodeBoth
            (exactK13Transcript input k12).initial
            (foldedReceived (exactK13ParsedProof input).schedule
              (exactK13Transcript input k12)))
          (exactK13ParsedProof input).schedule
          (exactK13ParsedProof input).disclosedFinal = some selected ∧
        (exactK13ParsedProof input).gamma ∈
          width29GoodChallenges decoder.initialEncoder
            AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
            (extractedWidth29InitialWords k12.words)
            (width29BadStrategy decoder.initialEncoder
              AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
              (extractedWidth29InitialWords k12.words)
              (selectedCandidateStrategy decoder
                (extractedWidth29InitialWords k12.words) selected)) := by
  rcases failure with ⟨selected, selectedEq, noMatching⟩
  refine ⟨selected, ?_, ?_⟩
  · exact selectedEq
  · let lanes := extractedWidth29InitialWords k12.words
    let strategy := selectedCandidateStrategy decoder lanes selected
    change (exactK13ParsedProof input).gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
          strategy)
    rw [mem_width29BadStrategy_good_iff]
    refine ⟨gammaNonzero, ?_⟩
    exact ⟨selected_chain_yields_valid_width29_response decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule selected selectedEq,
      noMatching⟩

/-- For every fixed selected response, the exact published theorem gives the
degree-28 target cap.  A later restoration-strategy module will assemble the
single challenge-indexed response strategy without a list-size union. -/
theorem fixed_selected_width29_bad_challenges_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (selected : ExactCandidatePair) :
    (width29GoodChallenges decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (width29BadStrategy decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (selectedCandidateStrategy decoder
          (extractedWidth29InitialWords words) selected))).card ≤
      initialBatchChallengeCap := by
  exact initial_bad_response_challenges_card_le decoder.initialEncoder
    published (extractedWidth29InitialWords words)
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) selected)

/-! ## One restoration-wide strategy, without a decoder-list union -/

/-- A same-tape restoration extractor supplies one selected initial response
for every possible nonzero batching challenge.  Its agreement support is
defined canonically from that response.  Unlike `selectedCandidateStrategy`,
this strategy may select a different response at each challenge, exactly as
the published correlated-agreement theorem permits. -/
noncomputable def restoredWidth29Strategy
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Fin 29 →
      AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact) :
    Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact) := by
  classical
  exact {
    candidate := response
    support := fun gamma => Finset.univ.filter fun index =>
      width29CurveValue lanes gamma index =
        decoder.initialEncoder (response gamma) index
  }

@[simp] theorem restoredWidth29Strategy_candidate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Fin 29 →
      AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (response : QM31Exact → InitialMessage QM31Exact) (gamma : QM31Exact) :
    (restoredWidth29Strategy decoder lanes response).candidate gamma =
      response gamma := by
  rfl

theorem restoredWidth29Strategy_support_eq_selected
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Fin 29 →
      AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (selected : ExactCandidatePair)
    (response : QM31Exact → InitialMessage QM31Exact)
    (gamma : QM31Exact)
    (responseAt : response gamma = selected.1) :
    (restoredWidth29Strategy decoder lanes response).support gamma =
      (selectedCandidateStrategy decoder lanes selected).support gamma := by
  classical
  change (Finset.univ.filter fun index =>
      width29CurveValue lanes gamma index =
        decoder.initialEncoder (response gamma) index) =
    Finset.univ.filter fun index =>
      width29CurveValue lanes gamma index =
        decoder.initialEncoder selected.1 index
  rw [responseAt]

set_option linter.constructorNameAsVariable false in
/-- A pointwise fixed-run bad response is counted by the single
restoration-wide strategy when the state-restoration adapter identifies its
selected message with the response at the sampled challenge. -/
theorem fixed_selected_bad_mem_restored_width29_bad_challenges
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Fin 29 →
      AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (selected : ExactCandidatePair)
    (response : QM31Exact → InitialMessage QM31Exact)
    (gamma : QM31Exact)
    (responseAt : response gamma = selected.1)
    (fixedMember : gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
          (selectedCandidateStrategy decoder lanes selected))) :
    gamma ∈ width29GoodChallenges decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
      (width29BadStrategy decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        (restoredWidth29Strategy decoder lanes response)) := by
  rw [mem_width29BadStrategy_good_iff] at fixedMember ⊢
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder lanes
    selected response gamma responseAt
  have restoredValid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      lanes (restoredWidth29Strategy decoder lanes response) gamma := by
    constructor
    · rw [supportEq]
      exact fixedMember.2.1.1
    · intro index member
      rw [supportEq] at member
      have fixedAgreement := fixedMember.2.1.2 index member
      rw [restoredWidth29Strategy_candidate, responseAt]
      rw [selectedCandidateStrategy_candidate] at fixedAgreement
      exact fixedAgreement
  have restoredNoMatching : ¬ HasMatchingWidth29Decomposition
      decoder.initialEncoder lanes
      (restoredWidth29Strategy decoder lanes response) gamma := by
    intro restoredMatching
    apply fixedMember.2.2
    rcases restoredMatching with ⟨components, shared, onCurve⟩
    refine ⟨components, ?_, ?_⟩
    · rw [← supportEq]
      exact shared
    · unfold Width29CandidateOnCurve at onCurve ⊢
      rw [restoredWidth29Strategy_candidate, responseAt] at onCurve
      rw [selectedCandidateStrategy_candidate]
      exact onCurve
  exact ⟨fixedMember.1, restoredValid, restoredNoMatching⟩

/-- The one restoration-wide bad set has the published degree-28 cap directly;
there is no factor 100 or 9,900 from unioning independently selected lists. -/
theorem restored_width29_bad_challenges_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (response : QM31Exact → InitialMessage QM31Exact) :
    (width29GoodChallenges decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (width29BadStrategy decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (restoredWidth29Strategy decoder
          (extractedWidth29InitialWords words) response))).card ≤
      initialBatchChallengeCap := by
  exact initial_bad_response_challenges_card_le decoder.initialEncoder
    published (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder
        (extractedWidth29InitialWords words) response)

#print axioms exact_k13_initial_encoder_overlap_cap
#print axioms exact_k13_initial_list_cap_failure_impossible
#print axioms exact_k13_error_reduces_to_query_or_onefold
#print axioms exact_k14_error_is_width29_failure
#print axioms exact_k13_k14_error_reduces_to_query_or_circle
#print axioms exact_k14_failure_mem_width29_bad_challenges
#print axioms fixed_selected_width29_bad_challenges_card_le
#print axioms fixed_selected_bad_mem_restored_width29_bad_challenges
#print axioms restored_width29_bad_challenges_card_le

end

end AspisK1.V7Tag73ExactFixedK13K14FailureReduction
