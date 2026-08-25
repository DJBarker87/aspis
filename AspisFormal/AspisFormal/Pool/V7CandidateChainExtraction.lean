import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import AspisFormal.V6OneFoldCandidateExtraction

/-!
# V7 deterministic one-fold candidate-chain selection

K1.3 returns two finite decoder lists.  K1.4 must not choose unrelated
existential candidates from those lists: one initial message must fold to one
final message, and that final message must be the exact disclosed terminal
object.  This module implements that finite search and connects it to the
existing one-fold deterministic inclusion theorem.

The remaining probabilistic reduction is deliberately visible in the four
failure-event hypotheses of `accepted_selects_one_consistent_chain`.  This
module does not assign those events a probability and does not yet decode the
selected initial message into a spend witness.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7CandidateChainExtraction

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The complete post-fold received word determined by the reconstructed
initial word, the deployed arity-four circle fold and the transcript alpha. -/
def foldedReceived (schedule : OneFoldSchedule F K)
    (transcript : IdealTranscript K) :
    AlgorithmicCircleDecoderV7.FinalWord K :=
  fun query =>
    circleFoldLayer 262144 schedule.alpha schedule.circleInv2x
      schedule.circleInv2y transcript.initial query

section FiniteField

variable [Fintype K] [DecidableEq K]

theorem final_agreement_count_eq_consistency_card
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) :
    agreementCount (foldedReceived schedule transcript)
        (encoders.final transcript.disclosedFinal) =
      (consistencySet schedule encoders transcript).card := by
  classical
  unfold agreementCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro query _
  change
    (foldedReceived schedule transcript query =
      encoders.final transcript.disclosedFinal query) ↔
      QueryConsistent schedule encoders transcript query
  rfl

theorem dense_consistency_implies_final_close
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (dense : 9557 < (consistencySet schedule encoders transcript).card) :
    closeAtLeast AlgorithmicCircleDecoderV7.finalAgreementThreshold encoders.final
      (foldedReceived schedule transcript) transcript.disclosedFinal := by
  unfold closeAtLeast finalAgreementThreshold
  rw [final_agreement_count_eq_consistency_card]
  omega

theorem near_initial_iff_decoder_close
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K) :
    NearInitial encoders transcript candidate ↔
      closeAtLeast AlgorithmicCircleDecoderV7.initialAgreementThreshold encoders.initial
        transcript.initial candidate := by
  rfl

abbrev CandidatePair (K : Type*) := InitialMessage K × FinalMessage K

/-- All and only pairs from the two decoder lists that form the exact
one-fold chain ending in the disclosed final coefficients. -/
def consistentCandidateChains (lists : DecodedCandidateLists K)
    (schedule : OneFoldSchedule F K) (disclosedFinal : FinalMessage K) :
    List (CandidatePair K) :=
  (lists.initial.product lists.final).filter fun pair =>
    decide (foldInitial schedule pair.1 = pair.2 ∧ pair.2 = disclosedFinal)

@[simp] theorem mem_consistentCandidateChains_iff
    (lists : DecodedCandidateLists K) (schedule : OneFoldSchedule F K)
    (disclosedFinal : FinalMessage K) (pair : CandidatePair K) :
    pair ∈ consistentCandidateChains lists schedule disclosedFinal ↔
      pair.1 ∈ lists.initial ∧ pair.2 ∈ lists.final ∧
        foldInitial schedule pair.1 = pair.2 ∧ pair.2 = disclosedFinal := by
  constructor
  · intro hmem
    have hfiltered := (List.mem_filter.mp hmem)
    have hproduct := List.mem_product.mp hfiltered.1
    have hpredicate := of_decide_eq_true hfiltered.2
    exact ⟨hproduct.1, hproduct.2, hpredicate.1, hpredicate.2⟩
  · rintro ⟨hinitial, hfinal, hfold, hterminal⟩
    exact List.mem_filter.mpr ⟨List.mem_product.mpr ⟨hinitial, hfinal⟩,
      decide_eq_true ⟨hfold, hterminal⟩⟩

/-- Deterministic selection: list order is the decoder's canonical order and
the first exact chain is returned. -/
def selectCandidateChain (lists : DecodedCandidateLists K)
    (schedule : OneFoldSchedule F K) (disclosedFinal : FinalMessage K) :
    Option (CandidatePair K) :=
  (consistentCandidateChains lists schedule disclosedFinal).head?

theorem selectCandidateChain_of_member
    (lists : DecodedCandidateLists K) (schedule : OneFoldSchedule F K)
    (disclosedFinal : FinalMessage K) (member : CandidatePair K)
    (hmember : member ∈ consistentCandidateChains lists schedule disclosedFinal) :
    ∃ selected,
      selectCandidateChain lists schedule disclosedFinal = some selected ∧
        selected ∈ consistentCandidateChains lists schedule disclosedFinal := by
  cases hchains : consistentCandidateChains lists schedule disclosedFinal with
  | nil =>
      simp [hchains] at hmember
  | cons first rest =>
      exact ⟨first, by simp [selectCandidateChain, hchains], by simp [hchains]⟩

theorem selectedCandidateChain_is_exact
    (lists : DecodedCandidateLists K) (schedule : OneFoldSchedule F K)
    (disclosedFinal : FinalMessage K) (selected : CandidatePair K)
    (hselected : selectCandidateChain lists schedule disclosedFinal = some selected) :
    selected.1 ∈ lists.initial ∧ selected.2 ∈ lists.final ∧
      foldInitial schedule selected.1 = selected.2 ∧
        selected.2 = disclosedFinal := by
  have hmember :
      selected ∈ consistentCandidateChains lists schedule disclosedFinal := by
    cases hchains : consistentCandidateChains lists schedule disclosedFinal with
    | nil =>
        simp [selectCandidateChain, hchains] at hselected
    | cons first rest =>
        have heq : first = selected := by
          simpa [selectCandidateChain, hchains] using hselected
        subst selected
        simp [hchains]
  exact (mem_consistentCandidateChains_iff lists schedule disclosedFinal selected).1 hmember

theorem consistentCandidateChains_length_le_product
    (lists : DecodedCandidateLists K) (schedule : OneFoldSchedule F K)
    (disclosedFinal : FinalMessage K) :
    (consistentCandidateChains lists schedule disclosedFinal).length ≤
      lists.initial.length * lists.final.length := by
  calc
    (consistentCandidateChains lists schedule disclosedFinal).length ≤
        (lists.initial.product lists.final).length := by
      exact List.length_filter_le
        (fun pair : CandidatePair K =>
          decide (foldInitial schedule pair.1 = pair.2 ∧
            pair.2 = disclosedFinal))
        (lists.initial.product lists.final)
    _ = lists.initial.length * lists.final.length :=
      List.length_product lists.initial lists.final

theorem decoded_consistent_chain_search_at_most_9900
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : AlgorithmicCircleDecoderV7.InitialWord K)
    (finalReceived : AlgorithmicCircleDecoderV7.FinalWord K)
    (schedule : OneFoldSchedule F K) (disclosedFinal : FinalMessage K) :
    (consistentCandidateChains
        (decoder.decodeBoth initialReceived finalReceived)
        schedule disclosedFinal).length ≤ 9900 := by
  apply (consistentCandidateChains_length_le_product
    (decoder.decodeBoth initialReceived finalReceived) schedule disclosedFinal).trans
  have hinitial := decoder.initialOutputBound initialReceived
  have hfinal := decoder.finalOutputBound finalReceived
  exact Nat.mul_le_mul hinitial hfinal

/-- Outside the already named query, fold-reduction and list-cap failures, the
two explicit K1.3 decoder lists contain an exact pair.  The executable selector
therefore returns one single chain; subsequent stages consume this selected
pair rather than choosing candidates independently at each layer. -/
theorem accepted_selects_one_consistent_chain
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144)
    (decoder : ExactDecoderInstantiation K)
    (initialEncoderExact : decoder.initialEncoder = encoders.initial)
    (finalEncoderExact : decoder.finalEncoder = encoders.final)
    (accepts : IdealAccepts schedule encoders transcript queries)
    (notQueryFailure : ¬ QueryPhaseFailure schedule encoders transcript queries)
    (notFoldFailure : ¬ OneFoldReductionFailure schedule encoders transcript)
    (notListCapFailure : ¬ InitialListCapFailure encoders transcript) :
    let lists := decoder.decodeBoth transcript.initial
      (foldedReceived schedule transcript)
    ∃ selected,
      selectCandidateChain lists schedule transcript.disclosedFinal = some selected ∧
        selected.1 ∈ lists.initial ∧ selected.2 ∈ lists.final ∧
          foldInitial schedule selected.1 = selected.2 ∧
            selected.2 = transcript.disclosedFinal := by
  dsimp only
  obtain ⟨candidate, candidateMem, candidateFold, _⟩ :=
    accepted_ideal_onefold_supplies_matching_initial_candidate schedule encoders
      transcript queries accepts notQueryFailure notFoldFailure notListCapFailure
  have dense := dense_consistency_of_accepts_not_queryFailure schedule encoders
    transcript queries accepts notQueryFailure
  have initialClose :
      closeAtLeast AlgorithmicCircleDecoderV7.initialAgreementThreshold
        decoder.initialEncoder
        transcript.initial candidate := by
    rw [initialEncoderExact]
    exact (near_initial_iff_decoder_close encoders transcript candidate).1
      ((mem_initialCandidateList_iff encoders transcript candidate).1 candidateMem)
  have finalClose :
      closeAtLeast AlgorithmicCircleDecoderV7.finalAgreementThreshold
        decoder.finalEncoder
        (foldedReceived schedule transcript) transcript.disclosedFinal := by
    rw [finalEncoderExact]
    exact dense_consistency_implies_final_close schedule encoders transcript dense
  have initialMem := decoder.initialComplete transcript.initial candidate initialClose
  have finalMem := decoder.finalComplete (foldedReceived schedule transcript)
    transcript.disclosedFinal finalClose
  let lists := decoder.decodeBoth transcript.initial (foldedReceived schedule transcript)
  have pairMem :
      (candidate, transcript.disclosedFinal) ∈
        consistentCandidateChains lists schedule transcript.disclosedFinal := by
    apply (mem_consistentCandidateChains_iff lists schedule
      transcript.disclosedFinal (candidate, transcript.disclosedFinal)).2
    exact ⟨initialMem, finalMem, candidateFold, rfl⟩
  obtain ⟨selected, selectedEq, selectedMem⟩ :=
    selectCandidateChain_of_member lists schedule transcript.disclosedFinal
      (candidate, transcript.disclosedFinal) pairMem
  refine ⟨selected, selectedEq, ?_⟩
  exact (mem_consistentCandidateChains_iff lists schedule
    transcript.disclosedFinal selected).1 selectedMem

#print axioms final_agreement_count_eq_consistency_card
#print axioms dense_consistency_implies_final_close
#print axioms mem_consistentCandidateChains_iff
#print axioms selectedCandidateChain_is_exact
#print axioms decoded_consistent_chain_search_at_most_9900
#print axioms accepted_selects_one_consistent_chain

end FiniteField

end AspisPool.V7CandidateChainExtraction
