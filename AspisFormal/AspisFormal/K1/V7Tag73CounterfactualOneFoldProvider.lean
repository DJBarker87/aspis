import AspisFormal.K1.V7Tag73CausalOneFoldProbability
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier

/-!
# Counterfactual Tag-73 alpha response provider

For fixed pre-alpha state and one complete ordinary-sampler nuisance skeleton,
the future-free prover is rerun at every returned alpha.  This file turns that
deterministic oracle into the adaptive one-fold response strategy used by the
causal degree-three theorem.  Its only operational seam is exact equality of
the returned parsed proof's gamma and one-fold schedule.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CounterfactualOneFoldProvider

open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces

noncomputable section

def ordinaryForSkeletonValue
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (value : QM31Exact) : SuccessfulTag73DuplexOrdinaryAttempt :=
  successfulDuplexOrdinaryFactorization.symm (skeleton, value)

@[simp] theorem ordinaryForSkeletonValue_factorization
    (sample : SuccessfulTag73DuplexOrdinaryAttempt) :
    ordinaryForSkeletonValue
        (successfulDuplexOrdinaryFactorization sample).1
        (successfulDuplexOrdinaryFactorization sample).2 = sample := by
  exact successfulDuplexOrdinaryFactorization.symm_apply_apply sample

@[simp] theorem ordinaryForSkeletonValue_returns_value
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (value : QM31Exact) :
    successfulDuplexOrdinaryValue (ordinaryForSkeletonValue skeleton value) =
      value := by
  have exact := successfulDuplexOrdinaryFactorization.apply_symm_apply
    (skeleton, value)
  rw [← successfulDuplexOrdinaryFactorization_value]
  exact congrArg Prod.snd exact

/-- Minimal deterministic future-free seam at alpha.  It contains no
probability, acceptance, extraction or witness conclusion. -/
structure CounterfactualParsedOneFoldOracle
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) where
  defaultFinal : FinalMessage QM31Exact
  proof? : SuccessfulTag73DuplexOrdinaryAttempt → Option Tag73K12ParsedProof
  proofGammaExact : ∀ sample proof, proof? sample = some proof →
    proof.gamma = gamma
  proofScheduleExact : ∀ sample proof, proof? sample = some proof →
    proof.schedule = scheduleAtAlpha baseSchedule
      (successfulDuplexOrdinaryValue sample)

def counterfactualOneFoldProof?
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (alpha : QM31Exact) : Option Tag73K12ParsedProof :=
  oracle.proof? (ordinaryForSkeletonValue skeleton alpha)

noncomputable def counterfactualOneFoldStrategy
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton) :
    ProximateStrategy QM31Exact (Fin 262144) (FinalCoefficients QM31Exact) := by
  classical
  exact {
    candidate := fun alpha =>
      match counterfactualOneFoldProof? oracle skeleton alpha with
      | some proof => proof.disclosedFinal
      | none => oracle.defaultFinal
    support := fun alpha =>
      match counterfactualOneFoldProof? oracle skeleton alpha with
      | some proof =>
          consistencySet (scheduleAtAlpha baseSchedule alpha)
            (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
      | none => ∅
  }

def counterfactualOneFoldBase
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule) :
    IdealTranscript QM31Exact :=
  extractedIdealTranscript words gamma oracle.defaultFinal

theorem actual_ordinary_counterfactual_proof_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    counterfactualOneFoldProof? oracle
        (successfulDuplexOrdinaryFactorization sample).1
        (successfulDuplexOrdinaryValue sample) = some proof := by
  unfold counterfactualOneFoldProof?
  rw [show ordinaryForSkeletonValue
      (successfulDuplexOrdinaryFactorization sample).1
      (successfulDuplexOrdinaryValue sample) = sample by
    rw [← successfulDuplexOrdinaryFactorization_value]
    exact ordinaryForSkeletonValue_factorization sample]
  exact proofExact

theorem actual_counterfactual_candidate_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldStrategy decoder oracle
      (successfulDuplexOrdinaryFactorization sample).1).candidate
        (successfulDuplexOrdinaryValue sample) = proof.disclosedFinal := by
  rw [counterfactualOneFoldStrategy]
  simp only
  rw [actual_ordinary_counterfactual_proof_exact oracle sample proof proofExact]

theorem actual_counterfactual_support_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldStrategy decoder oracle
      (successfulDuplexOrdinaryFactorization sample).1).support
        (successfulDuplexOrdinaryValue sample) =
      consistencySet proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) := by
  rw [counterfactualOneFoldStrategy]
  simp only
  rw [actual_ordinary_counterfactual_proof_exact oracle sample proof proofExact]
  rw [oracle.proofScheduleExact sample proof proofExact]

theorem actual_counterfactual_base_initial_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldBase oracle).initial =
      (parsedK13Transcript words proof).initial := by
  unfold counterfactualOneFoldBase parsedK13Transcript extractedIdealTranscript
  rw [oracle.proofGammaExact sample proof proofExact]

/-- A literal actual one-fold failure is a bad response of the complete
counterfactual alpha strategy built from the same future-free oracle. -/
theorem actual_oneFold_failure_is_counterfactual_bad_response
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : OneFoldAlgebraBinding baseSchedule
      (decoderCodeEncoders decoder))
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof)
    (failure : OneFoldReductionFailure proof.schedule
      (decoderCodeEncoders decoder) (parsedK13Transcript words proof)) :
    CausalOneFoldBadResponse baseSchedule (decoderCodeEncoders decoder) binding
      (counterfactualOneFoldBase oracle)
      (counterfactualOneFoldStrategy decoder oracle
        (successfulDuplexOrdinaryFactorization sample).1)
      (successfulDuplexOrdinaryValue sample) := by
  let alpha := successfulDuplexOrdinaryValue sample
  let strategy := counterfactualOneFoldStrategy decoder oracle
    (successfulDuplexOrdinaryFactorization sample).1
  have scheduleExact : proof.schedule = scheduleAtAlpha baseSchedule alpha :=
    oracle.proofScheduleExact sample proof proofExact
  have candidateExact : strategy.candidate alpha = proof.disclosedFinal :=
    actual_counterfactual_candidate_exact decoder oracle sample proof proofExact
  have supportExact : strategy.support alpha =
      consistencySet proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) :=
    actual_counterfactual_support_exact decoder oracle sample proof proofExact
  have initialExact : (counterfactualOneFoldBase oracle).initial =
      (parsedK13Transcript words proof).initial :=
    actual_counterfactual_base_initial_exact oracle sample proof proofExact
  have transcriptExact : causalOneFoldTranscriptAt
      (counterfactualOneFoldBase oracle) strategy alpha =
        parsedK13Transcript words proof := by
    cases leftEq : counterfactualOneFoldBase oracle with
    | mk leftInitial leftFinal =>
      cases rightEq : parsedK13Transcript words proof with
      | mk rightInitial rightFinal =>
        simp only [leftEq, rightEq] at initialExact
        have rightFinalExact : rightFinal = proof.disclosedFinal := by
          have exact : (parsedK13Transcript words proof).disclosedFinal =
              proof.disclosedFinal := rfl
          simpa only [rightEq] using exact
        have candidateRight : strategy.candidate alpha = rightFinal :=
          candidateExact.trans rightFinalExact.symm
        simp only [causalOneFoldTranscriptAt]
        rw [initialExact, candidateRight]
  constructor
  · constructor
    · rw [supportExact]
      exact failure.1
    · intro index member
      have member' : index ∈ consistencySet proof.schedule
          (decoderCodeEncoders decoder) (parsedK13Transcript words proof) := by
        rw [← supportExact]
        exact member
      have consistent : QueryConsistent proof.schedule
          (decoderCodeEncoders decoder) (parsedK13Transcript words proof) index := by
        simpa [consistencySet] using member'
      rw [curve_oneFoldDecodedLanes_eq_circleFold baseSchedule
        (decoderCodeEncoders decoder) binding
        (counterfactualOneFoldBase oracle) alpha index]
      change circleFoldLayer 262144 alpha baseSchedule.circleInv2x
          baseSchedule.circleInv2y (counterfactualOneFoldBase oracle).initial index =
        binding.finalLinear (strategy.candidate alpha) index
      rw [initialExact, candidateExact]
      calc
        (circleFoldLayer 262144 alpha baseSchedule.circleInv2x
            baseSchedule.circleInv2y)
              (parsedK13Transcript words proof).initial index =
            (decoderCodeEncoders decoder).final proof.disclosedFinal index := by
          simpa [QueryConsistent, scheduleExact, scheduleAtAlpha,
            parsedK13Transcript, extractedIdealTranscript] using consistent
        _ = binding.finalLinear proof.disclosedFinal index := by
          rw [binding.finalEncoderEq]
  · intro predecessor
    apply failure.2
    rcases predecessor with ⟨candidate, supported, folded⟩
    change SupportedNearInitial (scheduleAtAlpha baseSchedule alpha)
      (decoderCodeEncoders decoder)
      (causalOneFoldTranscriptAt (counterfactualOneFoldBase oracle)
        strategy alpha) candidate at supported
    change foldInitial (scheduleAtAlpha baseSchedule alpha) candidate =
      strategy.candidate alpha at folded
    rw [← scheduleExact, transcriptExact] at supported
    rw [← scheduleExact, candidateExact] at folded
    refine ⟨candidate, ?_, ?_⟩
    · exact supported
    · exact folded

end

#print axioms ordinaryForSkeletonValue_factorization
#print axioms actual_ordinary_counterfactual_proof_exact
#print axioms actual_counterfactual_support_exact
#print axioms actual_oneFold_failure_is_counterfactual_bad_response

end AspisK1.V7Tag73CounterfactualOneFoldProvider
