import AspisFormal.Pool.KnowledgeExtractorInterface
import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Exact algorithmic circle-decoder boundary for V7

Knowledge extraction needs executable finite-list decoders, not existential
decodability predicates.  This module fixes the two deployed one-fold stages,
their exact agreement thresholds and their proved list caps.  A concrete
instantiation must provide deterministic algorithms and the exact S-two
circle-to-GRS applicability proof; this file does not pretend that a citation
is executable Lean code.
-/

set_option autoImplicit false

namespace AspisPool.AlgorithmicCircleDecoderV7

open AspisPool.KnowledgeExtractorInterface

abbrev InitialMessage (K : Type*) := Fin 1024 → K
abbrev InitialWord (K : Type*) := Fin 1048576 → K
abbrev FinalMessage (K : Type*) := Fin 256 → K
abbrev FinalWord (K : Type*) := Fin 262144 → K

def initialAgreementThreshold : Nat := 38230
def finalAgreementThreshold : Nat := 9558
def initialListSizeCap : Nat := 100
def finalListSizeCap : Nat := 99

def agreementCount {K : Type*} [DecidableEq K] {n : Nat}
    (received encoded : Fin n → K) : Nat :=
  (Finset.univ.filter fun index => received index = encoded index).card

def closeAtLeast {K Message : Type*} [DecidableEq K] {n : Nat}
    (threshold : Nat) (encoder : Message → Fin n → K)
    (received : Fin n → K) (message : Message) : Prop :=
  threshold ≤ agreementCount received (encoder message)

theorem exact_decoder_parameters :
    initialAgreementThreshold = 38230 ∧
      finalAgreementThreshold = 9558 ∧
      initialListSizeCap = 100 ∧
      finalListSizeCap = 99 := by
  norm_num [initialAgreementThreshold, finalAgreementThreshold,
    initialListSizeCap, finalListSizeCap]

/-!
The soundness ledger writes the two agreement cutoffs in strict form
(`38229 < card` and `9557 < card`), while an executable decoder naturally
accepts a non-strict minimum count (`38230 ≤ card` and `9558 ≤ card`).  The
following two lemmas close that off-by-one interface explicitly.  They prevent
an algorithmic decoder from being connected to a nearby, weaker radius.
-/

theorem initial_close_iff_published_strict
    {K Message : Type*} [DecidableEq K]
    (encoder : Message → InitialWord K)
    (received : InitialWord K) (message : Message) :
    closeAtLeast initialAgreementThreshold encoder received message ↔
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
        agreementCount received (encoder message) := by
  change 38230 ≤ agreementCount received (encoder message) ↔
    38229 < agreementCount received (encoder message)
  omega

theorem final_close_iff_published_strict
    {K Message : Type*} [DecidableEq K]
    (encoder : Message → FinalWord K)
    (received : FinalWord K) (message : Message) :
    closeAtLeast finalAgreementThreshold encoder received message ↔
      AspisV6PublishedTheoremInterfaces.outputAgreementThreshold <
        agreementCount received (encoder message) := by
  change 9558 ≤ agreementCount received (encoder message) ↔
    9557 < agreementCount received (encoder message)
  omega

/-- Exact external algorithm package needed for the two reconstructed V7
received words.  The conversion and polynomial-time fields are intentionally
separate: list completeness alone is not an algorithmic theorem. -/
structure ExactDecoderInstantiation (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] where
  initialEncoder : InitialMessage K → InitialWord K
  finalEncoder : FinalMessage K → FinalWord K
  initialDecode : InitialWord K → List (InitialMessage K)
  finalDecode : FinalWord K → List (FinalMessage K)
  initialComplete : ∀ received message,
    closeAtLeast initialAgreementThreshold initialEncoder received message →
      message ∈ initialDecode received
  initialSound : ∀ received message,
    message ∈ initialDecode received →
      closeAtLeast initialAgreementThreshold initialEncoder received message
  initialOutputBound : ∀ received,
    (initialDecode received).length ≤ initialListSizeCap
  finalComplete : ∀ received message,
    closeAtLeast finalAgreementThreshold finalEncoder received message →
      message ∈ finalDecode received
  finalSound : ∀ received message,
    message ∈ finalDecode received →
      closeAtLeast finalAgreementThreshold finalEncoder received message
  finalOutputBound : ∀ received,
    (finalDecode received).length ≤ finalListSizeCap
  exactInitialCircleToGrsConversion : Prop
  exactFinalLineToGrsConversion : Prop
  multiplicityThreeGuruswamiSudanApplicable : Prop
  initialDeterministicPolynomialTime : Prop
  finalDeterministicPolynomialTime : Prop

/-- Package the exact initial algorithm as the common operational decoder
interface used by the K1 extraction composition. -/
def ExactDecoderInstantiation.initialAlgorithm
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) :
    AlgorithmicListDecoder (InitialWord K) (InitialMessage K) where
  close := closeAtLeast initialAgreementThreshold decoder.initialEncoder
  decode := decoder.initialDecode
  listSizeCap := initialListSizeCap
  complete := decoder.initialComplete
  sound := decoder.initialSound
  outputBound := decoder.initialOutputBound
  deterministicPolynomialTime := decoder.initialDeterministicPolynomialTime

/-- Package the exact post-fold algorithm. -/
def ExactDecoderInstantiation.finalAlgorithm
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) :
    AlgorithmicListDecoder (FinalWord K) (FinalMessage K) where
  close := closeAtLeast finalAgreementThreshold decoder.finalEncoder
  decode := decoder.finalDecode
  listSizeCap := finalListSizeCap
  complete := decoder.finalComplete
  sound := decoder.finalSound
  outputBound := decoder.finalOutputBound
  deterministicPolynomialTime := decoder.finalDeterministicPolynomialTime

/-- The concrete K1.3 output consumed by candidate-chain extraction.  Keeping
both lists in one value makes it impossible for a later composition theorem to
silently invoke a different decoder between the initial and final stages. -/
structure DecodedCandidateLists (K : Type*) where
  initial : List (InitialMessage K)
  final : List (FinalMessage K)

def ExactDecoderInstantiation.decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K) :
    DecodedCandidateLists K where
  initial := decoder.initialDecode initialReceived
  final := decoder.finalDecode finalReceived

theorem decodeBoth_has_exact_caps
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K) :
    (decoder.decodeBoth initialReceived finalReceived).initial.length ≤ 100 ∧
      (decoder.decodeBoth initialReceived finalReceived).final.length ≤ 99 := by
  exact ⟨decoder.initialOutputBound initialReceived,
    decoder.finalOutputBound finalReceived⟩

theorem initial_close_candidate_mem_decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K)
    (message : InitialMessage K)
    (close : closeAtLeast initialAgreementThreshold decoder.initialEncoder
      initialReceived message) :
    message ∈ (decoder.decodeBoth initialReceived finalReceived).initial := by
  exact decoder.initialComplete initialReceived message close

theorem final_close_candidate_mem_decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K)
    (message : FinalMessage K)
    (close : closeAtLeast finalAgreementThreshold decoder.finalEncoder
      finalReceived message) :
    message ∈ (decoder.decodeBoth initialReceived finalReceived).final := by
  exact decoder.finalComplete finalReceived message close

theorem initial_output_at_most_100
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) (received : InitialWord K) :
    (decoder.initialDecode received).length ≤ 100 := by
  simpa [initialListSizeCap] using decoder.initialOutputBound received

theorem final_output_at_most_99
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) (received : FinalWord K) :
    (decoder.finalDecode received).length ≤ 99 := by
  simpa [finalListSizeCap] using decoder.finalOutputBound received

/-- This conjunction is the exact literature/application boundary that must
be discharged before the algorithms can be attributed to S-two Theorem 7. -/
def ExactDecoderInstantiation.publishedApplicability
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) : Prop :=
  decoder.exactInitialCircleToGrsConversion ∧
    decoder.exactFinalLineToGrsConversion ∧
    decoder.multiplicityThreeGuruswamiSudanApplicable

#print axioms exact_decoder_parameters
#print axioms initial_close_iff_published_strict
#print axioms final_close_iff_published_strict
#print axioms decodeBoth_has_exact_caps
#print axioms initial_close_candidate_mem_decodeBoth
#print axioms final_close_candidate_mem_decodeBoth
#print axioms initial_output_at_most_100
#print axioms final_output_at_most_99

end AspisPool.AlgorithmicCircleDecoderV7
