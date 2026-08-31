import AspisFormal.K1.V7Tag73DerivedK13View
import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff
import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity
import AspisFormal.V6OneFoldCandidateExtraction

/-!
# Verifier-derived K1.3 q16 bad-set handoff

The legacy fixed-root K1.3 q16 accounting factors a consistency set through
the opaque parsed proof.  That is too broad for a state-restoring q16 replay:
the parser result may legitimately differ on a challenge-dependent
continuation.  The deployed verifier does not, however, obtain K1.3's gamma,
round-zero alpha, or selected query positions from that opaque result.

This leaf isolates the smaller object actually needed by the q16 theorem.  It
is determined by the authenticated K1.2 words, canonically decoded fixed
fields, and verifier-owned pre-q16 challenges.  q16 itself supplies only the
selected schedule.  No probability assertion or source-causality premise is
introduced here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73DerivedK13Q16Handoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73DerivedK13View
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The complete pre-q16 semantic input to the fixed K1.3 query bad set.
The q16-selected positions themselves are deliberately absent. -/
structure DerivedK13Q16BadProfile where
  words : ExtractedWords
  decoded : Fin 641 → QM31Exact
  gamma : QM31Exact
  alphaZero : QM31Exact

/-- The finite set of query positions inconsistent with one verifier-derived
K1.3 profile.  It depends on no selected q16 position. -/
def DerivedK13Q16BadProfile.bad
    (decoder : ExactDecoderInstantiation QM31Exact)
    (profile : DerivedK13Q16BadProfile) : Finset (Fin 262144) :=
  consistencySet (canonicalOneFoldSchedule profile.alphaZero)
    (decoderCodeEncoders decoder)
    (extractedIdealTranscript profile.words profile.gamma
      (decodedFinalMessage profile.decoded))

/-- Build the q16 bad-set profile from the literal operational state and a
K1.2 certificate.  The selected q16 schedule stays outside the profile. -/
def derivedK13Q16BadProfileOf
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact) : DerivedK13Q16BadProfile where
  words := k12.words
  decoded := decoded
  gamma := exactOperationalChallenge input .gamma
  alphaZero := exactOperationalChallenge input (.alpha 0)

/-- Equality of the four genuine pre-q16 profile components is sufficient for
equality of the complete 9,557-position consistency set. -/
theorem derived_k13_q16_bad_congr
    (decoder : ExactDecoderInstantiation QM31Exact)
    (left right : DerivedK13Q16BadProfile)
    (wordsExact : left.words = right.words)
    (decodedExact : left.decoded = right.decoded)
    (gammaExact : left.gamma = right.gamma)
    (alphaExact : left.alphaZero = right.alphaZero) :
    DerivedK13Q16BadProfile.bad decoder left =
      DerivedK13Q16BadProfile.bad decoder right := by
  cases left
  cases right
  simp_all only [DerivedK13Q16BadProfile.bad]

/-- A query-phase failure in the verifier-derived view makes the literal
first-cap-203 operational schedule land in its pre-q16 bad set.  This no
longer needs an equality premise about an opaque parser-owned query vector. -/
theorem derived_query_phase_failure_is_literal_selected_all_in_bad
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
    (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof)
    (failure : QueryPhaseFailure
      (derivedK13View input decoded openings).schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript k12.words
        (derivedK13View input decoded openings).gamma
        (derivedK13View input decoded openings).disclosedFinal)
      (derivedK13View input decoded openings).queries) :
    AllInBad (DerivedK13Q16BadProfile.bad decoder
      (derivedK13Q16BadProfileOf input k12 decoded))
      (exactOperationalTape input).search.selectedSchedule.positions := by
  intro ordinal
  have accepted := accepted_queries_mem_consistencySet
    (derivedK13View input decoded openings).schedule
    (decoderCodeEncoders decoder)
    (extractedIdealTranscript k12.words
      (derivedK13View input decoded openings).gamma
      (derivedK13View input decoded openings).disclosedFinal)
    (derivedK13View input decoded openings).queries failure.1 ordinal
  simpa only [derivedK13Q16BadProfileOf, DerivedK13Q16BadProfile.bad,
    derivedK13View] using accepted

/-- The same classifier certificate gives the exact deployed list-decoding
cardinality cap for the verifier-derived q16 bad set. -/
theorem derived_query_phase_failure_bad_card
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
    (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof)
    (failure : QueryPhaseFailure
      (derivedK13View input decoded openings).schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript k12.words
        (derivedK13View input decoded openings).gamma
        (derivedK13View input decoded openings).disclosedFinal)
      (derivedK13View input decoded openings).queries) :
    (DerivedK13Q16BadProfile.bad decoder
      (derivedK13Q16BadProfileOf input k12 decoded)).card ≤ 9557 := by
  simpa only [derivedK13Q16BadProfileOf, DerivedK13Q16BadProfile.bad,
    derivedK13View] using failure.2

/-- Package the exact bad-set and literal selected-schedule facts consumed by
the semantic q16 forest theorem. -/
theorem derived_query_phase_failure_exposes_literal_q16_bad_set
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
    (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof)
    (failure : QueryPhaseFailure
      (derivedK13View input decoded openings).schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript k12.words
        (derivedK13View input decoded openings).gamma
        (derivedK13View input decoded openings).disclosedFinal)
      (derivedK13View input decoded openings).queries) :
    ∃ bad : Finset (Fin 262144), bad.card ≤ 9557 ∧
      AllInBad bad
        (exactOperationalTape input).search.selectedSchedule.positions := by
  exact ⟨DerivedK13Q16BadProfile.bad decoder
      (derivedK13Q16BadProfileOf input k12 decoded),
    derived_query_phase_failure_bad_card decoded openings failure,
    derived_query_phase_failure_is_literal_selected_all_in_bad decoded openings
      failure⟩

#print axioms derived_k13_q16_bad_congr
#print axioms derived_query_phase_failure_is_literal_selected_all_in_bad
#print axioms derived_query_phase_failure_bad_card
#print axioms derived_query_phase_failure_exposes_literal_q16_bad_set

end

end AspisK1.V7Tag73DerivedK13Q16Handoff
