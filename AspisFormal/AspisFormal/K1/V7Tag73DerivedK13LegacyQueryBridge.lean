import AspisFormal.K1.V7Tag73DerivedK13Q16Handoff
import AspisFormal.K1.V7Tag73DerivedK13SourceBridge

/-!
# Legacy fixed K1.3 query failure through the verifier-derived view

This small adapter retains compatibility with the existing fixed K1.3 event
while the actual-law q16 argument migrates to the narrower derived profile.
Its premise is the already explicit parser/Aeneas source binding; it does not
claim that checked raw-return success alone determines parser fields.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73DerivedK13LegacyQueryBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DerivedK13Q16Handoff
open AspisK1.V7Tag73DerivedK13SourceBridge
open AspisK1.V7Tag73DerivedK13View
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The existing fixed classifier's q16 error is the same q16 error in the
verifier-derived view once the source binding has been established. -/
theorem exact_legacy_query_failure_is_derived_query_failure
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
    (binding : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (decoderCodeEncoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    QueryPhaseFailure (derivedK13View input decoded
      (exactK13ParsedProof input).openings).schedule
      (decoderCodeEncoders decoder)
      (extractedIdealTranscript k12.words
        (derivedK13View input decoded
          (exactK13ParsedProof input).openings).gamma
        (derivedK13View input decoded
          (exactK13ParsedProof input).openings).disclosedFinal)
      (derivedK13View input decoded
        (exactK13ParsedProof input).openings).queries := by
  have viewExact := exact_parsed_proof_eq_derived_k13_view_of_source_binding
    binding
  simpa only [exactK13Transcript, viewExact] using failure

/-- The legacy fixed K1.3 query event therefore exposes the same literal
first-cap-203 q16 schedule inside the narrower verifier-derived bad profile.
-/
theorem exact_legacy_query_failure_exposes_derived_q16_bad_set
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
    (binding : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (decoderCodeEncoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    ∃ bad : Finset (Fin 262144), bad.card ≤ 9557 ∧
      AllInBad bad
        (exactOperationalTape input).search.selectedSchedule.positions := by
  exact derived_query_phase_failure_exposes_literal_q16_bad_set decoded
    (exactK13ParsedProof input).openings
    (exact_legacy_query_failure_is_derived_query_failure binding failure)

#print axioms exact_legacy_query_failure_is_derived_query_failure
#print axioms exact_legacy_query_failure_exposes_derived_q16_bad_set

end

end AspisK1.V7Tag73DerivedK13LegacyQueryBridge
