import AspisFormal.K1.V7Tag73OperationalSemanticReplay
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding

/-!
# Exact source binding for the Tag-73 K1.3/K1.4 proof view

The fixed-run compiler obtains prover bytes, verifier-derived challenges and
the first compact q16 schedule through different typed paths.  The K1.3/K1.4
classifier deliberately stores the downstream values in one small parsed
view.  This module states the exact, data-only equality certificate that the
accepted production Rust/Aeneas bridge must construct:

* parsed `gamma` is the gamma decoded by the literal operational transcript;
* the one-fold `alpha` is the operational round-zero alpha;
* the disclosed final vector is the canonical decoding of the 256 prover
  field encodings; and
* the query injection is the positions of the literal first-cap-203 selected
  q16 branch.

The inverse-table equations are included because they are fixed public
parameter/source facts needed by the one-fold algebraic reduction.  No
acceptance, extraction, witness or probability conclusion is a field of this
certificate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactParsedProofSourceBinding

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6AcceptedPathObligations

noncomputable section

/-- The exact operational challenge decoded from the accepted Tag-73
transcript.  This is a projection of the fixed tape, not a new challenge
source. -/
def exactOperationalChallenge
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (id : ChallengeId) : QM31Exact :=
  exactChallengeValue
    (exactOperationalTape input).messages.challengeValue id

/-- Canonical mathematical final-256 view of the exact fixed-field decoder
output. -/
def decodedFinalMessage (decoded : Fin 641 → QM31Exact) :
    FinalMessage QM31Exact :=
  fun coefficient => (decodedFixedFieldView decoded).finalCoefficient coefficient

/-- Data-only boundary between literal production parsing and the already
proved operational/K1.3 objects.  A source bridge must construct this record
from the translated successful caller. -/
structure ExactParsedProofSourceBinding
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
    (decoded : Fin 641 → QM31Exact) : Prop where
  gammaExact :
    (exactK13ParsedProof input).gamma = exactOperationalChallenge input .gamma
  alphaZeroExact :
    (exactK13ParsedProof input).schedule.alpha =
      exactOperationalChallenge input (.alpha 0)
  disclosedFinalExact :
    (exactK13ParsedProof input).disclosedFinal = decodedFinalMessage decoded
  selectedQueriesExact :
    (exactK13ParsedProof input).queries =
      (exactOperationalTape input).search.selectedSchedule.positions
  inverseTablesExact :
    ExactOneFoldInverseTables (exactK13ParsedProof input).schedule

theorem exact_parsed_gamma_ne_zero
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (binding : ExactParsedProofSourceBinding input decoded) :
    (exactK13ParsedProof input).gamma ≠ 0 := by
  rw [binding.gammaExact]
  exact (exact_operational_input_constructs_post_eta_nonzero_challenges input).1

theorem exact_parsed_disclosed_final_coefficient
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (binding : ExactParsedProofSourceBinding input decoded)
    (coefficient : Fin 256) :
    (exactK13ParsedProof input).disclosedFinal coefficient =
      (decodedFixedFieldView decoded).finalCoefficient coefficient := by
  rw [binding.disclosedFinalExact]
  rfl

theorem exact_parsed_selected_query
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (binding : ExactParsedProofSourceBinding input decoded)
    (query : Fin 16) :
    (exactK13ParsedProof input).queries query =
      (exactOperationalTape input).search.selectedSchedule.positions query := by
  rw [binding.selectedQueriesExact]

theorem exact_parsed_alpha_zero
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (binding : ExactParsedProofSourceBinding input decoded) :
    (exactK13ParsedProof input).schedule.alpha =
      exactOperationalChallenge input (.alpha 0) :=
  binding.alphaZeroExact

theorem exact_parsed_onefold_inverse_tables
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (binding : ExactParsedProofSourceBinding input decoded) :
    ExactOneFoldInverseTables (exactK13ParsedProof input).schedule :=
  binding.inverseTablesExact

#print axioms exact_parsed_gamma_ne_zero
#print axioms exact_parsed_disclosed_final_coefficient
#print axioms exact_parsed_selected_query
#print axioms exact_parsed_alpha_zero
#print axioms exact_parsed_onefold_inverse_tables

end

end AspisK1.V7Tag73ExactParsedProofSourceBinding
