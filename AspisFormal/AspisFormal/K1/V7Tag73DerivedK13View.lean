import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding

/-!
# Derived K1.3 view from prover wire data and operational state

This is the corrected data flow for the K1.3 classifier.  The prover/source
side supplies only the two-tree openings and the 641 canonically decoded fixed
fields.  Gamma, alpha zero, and q16 positions are verifier-derived operational
values; the total inverse tables are the canonical mathematical schedule.

The file deliberately does not assert that the existing opaque `rawProof`
equals this view.  That equality is false as a modelling principle: the Rust
wire parser does not return verifier-derived challenges.  Consumers should be
migrated to this derived view after the current-revision fixed-field parser
bridge supplies the decoded family.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73DerivedK13View

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The K1.3 proof view derived from the literal operational transcript.  Its
only parser-owned field is `openings`. -/
def derivedK13View
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
    (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) : Tag73K12ParsedProof :=
  { openings := openings
    gamma := exactOperationalChallenge input .gamma
    disclosedFinal := decodedFinalMessage decoded
    schedule := canonicalOneFoldSchedule
      (exactOperationalChallenge input (.alpha 0))
    queries := (exactOperationalTape input).search.selectedSchedule.positions }

@[simp] theorem derived_k13_view_openings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).openings = openings := by
  rfl

@[simp] theorem derived_k13_view_gamma
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).gamma =
      exactOperationalChallenge input .gamma := by
  rfl

@[simp] theorem derived_k13_view_disclosed_final
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).disclosedFinal =
      decodedFinalMessage decoded := by
  rfl

@[simp] theorem derived_k13_view_alpha_zero
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).schedule.alpha =
      exactOperationalChallenge input (.alpha 0) := by
  rfl

@[simp] theorem derived_k13_view_queries
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).queries =
      (exactOperationalTape input).search.selectedSchedule.positions := by
  rfl

theorem derived_k13_view_inverse_tables
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    ExactOneFoldInverseTables
      (derivedK13View input decoded openings).schedule := by
  exact canonical_one_fold_schedule_exact _

/-- All five verifier-derived K1.3 coordinates are obtained together from
one construction.  This is the semantic replacement for trying to bind the
opaque stored `rawProof` to fields that the production parser never returns. -/
theorem derived_k13_view_exact_fields
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (decoded : Fin 641 → QM31Exact)
    (openings : TwoTreeOpeningProof) :
    (derivedK13View input decoded openings).gamma =
        exactOperationalChallenge input .gamma ∧
      (derivedK13View input decoded openings).schedule.alpha =
        exactOperationalChallenge input (.alpha 0) ∧
      (derivedK13View input decoded openings).disclosedFinal =
        decodedFinalMessage decoded ∧
      (derivedK13View input decoded openings).queries =
        (exactOperationalTape input).search.selectedSchedule.positions ∧
      ExactOneFoldInverseTables
        (derivedK13View input decoded openings).schedule := by
  exact ⟨rfl, rfl, rfl, rfl, canonical_one_fold_schedule_exact _⟩

#print axioms derived_k13_view_openings
#print axioms derived_k13_view_gamma
#print axioms derived_k13_view_disclosed_final
#print axioms derived_k13_view_alpha_zero
#print axioms derived_k13_view_queries
#print axioms derived_k13_view_inverse_tables
#print axioms derived_k13_view_exact_fields

end

end AspisK1.V7Tag73DerivedK13View
