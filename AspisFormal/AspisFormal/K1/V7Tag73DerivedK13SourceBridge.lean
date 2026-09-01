import AspisFormal.K1.V7Tag73CanonicalOneFoldScheduleUniqueness
import AspisFormal.K1.V7Tag73DerivedK13View

/-!
# Exact parsed-view bridge to the verifier-derived K1.3 view

`ExactParsedProofSourceBinding` is the explicit production/Aeneas boundary
which ties parser output to operational challenges, fixed field decoding, and
the literal selected q16 schedule.  The only apparently extra datum is its
total inverse-table condition.  The uniqueness theorem proves those equations
are precisely enough to identify the parsed schedule with the canonical
verifier-derived schedule.

This file makes that conditional equality available without deriving it from
the raw checked-return interface (which is deliberately too weak).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73DerivedK13SourceBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73CanonicalOneFoldScheduleUniqueness
open AspisK1.V7Tag73DerivedK13View
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The source binding's alpha and inverse equations identify the opaque
parsed schedule with the canonical total schedule constructed by the
verifier-derived view. -/
theorem exact_parsed_schedule_eq_canonical_of_source_binding
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
    (exactK13ParsedProof input).schedule =
      canonicalOneFoldSchedule
        (exactOperationalChallenge input (.alpha 0)) := by
  calc
    (exactK13ParsedProof input).schedule =
        canonicalOneFoldSchedule (exactK13ParsedProof input).schedule.alpha :=
      exact_one_fold_schedule_eq_canonical _ binding.inverseTablesExact
    _ = canonicalOneFoldSchedule
        (exactOperationalChallenge input (.alpha 0)) := by
      rw [binding.alphaZeroExact]

/-- With the explicit source binding in hand, the legacy parsed K1.3 object
is exactly the verifier-derived view with its own authenticated openings.
No raw-parser opacity is hidden: the binding remains a visible premise. -/
theorem exact_parsed_proof_eq_derived_k13_view_of_source_binding
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
    exactK13ParsedProof input =
      derivedK13View input decoded (exactK13ParsedProof input).openings := by
  have gammaExact := binding.gammaExact
  have finalExact := binding.disclosedFinalExact
  have scheduleExact :=
    exact_parsed_schedule_eq_canonical_of_source_binding binding
  have queriesExact := binding.selectedQueriesExact
  cases proofExact : exactK13ParsedProof input with
  | mk openings gamma disclosedFinal schedule queries =>
      simp only [proofExact] at gammaExact finalExact scheduleExact queriesExact ⊢
      cases gammaExact
      cases finalExact
      cases scheduleExact
      cases queriesExact
      rfl

#print axioms exact_parsed_schedule_eq_canonical_of_source_binding
#print axioms exact_parsed_proof_eq_derived_k13_view_of_source_binding

end

end AspisK1.V7Tag73DerivedK13SourceBridge
