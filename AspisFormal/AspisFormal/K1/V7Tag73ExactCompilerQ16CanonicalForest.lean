import AspisFormal.K1.V7Tag73ExactCompilerQ16ForestHandoff

/-!
# Canonical exact-compiler q16 output forest

The accepted source evaluator exposes the literal decoder prefix consumed at
every counter through the selected counter.  This module embeds those finite
prefixes in the fixed `64 × 8` q16 output rectangle, padding only coordinates
that the production decoder did not read.

Consequently the routed-byte premise disappears for the canonical accepted
output forest.  The remaining source boundary is solely the authenticated
frontier recurrence; no probability or random-oracle conclusion is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerQ16CanonicalForest

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73ExactCompilerQ16ForestHandoff

noncomputable section

/-- Fixed output rectangle obtained by embedding every literal consumed
decoder prefix and assigning zero only to unread suffix coordinates. -/
def exactOperationalQ16OutputForest
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Q16CandidateDigestForest := fun counter block =>
  let blocks := exactOperationalQ16CandidateBlocks input counter
  if inPrefix : block.val < blocks.length then
    blocks[block.val]
  else
    zeroBytes 32

theorem exact_operational_q16_output_forest_consumed_exact
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
    (counter : Fin 64) (index : Nat)
    (inBlocks : index <
      (exactOperationalQ16CandidateBlocks input counter).length)
    (indexCap : index < 8) :
    (exactOperationalQ16CandidateBlocks input counter)[index] =
      exactOperationalQ16OutputForest input counter ⟨index, indexCap⟩ := by
  simp [exactOperationalQ16OutputForest, inBlocks]

/-- The literal accepted source prefixes form a successful first-cap-203
forest.  Only the exact operational-to-semantic frontier equality remains as
an argument. -/
theorem exact_operational_q16_output_forest_succeeds
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
    (frontierExact : ∀ counter schedule,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      (exactOperationalTape input).search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        (exactOperationalTape input).frontierNodes schedule) :
    q16DigestForestSucceeds (exactOperationalQ16OutputForest input) := by
  apply exact_operational_q16_pointwise_implies_successful_forest input
    (exactOperationalQ16OutputForest input)
  · intro counter beforeSelected index inBlocks
    apply exact_operational_q16_output_forest_consumed_exact input counter index
      inBlocks
  · exact frontierExact

#print axioms exactOperationalQ16OutputForest
#print axioms exact_operational_q16_output_forest_consumed_exact
#print axioms exact_operational_q16_output_forest_succeeds

end

end AspisK1.V7Tag73ExactCompilerQ16CanonicalForest
