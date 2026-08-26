import AspisFormal.K1.V7Tag73AcceptedSemanticExecution
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier

/-!
# Exact operational Tag-73 semantic replay

This file connects the literal successful scheduler/refinement input used by
K1.2 to the compact accepted semantic transcript consumed by K1.5.  The only
additional input is the exact decoding of the 641 fixed QM31 wire values; that
is a byte-layout/source-parser certificate, not an acceptance or soundness
premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalSemanticReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisV5ComponentCQM31TowerExact
open AspisV6AcceptedPathObligations

noncomputable section

def exactOperationalTape
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : DeployedFixedTape :=
  input.package.root.fixedRoot.base.tape

def exactOperationalRawTrace
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : InteractiveRawTrace :=
  input.package.root.fixedRoot.base.raw

def exactOperationalTable
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : FixedOracleTable :=
  fixedTableOfOracleState (exactK12Runtime input).verifierFinalOracle

/-- The strict checked refinement stored in the actual operational input
constructs the complete work-erased evaluator run used by semantic replay. -/
theorem exact_operational_input_constructs_complete_evaluator
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    Nonempty (CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input)) := by
  have checkedErased : checkedRefineWorkErased (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input) =
        some (exactOperationalRawTrace input) :=
    checked_refinement_success_survives_work_erasure
      (exactOperationalTable input) exactDeterministicDecoders
      (exactOperationalTape input) (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement
  have erased : refineWorkErased (exactOperationalTable input)
      (exactOperationalTape input) = some (exactOperationalRawTrace input) :=
    checked_refine_work_erased_forgets_check (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) checkedErased
  exact refine_work_erased_exposes_complete_evaluator_run
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) erased

/-- The literal checked refinement also supplies the final deterministic
decoder ledger needed to transport every challenge back to its causal round. -/
theorem exact_operational_input_final_samples_decode
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
    (evaluator : CompleteWorkErasedEvaluatorRun (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input)) :
    StateSamplesDecodeAs (exactOperationalTape input).messages
      evaluator.finalState := by
  have wellFormed : TraceWellFormed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) :=
    (checked_refinement_is_well_formed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement).2
  exact complete_evaluator_final_samples_decode (exactOperationalTable input)
    (exactOperationalTape input) (exactOperationalRawTrace input) wellFormed
    evaluator

/-- Exact end product of the operational-to-semantic bridge.  The transcript,
all ten round challenges, and the nonzero eta fact are derived from the actual
fixed-table run. -/
theorem exact_operational_input_constructs_compact_semantic_replay
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
    (decoded : Fin 641 -> QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded) :
    ExactCompactSemanticReplay
      (semanticPreEtaOf (exactOperationalTable input)
        (exactOperationalTape input).messages)
      (exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .eta)
      (decodedFixedFieldView decoded)
      (fun round => exactChallengeValue
        (exactOperationalTape input).messages.challengeValue
        (.semantic round)) := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input evaluator
  exact complete_evaluator_constructs_exactCompactSemanticReplay
    (exactOperationalTable input) (exactOperationalTape input)
    (exactOperationalRawTrace input) evaluator segments finalDecoded decoded
    fixedDecode

#print axioms exact_operational_input_constructs_complete_evaluator
#print axioms exact_operational_input_final_samples_decode
#print axioms exact_operational_input_constructs_compact_semantic_replay

end

end AspisK1.V7Tag73OperationalSemanticReplay
