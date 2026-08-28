import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates

/-!
# Source-selected proof bridge at the constructed pre-gamma pause

The exact compiler now constructs one routed successful gamma sample and its
first scheduler pause from the same source execution.  This module uses that
single witness to remove the formerly separate operational-gamma equality
from the parsed-oracle selected-branch theorem.

The remaining implication hypotheses are the literal continuation replay and
normal returned-terminal equalities.  They are kept visible because the
fresh-only scheduler currently does not represent cached advance queries.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerPreGammaSelectedBinding

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- The exact source execution supplies the routed gamma witness, its literal
first-output pause, and the operational-gamma equality.  Consequently a
successful actual continuation is selected by the one whole pre-fixed parsed
oracle without accepting another gamma-coordinate premise. -/
theorem exact_compiler_constructs_pre_gamma_selected_proof_bridge
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    {decoded : Fin 641 → AspisV5ComponentCQM31TowerExact.QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (gammaOutputInput initialDigest)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
          .paused pause ∧
      ∀ (response : SchedulerNativeGammaResponse
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result))
        (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload Result),
        exactCompilerRoutedGammaReplay input initialDigest
            (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response →
        response.run.terminal =
            .returned (.completed (exactK12Runtime input) clientRun) →
        (exactCompilerRoutedParsedOracle input initialDigest).proof?
            (successfulGammaPrefixFlatRoutingEquiv flat) =
          some (exactK13ParsedProof input) := by
  obtain ⟨initialDigest, flat, pause, gammaExact, paused⟩ :=
    exact_compiler_constructs_routed_gamma_with_first_pause input
  refine ⟨initialDigest, flat, pause, gammaExact, paused, ?_⟩
  intro response clientRun replayExact returned
  exact exact_compiler_routed_parsed_oracle_actual_proof_of_source input source
    initialDigest (successfulGammaPrefixFlatRoutingEquiv flat) response
    clientRun replayExact returned gammaExact

#print axioms exact_compiler_constructs_pre_gamma_selected_proof_bridge

end

end AspisK1.V7Tag73ExactCompilerPreGammaSelectedBinding
