import AspisFormal.K1.V7Tag73ExactCompilerSchedulerPauseBinding
import AspisFormal.K1.V7Tag73SchedulerNativeReplayProofFilter

/-!
# Exact compiler parsed-proof projection from scheduler-native replay

The native exact-compiler scheduler returns a
`SchedulerNativePlainRomResult`.  On its completed branch the root runtime
contains the literal checked raw adversary value used by `exactK13ParsedProof`.
This module filters that concrete result directly, rather than accepting an
opaque parsed-proof provider.

The selected-branch theorem below reduces the requested provider equality to
the executable replay result and the literal sampled-gamma equality.  The
proof value itself is definitionally the exact K1.3 parser projection.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerSchedulerReplayProof

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeReplayProofFilter
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Project the exact parsed proof from a normally completed compiler replay,
and expose it only when its embedded gamma is the supplied one. -/
def exactCompilerSchedulerResponseProofAtGamma?
    {Failure TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact)
    (replayResult : Except Failure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result))) : Option Tag73K12ParsedProof :=
  match replayResult with
  | .error _ => none
  | .ok response =>
      match response.run.terminal with
      | .failed _ => none
      | .returned (.initialFailure _) => none
      | .returned (.completed root _) =>
          let proof := root.adversaryValue.1.publicProof.proof.rawProof
          if proof.gamma = gamma then some proof else none

theorem exactCompilerSchedulerResponseProofAtGamma_gammaExact
    {Failure TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact)
    (replayResult : Except Failure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)))
    (proof : Tag73K12ParsedProof)
    (proofExact : exactCompilerSchedulerResponseProofAtGamma? gamma
      replayResult = some proof) :
    proof.gamma = gamma := by
  cases replayResult with
  | error failure =>
      simp [exactCompilerSchedulerResponseProofAtGamma?] at proofExact
  | ok response =>
      cases terminalExact : response.run.terminal with
      | failed reason =>
          simp [exactCompilerSchedulerResponseProofAtGamma?, terminalExact]
            at proofExact
      | returned result =>
          cases result with
          | initialFailure reason =>
              simp [exactCompilerSchedulerResponseProofAtGamma?, terminalExact]
                at proofExact
          | completed root clientRun =>
              simp only [exactCompilerSchedulerResponseProofAtGamma?,
                terminalExact] at proofExact
              split at proofExact
              next gammaExact =>
                exact Option.some.inj proofExact ▸ gammaExact
              next gammaMismatch => simp at proofExact

/-- Construct the routed proof oracle from the concrete exact-compiler
scheduler replay family. -/
def routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay
    {Failure TapeIdentity Statement Payload Result : Type}
    (replay : RoutedSuccessfulGammaTape → Except Failure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result))) :
    RoutedCounterfactualParsedK13Oracle where
  proof? := fun sample =>
    exactCompilerSchedulerResponseProofAtGamma?
      (routedSuccessfulGammaValue sample).1 (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact exactCompilerSchedulerResponseProofAtGamma_gammaExact
      (routedSuccessfulGammaValue sample).1 (replay sample) proof proofExact

/-- The key selected-coordinate equality.  Once native replay returns the
actual exact root runtime and the operational gamma equals the routed sample
value, the constructed oracle exposes `exactK13ParsedProof` definitionally. -/
theorem exact_compiler_scheduler_replay_provider_actual_proof
    {HiddenTape TapeIdentity Observation Statement Payload Result Failure : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (replay : RoutedSuccessfulGammaTape → Except Failure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)))
    (sample : RoutedSuccessfulGammaTape)
    (response : SchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (replayExact : replay sample = .ok response)
    (returned : response.run.terminal =
      .returned (.completed (exactK12Runtime input) clientRun))
    (gammaExact : (exactK13ParsedProof input).gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay replay).proof?
        sample = some (exactK13ParsedProof input) := by
  unfold routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay
  simp only
  rw [replayExact]
  simp only [exactCompilerSchedulerResponseProofAtGamma?]
  rw [returned]
  change (if (exactK13ParsedProof input).gamma =
      (routedSuccessfulGammaValue sample).1 then
        some (exactK13ParsedProof input) else none) =
    some (exactK13ParsedProof input)
  rw [if_pos gammaExact]

#print axioms exactCompilerSchedulerResponseProofAtGamma_gammaExact
#print axioms routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay
#print axioms exact_compiler_scheduler_replay_provider_actual_proof

end

end AspisK1.V7Tag73ExactCompilerSchedulerReplayProof
