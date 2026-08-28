import AspisFormal.K1.V7Tag73CounterfactualReplayProofFilter
import AspisFormal.K1.V7Tag73SchedulerNativeGammaReplay

/-!
# Parsed-proof families from scheduler-native gamma replay

The scheduler-native counterfactual driver returns a complete result-carrying
scheduler run.  This module projects a parsed proof only from a literal normal
return whose embedded gamma equals the value supplied to the replay.  Abort,
exhaustion, malformed, and wrong-gamma branches are represented by `none`.

Thus the proof family and its all-gamma coherence theorem are constructed from
one executable replay function.  Neither a completed execution context nor an
opaque provider equality is accepted as input.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeReplayProofFilter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Expose a parsed proof only from a returned scheduler result with the
literal counterfactual gamma recorded in the raw proof. -/
def schedulerNativeResponseProofAtGamma?
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (SchedulerNativeGammaResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload))) : Option Tag73K12ParsedProof :=
  match result with
  | .error _ => none
  | .ok response =>
      match response.run.terminal with
      | .failed _ => none
      | .returned value =>
          let proof := value.1.publicProof.proof.rawProof
          if proof.gamma = gamma then some proof else none

/-- The executable scheduler filter never exposes a proof under a different
gamma. -/
theorem schedulerNativeResponseProofAtGamma_gammaExact
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (SchedulerNativeGammaResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)))
    (proof : Tag73K12ParsedProof)
    (proofExact : schedulerNativeResponseProofAtGamma? gamma result =
      some proof) :
    proof.gamma = gamma := by
  cases result with
  | error failure =>
      simp [schedulerNativeResponseProofAtGamma?] at proofExact
  | ok response =>
      cases terminalExact : response.run.terminal with
      | failed reason =>
          simp [schedulerNativeResponseProofAtGamma?, terminalExact]
            at proofExact
      | returned value =>
          simp only [schedulerNativeResponseProofAtGamma?, terminalExact]
            at proofExact
          split at proofExact
          next gammaExact =>
            exact Option.some.inj proofExact ▸ gammaExact
          next gammaMismatch => simp at proofExact

/-- A literal returned scheduler value with matching gamma is selected by the
filter. -/
theorem schedulerNativeResponseProofAtGamma_of_returned
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (SchedulerNativeGammaResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)))
    (response : SchedulerNativeGammaResponse
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (resultExact : result = .ok response)
    (returned : response.run.terminal = .returned value)
    (gammaExact : value.1.publicProof.proof.rawProof.gamma = gamma) :
    schedulerNativeResponseProofAtGamma? gamma result =
      some value.1.publicProof.proof.rawProof := by
  simp [schedulerNativeResponseProofAtGamma?, resultExact, returned,
    gammaExact]

/-- Construct the complete routed parsed-proof oracle directly from one
scheduler-native replay family. -/
def routedCounterfactualParsedK13OracleOfSchedulerReplay
    {Failure Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      Except Failure
        (SchedulerNativeGammaResponse
          (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
            Payload))) : RoutedCounterfactualParsedK13Oracle where
  proof? := fun sample =>
    schedulerNativeResponseProofAtGamma?
      (routedSuccessfulGammaValue sample).1 (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact schedulerNativeResponseProofAtGamma_gammaExact
      (routedSuccessfulGammaValue sample).1 (replay sample) proof proofExact

/-- Selected-branch equality follows from the literal scheduler return and
parser gamma equality; it is not a provider premise. -/
theorem routed_scheduler_replay_provider_actual_proof
    {Failure Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      Except Failure
        (SchedulerNativeGammaResponse
          (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
            Payload)))
    (sample : RoutedSuccessfulGammaTape)
    (response : SchedulerNativeGammaResponse
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (resultExact : replay sample = .ok response)
    (returned : response.run.terminal = .returned value)
    (gammaExact : value.1.publicProof.proof.rawProof.gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedCounterfactualParsedK13OracleOfSchedulerReplay replay).proof?
        sample = some value.1.publicProof.proof.rawProof := by
  exact schedulerNativeResponseProofAtGamma_of_returned
    (routedSuccessfulGammaValue sample).1 (replay sample) response value
      resultExact returned gammaExact

#print axioms schedulerNativeResponseProofAtGamma_gammaExact
#print axioms schedulerNativeResponseProofAtGamma_of_returned
#print axioms routedCounterfactualParsedK13OracleOfSchedulerReplay
#print axioms routed_scheduler_replay_provider_actual_proof

end

end AspisK1.V7Tag73SchedulerNativeReplayProofFilter
