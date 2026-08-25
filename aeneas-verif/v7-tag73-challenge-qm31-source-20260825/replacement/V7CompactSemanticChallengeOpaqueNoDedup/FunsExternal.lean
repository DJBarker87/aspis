import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7CompactSemanticChallengeOpaqueNoDedup.Types
import V7Tag73ChallengeQm31.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 50000

namespace V7CompactSemanticFullGenerated

/-- The ordinary `Result.map_err` body from the original generated external
file. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type}
  (opsfunctionFnOnceOTupleEFInst : core.ops.function.FnOnce O E F) :
  (core.result.Result T E) → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, state => do
      let mapped ← opsfunctionFnOnceOTupleEFInst.call_once state error
      ok (.Err mapped)

/-- Give the source-generated sampler the compact extraction's hash callback.
Aeneas makes function calls explicit in its outer `Result`; the deployed hash
callback itself is total. -/
def transcript.Transcript.toChallengeSource
    (self : transcript.Transcript) :
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript :=
  { state := self.state
    hash := fun input => ok (self.hash input) }

def field.CM31.ofChallengeSource
    (value : V7Tag73ChallengeQm31Generated.aspis_core.field.CM31) : field.CM31 :=
  { a := value.a, b := value.b }

def field.QM31.ofChallengeSource
    (value : V7Tag73ChallengeQm31Generated.aspis_core.field.QM31) : field.QM31 :=
  { c0 := field.CM31.ofChallengeSource value.c0
    c1 := field.CM31.ofChallengeSource value.c1 }

def transcript.challengeResultOfSource :
    core.result.Result V7Tag73ChallengeQm31Generated.aspis_core.field.QM31
        V7Tag73ChallengeQm31Generated.aspis_core.transcript.ChallengeSampleExhausted →
      core.result.Result field.QM31 transcript.ChallengeSampleExhausted
  | .Ok value => .Ok (field.QM31.ofChallengeSource value)
  | .Err _ => .Err ()

/-- Concrete replacement for the sole opaque callback in the compact
semantic extraction.  Its body calls the transparent Charon/Aeneas extraction
of the unchanged deployed method and converts only the duplicate generated
record namespaces. -/
def transcript.Transcript.challenge_qm31
    (self : transcript.Transcript) :
    Result ((core.result.Result field.QM31
      transcript.ChallengeSampleExhausted) × transcript.Transcript) := do
  let (sample, sourceTranscript) ←
    V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31
      self.toChallengeSource
  ok
    (transcript.challengeResultOfSource sample,
      { self with state := sourceTranscript.state })

theorem transcript.Transcript.challenge_qm31_is_source_generated
    (self : transcript.Transcript) :
    self.challenge_qm31 = (do
      let (sample, sourceTranscript) ←
        V7Tag73ChallengeQm31Generated.aspis_core.transcript.Transcript.challenge_qm31
          self.toChallengeSource
      ok
        (transcript.challengeResultOfSource sample,
          { self with state := sourceTranscript.state })) := rfl

#print axioms transcript.Transcript.challenge_qm31_is_source_generated

end V7CompactSemanticFullGenerated
