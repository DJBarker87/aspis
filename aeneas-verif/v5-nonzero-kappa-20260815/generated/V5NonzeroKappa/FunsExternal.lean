import Aeneas.Std
import V5NonzeroKappa.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V5NonzeroKappaGenerated

namespace V5NonzeroKappaGenerated

def field.QM31.ofRaw (a b c d : Std.U32) : field.QM31 :=
  { c0 := { a, b }, c1 := { a := c, b := d } }

/-- Total arbitrary-result interpretation of the opaque lower-level sampler.
Every list head is consumed exactly once; an empty list is an exhaustion. -/
def transcript.Transcript.challenge_qm31
    (self : transcript.Transcript) :
    Result ((core.result.Result field.QM31
      transcript.ChallengeSampleExhausted) × transcript.Transcript) :=
  match self with
  | [] => ok (core.result.Result.Err (), [])
  | transcript.RawChallenge.exhausted :: tail =>
      ok (core.result.Result.Err (), tail)
  | transcript.RawChallenge.value a b c d :: tail =>
      ok (core.result.Result.Ok (field.QM31.ofRaw a b c d), tail)

end V5NonzeroKappaGenerated
