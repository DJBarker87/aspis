import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace V5NonzeroKappaGenerated

/-- One arbitrary result of the lower-level `challenge_qm31` call.  The
four words cover every generated `QM31` representation; `exhausted` covers
the propagated error. -/
inductive transcript.RawChallenge where
  | value (a b c d : Std.U32)
  | exhausted
  deriving Repr, DecidableEq

/-- An arbitrary stream of lower-level sampler results.  This replaces only
the opaque transcript type in the extraction proof; it makes no hash or
uniformity claim. -/
@[reducible]
def transcript.Transcript := List transcript.RawChallenge

end V5NonzeroKappaGenerated
