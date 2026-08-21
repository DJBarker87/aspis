import Aeneas.Std
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5ZeroUnchangedGenerated

/-- Transcript calls visible in the unchanged zerocheck helper. -/
inductive ZeroTranscriptEvent where
  | absorb (label : Std.U8) (payload : List Std.U8)
  | squeeze
  deriving DecidableEq, Repr

/-- Field values are erased in this event-only source projection.  Challenge
value forwarding is checked by the unchanged outer-prefix extraction. -/
@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Unit

/-- Event log for the successful transcript projection. -/
@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  events : List ZeroTranscriptEvent
  deriving DecidableEq, Repr

end V5ZeroUnchangedGenerated
