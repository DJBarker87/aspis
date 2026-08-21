import Aeneas.Std
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5SemanticUnchangedGenerated

/-- Exact transcript-visible calls made by one accepted semantic-sumcheck
round.  Field arithmetic is intentionally outside this event projection. -/
inductive SemanticTranscriptEvent where
  | absorb (label : Std.U8) (payload : List Std.U8)
  | squeeze
  deriving DecidableEq, Repr

@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Unit

@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  events : List SemanticTranscriptEvent
  deriving DecidableEq, Repr

end V5SemanticUnchangedGenerated
