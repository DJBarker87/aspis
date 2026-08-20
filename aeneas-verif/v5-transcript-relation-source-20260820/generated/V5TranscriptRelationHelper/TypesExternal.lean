import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace V5TranscriptRelationGenerated

/-- Transcript-affecting calls observed through the opaque production
helpers.  Field values are deliberately erased: this extraction checks call
order and indices, not field arithmetic or hash security. -/
inductive RelationTranscriptEvent where
  | secureCirclePoint
  | lineOodPoint
  | absorbOod (label round sample : Nat)
  | squeezeQm31
  | relationSumcheck (round : Nat)
  | foldWork (round : Nat) (nonce : Nat)
  | laterRoot (round : Nat)
  deriving DecidableEq, Repr

@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Unit

@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  events : List RelationTranscriptEvent
  deriving DecidableEq, Repr

end V5TranscriptRelationGenerated
