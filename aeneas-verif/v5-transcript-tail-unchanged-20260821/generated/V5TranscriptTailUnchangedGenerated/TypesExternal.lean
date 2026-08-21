import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace V5TranscriptTailUnchangedGenerated

@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Std.Usize

/-- Calls made by the extracted transcript tail.  This is an observation type,
not a replacement implementation of the production transcript. -/
inductive TailTranscriptEvent where
  | absorb (label : Std.U8) (payload : List Std.U8)
  | finalNonce (nonce : Std.U64)
  | querySample
      (count : Std.Usize) (bound : Std.U32) (drawLimit : Std.Usize)
  deriving DecidableEq

/-- Observation state for the opaque transcript implementation.  The generated
tail must return exactly this query vector after converting it to an array,
and every transcript-affecting external call appends one event. -/
@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  sampledQueries : alloc.vec.Vec Std.U32
  events : List TailTranscriptEvent

@[reducible, rust_type
  "aspis_v5_prefix_program_helpers_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots"]
def v5_cu_probe.private_openings.V5PrivateOpeningRoots := Unit

end V5TranscriptTailUnchangedGenerated
