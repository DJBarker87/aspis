import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace V5TranscriptTailGenerated

@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Std.Usize

/-- Observation state for the opaque transcript implementation.  The generated
tail must return exactly this query vector after converting it to an array. -/
@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  sampledQueries : alloc.vec.Vec Std.U32

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots"]
def v5_cu_probe.private_openings.V5PrivateOpeningRoots := Unit

end V5TranscriptTailGenerated
