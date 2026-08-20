import Aeneas.Std
import V5TranscriptTailGenerated.TypesExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace V5TranscriptSelectedWrapperGenerated

/-- The outer-wrapper extraction observes the same field values as the
already-proved transcript-tail extraction. -/
@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 :=
  V5TranscriptTailGenerated.aspis_core.field.QM31

/-- Reuse the transcript-tail observation state.  This lets the generated
outer wrapper call the already-proved lower generated function directly. -/
@[reducible, rust_type "aspis_core::transcript::Transcript"]
def aspis_core.transcript.Transcript :=
  V5TranscriptTailGenerated.aspis_core.transcript.Transcript

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots"]
def v5_cu_probe.private_openings.V5PrivateOpeningRoots := Unit

end V5TranscriptSelectedWrapperGenerated
