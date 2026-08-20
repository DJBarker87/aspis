import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5PrefixMaskHelperGenerated

/-- The byte-complete observation used for the extracted masked-sumcheck
helper.  It records only calls that can affect the transcript. -/
inductive MaskTranscriptEvent where
  | absorb (label : Std.U8) (payload : List Std.U8)
  | squeezeNonzero
  deriving DecidableEq, Repr

/-- For this source proof a field value is represented by its exact 16-byte
encoding.  The separate deployed decoder proof connects accepted wire bytes
to this representation. -/
@[reducible, rust_type "aspis_core::field::QM31"]
def aspis_core.field.QM31 := Array Std.U8 16#usize

/-- Transcript observation state.  `next` supplies the next nonzero challenge;
`none` represents sampler exhaustion. -/
@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  events : List MaskTranscriptEvent
  next : Option aspis_core.field.QM31

end V5PrefixMaskHelperGenerated
