import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5PrefixProgramHelpersGenerated

inductive ProgramTranscriptEvent where
  | absorb (label : Std.U8) (payload : List Std.U8)
  deriving DecidableEq, Repr

/-- Observation state for the three extracted program-local helpers.  The
work predicate represents the already proved `Transcript::grinding_ok`
result without changing transcript state. -/
@[rust_type "aspis_core::transcript::Transcript"]
structure aspis_core.transcript.Transcript where
  events : List ProgramTranscriptEvent
  workValid : Std.U64 → Std.U8 → Bool

end V5PrefixProgramHelpersGenerated
