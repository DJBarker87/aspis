import Aeneas.Std
import V5TranscriptSelectedWrapperGenerated.Types
import V5TranscriptTailGenerated.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace V5TranscriptSelectedWrapperGenerated

def core.option.Option.ok_or
    {T E : Type} : Option T → E → Result (core.result.Result T E)
  | .some value, _ => ok (.Ok value)
  | .none, error => ok (.Err error)

def aspis_core.transcript.Transcript.Insts.CoreCloneClone.clone
    (transcript : aspis_core.transcript.Transcript) :
    Result aspis_core.transcript.Transcript :=
  ok transcript

/-- Field-for-field conversion between the independently generated outer and
tail parser records.  Both records were extracted from the same Rust
`ParsedProbeData` declaration. -/
def toTailParsed (parsed : v5_cu_probe.ParsedProbeData) :
    V5TranscriptTailGenerated.v5_cu_probe.ParsedProbeData := {
  gamma := parsed.gamma
  production_c1 := parsed.production_c1
  candidate_c1 := parsed.candidate_c1
  c2 := parsed.c2
  relation_scales := parsed.relation_scales
  relation_points := parsed.relation_points
  relation_claims := parsed.relation_claims
  relation_alphas := parsed.relation_alphas
  relation_final := parsed.relation_final
  v5_fold_nonces := parsed.v5_fold_nonces
  v5_batch_nonce := parsed.v5_batch_nonce
  v5_wire_prefix := parsed.v5_wire_prefix
  v5_atomic_terminal_context := parsed.v5_atomic_terminal_context
  v5_private_roots := parsed.v5_private_roots
  v5_final_coefficients := parsed.v5_final_coefficients
  v5_relation_stress := parsed.v5_relation_stress
  v5_final_nonce := parsed.v5_final_nonce
  v5_query_selector := parsed.v5_query_selector
  v5_private_proof := parsed.v5_private_proof
}

/-- The formerly opaque lower call is interpreted by the checked generated
tail definition, rather than by a new model. -/
def v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData) (selector : Std.U8) :
    Result (core.result.Result
      ((Array aspis_core.field.QM31 4#usize) × (Array Std.U32 18#usize))
      solana_program_error.ProgramError) :=
  V5TranscriptTailGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
      transcript (toTailParsed parsed) selector

/-- A small observation predicate for the opaque production GoodA/GoodB
helper.  It is deliberately not a cryptographic model of that helper: the
wrapper proof uses it only to show that the exact returned query array is the
array passed to the goodness check. -/
def candidateObservation
    (point : Array aspis_core.field.QM31 10#usize)
    (queries : Array Std.U32 18#usize) : Bool :=
  point.val.head?.map (fun value => value.val) ==
    queries.val.head?.map (fun value => value.val)

def v5_cu_probe.good_gate_probe.candidate_is_good
    (point : Array aspis_core.field.QM31 10#usize)
    (queries : Array Std.U32 18#usize) : Result (Option Bool) :=
  ok (.some (candidateObservation point queries))

end V5TranscriptSelectedWrapperGenerated
