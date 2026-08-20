import V5TranscriptSelectedWrapperGenerated.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5TranscriptSelectedWrapperGenerated

set_option maxRecDepth 3000

namespace AspisV5TranscriptSelectedWrapperProof

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

/-- Successful execution of the generated outer wrapper has only one path:
the serialized selector is in `0..2`, the already-proved lower transcript tail
succeeds for that exact selector, the returned query array passes the check,
and the same polynomial/query pair is returned unchanged. -/
theorem generated_selected_wrapper_success_exact
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (point : Array aspis_core.field.QM31 10#usize)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    parsed.v5_query_selector.val < 3 ∧
      V5TranscriptTailGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
            transcript (toTailParsed parsed) parsed.v5_query_selector =
        .ok (.Ok (polynomial, queries)) ∧
      candidateObservation point queries = true := by
  generalize htail :
    V5TranscriptTailGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript (toTailParsed parsed) parsed.v5_query_selector =
      tailResult
  unfold v5_cu_probe.derive_v5_selected_good_queries_from_transcript at success
  simp [v5_cu_probe.checked_v5_selected_good_candidate,
    v5_cu_probe.v5_query_selector_is_valid,
    v5_cu_probe.derive_v5_selected_good_queries_from_transcript.closure.Insts.CoreOpsFunctionFnMutTupleU8ResultPairArrayQM314ArrayU3218ProgramError.call_mut,
    v5_cu_probe.derive_v5_selected_good_queries_from_transcript.closure_1.Insts.CoreOpsFunctionFnMutPairU8SharedPairArrayQM314ArrayU3218ResultBoolProgramError.call_mut,
    aspis_core.transcript.Transcript.Insts.CoreCloneClone.clone,
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript,
    v5_cu_probe.good_gate_probe.candidate_is_good,
    core.option.Option.ok_or, htail] at success
  cases tailResult with
  | fail error =>
      by_cases hselector : parsed.v5_query_selector.val < 3 <;>
        simp_all
  | div =>
      by_cases hselector : parsed.v5_query_selector.val < 3 <;>
        simp_all
  | ok result =>
      cases result with
      | Err error =>
          by_cases hselector : parsed.v5_query_selector.val < 3 <;>
            simp_all
      | Ok output =>
          by_cases hselector : parsed.v5_query_selector.val < 3
          · by_cases hgood : candidateObservation point output.2 = true <;>
              simp_all
          · simp_all

#print axioms generated_selected_wrapper_success_exact

end AspisV5TranscriptSelectedWrapperProof
