import V7FirstCompactFrontierK13Integration

/-!
# First-cap-203 candidate return bridge

The production source exposes one loop-free candidate helper. Charon/Aeneas
therefore preserve the full five-field accepted schedule, while the outer loop
only selects the first helper result that is `some`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace V7FirstCompactCallerBridge

open V7FirstCompactSource
open V7FirstCompactFrontierK13Integration
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73Q16SemanticFrontierBridge

noncomputable section

/-- Successful literal operations preceding the production frontier helper. -/
structure CandidatePrefixRuns
    (inputTranscript cloned absorbed sampledTranscript : transcript.Transcript)
    (counterData : Slice Std.U8)
    (counter : Std.U8) (sampled : alloc.vec.Vec Std.U32)
    (schedule : QuerySchedule) : Prop where
  cloneRun :
    transcript.Transcript.Insts.CoreCloneClone.clone inputTranscript =
      .ok cloned
  sliceRun :
    lift (Array.to_slice (Array.make 1#usize [counter])) =
      (.ok counterData : Result (Slice Std.U8))
  absorbRun :
    transcript.Transcript.absorb cloned
        transcript.label.V7_QUERY_CANDIDATE counterData =
      .ok absorbed
  shiftRun :
    (1#u32 <<< 18#i32) = (.ok 262144#u32 : Result Std.U32)
  samplerRun :
    transcript.Transcript.challenge_queries_without_replacement absorbed
        16#usize 262144#u32 64#usize =
      .ok (.Ok sampled, sampledTranscript)
  arrayRun :
    Array.Insts.CoreConvertTryFromVecVec.try_from Global 16#usize sampled =
      .ok (.Ok (queryScheduleArray schedule))

private def returnedSchedule
    (schedule : QuerySchedule) (counter : Std.U8) (frontier : Std.Usize)
    (acceptedTranscript : transcript.Transcript) :
    v7_onefold.V7CompactQuerySchedule := {
  queries := queryScheduleArray schedule
  counter := counter
  frontier_nodes := frontier
  transcript_state := acceptedTranscript.state
  accepted_transcript := acceptedTranscript
}

/-- Exact generated continuation after the sampler has returned successfully.
Keeping this as a named stage avoids asking simplification to traverse the
preceding pair-destructuring and the complete frontier implementation at once. -/
private def candidateAfterSample
    (sampledTranscript : transcript.Transcript) (counter : Std.U8)
    (sampled : alloc.vec.Vec Std.U32) :
    Result (core.result.Result (Option v7_onefold.V7CompactQuerySchedule)
      v6_onefold.V6WireError) := do
  let r2 ←
    Array.Insts.CoreConvertTryFromVecVec.try_from Global 16#usize sampled
  let r3 ←
    core.result.Result.map_err
      v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError
      r2 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let r4 ← v6_onefold.binary_frontier_nodes val1 18#u8
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      if val2 ≤ v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE then
        let a ← transcript.Transcript.diagnostic_state sampledTranscript
        .ok (.Ok (some {
          queries := val1
          counter := counter
          frontier_nodes := val2
          transcript_state := a
          accepted_transcript := sampledTranscript
        }))
      else .ok (.Ok none)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Option v7_onefold.V7CompactQuerySchedule)
        (core.convert.FromSame v6_onefold.V6WireError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Option v7_onefold.V7CompactQuerySchedule)
      (core.convert.FromSame v6_onefold.V6WireError) residual

private theorem source_candidate_reduces
    (inputTranscript cloned absorbed sampledTranscript : transcript.Transcript)
    (counterData : Slice Std.U8)
    (counter : Std.U8) (sampled : alloc.vec.Vec Std.U32)
    (schedule : QuerySchedule)
    (runs : CandidatePrefixRuns inputTranscript cloned absorbed sampledTranscript
      counterData counter sampled schedule)
    (frontier : Std.Usize)
    (frontierRun :
      v6_onefold.binary_frontier_nodes (queryScheduleArray schedule) 18#u8 =
        .ok (.Ok frontier)) :
    v7_onefold.derive_v7_compact_candidate inputTranscript counter =
      if frontier ≤ v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE then
        .ok (.Ok (some (returnedSchedule schedule counter frontier
          sampledTranscript)))
      else .ok (.Ok none) := by
  unfold v7_onefold.derive_v7_compact_candidate
  rw [runs.cloneRun]
  simp only [bind_tc_ok]
  rw [runs.sliceRun]
  simp only [bind_tc_ok]
  rw [runs.absorbRun]
  simp only [bind_tc_ok]
  norm_num [v6_onefold.V6_QUERY_COUNT]
  rw [runs.shiftRun]
  simp only [bind_tc_ok]
  rw [runs.samplerRun]
  simp only [bind_tc_ok, core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    v7_onefold.derive_v7_compact_candidate.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorV6WireError.call_once]
  change candidateAfterSample sampledTranscript counter sampled = _
  unfold candidateAfterSample
  rw [runs.arrayRun]
  simp only [bind_tc_ok,
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError.call_once]
  rw [frontierRun]
  simp only [bind_tc_ok]
  simp [transcript.Transcript.diagnostic_state, returnedSchedule]

/-- Semantic cap admission makes the translated production candidate return
the exact queries, counter, frontier, state and accepted transcript. -/
theorem translated_candidate_returns_on_semantic_compact
    (inputTranscript cloned absorbed sampledTranscript : transcript.Transcript)
    (counterData : Slice Std.U8)
    (counter : Std.U8) (sampled : alloc.vec.Vec Std.U32)
    (schedule : QuerySchedule)
    (runs : CandidatePrefixRuns inputTranscript cloned absorbed sampledTranscript
      counterData counter sampled schedule)
    (admitted : SemanticCap203Admitted schedule.positions) :
    ∃ frontier,
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok (some (returnedSchedule schedule counter frontier
          sampledTranscript))) := by
  obtain ⟨frontier, frontierRun, compactIff⟩ :=
    translated_frontier_compact_iff_semantic schedule
  refine ⟨frontier, ?_⟩
  rw [source_candidate_reduces inputTranscript cloned absorbed sampledTranscript
    counterData counter sampled schedule runs frontier frontierRun]
  rw [if_pos (by
    simpa [v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE] using
      compactIff.mpr admitted)]

/-- A semantically non-admitted candidate returns `none`; it cannot be chosen
by the first-success outer loop. -/
theorem translated_candidate_skips_on_semantic_noncompact
    (inputTranscript cloned absorbed sampledTranscript : transcript.Transcript)
    (counterData : Slice Std.U8)
    (counter : Std.U8) (sampled : alloc.vec.Vec Std.U32)
    (schedule : QuerySchedule)
    (runs : CandidatePrefixRuns inputTranscript cloned absorbed sampledTranscript
      counterData counter sampled schedule)
    (noncompact : ¬ SemanticCap203Admitted schedule.positions) :
    v7_onefold.derive_v7_compact_candidate inputTranscript counter =
      .ok (.Ok none) := by
  obtain ⟨frontier, frontierRun, compactIff⟩ :=
    translated_frontier_compact_iff_semantic schedule
  rw [source_candidate_reduces inputTranscript cloned absorbed sampledTranscript
    counterData counter sampled schedule runs frontier frontierRun]
  rw [if_neg (by
    simpa [v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE] using
      fun compact => noncompact (compactIff.mp compact))]

#print axioms source_candidate_reduces
#print axioms translated_candidate_returns_on_semantic_compact
#print axioms translated_candidate_skips_on_semantic_noncompact

end

end V7FirstCompactCallerBridge
