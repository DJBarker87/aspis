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

/-! ## Exact first-success outer loop -/

/-- Exact generated continuation after the range iterator yields one counter. -/
private def firstSuccessAfterNext
    (inputTranscript : transcript.Transcript) (counter : Std.U8)
    (nextIter : core.ops.range.Range Std.U8) :
    Result (ControlFlow (core.ops.range.Range Std.U8) ((Option
      v7_onefold.V7CompactQuerySchedule) × (Option (core.result.Result
      v7_onefold.V7CompactQuerySchedule v6_onefold.V6WireError)))) := do
  let r ← v7_onefold.derive_v7_compact_candidate inputTranscript counter
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    match val with
    | none => .ok (.cont nextIter)
    | some _ => .ok (.done (val, none))
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        v7_onefold.V7CompactQuerySchedule
        (core.convert.FromSame v6_onefold.V6WireError) residual
    .ok (.done (none, some r1))

private theorem first_success_body_skips
    (inputTranscript : transcript.Transcript)
    (iter nextIter : core.ops.range.Range Std.U8) (counter : Std.U8)
    (nextRun :
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        .ok (some counter, nextIter))
    (candidateRun :
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok none)) :
    v7_onefold.derive_first_v7_compact_queries_loop.body
        inputTranscript iter = .ok (.cont nextIter) := by
  unfold v7_onefold.derive_first_v7_compact_queries_loop.body
  rw [nextRun]
  simp only [bind_tc_ok]
  change firstSuccessAfterNext inputTranscript counter nextIter = _
  unfold firstSuccessAfterNext
  rw [candidateRun]
  rfl

private theorem first_success_body_selects
    (inputTranscript : transcript.Transcript)
    (iter nextIter : core.ops.range.Range Std.U8) (counter : Std.U8)
    (schedule : v7_onefold.V7CompactQuerySchedule)
    (nextRun :
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        .ok (some counter, nextIter))
    (candidateRun :
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok (some schedule))) :
    v7_onefold.derive_first_v7_compact_queries_loop.body
        inputTranscript iter = .ok (.done (some schedule, none)) := by
  unfold v7_onefold.derive_first_v7_compact_queries_loop.body
  rw [nextRun]
  simp only [bind_tc_ok]
  change firstSuccessAfterNext inputTranscript counter nextIter = _
  unfold firstSuccessAfterNext
  rw [candidateRun]
  rfl

/-- The translated range loop returns the selected schedule when every earlier
candidate returns `none` and the selected candidate returns that schedule.  The
proof follows the literal `u8` range iterator and its first-success control
flow; it does not assume the loop result. -/
theorem translated_first_success_loop_exact
    (inputTranscript : transcript.Transcript)
    (selected : Std.U8) (schedule : v7_onefold.V7CompactQuerySchedule)
    (iter : core.ops.range.Range Std.U8)
    (endExact : iter.end.val = 64)
    (startLe : iter.start.val ≤ selected.val)
    (selectedLt : selected.val < 64)
    (earlierRun : ∀ counter : Std.U8, counter.val < selected.val →
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok none))
    (selectedRun :
      v7_onefold.derive_v7_compact_candidate inputTranscript selected =
        .ok (.Ok (some schedule))) :
    v7_onefold.derive_first_v7_compact_queries_loop iter inputTranscript =
      .ok (some schedule, none) := by
  have active : iter.start.val < iter.end.val := by omega
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart, nextEnd⟩ :=
    WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty := .U8)
        (cloneInst := core.clone.CloneU8)
        (partialOrdInst := core.cmp.PartialOrdU8)
        (by intro value; rfl)
        (by intro left right; rfl)
        iter active)
  rw [optionExact] at nextRun
  by_cases earlier : iter.start.val < selected.val
  · have bodyRun := first_success_body_skips inputTranscript iter nextIter
      iter.start nextRun (earlierRun iter.start earlier)
    have nextEndExact : nextIter.end.val = 64 := by
      rw [nextEnd, endExact]
    have nextStartLe : nextIter.start.val ≤ selected.val := by omega
    have recursiveRun := translated_first_success_loop_exact inputTranscript
      selected schedule
      nextIter nextEndExact nextStartLe selectedLt earlierRun selectedRun
    unfold v7_onefold.derive_first_v7_compact_queries_loop
    rw [loop.eq_def, bodyRun]
    exact recursiveRun
  · have startValue : iter.start.val = selected.val := by omega
    have startExact : iter.start = selected :=
      UScalar.eq_of_val_eq startValue
    have bodyRun := first_success_body_selects inputTranscript iter nextIter
      selected schedule (by simpa only [startExact] using nextRun) selectedRun
    unfold v7_onefold.derive_first_v7_compact_queries_loop
    rw [loop.eq_def, bodyRun]
termination_by selected.val - iter.start.val
decreasing_by omega

/-- The complete translated production wrapper returns the exact first
successful candidate selected from counters `0..64`. -/
theorem translated_first_v7_compact_queries_exact
    (inputTranscript : transcript.Transcript)
    (selected : Std.U8) (schedule : v7_onefold.V7CompactQuerySchedule)
    (selectedLt : selected.val < 64)
    (earlierRun : ∀ counter : Std.U8, counter.val < selected.val →
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok none))
    (selectedRun :
      v7_onefold.derive_v7_compact_candidate inputTranscript selected =
        .ok (.Ok (some schedule))) :
    v7_onefold.derive_first_v7_compact_queries inputTranscript =
      .ok (.Ok schedule) := by
  have initialStartLe :
      ({ start := 0#u8, «end» := 64#u8 } :
        core.ops.range.Range Std.U8).start.val ≤ selected.val :=
    Nat.zero_le selected.val
  have loopRun := translated_first_success_loop_exact inputTranscript selected
    schedule { start := 0#u8, «end» := 64#u8 } rfl initialStartLe
    selectedLt earlierRun selectedRun
  have castExact :
      UScalar.cast .U8 v7_onefold.V7_COMPACT_QUERY_CANDIDATES = 64#u8 := by
    unfold v7_onefold.V7_COMPACT_QUERY_CANDIDATES
    apply UScalar.eq_of_val_eq
    norm_num [UScalar.cast_val_eq]
  unfold v7_onefold.derive_first_v7_compact_queries
  rw [castExact]
  simp only [lift, bind_tc_ok]
  rw [loopRun]
  rfl

/-- Semantic first-cap-203 evidence for every examined candidate composes with
the literal translated candidate helper and outer loop to return the selected
five-field schedule from the production wrapper. -/
theorem translated_wrapper_returns_first_semantic_candidate
    (inputTranscript selectedCloned selectedAbsorbed
      selectedSampledTranscript : transcript.Transcript)
    (selectedCounterData : Slice Std.U8)
    (selected : Std.U8) (selectedSampled : alloc.vec.Vec Std.U32)
    (selectedSchedule : QuerySchedule)
    (selectedRuns : CandidatePrefixRuns inputTranscript selectedCloned
      selectedAbsorbed selectedSampledTranscript selectedCounterData selected
      selectedSampled selectedSchedule)
    (selectedLt : selected.val < 64)
    (selectedAdmitted :
      SemanticCap203Admitted selectedSchedule.positions)
    (earlier : ∀ counter : Std.U8, counter.val < selected.val →
      ∃ cloned absorbed sampledTranscript counterData sampled schedule,
        CandidatePrefixRuns inputTranscript cloned absorbed sampledTranscript
          counterData counter sampled schedule ∧
        ¬ SemanticCap203Admitted schedule.positions) :
    ∃ frontier,
      v7_onefold.derive_first_v7_compact_queries inputTranscript =
        .ok (.Ok (returnedSchedule selectedSchedule selected frontier
          selectedSampledTranscript)) := by
  obtain ⟨frontier, selectedRun⟩ :=
    translated_candidate_returns_on_semantic_compact inputTranscript
      selectedCloned selectedAbsorbed selectedSampledTranscript
      selectedCounterData selected selectedSampled selectedSchedule
      selectedRuns selectedAdmitted
  have earlierRun : ∀ counter : Std.U8, counter.val < selected.val →
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok none) := by
    intro counter counterLt
    obtain ⟨cloned, absorbed, sampledTranscript, counterData, sampled,
      schedule, runs, noncompact⟩ := earlier counter counterLt
    exact translated_candidate_skips_on_semantic_noncompact inputTranscript
      cloned absorbed sampledTranscript counterData counter sampled schedule
      runs noncompact
  exact ⟨frontier,
    translated_first_v7_compact_queries_exact inputTranscript selected
      (returnedSchedule selectedSchedule selected frontier
        selectedSampledTranscript) selectedLt earlierRun selectedRun⟩

#print axioms source_candidate_reduces
#print axioms translated_candidate_returns_on_semantic_compact
#print axioms translated_candidate_skips_on_semantic_noncompact
#print axioms translated_first_success_loop_exact
#print axioms translated_first_v7_compact_queries_exact
#print axioms translated_wrapper_returns_first_semantic_candidate

end

end V7FirstCompactCallerBridge
