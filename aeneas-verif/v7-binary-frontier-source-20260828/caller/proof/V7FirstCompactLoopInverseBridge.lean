import V7FirstCompactCallerBridge

/-!
# Inverting the production first-compact q16 loop

The generated range loop selects its first compact candidate.  This module
starts from a literal successful loop result and recovers the source call made
at the current range position.  It is the first step toward a complete
source-side certificate for every scanned q16 candidate.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace V7FirstCompactLoopInverseBridge

open V7FirstCompactSource
open V7FirstCompactCallerBridge

/-- A `some` result from the literal candidate helper retains the counter
which the generated code put in that result. -/
theorem candidate_success_some_retains_counter
    (inputTranscript : transcript.Transcript) (counter : Std.U8)
    (schedule : v7_onefold.V7CompactQuerySchedule)
    (run : v7_onefold.derive_v7_compact_candidate inputTranscript counter =
      .ok (.Ok (some schedule))) :
    schedule.counter = counter := by
  let raw := candidate_success_exposes_raw_execution inputTranscript counter
    (some schedule) run
  have outputExact := raw.outputExact
  change some schedule = _ at outputExact
  split at outputExact
  · have scheduleExact := Option.some.inj outputExact
    rw [scheduleExact]
  · simp at outputExact

/-- A literal `continue` result of the generated loop body can only arise
when the range yielded one counter and that candidate returned `Ok none`. -/
theorem first_success_body_continue_inverts
    (inputTranscript : transcript.Transcript)
    (iter nextIter : core.ops.range.Range Std.U8)
    (run : v7_onefold.derive_first_v7_compact_queries_loop.body
      inputTranscript iter = .ok (.cont nextIter)) :
    ∃ counter : Std.U8,
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        .ok (some counter, nextIter) ∧
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok none) := by
  unfold v7_onefold.derive_first_v7_compact_queries_loop.body at run
  generalize nextRun :
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        nextResult at run
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok result =>
      rcases result with ⟨next, returnedIter⟩
      cases next with
      | none => simp only [bind_tc_ok] at run; cases run
      | some counter =>
          simp only [bind_tc_ok] at run
          generalize candidateRun :
              v7_onefold.derive_v7_compact_candidate inputTranscript counter =
                candidateResult at run
          cases candidateResult with
          | fail error =>
              simp [Bind.bind, Aeneas.Std.bind, candidateRun] at run
          | div =>
              simp [Bind.bind, Aeneas.Std.bind, candidateRun] at run
          | ok candidate =>
              cases candidate with
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    candidateRun] at run
              | Ok candidate =>
                  cases candidate with
                  | none =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        candidateRun] at run
                      cases run
                      exact ⟨counter, rfl, candidateRun⟩
                  | some schedule =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        candidateRun] at run

/-- A literal `done (some schedule, none)` result of the generated loop body
comes from exactly one range counter whose candidate returned that schedule. -/
theorem first_success_body_select_inverts
    (inputTranscript : transcript.Transcript) (iter : core.ops.range.Range Std.U8)
    (schedule : v7_onefold.V7CompactQuerySchedule)
    (run : v7_onefold.derive_first_v7_compact_queries_loop.body
      inputTranscript iter = .ok (.done (some schedule, none))) :
    ∃ (counter : Std.U8) (nextIter : core.ops.range.Range Std.U8),
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        .ok (some counter, nextIter) ∧
      v7_onefold.derive_v7_compact_candidate inputTranscript counter =
        .ok (.Ok (some schedule)) := by
  unfold v7_onefold.derive_first_v7_compact_queries_loop.body at run
  generalize nextRun :
      core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
        nextResult at run
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok result =>
      rcases result with ⟨next, returnedIter⟩
      cases next with
      | none => simp only [bind_tc_ok] at run; cases run
      | some counter =>
          simp only [bind_tc_ok] at run
          generalize candidateRun :
              v7_onefold.derive_v7_compact_candidate inputTranscript counter =
                candidateResult at run
          cases candidateResult with
          | fail error =>
              simp [Bind.bind, Aeneas.Std.bind, candidateRun] at run
          | div =>
              simp [Bind.bind, Aeneas.Std.bind, candidateRun] at run
          | ok candidate =>
              cases candidate with
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    candidateRun] at run
              | Ok candidate =>
                  cases candidate with
                  | none =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        candidateRun] at run
                  | some returnedSchedule =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        candidateRun] at run
                      cases run
                      exact ⟨counter, returnedIter, rfl, candidateRun⟩

/-- An actual successful range `next` call exposes its current counter and
the exact successor range.  This is an inversion of translated iterator
control flow, not an arithmetic convention about loop indices. -/
theorem range_next_some_is_exact_successor
    (iter nextIter : core.ops.range.Range Std.U8) (counter : Std.U8)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter =
      .ok (some counter, nextIter)) :
    counter = iter.start ∧
      nextIter.start.val = iter.start.val + 1 ∧
      nextIter.end = iter.end ∧
      iter.start.val < iter.end.val := by
  have active : iter.start.val < iter.end.val := by
    by_contra inactive
    have endLeStart : iter.end.val ≤ iter.start.val := by omega
    obtain ⟨⟨option, noNext⟩, noRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_none_spec
          (ty := .U8)
          (partialOrdInst := core.cmp.PartialOrdU8)
          (by intro left right; rfl) iter endLeStart)
    rw [optionExact, nextExact] at noRun
    rw [noRun] at run
    simp only [Result.ok.injEq] at run
    have differentOptions : (none : Option Std.U8) = some counter :=
      congrArg Prod.fst run
    cases differentOptions
  obtain ⟨⟨option, canonicalNext⟩, canonicalRun, optionExact,
    canonicalStart, canonicalEnd⟩ :=
    WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty := .U8)
        (cloneInst := core.clone.CloneU8)
        (partialOrdInst := core.cmp.PartialOrdU8)
        (by intro value; rfl)
        (by intro left right; rfl)
        iter active)
  rw [optionExact] at canonicalRun
  have exact : (some counter, nextIter) =
      (some iter.start, canonicalNext) := by
    exact Result.ok.inj (run.symm.trans canonicalRun)
  constructor
  · exact Option.some.inj (congrArg Prod.fst exact)
  constructor
  · have nextExact : nextIter = canonicalNext := congrArg Prod.snd exact
    rw [nextExact]
    exact canonicalStart
  constructor
  · have nextExact : nextIter = canonicalNext := congrArg Prod.snd exact
    rw [nextExact]
    exact canonicalEnd
  · exact active

/-- If the loop ultimately returns a schedule whose embedded counter is later
than the current range start, the current literal body must have continued.
It cannot have selected a different candidate first. -/
theorem first_success_loop_at_earlier_start_continues
    (inputTranscript : transcript.Transcript)
    (iter : core.ops.range.Range Std.U8)
    (selected : Std.U8) (schedule : v7_onefold.V7CompactQuerySchedule)
    (scheduleCounter : schedule.counter = selected)
    (endExact : iter.end.val = 64)
    (startEarlier : iter.start.val < selected.val)
    (selectedBound : selected.val < 64)
    (run : v7_onefold.derive_first_v7_compact_queries_loop iter
      inputTranscript = .ok (some schedule, none)) :
    ∃ nextIter,
      v7_onefold.derive_first_v7_compact_queries_loop.body inputTranscript
        iter = .ok (.cont nextIter) ∧
      v7_onefold.derive_first_v7_compact_queries_loop nextIter
        inputTranscript = .ok (some schedule, none) := by
  unfold v7_onefold.derive_first_v7_compact_queries_loop at run
  rw [loop.eq_def] at run
  generalize bodyRun :
      v7_onefold.derive_first_v7_compact_queries_loop.body inputTranscript
        iter = bodyResult at run
  cases bodyResult with
  | fail error => simp at run
  | div => simp at run
  | ok control =>
      cases control with
      | cont nextIter =>
          simp at run
          exact ⟨nextIter, rfl, run⟩
      | done result =>
          rcases result with ⟨accepted, pending⟩
          cases pending with
          | some failure => simp at run
          | none =>
              cases accepted with
              | none => simp at run
              | some returnedSchedule =>
                  have selectedBody := first_success_body_select_inverts
                    inputTranscript iter returnedSchedule bodyRun
                  obtain ⟨counter, nextIter, nextRun, candidateRun⟩ :=
                    selectedBody
                  have returnedCounter := candidate_success_some_retains_counter
                    inputTranscript counter returnedSchedule candidateRun
                  have scheduleExact : returnedSchedule = schedule := by
                    simpa [bodyRun] using run
                  rw [scheduleExact, scheduleCounter] at returnedCounter
                  have active : iter.start.val < iter.end.val := by
                    omega
                  obtain ⟨⟨option, canonicalNext⟩, canonicalRun, optionExact,
                    canonicalStart, canonicalEnd⟩ :=
                    WP.spec_imp_exists
                      (core.iter.range.IteratorRange.next_UScalar_some_spec
                        (ty := .U8)
                        (cloneInst := core.clone.CloneU8)
                        (partialOrdInst := core.cmp.PartialOrdU8)
                        (by intro value; rfl)
                        (by intro left right; rfl)
                        iter active)
                  rw [optionExact] at canonicalRun
                  have returnedExact : (some counter, nextIter) =
                      (some iter.start, canonicalNext) := by
                    exact Result.ok.inj (nextRun.symm.trans canonicalRun)
                  have counterExact : counter = iter.start := by
                    exact Option.some.inj (congrArg Prod.fst returnedExact)
                  have counterValue : counter.val = iter.start.val := by
                    rw [counterExact]
                  have selectedValue : selected.val = counter.val :=
                    congrArg UScalar.val returnedCounter
                  have startEqualsSelected : iter.start.val = selected.val :=
                    counterValue.symm.trans selectedValue.symm
                  exact False.elim
                    ((Nat.ne_of_lt startEarlier) startEqualsSelected)

/-- A successful literal first-compact loop certifies every earlier examined
counter: each such production candidate returned `Ok none`.  This is derived
by inverting the generated range-loop control flow, not by assuming a
first-success property of the result. -/
theorem first_success_loop_exposes_all_prior_none
    (inputTranscript : transcript.Transcript)
    (iter : core.ops.range.Range Std.U8)
    (selected : Std.U8) (schedule : v7_onefold.V7CompactQuerySchedule)
    (scheduleCounter : schedule.counter = selected)
    (endExact : iter.end.val = 64)
    (startLeSelected : iter.start.val ≤ selected.val)
    (selectedBound : selected.val < 64)
    (run : v7_onefold.derive_first_v7_compact_queries_loop iter
      inputTranscript = .ok (some schedule, none))
    (target : Std.U8)
    (targetAfterStart : iter.start.val ≤ target.val)
    (targetEarlier : target.val < selected.val) :
    v7_onefold.derive_v7_compact_candidate inputTranscript target =
      .ok (.Ok none) := by
  by_cases startEarlier : iter.start.val < selected.val
  · obtain ⟨nextIter, bodyRun, nextRun⟩ :=
      first_success_loop_at_earlier_start_continues inputTranscript iter
        selected schedule scheduleCounter endExact startEarlier selectedBound run
    obtain ⟨current, currentNext, currentRun⟩ :=
      first_success_body_continue_inverts inputTranscript iter nextIter bodyRun
    have active : iter.start.val < iter.end.val := by omega
    obtain ⟨⟨option, canonicalNext⟩, canonicalRun, optionExact,
      canonicalStart, canonicalEnd⟩ :=
      WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_some_spec
          (ty := .U8)
          (cloneInst := core.clone.CloneU8)
          (partialOrdInst := core.cmp.PartialOrdU8)
          (by intro value; rfl)
          (by intro left right; rfl)
          iter active)
    rw [optionExact] at canonicalRun
    have currentNextExact : (some current, nextIter) =
        (some iter.start, canonicalNext) := by
      exact Result.ok.inj (currentNext.symm.trans canonicalRun)
    have currentExact : current = iter.start := by
      exact Option.some.inj (congrArg Prod.fst currentNextExact)
    have nextExact : nextIter = canonicalNext := by
      exact congrArg Prod.snd currentNextExact
    have nextStart : nextIter.start.val = iter.start.val + 1 := by
      rw [nextExact]
      exact canonicalStart
    have nextEnd : nextIter.end.val = 64 := by
      rw [nextExact, canonicalEnd, endExact]
    have nextLeSelected : nextIter.start.val ≤ selected.val := by
      rw [nextStart]
      omega
    by_cases targetCurrent : target.val = iter.start.val
    · have targetExact : target = current := by
        apply UScalar.eq_of_val_eq
        rw [currentExact]
        exact targetCurrent
      simpa [targetExact] using currentRun
    · have targetAfterNext : nextIter.start.val ≤ target.val := by
        rw [nextStart]
        omega
      exact first_success_loop_exposes_all_prior_none inputTranscript nextIter
        selected schedule scheduleCounter nextEnd nextLeSelected selectedBound
        nextRun target targetAfterNext targetEarlier
  · have startExact : iter.start.val = selected.val := by omega
    omega
termination_by selected.val - iter.start.val
decreasing_by
  rw [nextStart]
  omega

#print axioms first_success_body_continue_inverts
#print axioms first_success_body_select_inverts
#print axioms range_next_some_is_exact_successor
#print axioms first_success_loop_at_earlier_start_continues
#print axioms first_success_loop_exposes_all_prior_none
#print axioms candidate_success_some_retains_counter

end V7FirstCompactLoopInverseBridge
