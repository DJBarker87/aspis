import AspisFormal.K1.V7Tag73SchedulerNativeQ16ForestReplay
import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Exact accepting-source branch plan for scheduler-native q16 replay

An accepting `FirstCap203Search` already contains the exact outcome for every
counter before the selected counter and the selected schedule itself.  This
module converts that source object into the ordered branch list consumed by
the cache-aware scheduler replay.  No probability statement is used: the
list is literally `earlierSpecs ++ [selected]`, so sampler block counts and
the first-cap-203 boundary remain the production values.

The per-counter initial digest is retained as nuisance data.  The next bridge
must identify it with the digest immediately after the production candidate
absorb in the translated accepted run.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeQ16SourcePlan

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SchedulerNativeQ16Replay

noncomputable section

/-- Every deployed candidate outcome consumes a positive number of blocks. -/
theorem candidate_outcome_blocks_positive (outcome : CandidateOutcome) :
    0 < outcome.blocksUsed := by
  cases outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule =>
      exact Nat.zero_lt_of_lt schedule.atLeastTwoBlocks

theorem candidate_outcome_blocks_cap (outcome : CandidateOutcome) :
    outcome.blocksUsed ≤ 8 := by
  cases outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule => exact schedule.withinSixtyFourDraws

/-- The literal accepting source prefix, including the selected branch and
excluding all counters after it. -/
def q16SpecsOfSearch {frontierNodes : QuerySchedule -> Nat}
    (search : FirstCap203Search frontierNodes) : List CandidateSpec :=
  earlierSpecs search ++
    [{ counter := search.selectedCounter
       outcome := .schedule search.selectedSchedule }]

@[simp] theorem q16_specs_of_search_length
    {frontierNodes : QuerySchedule -> Nat}
    (search : FirstCap203Search frontierNodes) :
    (q16SpecsOfSearch search).length = search.selectedCounter.val + 1 := by
  simp [q16SpecsOfSearch, earlierSpecs]

theorem q16_specs_of_search_nonempty
    {frontierNodes : QuerySchedule -> Nat}
    (search : FirstCap203Search frontierNodes) :
    q16SpecsOfSearch search ≠ [] := by
  simp [q16SpecsOfSearch]

/-- Convert one exact source candidate into the replay geometry. -/
def schedulerNativeQ16BranchOfSpec
    (initialDigest : Fin 64 -> Digest256) (spec : CandidateSpec) :
    SchedulerNativeQ16Branch where
  counter := spec.counter
  initialDigest := initialDigest spec.counter
  blocksUsed := spec.outcome.blocksUsed
  blocksPositive := candidate_outcome_blocks_positive spec.outcome
  blocksCap := candidate_outcome_blocks_cap spec.outcome

/-- Exact ordered replay plan through the selected source counter. -/
def schedulerNativeQ16BranchesOfSearch
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    List SchedulerNativeQ16Branch :=
  (q16SpecsOfSearch search).map
    (schedulerNativeQ16BranchOfSpec initialDigest)

@[simp] theorem scheduler_native_q16_branches_of_search_length
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    (schedulerNativeQ16BranchesOfSearch initialDigest search).length =
      search.selectedCounter.val + 1 := by
  simp [schedulerNativeQ16BranchesOfSearch]

theorem scheduler_native_q16_branches_of_search_nonempty
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    schedulerNativeQ16BranchesOfSearch initialDigest search ≠ [] := by
  simp [schedulerNativeQ16BranchesOfSearch, q16SpecsOfSearch]

/-- The final replay branch is definitionally the selected source branch. -/
theorem scheduler_native_q16_branches_getLast_selected
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    (schedulerNativeQ16BranchesOfSearch initialDigest search).getLast
        (scheduler_native_q16_branches_of_search_nonempty initialDigest
          search) =
      schedulerNativeQ16BranchOfSpec initialDigest
        { counter := search.selectedCounter
          outcome := .schedule search.selectedSchedule } := by
  simp [schedulerNativeQ16BranchesOfSearch, q16SpecsOfSearch]

theorem scheduler_native_q16_selected_counter_exact
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    ((schedulerNativeQ16BranchesOfSearch initialDigest search).getLast
        (scheduler_native_q16_branches_of_search_nonempty initialDigest
          search)).counter = search.selectedCounter := by
  rw [scheduler_native_q16_branches_getLast_selected]
  rfl

theorem scheduler_native_q16_selected_blocks_exact
    {frontierNodes : QuerySchedule -> Nat}
    (initialDigest : Fin 64 -> Digest256)
    (search : FirstCap203Search frontierNodes) :
    ((schedulerNativeQ16BranchesOfSearch initialDigest search).getLast
        (scheduler_native_q16_branches_of_search_nonempty initialDigest
          search)).blocksUsed = search.selectedSchedule.blocksUsed := by
  rw [scheduler_native_q16_branches_getLast_selected]
  rfl

/-- Every source branch strictly before the selected counter is a sampled
schedule rejected only because its exact frontier exceeds 203. -/
theorem q16_specs_of_search_earlier_noncompact
    {frontierNodes : QuerySchedule -> Nat}
    (search : FirstCap203Search frontierNodes)
    (counter : Fin 64)
    (earlier : counter.val < search.selectedCounter.val) :
    exists schedule,
      search.outcome counter = .schedule schedule /\
      203 < frontierNodes schedule := by
  exact search.everyEarlierSampledAndNoncompact counter earlier

/-- The selected source branch is the exact compact schedule, not merely a
branch with the same counter. -/
theorem q16_specs_of_search_selected_exact
    {frontierNodes : QuerySchedule -> Nat}
    (search : FirstCap203Search frontierNodes) :
    search.outcome search.selectedCounter =
        .schedule search.selectedSchedule /\
      frontierNodes search.selectedSchedule <= 203 :=
  ⟨search.selectedOutcome, search.selectedCompact⟩

#print axioms candidate_outcome_blocks_positive
#print axioms candidate_outcome_blocks_cap
#print axioms scheduler_native_q16_branches_getLast_selected
#print axioms scheduler_native_q16_selected_counter_exact
#print axioms scheduler_native_q16_selected_blocks_exact
#print axioms q16_specs_of_search_earlier_noncompact
#print axioms q16_specs_of_search_selected_exact

end

end AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
