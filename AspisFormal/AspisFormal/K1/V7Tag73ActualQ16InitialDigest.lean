import AspisFormal.K1.V7Tag73ExactCompilerQ16TraceOccurrence

/-!
# Actual post-counter digests for every scanned q16 branch

The q16 replay grammar needs the digest reached after absorbing each candidate
counter and before its first squeeze.  These digests are not supplied by a
caller: successful production `runQ16` contains a literal `runCandidate` for
every counter through the selected one.  This module extracts those runs and
defines the canonical post-counter digest map from them.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ActualQ16InitialDigest

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73ActualQ16DecoderExtraction
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence

noncomputable section

/-- Membership in a successful discarded-candidate list exposes the literal
production `runCandidate` call for that specification. -/
theorem run_discarded_candidates_exposes_member_execution
    (table : FixedOracleTable) (base : Digest256)
    (specs : List CandidateSpec) (state final : EvalState)
    (run : runDiscardedCandidates table base specs state = some final)
    (spec : CandidateSpec) (member : spec ∈ specs) :
    ∃ before after,
      runCandidate table before spec = some after := by
  induction specs generalizing state with
  | nil => simp at member
  | cons head rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨afterHead, headRun, restRun⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases List.mem_cons.mp member with equal | tailMember
      · subst spec
        exact ⟨state, afterHead, headRun⟩
      · exact ih (state := restoreDigest base afterHead) restRun tailMember

/-- Membership in the complete q16 plan exposes the corresponding literal
candidate execution, whether discarded or selected. -/
theorem run_q16_exposes_member_execution
    (table : FixedOracleTable) (state final : EvalState) (tape : Q16Tape)
    (run : runQ16 table state tape = some final)
    (spec : CandidateSpec) (member : spec ∈ tape.earlier ++ [tape.selected]) :
    ∃ before after,
      runCandidate table before spec = some after := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases List.mem_append.mp member with earlierMember | selectedMember
  · exact run_discarded_candidates_exposes_member_execution table state.digest
      tape.earlier state beforeSelected earlierRun spec earlierMember
  · have equal : spec = tape.selected := by simpa using selectedMember
    subst spec
    exact ⟨beforeSelected, final, selectedRun⟩

/-- Literal production evidence for one source q16 branch. -/
structure ActualQ16InitialDigestWitness
    (table : FixedOracleTable) (counter : Fin 64)
    (outcome : CandidateOutcome) where
  before : EvalState
  after : EvalState
  afterCounter : EvalState
  candidateRun : runCandidate table before
    { counter := counter, outcome := outcome } = some after
  absorbRun : absorbStep table before (.queryCandidate counter) =
    some afterCounter
  firstAnswer : Digest256
  firstOutputLookup : tableLookup table
    (q16OutputInput afterCounter.digest) = some firstAnswer

/-- Every source counter through the selected one has a literal
post-counter-absorb state and a positive first q16 output lookup. -/
theorem accepted_q16_run_exposes_initial_digest
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    Nonempty (ActualQ16InitialDigestWitness table counter
      (search.outcome counter)) := by
  let spec : CandidateSpec :=
    { counter := counter, outcome := search.outcome counter }
  have member : spec ∈
      (q16TapeOfSearch search).earlier ++ [(q16TapeOfSearch search).selected] := by
    simpa [spec, q16SpecsOfSearch, q16TapeOfSearch] using
      source_spec_mem_q16_plan search counter beforeSelected
  obtain ⟨before, after, candidateRun⟩ :=
    run_q16_exposes_member_execution table state afterQ16
      (q16TapeOfSearch search) run spec member
  obtain ⟨afterCounter, blocks, afterBlocks, absorbRun, squeezeRun,
      _afterExact, _lengthExact, _recordMember⟩ :=
    run_candidate_exposes_exact_record table before after spec candidateRun
  obtain ⟨answer, found⟩ := squeeze_many_positive_first_output_lookup table
    (.queryCandidate counter) (search.outcome counter).blocksUsed
    (candidate_outcome_blocks_positive (search.outcome counter)) afterCounter
    afterBlocks blocks (by simpa [spec] using squeezeRun)
  exact ⟨{
    before := before
    after := after
    afterCounter := afterCounter
    candidateRun := by simpa [spec] using candidateRun
    absorbRun := by simpa [spec] using absorbRun
    firstAnswer := answer
    firstOutputLookup := by simpa [q16OutputInput] using found }⟩

/-- Canonical actual post-counter digest.  Unscanned counters are irrelevant
and receive the all-zero default. -/
noncomputable def acceptedQ16InitialDigest
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16) :
    Fin 64 → Digest256 := fun counter =>
  if beforeSelected : counter.val ≤ search.selectedCounter.val then
    (Classical.choice
      (accepted_q16_run_exposes_initial_digest table state afterQ16 search run
        counter beforeSelected)).afterCounter.digest
  else
    zeroBytes 32

theorem accepted_q16_initial_digest_has_literal_candidate_run
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    ∃ before after afterCounter,
      runCandidate table before
          { counter := counter, outcome := search.outcome counter } =
        some after ∧
      absorbStep table before (.queryCandidate counter) = some afterCounter ∧
      afterCounter.digest =
        acceptedQ16InitialDigest table state afterQ16 search run counter := by
  rw [acceptedQ16InitialDigest, dif_pos beforeSelected]
  let witness := Classical.choice
    (accepted_q16_run_exposes_initial_digest table state afterQ16 search run
      counter beforeSelected)
  exact ⟨witness.before, witness.after, witness.afterCounter,
    witness.candidateRun, witness.absorbRun, rfl⟩

theorem accepted_q16_initial_digest_first_output_lookup
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    ∃ answer,
      tableLookup table
          (q16OutputInput
            (acceptedQ16InitialDigest table state afterQ16 search run counter)) =
        some answer := by
  rw [acceptedQ16InitialDigest, dif_pos beforeSelected]
  let witness := Classical.choice
    (accepted_q16_run_exposes_initial_digest table state afterQ16 search run
      counter beforeSelected)
  exact ⟨witness.firstAnswer, witness.firstOutputLookup⟩

#print axioms run_discarded_candidates_exposes_member_execution
#print axioms run_q16_exposes_member_execution
#print axioms accepted_q16_run_exposes_initial_digest
#print axioms accepted_q16_initial_digest_has_literal_candidate_run
#print axioms accepted_q16_initial_digest_first_output_lookup

end

end AspisK1.V7Tag73ActualQ16InitialDigest
