import AspisFormal.K1.V7Tag73ExactCompilerQ16DuplexForest
import AspisFormal.K1.V7Tag73ExactCompilerQ16TraceOccurrence

/-!
# Exact compiler q16 forest replay closure

The literal source branch list is replayed from the exact compiler root using
the canonical checked duplex forest.  Cache hits—including adversary-first
coordinates—are inert; fresh coordinates advance the same chronological
source alignment.  The completed cursor reconstructs the ordinary production
run.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16ForestReplayClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16ForestReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerQ16CoordinateStep
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16BranchReplayLift
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerQ16DuplexForest
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding

noncomputable section

/-- Every literal source-plan member is its exact search outcome and lies no
later than the selected counter. -/
theorem q16_specs_of_search_match
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (spec : CandidateSpec) (member : spec ∈ q16SpecsOfSearch search) :
    spec.counter.val ≤ search.selectedCounter.val ∧
      spec.outcome = search.outcome spec.counter := by
  rw [q16SpecsOfSearch] at member
  rcases List.mem_append.mp member with earlier | selected
  · unfold earlierSpecs at earlier
    rw [List.mem_map] at earlier
    obtain ⟨index, _indexMember, specExact⟩ := earlier
    rw [← specExact]
    constructor
    · dsimp
      omega
    · rfl
  · have specExact : spec =
        { counter := search.selectedCounter
          outcome := .schedule search.selectedSchedule } := by
      simpa using selected
    rw [specExact]
    exact ⟨by rfl, search.selectedOutcome.symm⟩

/-- The literal head of the accepted q16 source plan has a scheduler pause at
its canonical first-output coordinate.  This is the chronological entry point
for a state-restoring q16 response family: the pause records the actual actor
that first exposed the coordinate, so an adversary-first exposure is retained
as such rather than relabelled as a verifier draw. -/
theorem exact_compiler_actual_q16_source_plan_first_pause
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ first rest,
      schedulerNativeQ16BranchesOfSearch
          (exactOperationalQ16InitialDigest input)
          (exactOperationalTape input).search = first :: rest ∧
      ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (q16OutputInput first.initialDigest),
        exactCompilerFullTargetScan input (q16OutputInput first.initialDigest) =
          .paused pause := by
  let search := (exactOperationalTape input).search
  cases planExact : q16SpecsOfSearch search with
  | nil =>
      exact False.elim (q16_specs_of_search_nonempty search planExact)
  | cons spec specs =>
      let first := schedulerNativeQ16BranchOfSpec
        (exactOperationalQ16InitialDigest input) spec
      let rest := specs.map (schedulerNativeQ16BranchOfSpec
        (exactOperationalQ16InitialDigest input))
      have specMember : spec ∈ q16SpecsOfSearch search := by
        rw [planExact]
        simp
      obtain ⟨beforeSelected, _outcomeExact⟩ :=
        q16_specs_of_search_match search spec specMember
      obtain ⟨pause, paused⟩ :=
        exact_compiler_each_q16_initial_target_scan_paused input spec.counter
          beforeSelected
      have branchesExact :
          schedulerNativeQ16BranchesOfSearch
              (exactOperationalQ16InitialDigest input) search =
            first :: rest := by
        change List.map (schedulerNativeQ16BranchOfSpec
          (exactOperationalQ16InitialDigest input))
            (q16SpecsOfSearch search) = first :: rest
        rw [planExact]
        rfl
      refine ⟨first, rest, ?_, ?_⟩
      · simpa [search] using branchesExact
      · exact ⟨pause, by
          simpa [first, schedulerNativeQ16BranchOfSpec] using paused⟩

/-- Fold exact branch replay across any sublist of the literal source plan. -/
theorem run_scheduler_native_q16_source_specs_actual
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerQ16CoordinateStep input) :
    ∀ (specs : List CandidateSpec),
      (∀ spec ∈ specs,
        spec.counter.val ≤
            (exactOperationalTape input).search.selectedCounter.val ∧
          spec.outcome =
            (exactOperationalTape input).search.outcome spec.counter) →
      ∀ (state : SchedulerNativeQ16Cursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        ExactCompilerRootQ16CursorAligned input state →
        ∃ final,
          runSchedulerNativeQ16BranchList transitionFuel
              (exactOperationalQ16DuplexForest input)
              (specs.map (schedulerNativeQ16BranchOfSpec
                (exactOperationalQ16InitialDigest input))) state = .ok final ∧
          Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  intro specs hspecs state aligned
  induction specs generalizing state with
  | nil =>
      exact ⟨state, rfl, ⟨aligned⟩⟩
  | cons head rest ih =>
      obtain ⟨headBefore, headOutcome⟩ := hspecs head (by simp)
      have tailMatches : ∀ spec ∈ rest,
          spec.counter.val ≤
              (exactOperationalTape input).search.selectedCounter.val ∧
            spec.outcome =
              (exactOperationalTape input).search.outcome spec.counter := by
        intro spec member
        exact hspecs spec (by simp [member])
      cases head with
      | mk counter outcome =>
          simp only at headBefore headOutcome ⊢
          subst outcome
          let coordinates := exactOperationalQ16BranchCoordinates input counter
            headBefore
          let branch := schedulerNativeQ16BranchOfSpec
            (exactOperationalQ16InitialDigest input)
            { counter := counter
              outcome := (exactOperationalTape input).search.outcome counter }
          have outputsPositive : coordinates.outputs ≠ [] := by
            intro empty
            have lengthZero := congrArg List.length empty
            rw [coordinates.outputsLength] at lengthZero
            exact (candidate_outcome_blocks_positive
              ((exactOperationalTape input).search.outcome counter)).ne'
                lengthZero
          obtain ⟨afterHead, headRun, ⟨headAligned⟩⟩ :=
            run_scheduler_native_q16_branch_from_cursor_actual_chain input
              coordinateStep branch (exactOperationalQ16DuplexForest input)
              coordinates.outputs coordinates.advances coordinates.tableChain
              outputsPositive
              (exact_operational_q16_branch_duplex_pairs input counter
                headBefore)
              state aligned
          obtain ⟨final, tailRun, finalAligned⟩ :=
            ih tailMatches afterHead headAligned
          refine ⟨final, ?_, finalAligned⟩
          simp only [List.map_cons, runSchedulerNativeQ16BranchList]
          dsimp [branch] at headRun
          rw [headRun]
          exact tailRun

/-- The exact accepted source plan executes from the compiler root and
preserves the chronological alignment through its selected branch. -/
theorem exact_compiler_actual_q16_forest_replay
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ final,
      runSchedulerNativeQ16BranchList transitionFuel
          (exactOperationalQ16DuplexForest input)
          (schedulerNativeQ16BranchesOfSearch
            (exactOperationalQ16InitialDigest input)
            (exactOperationalTape input).search)
          (exactCompilerInitialQ16Cursor input) = .ok final ∧
      Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  apply run_scheduler_native_q16_source_specs_actual input
    (exact_compiler_actual_q16_coordinate_step transitionRoom input)
    (q16SpecsOfSearch (exactOperationalTape input).search)
  · intro spec member
    exact q16_specs_of_search_match (exactOperationalTape input).search spec
      member
  · exact exactCompilerInitialQ16CursorAlignment input

/-- Finishing any aligned q16 cursor gives the literal root production run. -/
theorem exact_compiler_root_q16_alignment_reconstructs_run
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (state : SchedulerNativeQ16Cursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootQ16CursorAligned input state) :
    (finishSchedulerNativeQ16Forest transitionFuel state).run =
      runExactPlainRom transitionFuel configuration sample := by
  have reconstructed := exact_compiler_root_gamma_alignment_reconstructs_run
    input (q16CursorToGamma state) aligned
  simpa [finishSchedulerNativeQ16Forest, q16CursorToGamma,
    runExactPlainRom, run_scheduler_native_eq_list_run] using reconstructed

/-- Deterministic q16 closure: the exact successful forest is executable from
the actual compiler root and the completed execution is the production run. -/
theorem exact_compiler_actual_q16_forest_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ∃ final,
      runSchedulerNativeQ16BranchList transitionFuel
          (exactOperationalQ16DuplexForest input)
          (schedulerNativeQ16BranchesOfSearch
            (exactOperationalQ16InitialDigest input)
            (exactOperationalTape input).search)
          (exactCompilerInitialQ16Cursor input) = .ok final ∧
      (finishSchedulerNativeQ16Forest transitionFuel final).run =
        runExactPlainRom transitionFuel configuration sample ∧
      q16DigestForestSucceeds (exactOperationalQ16DuplexForest input).1 := by
  obtain ⟨final, executed, ⟨aligned⟩⟩ :=
    exact_compiler_actual_q16_forest_replay transitionRoom input
  exact ⟨final, executed,
    exact_compiler_root_q16_alignment_reconstructs_run input final aligned,
    exact_operational_q16_duplex_forest_succeeds input frontierExact⟩

#print axioms q16_specs_of_search_match
#print axioms exact_compiler_actual_q16_source_plan_first_pause
#print axioms run_scheduler_native_q16_source_specs_actual
#print axioms exact_compiler_actual_q16_forest_replay
#print axioms exact_compiler_root_q16_alignment_reconstructs_run
#print axioms exact_compiler_actual_q16_forest_closure

end

end AspisK1.V7Tag73ExactCompilerQ16ForestReplayClosure
