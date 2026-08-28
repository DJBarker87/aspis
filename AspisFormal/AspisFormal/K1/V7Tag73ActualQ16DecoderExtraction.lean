import AspisFormal.K1.V7Tag73SchedulerNativeQ16SourcePlan
import AspisFormal.K1.V7Tag73CheckedRefinementFullFutureFreePath

/-!
# Extract exact q16 decoder records from the accepted evaluator run

The cache-aware scheduler replay routes digest values, but it must not assume
that those values decode as the source `FirstCap203Search`.  This module gets
that fact from the literal deterministic evaluator instead.  Every successful
`runCandidate` appends a concrete `CandidateRecord`; successful `runQ16`
therefore exposes one such record for every counter through the selected
counter, and `StateCandidatesDecodeAs` proves that its exact byte list decodes
to the recorded source outcome.

No probability claim, Merkle claim, or frontier equality occurs here.  The
remaining source-to-router bridge only has to identify these already-decoded
record bytes with the corresponding cache-aware routed forest prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ActualQ16DecoderExtraction

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan

noncomputable section

/-- Every branch listed in a successful discarded-candidate run leaves an
exact concrete record in the final evaluator state. -/
theorem run_discarded_candidates_exposes_member_record
    (table : FixedOracleTable) (base : Digest256)
    (specs : List CandidateSpec) (state final : EvalState)
    (run : runDiscardedCandidates table base specs state = some final)
    (spec : CandidateSpec) (member : spec ∈ specs) :
    ∃ record ∈ final.candidates,
      record.counter = spec.counter ∧
      record.outcome = spec.outcome ∧
      record.blocks.length = spec.outcome.blocksUsed := by
  induction specs generalizing state with
  | nil => simp at member
  | cons head rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, branchRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      rcases List.mem_cons.mp member with equal | tailMember
      · subst spec
        obtain ⟨afterCounter, blocks, afterBlocks, _absorbRun, _squeezeRun,
            _branchExact, blocksLength, recordMember⟩ :=
          run_candidate_exposes_exact_record table state branch head branchRun
        let record : CandidateRecord :=
          { counter := head.counter
            outcome := head.outcome
            baseDigest := state.digest
            endDigest := afterBlocks.digest
            blocks := blocks }
        have included := run_discarded_candidates_preserves_prior_candidates
          table base rest (restoreDigest base branch) final restRun
        have memberFinal : record ∈ final.candidates := by
          apply included record
          change record ∈ branch.candidates
          simpa [record] using recordMember
        exact ⟨record, memberFinal, rfl, rfl, blocksLength⟩
      · exact ih (state := restoreDigest base branch) restRun tailMember

/-- A successful complete q16 scan exposes an exact record for every branch
in its literal `earlier ++ [selected]` plan. -/
theorem run_q16_exposes_member_record
    (table : FixedOracleTable) (state final : EvalState) (tape : Q16Tape)
    (run : runQ16 table state tape = some final)
    (spec : CandidateSpec) (member : spec ∈ tape.earlier ++ [tape.selected]) :
    ∃ record ∈ final.candidates,
      record.counter = spec.counter ∧
      record.outcome = spec.outcome ∧
      record.blocks.length = spec.outcome.blocksUsed := by
  rw [runQ16] at run
  obtain ⟨beforeSelected, earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases List.mem_append.mp member with earlierMember | selectedMember
  · obtain ⟨record, recordMember, counterExact, outcomeExact, lengthExact⟩ :=
      run_discarded_candidates_exposes_member_record table state.digest
        tape.earlier state beforeSelected earlierRun spec earlierMember
    have included := run_candidate_preserves_prior_candidates table
      beforeSelected final tape.selected selectedRun
    exact ⟨record, included record recordMember, counterExact, outcomeExact,
      lengthExact⟩
  · have equal : spec = tape.selected := by simpa using selectedMember
    subst spec
    obtain ⟨afterCounter, blocks, afterBlocks, _absorbRun, _squeezeRun,
        _finalExact, blocksLength, recordMember⟩ :=
      run_candidate_exposes_exact_record table beforeSelected final
        tape.selected selectedRun
    let record : CandidateRecord :=
      { counter := tape.selected.counter
        outcome := tape.selected.outcome
        baseDigest := beforeSelected.digest
        endDigest := afterBlocks.digest
        blocks := blocks }
    exact ⟨record, by simpa [record] using recordMember, rfl, rfl,
      blocksLength⟩

/-- Counter `c <= selected` occurs in the source branch list with exactly the
outcome stored by `FirstCap203Search`. -/
theorem source_spec_mem_q16_plan
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    ({ counter := counter, outcome := search.outcome counter } :
        CandidateSpec) ∈ q16SpecsOfSearch search := by
  rw [q16SpecsOfSearch]
  by_cases selected : counter = search.selectedCounter
  · subst counter
    apply List.mem_append.mpr
    right
    simp [search.selectedOutcome]
  · have earlier : counter.val < search.selectedCounter.val := by omega
    apply List.mem_append.mpr
    left
    unfold earlierSpecs
    rw [List.mem_map]
    let index : Fin search.selectedCounter.val := ⟨counter.val, earlier⟩
    refine ⟨index, ?_, ?_⟩
    · simp [index]
    · let lifted : Fin 64 :=
        ⟨index.val, Nat.lt_trans index.isLt search.selectedCounter.isLt⟩
      have liftedExact : lifted = counter := by
        apply Fin.ext
        simp [lifted, index]
      change
        ({ counter := lifted, outcome := search.outcome lifted } :
          CandidateSpec) =
        { counter := counter, outcome := search.outcome counter }
      rw [liftedExact]

/-- Literal accepted-run decoder extraction through the first cap-203
counter.  The returned byte list is the one actually appended by production
control flow; its length and decoder result are both exact. -/
theorem accepted_q16_run_exposes_exact_decoder_prefix
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    ∃ blocks : List Digest256,
      blocks.length = (search.outcome counter).blocksUsed ∧
      decodeCandidateOutcome counter blocks = some (search.outcome counter) := by
  let spec : CandidateSpec :=
    { counter := counter, outcome := search.outcome counter }
  have specMember : spec ∈
      (q16TapeOfSearch search).earlier ++ [(q16TapeOfSearch search).selected] := by
    simpa [spec, q16SpecsOfSearch, q16TapeOfSearch] using
      source_spec_mem_q16_plan search counter beforeSelected
  obtain ⟨record, recordMember, counterExact, outcomeExact, lengthExact⟩ :=
    run_q16_exposes_member_record table state afterQ16
      (q16TapeOfSearch search) run spec specMember
  refine ⟨record.blocks, ?_, ?_⟩
  · simpa [spec, ← outcomeExact] using lengthExact
  · have exactDecode := decodedState record recordMember
    rw [exactDeterministicDecoders_candidate] at exactDecode
    simpa [spec, counterExact, outcomeExact] using exactDecode

/-- Canonical source byte list for each scanned counter.  Counters after the
selected one are irrelevant and receive the empty list. -/
noncomputable def acceptedQ16CandidateBlocks
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (decodedState : StateCandidatesDecodeAs afterQ16) :
    Fin 64 → List Digest256 := fun counter =>
  if beforeSelected : counter.val ≤ search.selectedCounter.val then
    Classical.choose
      (accepted_q16_run_exposes_exact_decoder_prefix table state afterQ16
        search run decodedState counter beforeSelected)
  else
    []

theorem accepted_q16_candidate_blocks_length
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    (acceptedQ16CandidateBlocks table state afterQ16 search run decodedState
      counter).length = (search.outcome counter).blocksUsed := by
  rw [acceptedQ16CandidateBlocks, dif_pos beforeSelected]
  exact (Classical.choose_spec
    (accepted_q16_run_exposes_exact_decoder_prefix table state afterQ16
      search run decodedState counter beforeSelected)).1

theorem accepted_q16_candidate_blocks_decode
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤ search.selectedCounter.val) :
    decodeCandidateOutcome counter
        (acceptedQ16CandidateBlocks table state afterQ16 search run decodedState
          counter) =
      some (search.outcome counter) := by
  rw [acceptedQ16CandidateBlocks, dif_pos beforeSelected]
  exact (Classical.choose_spec
    (accepted_q16_run_exposes_exact_decoder_prefix table state afterQ16
      search run decodedState counter beforeSelected)).2

/-- Final deterministic source-to-forest reduction.  Successful production
evaluation supplies the byte lists and their decoder results.  Consequently,
to realize the semantic successful forest it is enough to prove pointwise
that the cache-aware scheduler router placed those same bytes in the routed
output forest.  No decoder conclusion is assumed at this boundary. -/
theorem accepted_q16_run_and_routed_bytes_realize_successful_forest
    (table : FixedOracleTable) (state afterQ16 : EvalState)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (run : runQ16 table state (q16TapeOfSearch search) = some afterQ16)
    (decodedState : StateCandidatesDecodeAs afterQ16)
    (initialDigest : Fin 64 → Digest256)
    (forest : AspisK1.V7Tag73SchedulerNativeQ16Replay.TotalQ16DuplexForest)
    (frontierExact : ∀ schedule,
      frontierNodes schedule =
        AspisK1.V7Tag73Q16SemanticFrontierBridge.semanticFrontierNodes
          schedule.positions)
    (routedBytesExact : ∀ counter
      (beforeSelected : counter.val ≤ search.selectedCounter.val)
      (index : Nat)
      (inBlocks : index <
        (acceptedQ16CandidateBlocks table state afterQ16 search run
          decodedState counter).length),
      (acceptedQ16CandidateBlocks table state afterQ16 search run decodedState
        counter)[index] =
        forest.1 counter
          ⟨index, by
            rw [accepted_q16_candidate_blocks_length table state afterQ16
              search run decodedState counter beforeSelected] at inBlocks
            exact Nat.lt_of_lt_of_le inBlocks
              (candidate_outcome_blocks_cap (search.outcome counter))⟩) :
    AspisK1.V7Tag73Q16SuccessfulForestBridge.q16DigestForestSucceeds
      forest.1 := by
  apply scheduler_native_q16_source_plan_realizes_successful_forest
    initialDigest search forest frontierExact
  intro counter beforeSelected
  have outputLength :
      (AspisK1.V7Tag73SchedulerNativeQ16Replay.q16BranchOutputBlocks
        (schedulerNativeQ16BranchOfSpec initialDigest
          { counter := counter, outcome := search.outcome counter })
        forest).length =
        (acceptedQ16CandidateBlocks table state afterQ16 search run decodedState
          counter).length := by
    rw [AspisK1.V7Tag73SchedulerNativeQ16Replay.q16_branch_output_blocks_length,
      accepted_q16_candidate_blocks_length table state afterQ16 search run
        decodedState counter beforeSelected]
    rfl
  have outputExact :
      AspisK1.V7Tag73SchedulerNativeQ16Replay.q16BranchOutputBlocks
          (schedulerNativeQ16BranchOfSpec initialDigest
            { counter := counter, outcome := search.outcome counter })
          forest =
        acceptedQ16CandidateBlocks table state afterQ16 search run decodedState
          counter := by
    rw [AspisK1.V7Tag73SchedulerNativeQ16Replay.q16_branch_output_blocks_eq_take]
    rw [AspisK1.V7Tag73SchedulerNativeQ16Replay.q16_branch_output_blocks_eq_take]
      at outputLength
    apply List.ext_getElem
    · exact outputLength
    · intro index outputBound sourceBound
      rw [List.getElem_take, List.getElem_ofFn]
      exact (routedBytesExact counter beforeSelected index sourceBound).symm
  rw [outputExact]
  exact accepted_q16_candidate_blocks_decode table state afterQ16 search run
    decodedState counter beforeSelected

#print axioms run_discarded_candidates_exposes_member_record
#print axioms run_q16_exposes_member_record
#print axioms source_spec_mem_q16_plan
#print axioms accepted_q16_run_exposes_exact_decoder_prefix
#print axioms accepted_q16_candidate_blocks_length
#print axioms accepted_q16_candidate_blocks_decode
#print axioms accepted_q16_run_and_routed_bytes_realize_successful_forest

end

end AspisK1.V7Tag73ActualQ16DecoderExtraction
