import AspisFormal.K1.V7Tag73ExactCompilerQ16CoordinateStep
import AspisFormal.K1.V7Tag73ExactCompilerQ16InitialDigestMap
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates

/-!
# Exact source coordinates for every accepted q16 branch

This file recovers both halves of every duplex block from the literal
production `runCandidate` execution.  The output half is the deployed decoder
input; the advance half is retained explicitly because it determines the next
SHA coordinate.  The chosen branch execution is also proved to survive into
the checked final candidate ledger, so its decoder result is not assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73ActualQ16DecoderExtraction
open AspisK1.V7Tag73ActualQ16InitialDigest
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates

noncomputable section

/-- Any successful evaluator squeeze exposes the same output/advance table
chain, independently of the logical owner tag. -/
theorem evaluator_squeeze_chain_table_coordinates
    (table : FixedOracleTable) (owner : SqueezeOwner) (first : Nat)
    (state finalState : EvalState) (outputs : List Digest256)
    (chain : EvaluatorSqueezeChain table owner first state outputs finalState) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances := by
  induction chain with
  | done first state =>
      exact ⟨[], rfl, .done state.digest⟩
  | @next first state middle final output outputs head tail ih =>
      obtain ⟨advances, lengthExact, tailCoordinates⟩ := ih
      obtain ⟨outputLookup, advanceLookup, _calls⟩ :=
        squeeze_step_emits_two_distinct_queries table state middle owner first
          output head
      refine ⟨middle.digest :: advances, by simp [lengthExact], ?_⟩
      exact .next
        (by simpa [gammaOutputInput, q16OutputInput, domSqueeze] using
          outputLookup)
        (by simpa [gammaAdvanceInput, q16AdvanceInput, domAdvance] using
          advanceLookup)
        tailCoordinates

theorem squeeze_many_table_coordinates
    (table : FixedOracleTable) (owner : SqueezeOwner) (count : Nat)
    (state finalState : EvalState) (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, finalState)) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances := by
  have chain := evaluator_squeeze_chain_of_run table owner 0 count state
    finalState outputs (by simpa [squeezeMany] using run)
  exact evaluator_squeeze_chain_table_coordinates table owner 0 state
    finalState outputs chain

/-- The exact evaluator chosen for the initial-digest map has its q16 ledger
checked by the literal strict source refinement. -/
theorem exact_operational_q16_evaluator_after_q16_decoded
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
    StateCandidatesDecodeAs (exactOperationalQ16Evaluator input).afterQ16 := by
  let evaluator := exactOperationalQ16Evaluator input
  have wellFormed : TraceWellFormed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) :=
    (checked_refinement_is_well_formed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement).2
  have finalDecoded : StateCandidatesDecodeAs evaluator.finalState :=
    complete_evaluator_final_candidates_decode (exactOperationalTable input)
      (exactOperationalTape input) (exactOperationalRawTrace input) wellFormed
      evaluator
  have included : CandidatesIncluded evaluator.afterQ16 evaluator.finalState :=
    machine_events_work_erased_candidates_included (exactOperationalTable input)
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState evaluator.afterQ16Run
  exact state_candidates_decode_of_included evaluator.afterQ16
    evaluator.finalState included finalDecoded

/-- Both table-coordinate halves and the checked decoder result for one
literal source candidate. -/
structure ExactOperationalQ16BranchCoordinates
    (table : FixedOracleTable) (counter : Fin 64)
    (outcome : CandidateOutcome) (initialDigest : Digest256) where
  outputs : List Digest256
  advances : List Digest256
  outputsLength : outputs.length = outcome.blocksUsed
  advancesLength : advances.length = outputs.length
  tableChain : GammaTableCoordinateChain table initialDigest outputs advances
  decoded : decodeCandidateOutcome counter outputs = some outcome

/-- Every counter through the selected one receives its coordinates from the
same chosen literal candidate execution used by the canonical initial-digest
map. -/
theorem exact_operational_q16_branch_coordinates_exist
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    Nonempty (ExactOperationalQ16BranchCoordinates
      (exactOperationalTable input) counter
      ((exactOperationalTape input).search.outcome counter)
      (exactOperationalQ16InitialDigest input counter)) := by
  let evaluator := exactOperationalQ16Evaluator input
  let witness := Classical.choice
    (accepted_q16_run_exposes_initial_digest (exactOperationalTable input)
      evaluator.prefixState evaluator.afterQ16
      (exactOperationalTape input).search evaluator.q16Run counter
      beforeSelected)
  let spec : CandidateSpec :=
    { counter := counter
      outcome := (exactOperationalTape input).search.outcome counter }
  obtain ⟨afterCounter, outputs, afterBlocks, absorbRun, squeezeRun,
      _afterExact, outputsLength, recordMember⟩ :=
    run_candidate_exposes_exact_record (exactOperationalTable input)
      witness.before witness.after spec (by
        simpa [spec] using witness.candidateRun)
  have afterCounterExact : afterCounter = witness.afterCounter := by
    apply Option.some.inj
    exact absorbRun.symm.trans (by simpa [spec] using witness.absorbRun)
  obtain ⟨advances, advancesLength, tableChain⟩ :=
    squeeze_many_table_coordinates (exactOperationalTable input)
      (.queryCandidate counter)
      ((exactOperationalTape input).search.outcome counter).blocksUsed
      afterCounter afterBlocks outputs (by simpa [spec] using squeezeRun)
  have recordInAfterQ16 :
      ({ counter := counter
         outcome := (exactOperationalTape input).search.outcome counter
         baseDigest := witness.before.digest
         endDigest := afterBlocks.digest
         blocks := outputs } : CandidateRecord) ∈ evaluator.afterQ16.candidates := by
    apply witness.afterIncluded
    simpa [spec] using recordMember
  have decoded := exact_operational_q16_evaluator_after_q16_decoded input
    _ recordInAfterQ16
  refine ⟨{
    outputs := outputs
    advances := advances
    outputsLength := by simpa [spec] using outputsLength
    advancesLength := advancesLength
    tableChain := ?_
    decoded := ?_ }⟩
  · rw [afterCounterExact] at tableChain
    simpa [exactOperationalQ16InitialDigest, acceptedQ16InitialDigest,
      beforeSelected, evaluator, witness] using tableChain
  · rw [exactDeterministicDecoders_candidate] at decoded
    simpa using decoded

/-- Canonical branch coordinate record. -/
noncomputable def exactOperationalQ16BranchCoordinates
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ExactOperationalQ16BranchCoordinates
      (exactOperationalTable input) counter
      ((exactOperationalTape input).search.outcome counter)
      (exactOperationalQ16InitialDigest input counter) :=
  Classical.choice
    (exact_operational_q16_branch_coordinates_exist input counter
      beforeSelected)

#print axioms evaluator_squeeze_chain_table_coordinates
#print axioms squeeze_many_table_coordinates
#print axioms exact_operational_q16_evaluator_after_q16_decoded
#print axioms exact_operational_q16_branch_coordinates_exist

end

end AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
