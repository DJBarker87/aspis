import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay
import AspisFormal.K1.V7Tag73Q16CandidateParserExact

/-!
# Segment-stable replay of one raw q16 branch

The exposure-indexed candidate controller updates all 64 branch cells at
every fresh root answer.  This module proves that one selected cell is stable
across any aligned machine-fresh record segment that avoids its unique
candidate input and its two current duplex sibling inputs.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16BranchRecordReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16CandidateParserExact
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A raw input other than the selected counter's unique candidate and the
two current sibling inputs leaves that branch cell unchanged. -/
theorem update_raw_q16_branches_preserves_pending_of_irrelevant
    (base digest answer : Digest256) (counter : Fin 64) (block : Nat)
    (outputSeen : Bool) (advanceAnswer : Option Digest256)
    (branches : Fin 64 → RawQ16BranchPhase) (input : ShaInput)
    (phaseExact : branches counter =
      .pending digest block outputSeen advanceAnswer)
    (candidateNe : input ≠
      bytes base ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat counter.val])
    (outputNe : input ≠ bytes digest ++ [domSqueeze])
    (advanceNe : input ≠ bytes digest ++ [domAdvance]) :
    updateRawQ16Branches base branches input answer counter =
      .pending digest block outputSeen advanceAnswer := by
  have candidateParsedNe :
      q16CandidateOfBaseInput? base input ≠ some counter := by
    intro parsed
    exact candidateNe (q16_candidate_of_base_input_exact base input counter
      parsed)
  simp [updateRawQ16Branches, candidateParsedNe, phaseExact,
    RawQ16BranchPhase.afterInput, outputNe, advanceNe]

/-- Replay an irrelevant aligned segment while retaining the complete tracked
key/base state and the exact selected branch phase.  Work acceptance and all
other branch cells may evolve. -/
theorem aligned_machine_records_preserve_pending_q16_branch
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (key : RawFinalWorkKey) (base digest : Digest256)
    (counter : Fin 64) (block : Nat)
    (outputSeen : Bool) (advanceAnswer : Option Digest256) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory)
      (workSeen : Bool) (branches : Fin 64 → RawQ16BranchPhase),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16CandidateController globalOracleCalls transitionFuel
            anchor) state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records, causalInput? record ≠
        some (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val])) →
      (∀ record ∈ records, causalInput? record ≠
        some (bytes digest ++ [domSqueeze])) →
      (∀ record ∈ records, causalInput? record ≠
        some (bytes digest ++ [domAdvance])) →
      state.memory = .tracked key workSeen (some base) branches →
      branches counter = .pending digest block outputSeen advanceAnswer →
      ∃ laterWorkSeen laterBranches,
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16CandidateController globalOracleCalls transitionFuel
            anchor) records state).memory =
          .tracked key laterWorkSeen (some base) laterBranches ∧
        laterBranches counter =
          .pending digest block outputSeen advanceAnswer := by
  intro records
  induction records with
  | nil =>
      intro state workSeen branches _aligned _onlyMachine _candidateAvoids
        _outputAvoids _advanceAvoids stateMemory phaseExact
      exact ⟨workSeen, branches, by
        simpa only [indexed_state_after_records_nil] using stateMemory,
        phaseExact⟩
  | cons head tail ih =>
      intro state workSeen branches aligned onlyMachine candidateAvoids
        outputAvoids advanceAvoids stateMemory phaseExact
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have candidateNe : input ≠
          bytes base ++ [domAbsorb, queryCandidateLabel,
            UInt8.ofNat counter.val] := by
        intro equal
        apply candidateAvoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      have outputNe : input ≠ bytes digest ++ [domSqueeze] := by
        intro equal
        apply outputAvoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      have advanceNe : input ≠ bytes digest ++ [domAdvance] := by
        intro equal
        apply advanceAvoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      let controller := finalWorkQ16CandidateController globalOracleCalls
        transitionFuel anchor
      let next := controller.afterAnswer transitionFuel state answer
      let nextWorkSeen := workSeen || decide (input = key.workInput)
      let nextBranches := updateRawQ16Branches base branches input answer
      have nextMemory : next.memory =
          .tracked key nextWorkSeen (some base) nextBranches := by
        simp [next, nextWorkSeen, nextBranches, controller,
          finalWorkQ16CandidateController,
          IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
          stateMemory, inputExact]
      have nextPhase : nextBranches counter =
          .pending digest block outputSeen advanceAnswer := by
        exact update_raw_q16_branches_preserves_pending_of_irrelevant
          base digest answer counter block outputSeen advanceAnswer branches
          input phaseExact candidateNe outputNe advanceNe
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have tailCandidateAvoids : ∀ record ∈ tail, causalInput? record ≠
          some (bytes base ++ [domAbsorb, queryCandidateLabel,
            UInt8.ofNat counter.val]) := by
        intro record member
        exact candidateAvoids record (by simp [member])
      have tailOutputAvoids : ∀ record ∈ tail,
          causalInput? record ≠ some (bytes digest ++ [domSqueeze]) := by
        intro record member
        exact outputAvoids record (by simp [member])
      have tailAdvanceAvoids : ∀ record ∈ tail,
          causalInput? record ≠ some (bytes digest ++ [domAdvance]) := by
        intro record member
        exact advanceAvoids record (by simp [member])
      rw [indexed_state_after_records_cons]
      exact ih next nextWorkSeen nextBranches tailAligned tailOnly
        tailCandidateAvoids tailOutputAvoids tailAdvanceAvoids nextMemory
        nextPhase

#print axioms update_raw_q16_branches_preserves_pending_of_irrelevant
#print axioms aligned_machine_records_preserve_pending_q16_branch

end

end AspisK1.V7Tag73Q16BranchRecordReplay
