import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullGroupTraceLists
import V5MerkleUnchangedFullTopologyAccessors

/-! Ordered-list consequences of the exact generated outer Merkle loop. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullLevelTraceLists

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullTopologyAccessors
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleTopologyConstructorModel
open AspisV5TopologyConstruction

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

def remainingPlanLevels
    (iter : core.ops.range.Range Std.Usize) : List Nat :=
  List.range' iter.start.val (iter.end.val - iter.start.val)

/-- One exact outer-loop iteration.  The generated level vector is consumed
according to one topology mask slice, and the ordered group summaries produce
the complete next level. -/
structure RawLevelStepSummary
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) where
  planLevel : Std.Usize
  levelBefore : GeneratedDigestVec
  nextBefore : GeneratedDigestVec
  nextCleared : GeneratedDigestVec
  levelAfter : GeneratedDigestVec
  nextAfter : GeneratedDigestVec
  startNodePos : Std.Usize
  endNodePos : Std.Usize
  pendingBefore : Option Bool
  pendingAfter : Option Bool
  masks : Slice Std.U8
  maskIter : core.slice.iter.Iter Std.U8
  clear_run : alloc.vec.Vec.clear Global nextBefore = .ok nextCleared
  masks_run : aspis_core.merkle.Radix4BinaryCapTopology.impl.group_masks topology
    planLevel = .ok (some masks)
  mask_iterator_run :
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      masks = .ok maskIter
  group_trace : RawGroupTrace sha256 nodeBytes levelBefore maskIter nextCleared
    startNodePos 0#usize pendingBefore levelAfter nextAfter endNodePos
    pendingAfter
  groupSteps : List (RawGroupStepSummary sha256 nodeBytes levelBefore)
  groupTerminalNext : GeneratedDigestVec
  groupTerminalValuePos : Std.Usize
  group_view : RawGroupTraceListView sha256 nodeBytes levelBefore maskIter
    nextCleared startNodePos 0#usize pendingBefore levelAfter nextAfter
    endNodePos pendingAfter groupSteps groupTerminalNext
    groupTerminalValuePos
  cleared_empty : nextCleared.val = []
  masks_exact : groupMasks groupSteps = masks.val
  parents_exact : levelAfter.val = groupDigests groupSteps
  scratch_after_exact : nextAfter = levelBefore

/-- Source states of adjacent outer-loop summaries agree exactly. -/
inductive OrderedLevelStepChain
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) :
    GeneratedDigestVec → GeneratedDigestVec → Std.Usize → Option Bool →
      List (RawLevelStepSummary sha256 root nodeBytes topology binaryDepth) →
      GeneratedDigestVec → GeneratedDigestVec → Std.Usize → Option Bool → Prop
  | nil (level next : GeneratedDigestVec) (nodePos : Std.Usize)
      (pending : Option Bool) :
      OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth level
        next nodePos pending [] level next nodePos pending
  | cons (summary : RawLevelStepSummary sha256 root nodeBytes topology
        binaryDepth)
      (tail : List (RawLevelStepSummary sha256 root nodeBytes topology
        binaryDepth))
      (finalLevel finalNext : GeneratedDigestVec) (finalNodePos : Std.Usize)
      (finalPending : Option Bool)
      (rest : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
        summary.levelAfter summary.nextAfter summary.endNodePos
        summary.pendingAfter tail finalLevel finalNext finalNodePos
        finalPending) :
      OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
        summary.levelBefore summary.nextBefore summary.startNodePos
        summary.pendingBefore (summary :: tail) finalLevel finalNext
        finalNodePos finalPending

def levelPlans
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)) : List Nat :=
  steps.map (fun summary => summary.planLevel.val)

/-- Flat view of a complete accepted outer loop. -/
structure RawLevelTraceListView
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32)
    (iter : core.ops.range.Range Std.Usize)
    (initialLevel initialNext : GeneratedDigestVec)
    (initialNodePos : Std.Usize) (initialPending : Option Bool)
    (finalLevel finalNext : GeneratedDigestVec)
    (steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)) (terminalNodePos : Std.Usize) : Prop where
  chain : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
    initialLevel initialNext initialNodePos initialPending steps finalLevel
    finalNext terminalNodePos none
  plans_exact : levelPlans steps = remainingPlanLevels iter
  root_witness : RawFinalRootWitness sha256 root nodeBytes topology
    binaryDepth finalLevel terminalNodePos

private theorem range_next_some_exact
    (iter iter' : core.ops.range.Range Std.Usize) (planLevel : Std.Usize)
    (hrun : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some planLevel, iter')) :
    iter.start.val < iter.end.val ∧ planLevel = iter.start ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have active : iter.start.val < iter.end.val := by
    by_contra notActive
    have finished : iter.end.val ≤ iter.start.val := by omega
    have spec := core.iter.range.IteratorRange.next_Usize_none_spec iter
      finished
    rcases Aeneas.Std.WP.spec_imp_exists spec with
      ⟨⟨option, stopped⟩, stoppedRun, optionNone, stoppedEq⟩
    have outputs := Result.ok.inj (stoppedRun.symm.trans hrun)
    have options := congrArg Prod.fst outputs
    simp [optionNone] at options
  have spec := core.iter.range.IteratorRange.next_Usize_some_spec iter active
  rcases Aeneas.Std.WP.spec_imp_exists spec with
    ⟨⟨option, advanced⟩, advancedRun, optionEq, startEq, endEq⟩
  have outputs := Result.ok.inj (advancedRun.symm.trans hrun)
  have options := congrArg Prod.fst outputs
  have iterators := congrArg Prod.snd outputs
  have planEq : planLevel = iter.start := by
    simpa [optionEq] using options.symm
  have advancedEq : iter' = advanced := iterators.symm
  exact ⟨active, planEq,
    advancedEq ▸ startEq,
    advancedEq ▸ endEq⟩

private theorem plan_levels_step_exact
    (iter iter' : core.ops.range.Range Std.Usize) (planLevel : Std.Usize)
    (facts : iter.start.val < iter.end.val ∧ planLevel = iter.start ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end) :
    planLevel.val :: remainingPlanLevels iter' = remainingPlanLevels iter := by
  rcases facts with ⟨active, planEq, nextStart, sameEnd⟩
  unfold remainingPlanLevels
  rw [sameEnd, nextStart, planEq]
  have span : iter.end.val - iter.start.val =
      (iter.end.val - (iter.start.val + 1)) + 1 := by omega
  rw [span, List.range'_succ]

private theorem clear_success_empty
    (input output : GeneratedDigestVec)
    (hrun : alloc.vec.Vec.clear Global input = .ok output) :
    output.val = [] := by
  unfold alloc.vec.Vec.clear at hrun
  simp only at hrun
  have cleared := Result.ok.inj hrun
  have values := congrArg (fun value : GeneratedDigestVec => value.val) cleared
  simpa [alloc.vec.Vec.new] using values.symm

private theorem mask_iterator_exact
    (masks : Slice Std.U8) (iter : core.slice.iter.Iter Std.U8)
    (hrun :
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        masks = .ok iter) :
    iter = { slice := masks, i := 0 } := by
  unfold
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    at hrun
  exact (Result.ok.inj hrun).symm

theorem raw_level_trace_yields_list_view
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {iter : core.ops.range.Range Std.Usize}
    {level next finalLevel finalNext : GeneratedDigestVec}
    {nodePos : Std.Usize} {pending : Option Bool}
    (trace : RawLevelTrace sha256 root nodeBytes topology binaryDepth iter
      level next nodePos pending finalLevel finalNext) :
    ∃ (steps : List (RawLevelStepSummary sha256 root nodeBytes topology
          binaryDepth)) (terminalNodePos : Std.Usize),
      RawLevelTraceListView sha256 root nodeBytes topology binaryDepth iter
        level next nodePos pending finalLevel finalNext steps
        terminalNodePos := by
  induction trace with
  | done iter level next nodePos pending iterator_finished pending_none
      root_check =>
      subst pending
      refine ⟨[], nodePos, {
        chain := OrderedLevelStepChain.nil level next nodePos none
        plans_exact := ?_
        root_witness := root_check }⟩
      simp [levelPlans, remainingPlanLevels,
        Nat.sub_eq_zero_of_le iterator_finished]
  | step iter iter' planLevel level next nextCleared level' next' finalLevel
      finalNext nodePos nodePos' pending pending' masks maskIter iterator_next
      clear_run masks_run mask_iterator_run groups_run groups tail ih =>
      have rangeFacts := range_next_some_exact iter iter' planLevel
        iterator_next
      rcases raw_group_trace_yields_list_view groups with
        ⟨groupSteps, groupTerminalNext, groupTerminalValuePos, groupView⟩
      have clearedEmpty := clear_success_empty next nextCleared clear_run
      have maskIterEq := mask_iterator_exact masks maskIter mask_iterator_run
      have masksExact : groupMasks groupSteps = masks.val := by
        rw [groupView.masks_exact, maskIterEq]
        simp
      have parentsExact : level'.val = groupDigests groupSteps := by
        have output := final_level_is_initial_next_plus_one_digest_per_mask
          groupView
        simpa [clearedEmpty] using output
      have scratchExact : next' = level := groupView.terminal_swap_exact
      let summary : RawLevelStepSummary sha256 root nodeBytes topology
          binaryDepth := {
        planLevel := planLevel
        levelBefore := level
        nextBefore := next
        nextCleared := nextCleared
        levelAfter := level'
        nextAfter := next'
        startNodePos := nodePos
        endNodePos := nodePos'
        pendingBefore := pending
        pendingAfter := pending'
        masks := masks
        maskIter := maskIter
        clear_run := clear_run
        masks_run := masks_run
        mask_iterator_run := mask_iterator_run
        group_trace := groups
        groupSteps := groupSteps
        groupTerminalNext := groupTerminalNext
        groupTerminalValuePos := groupTerminalValuePos
        group_view := groupView
        cleared_empty := clearedEmpty
        masks_exact := masksExact
        parents_exact := parentsExact
        scratch_after_exact := scratchExact }
      rcases ih with ⟨tailSteps, terminalNodePos, tailView⟩
      refine ⟨summary :: tailSteps, terminalNodePos, {
        chain := OrderedLevelStepChain.cons summary tailSteps finalLevel
          finalNext terminalNodePos none tailView.chain
        plans_exact := ?_
        root_witness := tailView.root_witness }⟩
      change planLevel.val :: levelPlans tailSteps = remainingPlanLevels iter
      rw [tailView.plans_exact]
      exact plan_levels_step_exact iter iter' planLevel rangeFacts

theorem level_plan_count_is_exact
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {iter : core.ops.range.Range Std.Usize}
    {level next finalLevel finalNext : GeneratedDigestVec}
    {nodePos : Std.Usize} {pending : Option Bool}
    {terminalNodePos : Std.Usize}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (view : RawLevelTraceListView sha256 root nodeBytes topology binaryDepth
      iter level next nodePos pending finalLevel finalNext steps
      terminalNodePos) :
    steps.length = iter.end.val - iter.start.val := by
  have lengths := congrArg List.length view.plans_exact
  simpa [levelPlans, remainingPlanLevels] using lengths

theorem level_plans_have_no_duplicates
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {iter : core.ops.range.Range Std.Usize}
    {level next finalLevel finalNext : GeneratedDigestVec}
    {nodePos : Std.Usize} {pending : Option Bool}
    {terminalNodePos : Std.Usize}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (view : RawLevelTraceListView sha256 root nodeBytes topology binaryDepth
      iter level next nodePos pending finalLevel finalNext steps
      terminalNodePos) :
    (levelPlans steps).Nodup := by
  rw [view.plans_exact]
  exact List.nodup_range'

/-- For a topology produced by the released constructor, the mask bytes in
each flattened source step are exactly the maintained masks for that plan
level. -/
theorem level_summary_masks_follow_shared_plan
    (queries : Finset V5Query)
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (summary : RawLevelStepSummary sha256 root nodeBytes topology binaryDepth)
    (fields : FullExactConstructedTopologyFields queries topology)
    (level_lt : summary.planLevel.val < 8) :
    summary.masks.val.map (fun mask => mask.val) =
      sharedGroupMasks queries summary.planLevel.val :=
  group_masks_follow_shared_plan queries topology summary.planLevel
    summary.masks fields level_lt summary.masks_run

#print axioms raw_level_trace_yields_list_view
#print axioms level_summary_masks_follow_shared_plan

end AspisV5MerkleUnchangedFullLevelTraceLists
