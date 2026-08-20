import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullOrderedChildPositions

/-! Ordered-list consequences of the exact generated radix group trace. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullGroupTraceLists

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullOrderedChildPositions

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- One source-ordered mask iteration, retaining both cursor endpoints and
the exact four-child hash witness produced by the unchanged Rust loop. -/
structure RawGroupStepSummary
    (sha256 : List ModelByte → Digest32)
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec) where
  present : Std.U8
  nextBefore : GeneratedDigestVec
  nextAfter : GeneratedDigestVec
  startNodePos : Std.Usize
  startValuePos : Std.Usize
  endNodePos : Std.Usize
  endValuePos : Std.Usize
  witness : RawChildHashWitness sha256 nodeBytes level present startNodePos
    startValuePos nextBefore nextAfter endNodePos endValuePos

def RawGroupStepSummary.digest
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (summary : RawGroupStepSummary sha256 nodeBytes level) :
    GeneratedDigest :=
  summary.witness.digest

/-- The list summaries form one cursor- and scratch-vector-contiguous run. -/
inductive OrderedGroupStepChain
    (sha256 : List ModelByte → Digest32)
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec) :
    GeneratedDigestVec → Std.Usize → Std.Usize →
      List (RawGroupStepSummary sha256 nodeBytes level) →
      GeneratedDigestVec → Std.Usize → Std.Usize → Prop
  | nil (next : GeneratedDigestVec) (nodePos valuePos : Std.Usize) :
      OrderedGroupStepChain sha256 nodeBytes level next nodePos valuePos []
        next nodePos valuePos
  | cons (summary : RawGroupStepSummary sha256 nodeBytes level)
      (tail : List (RawGroupStepSummary sha256 nodeBytes level))
      (terminalNext : GeneratedDigestVec)
      (terminalNodePos terminalValuePos : Std.Usize)
      (rest : OrderedGroupStepChain sha256 nodeBytes level
        summary.nextAfter summary.endNodePos summary.endValuePos tail
        terminalNext terminalNodePos terminalValuePos) :
      OrderedGroupStepChain sha256 nodeBytes level
        summary.nextBefore summary.startNodePos summary.startValuePos
        (summary :: tail) terminalNext terminalNodePos terminalValuePos

def groupMasks
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (steps : List (RawGroupStepSummary sha256 nodeBytes level)) :
    List Std.U8 :=
  steps.map RawGroupStepSummary.present

def groupDigests
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (steps : List (RawGroupStepSummary sha256 nodeBytes level)) :
    List GeneratedDigest :=
  steps.map RawGroupStepSummary.digest

/-- Flat, source-ordered view of one successful mask loop, including the
terminal swap and the production all-live-values-consumed check. -/
structure RawGroupTraceListView
    (sha256 : List ModelByte → Digest32)
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec)
    (iter : core.slice.iter.Iter Std.U8)
    (initialNext : GeneratedDigestVec)
    (initialNodePos initialValuePos : Std.Usize)
    (initialPending : Option Bool)
    (finalLevel finalNext : GeneratedDigestVec)
    (finalNodePos : Std.Usize) (finalPending : Option Bool)
    (steps : List (RawGroupStepSummary sha256 nodeBytes level))
    (terminalNext : GeneratedDigestVec)
    (terminalValuePos : Std.Usize) : Prop where
  chain : OrderedGroupStepChain sha256 nodeBytes level initialNext
    initialNodePos initialValuePos steps terminalNext finalNodePos
    terminalValuePos
  masks_exact : groupMasks steps = iter.slice.val.drop iter.i
  produced_exact :
    terminalNext.val = initialNext.val ++ groupDigests steps
  final_level_exact : finalLevel = terminalNext
  terminal_swap_exact : finalNext = level
  all_values_consumed : terminalValuePos = alloc.vec.Vec.len level
  pending_exact : finalPending = initialPending

private theorem iterator_next_some_drop_exact
    (iter iter' : core.slice.iter.Iter Std.U8) (present : Std.U8)
    (hrun : core.slice.iter.IteratorSliceIter.next iter =
      .ok (some present, iter')) :
    present :: iter'.slice.val.drop iter'.i =
      iter.slice.val.drop iter.i := by
  unfold core.slice.iter.IteratorSliceIter.next at hrun
  split at hrun
  next active =>
    have output := Result.ok.inj hrun
    have present_eq : present = iter.slice[iter.i] := by
      simpa using congrArg (fun pair => pair.1.get!) output.symm
    have iter_eq : iter' =
        ({ slice := iter.slice, i := iter.i + 1 } :
          core.slice.iter.Iter Std.U8) := by
      simpa using congrArg Prod.snd output.symm
    subst iter'
    rw [List.drop_eq_getElem_cons active]
    congr 1
  next inactive =>
    simp at hrun

private theorem push_success_exact
    (level level' : GeneratedDigestVec) (digest : GeneratedDigest)
    (hrun : alloc.vec.Vec.push level digest = .ok level') :
    level'.val = level.val ++ [digest] := by
  unfold alloc.vec.Vec.push at hrun
  dsimp only at hrun
  split at hrun
  · injection hrun with heq
    subst level'
    simp [List.concat_eq_append]
  · simp at hrun

theorem child_witness_appends_exact_digest
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {present : Std.U8} {startNodePos startValuePos : Std.Usize}
    {next finalNext : GeneratedDigestVec}
    {finalNodePos finalValuePos : Std.Usize}
    (witness : RawChildHashWitness sha256 nodeBytes level present
      startNodePos startValuePos next finalNext finalNodePos finalValuePos) :
    finalNext.val = next.val ++ [witness.digest] :=
  push_success_exact next finalNext witness.digest witness.push_run

theorem raw_group_trace_yields_list_view
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    (trace : RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos
      pending finalLevel finalNext finalNodePos finalPending) :
    ∃ (steps : List (RawGroupStepSummary sha256 nodeBytes level))
        (terminalNext : GeneratedDigestVec) (terminalValuePos : Std.Usize),
      RawGroupTraceListView sha256 nodeBytes level iter next nodePos valuePos
        pending finalLevel finalNext finalNodePos finalPending steps
        terminalNext terminalValuePos := by
  induction trace with
  | done iter next nodePos valuePos pending iterator_finished values_consumed =>
      refine ⟨[], next, valuePos, {
        chain := OrderedGroupStepChain.nil next nodePos valuePos
        masks_exact := ?_
        produced_exact := by simp [groupDigests]
        final_level_exact := by simp [core.mem.swap]
        terminal_swap_exact := by simp [core.mem.swap]
        all_values_consumed := values_consumed
        pending_exact := rfl }⟩
      simp only [groupMasks, List.map_nil]
      exact (List.drop_eq_nil_iff.mpr iterator_finished).symm
  | step iter iter' present next next' finalLevel finalNext nodePos valuePos
      nodePos' valuePos' finalNodePos pending pending' finalPending input
      iterator_next input_init children_run pending_unchanged children tail ih =>
      let summary : RawGroupStepSummary sha256 nodeBytes level := {
        present := present
        nextBefore := next
        nextAfter := next'
        startNodePos := nodePos
        startValuePos := valuePos
        endNodePos := nodePos'
        endValuePos := valuePos'
        witness := children }
      rcases ih with ⟨tailSteps, terminalNext, terminalValuePos, tailView⟩
      refine ⟨summary :: tailSteps, terminalNext, terminalValuePos, {
        chain := OrderedGroupStepChain.cons summary tailSteps terminalNext
          finalNodePos terminalValuePos tailView.chain
        masks_exact := ?_
        produced_exact := ?_
        final_level_exact := tailView.final_level_exact
        terminal_swap_exact := tailView.terminal_swap_exact
        all_values_consumed := tailView.all_values_consumed
        pending_exact := tailView.pending_exact.trans pending_unchanged }⟩
      · simp only [groupMasks, List.map_cons, summary]
        change present :: groupMasks tailSteps = iter.slice.val.drop iter.i
        rw [tailView.masks_exact]
        exact iterator_next_some_drop_exact iter iter' present iterator_next
      · have appended := child_witness_appends_exact_digest children
        rw [tailView.produced_exact, appended]
        simp [groupDigests, RawGroupStepSummary.digest, summary,
          List.append_assoc]

theorem group_summary_count_eq_remaining_masks
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    {steps : List (RawGroupStepSummary sha256 nodeBytes level)}
    {terminalNext : GeneratedDigestVec} {terminalValuePos : Std.Usize}
    (view : RawGroupTraceListView sha256 nodeBytes level iter next nodePos
      valuePos pending finalLevel finalNext finalNodePos finalPending steps
      terminalNext terminalValuePos) :
    steps.length = iter.slice.val.length - iter.i := by
  have lengths := congrArg List.length view.masks_exact
  simpa [groupMasks] using lengths

theorem group_digest_count_eq_summary_count
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (steps : List (RawGroupStepSummary sha256 nodeBytes level)) :
    (groupDigests steps).length = steps.length := by
  simp [groupDigests]

theorem summary_mask_at_is_exact
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    {steps : List (RawGroupStepSummary sha256 nodeBytes level)}
    {terminalNext : GeneratedDigestVec} {terminalValuePos : Std.Usize}
    (view : RawGroupTraceListView sha256 nodeBytes level iter next nodePos
      valuePos pending finalLevel finalNext finalNodePos finalPending steps
      terminalNext terminalValuePos)
    (index : Nat) (index_lt : index < steps.length) :
    (steps.get ⟨index, index_lt⟩).present =
      (iter.slice.val.drop iter.i)[index]! := by
  rw [← view.masks_exact]
  simp [groupMasks, index_lt]

theorem summary_child_positions_are_exact
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (summary : RawGroupStepSummary sha256 nodeBytes level) :
    OrderedChildPositionFacts nodeBytes level summary.present 4
      summary.startNodePos summary.startValuePos summary.witness.children
      summary.endNodePos summary.endValuePos :=
  AspisV5MerkleUnchangedFullOrderedChildPositions.OrderedChildReads.position_facts
    summary.witness.ordered_reads

theorem final_level_is_initial_next_plus_one_digest_per_mask
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    {steps : List (RawGroupStepSummary sha256 nodeBytes level)}
    {terminalNext : GeneratedDigestVec} {terminalValuePos : Std.Usize}
    (view : RawGroupTraceListView sha256 nodeBytes level iter next nodePos
      valuePos pending finalLevel finalNext finalNodePos finalPending steps
      terminalNext terminalValuePos) :
    finalLevel.val = next.val ++ groupDigests steps := by
  exact congrArg Subtype.val view.final_level_exact |>.trans view.produced_exact

#print axioms raw_group_trace_yields_list_view
#print axioms summary_mask_at_is_exact
#print axioms summary_child_positions_are_exact

end AspisV5MerkleUnchangedFullGroupTraceLists
