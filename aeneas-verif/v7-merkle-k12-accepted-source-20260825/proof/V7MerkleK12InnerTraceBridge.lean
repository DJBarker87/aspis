import V7MerkleK12TraversalBridge

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Direct inversion of the translated sparse-frontier inner loop

The lemmas here inspect `verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body`
itself.  They do not postulate a semantic loop invariant.
-/

namespace AspisV7MerkleK12InnerTraceBridge

theorem u32_shr_one_i32_val (position : Std.U32) :
    (Std.U32.wrapping_shr position 1#i32).val = position.val / 2 := by
  unfold Std.U32.wrapping_shr UScalar.wrapping_shr
  norm_num
  change (BitVec.ushiftRight position.bv 1).toNat =
    position.bv.toNat / 2
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem u32_and_one_val (position : Std.U32) :
    (position &&& 1#u32).val = position.val % 2 := by
  simp only [UScalar.val_and, UScalar.ofNatCore_val_eq,
    Nat.and_one_is_mod]

theorem u32_shr_one_success_val (position output : Std.U32)
    (run : position >>> 1#i32 = (.ok output : Result Std.U32)) :
    output.val = position.val / 2 := by
  have canonical : position >>> 1#i32 =
      (.ok (Std.U32.wrapping_shr position 1#i32) : Result Std.U32) := by
    rfl
  have outputExact := Result.ok.inj (canonical.symm.trans run)
  rw [← outputExact]
  exact u32_shr_one_i32_val position

theorem testBit_zero_false_of_and_one_eq_zero (position : Std.U32)
    (even : position &&& 1#u32 = 0#u32) :
    position.val.testBit 0 = false := by
  have modulo : position.val % 2 = 0 := by
    have values := congrArg UScalar.val even
    simpa [u32_and_one_val] using values
  simp [Nat.testBit_zero, modulo]

theorem testBit_zero_true_of_and_one_ne_zero (position : Std.U32)
    (odd : position &&& 1#u32 ≠ 0#u32) :
    position.val.testBit 0 = true := by
  have moduloNonzero : position.val % 2 ≠ 0 := by
    intro modulo
    apply odd
    apply UScalar.eq_of_val_eq
    simpa [u32_and_one_val] using modulo
  have moduloBound : position.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have modulo : position.val % 2 = 1 := by omega
  simp [Nat.testBit_zero, modulo]

def resultDoneNone {state left middle : Type}
    (result : Result (ControlFlow state (left × middle × Option Bool))) :
    Bool :=
  match result with
  | .ok (.done (_, _, none)) => true
  | _ => false

theorem resultDoneNone_bind_eq_false
    {state left middle value : Type}
    (computation : Result value)
    (continuation : value →
      Result (ControlFlow state (left × middle × Option Bool)))
    (continuationFalse : ∀ output,
      resultDoneNone (continuation output) = false) :
    resultDoneNone (do
      let output ← computation
      continuation output) = false := by
  cases computation with
  | ok output => exact continuationFalse output
  | fail error => rfl
  | div => rfl

theorem resultDoneNone_bind_pair_eq_false
    {state left middle first second : Type}
    (computation : Result (first × second))
    (continuation : first → second →
      Result (ControlFlow state (left × middle × Option Bool)))
    (continuationFalse : ∀ first second,
      resultDoneNone (continuation first second) = false) :
    resultDoneNone (do
      let (first, second) ← computation
      continuation first second) = false := by
  cases computation with
  | ok output =>
      rcases output with ⟨first, second⟩
      exact continuationFalse first second
  | fail error => rfl
  | div => rfl

theorem resultDoneNone_bind_triple_eq_false
    {state left middle first second third : Type}
    (computation : Result (first × second × third))
    (continuation : first → second → third →
      Result (ControlFlow state (left × middle × Option Bool)))
    (continuationFalse : ∀ first second third,
      resultDoneNone (continuation first second third) = false) :
    resultDoneNone (do
      let (first, second, third) ← computation
      continuation first second third) = false := by
  cases computation with
  | ok output =>
      rcases output with ⟨first, second, third⟩
      exact continuationFalse first second third
  | fail error => rfl
  | div => rfl

theorem resultDoneNone_ite_eq_false
    {state left middle : Type}
    (condition : Prop) [Decidable condition]
    (ifTrue ifFalse :
      Result (ControlFlow state (left × middle × Option Bool)))
    (trueFalse : resultDoneNone ifTrue = false)
    (falseFalse : resultDoneNone ifFalse = false) :
    resultDoneNone (if condition then ifTrue else ifFalse) = false := by
  by_cases condition <;> simp_all

/-- No active inner iteration can be the normal `pending = none` terminal.
All active successful branches either continue after hashing/pushing or return
the fail-closed `some false`. -/
theorem exact_inner_body_active_cannot_done_none
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputNext : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos index outputNodePos : Std.Usize)
    (active : index < alloc.vec.Vec.len level)
    (run :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level next nodePos index =
        .ok (.done (outputNext, outputNodePos, none))) : False := by
  have projected := congrArg resultDoneNone run
  have activeProjection :
      resultDoneNone
        (V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level next nodePos index) = false := by
    unfold
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    simp only [if_pos active]
    repeat'
      first
      | apply resultDoneNone_bind_triple_eq_false
        intro first second third
      | apply resultDoneNone_bind_pair_eq_false
        intro first second
      | apply resultDoneNone_bind_eq_false
        intro value
      | apply resultDoneNone_ite_eq_false
      | rfl
  rw [activeProjection] at projected
  exact Bool.noConfusion projected

/-- Normal inner-body termination is exactly exhaustion of the current level,
and preserves the scratch vector and frontier cursor. -/
theorem exact_inner_body_done_none_is_exhausted
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputNext : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos index outputNodePos : Std.Usize)
    (run :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level next nodePos index =
        .ok (.done (outputNext, outputNodePos, none))) :
    level.val.length ≤ index.val ∧ outputNext = next ∧
      outputNodePos = nodePos := by
  have inactive : ¬ index < alloc.vec.Vec.len level := by
    intro active
    exact exact_inner_body_active_cannot_done_none hash c1Nodes c2Nodes level
      next outputNext nodePos index outputNodePos active run
  have exhausted : level.val.length ≤ index.val := by
    change ¬ index.val < level.val.length at inactive
    omega
  have terminalRun := run
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at terminalRun
  simp only [if_neg inactive] at terminalRun
  have exactOutput := Result.ok.inj terminalRun
  have nextExact : next = outputNext :=
    congrArg (fun flow => match flow with
      | .done output => output.1
      | .cont _ => next) exactOutput
  have nodePosExact : nodePos = outputNodePos :=
    congrArg (fun flow => match flow with
      | .done output => output.2.1
      | .cont _ => nodePos) exactOutput
  exact ⟨exhausted, nextExact.symm, nodePosExact.symm⟩

/-! ## Cursor-indexed edge trace

The generated loop walks an immutable `level` with a `usize` cursor.  This
intermediate trace keeps that cursor explicit.  It is the convenient target
for direct body inversion: a frontier branch advances by one entry and an
adjacent-pair branch advances by two.  The conversion below then removes the
cursor and yields the list-consuming `ExactInnerEdgeTrace` used by the path
construction.
-/

theorem list_drop_eq_getElem_cons {T : Type} [Inhabited T]
    (values : List T) (index : Nat)
    (bound : index < values.length) :
    values.drop index = values[index]! :: values.drop (index + 1) := by
  induction values generalizing index with
  | nil => simp at bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            (inductionHypothesis index bound)

theorem list_drop_eq_two_getElem_cons {T : Type} [Inhabited T]
    (values : List T)
    (index : Nat) (bound : index + 1 < values.length) :
    values.drop index = values[index]! :: values[index + 1]! ::
      values.drop (index + 2) := by
  calc
    values.drop index = values[index]! :: values.drop (index + 1) :=
      list_drop_eq_getElem_cons values index (by omega)
    _ = values[index]! :: values[index + 1]! ::
        values.drop ((index + 1) + 1) := by
      rw [list_drop_eq_getElem_cons values (index + 1) bound]
    _ = values[index]! :: values[index + 1]! ::
        values.drop (index + 2) := by simp [Nat.add_assoc]

theorem usize_add_success_val (left right output : Std.Usize)
    (run : left + right = (.ok output : Result Std.Usize)) :
    output.val = left.val + right.val := by
  have specification := @UScalar.add_equiv UScalarTy.Usize left right
  rw [run] at specification
  exact specification.2.1

theorem u32_add_success_val (left right output : Std.U32)
    (run : left + right = (.ok output : Result Std.U32)) :
    output.val = left.val + right.val := by
  have specification := @UScalar.add_equiv UScalarTy.U32 left right
  rw [run] at specification
  exact specification.2.1

inductive ExactInnerIndexedTrace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (level : AspisV7MerkleK12SourceBridge.GeneratedLevel) :
    Std.Usize → AspisV7MerkleK12SourceBridge.GeneratedLevel →
      AspisV7MerkleK12SourceBridge.GeneratedLevel → Type
  | done {index : Std.Usize}
      (scratch : AspisV7MerkleK12SourceBridge.GeneratedLevel)
      (exhausted : level.val.length ≤ index.val) :
      ExactInnerIndexedTrace hash level index scratch scratch
  | frontier {index nextIndex : Std.Usize}
      {scratch pushed final : AspisV7MerkleK12SourceBridge.GeneratedLevel}
      {child parent : AspisV7MerkleK12SourceBridge.GeneratedEntry}
      (indexBound : index.val < level.val.length)
      (childExact : child = level.val[index.val]!)
      (nextIndexExact : nextIndex.val = index.val + 1)
      (edge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash child parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed)
      (tail : ExactInnerIndexedTrace hash level nextIndex pushed final) :
      ExactInnerIndexedTrace hash level index scratch final
  | paired {index nextIndex : Std.Usize}
      {scratch pushed final : AspisV7MerkleK12SourceBridge.GeneratedLevel}
      {left right parent : AspisV7MerkleK12SourceBridge.GeneratedEntry}
      (rightIndexBound : index.val + 1 < level.val.length)
      (leftExact : left = level.val[index.val]!)
      (rightExact : right = level.val[index.val + 1]!)
      (nextIndexExact : nextIndex.val = index.val + 2)
      (leftEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash left parent)
      (rightEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash right parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed)
      (tail : ExactInnerIndexedTrace hash level nextIndex pushed final) :
      ExactInnerIndexedTrace hash level index scratch final

/-- The semantic payload of one literal successful `cont` edge of the
translated body.  The source frontier cursor is intentionally retained in
the indices even though path construction only needs the entry cursor. -/
inductive ExactInnerContinueStep
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (level : AspisV7MerkleK12SourceBridge.GeneratedLevel) :
    AspisV7MerkleK12SourceBridge.GeneratedLevel → Std.Usize → Std.Usize →
      AspisV7MerkleK12SourceBridge.GeneratedLevel → Std.Usize → Std.Usize →
      Type
  | frontier {index nextIndex nodePos nextNodePos : Std.Usize}
      {scratch pushed : AspisV7MerkleK12SourceBridge.GeneratedLevel}
      {child parent : AspisV7MerkleK12SourceBridge.GeneratedEntry}
      (indexBound : index.val < level.val.length)
      (childExact : child = level.val[index.val]!)
      (nextIndexExact : nextIndex.val = index.val + 1)
      (edge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash child parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed) :
      ExactInnerContinueStep hash level scratch nodePos index pushed
        nextNodePos nextIndex
  | paired {index nextIndex nodePos : Std.Usize}
      {scratch pushed : AspisV7MerkleK12SourceBridge.GeneratedLevel}
      {left right parent : AspisV7MerkleK12SourceBridge.GeneratedEntry}
      (rightIndexBound : index.val + 1 < level.val.length)
      (leftExact : left = level.val[index.val]!)
      (rightExact : right = level.val[index.val + 1]!)
      (nextIndexExact : nextIndex.val = index.val + 2)
      (leftEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash left parent)
      (rightEdge : AspisV7MerkleK12AcceptedBridge.PairedHashEdge hash right parent)
      (pushRun : alloc.vec.Vec.push scratch parent = .ok pushed) :
      ExactInnerContinueStep hash level scratch nodePos index pushed nodePos
        nextIndex

def ExactInnerContinueStep.prepend
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {level scratch nextScratch final : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    {nodePos nextNodePos index nextIndex : Std.Usize}
    (step : ExactInnerContinueStep hash level scratch nodePos index nextScratch
      nextNodePos nextIndex)
    (tail : ExactInnerIndexedTrace hash level nextIndex nextScratch final) :
    ExactInnerIndexedTrace hash level index scratch final := by
  cases step with
  | frontier indexBound childExact nextIndexExact edge pushRun =>
      exact .frontier indexBound childExact nextIndexExact edge pushRun tail
  | paired rightIndexBound leftExact rightExact nextIndexExact leftEdge
      rightEdge pushRun =>
      exact .paired rightIndexBound leftExact rightExact nextIndexExact
        leftEdge rightEdge pushRun tail

def frontier_even_continue_step_of_exact_runs
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (level scratch pushed : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos nextNodePos index nextIndex : Std.Usize)
    (position parentPosition : Std.U32)
    (c1 c2 c1Sibling c2Sibling parentC1 parentC2 :
      Array Std.U8 26#usize)
    (indexBound : index.val < level.val.length)
    (childExact : (position, c1, c2) = level.val[index.val]!)
    (indexAddRun : index + 1#usize = (.ok nextIndex : Result Std.Usize))
    (positionEven : position &&& 1#u32 = 0#u32)
    (parentPositionExact : parentPosition.val = position.val / 2)
    (c1HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1 c1Sibling =
        .ok parentC1)
    (c2HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2 c2Sibling =
        .ok parentC2)
    (pushRun : alloc.vec.Vec.push scratch
      (parentPosition, parentC1, parentC2) = .ok pushed) :
    ExactInnerContinueStep hash level scratch nodePos index pushed nextNodePos
      nextIndex := by
  apply ExactInnerContinueStep.frontier indexBound childExact
    (usize_add_success_val index 1#usize nextIndex indexAddRun)
  · exact AspisV7MerkleK12AcceptedBridge.PairedHashEdge.left
      c1Sibling c2Sibling
      (testBit_zero_false_of_and_one_eq_zero position positionEven)
      parentPositionExact c1HashRun c2HashRun
  · exact pushRun

def frontier_odd_continue_step_of_exact_runs
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (level scratch pushed : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos nextNodePos index nextIndex : Std.Usize)
    (position parentPosition : Std.U32)
    (c1 c2 c1Sibling c2Sibling parentC1 parentC2 :
      Array Std.U8 26#usize)
    (indexBound : index.val < level.val.length)
    (childExact : (position, c1, c2) = level.val[index.val]!)
    (indexAddRun : index + 1#usize = (.ok nextIndex : Result Std.Usize))
    (positionOdd : position &&& 1#u32 ≠ 0#u32)
    (parentPositionExact : parentPosition.val = position.val / 2)
    (c1HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1Sibling c1 =
        .ok parentC1)
    (c2HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2Sibling c2 =
        .ok parentC2)
    (pushRun : alloc.vec.Vec.push scratch
      (parentPosition, parentC1, parentC2) = .ok pushed) :
    ExactInnerContinueStep hash level scratch nodePos index pushed nextNodePos
      nextIndex := by
  apply ExactInnerContinueStep.frontier indexBound childExact
    (usize_add_success_val index 1#usize nextIndex indexAddRun)
  · exact AspisV7MerkleK12AcceptedBridge.PairedHashEdge.right
      c1Sibling c2Sibling
      (testBit_zero_true_of_and_one_ne_zero position positionOdd)
      parentPositionExact c1HashRun c2HashRun
  · exact pushRun

def paired_continue_step_of_exact_runs
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (level scratch pushed : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos index rightIndex nextIndex : Std.Usize)
    (position rightPosition parentPosition : Std.U32)
    (c1 c2 rightC1 rightC2 parentC1 parentC2 : Array Std.U8 26#usize)
    (rightIndexBoundScalar : rightIndex < alloc.vec.Vec.len level)
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (rightExact : (rightPosition, rightC1, rightC2) =
      level.val[rightIndex.val]!)
    (rightIndexRun : index + 1#usize = (.ok rightIndex : Result Std.Usize))
    (nextIndexRun : index + 2#usize = (.ok nextIndex : Result Std.Usize))
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightPositionRun : position + 1#u32 =
      (.ok rightPosition : Result Std.U32))
    (parentPositionExact : parentPosition.val = position.val / 2)
    (c1HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1 rightC1 =
        .ok parentC1)
    (c2HashRun :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2 rightC2 =
        .ok parentC2)
    (pushRun : alloc.vec.Vec.push scratch
      (parentPosition, parentC1, parentC2) = .ok pushed) :
    ExactInnerContinueStep hash level scratch nodePos index pushed nodePos
      nextIndex := by
  have rightIndexVal : rightIndex.val = index.val + 1 :=
    usize_add_success_val index 1#usize rightIndex rightIndexRun
  have rightIndexBound : index.val + 1 < level.val.length := by
    have boundValues : rightIndex.val < level.val.length := by
      change rightIndex.val < level.val.length at rightIndexBoundScalar
      exact rightIndexBoundScalar
    omega
  have rightExactAtSuccessor :
      (rightPosition, rightC1, rightC2) = level.val[index.val + 1]! := by
    simpa [rightIndexVal] using rightExact
  have nextIndexExact : nextIndex.val = index.val + 2 :=
    usize_add_success_val index 2#usize nextIndex nextIndexRun
  have leftPositionEven :=
    testBit_zero_false_of_and_one_eq_zero position positionEven
  have positionModulo : position.val % 2 = 0 := by
    have values := congrArg UScalar.val positionEven
    simpa [u32_and_one_val] using values
  have rightPositionVal : rightPosition.val = position.val + 1 :=
    u32_add_success_val position 1#u32 rightPosition rightPositionRun
  have rightModulo : rightPosition.val % 2 = 1 := by omega
  have rightPositionOdd : rightPosition.val.testBit 0 = true := by
    simp [Nat.testBit_zero, rightModulo]
  have rightParentPositionExact :
      parentPosition.val = rightPosition.val / 2 := by omega
  apply ExactInnerContinueStep.paired rightIndexBound leftExact
    rightExactAtSuccessor nextIndexExact
  · exact AspisV7MerkleK12AcceptedBridge.PairedHashEdge.left rightC1 rightC2
      leftPositionEven parentPositionExact c1HashRun c2HashRun
  · exact AspisV7MerkleK12AcceptedBridge.PairedHashEdge.right c1 c2
      rightPositionOdd rightParentPositionExact c1HashRun c2HashRun
  · exact pushRun

/-- Direct inversion of production's adjacent even/odd branch.  Every
equation before the four generalized calls is an actual translated read or
checked arithmetic result; the remaining calls are exposed by case analysis
of the successful body equation itself. -/
theorem exact_inner_body_paired_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex rightIndex : Std.Usize)
    (position rightPosition : Std.U32)
    (c1 c2 rightC1 rightC2 : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightIndexRun : index + 1#usize =
      (.ok rightIndex : Result Std.Usize))
    (rightIndexBound : rightIndex < alloc.vec.Vec.len level)
    (rightEntryRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level rightIndex =
        .ok (rightPosition, rightC1, rightC2))
    (rightExact : (rightPosition, rightC1, rightC2) =
      level.val[rightIndex.val]!)
    (rightPositionRun : position + 1#u32 =
      (.ok rightPosition : Result Std.U32))
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at bodyRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at bodyRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at bodyRun
  simp only [if_pos positionEven] at bodyRun
  rw [rightIndexRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, if_pos rightIndexBound] at bodyRun
  rw [rightEntryRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [rightPositionRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, if_pos rfl] at bodyRun
  generalize nextIndexEquation : index + 2#usize = nextIndexResult at bodyRun
  cases nextIndexResult with
  | fail error => simp [nextIndexEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [nextIndexEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok nextIndex =>
      try simp only [nextIndexEquation, Aeneas.Std.bind_tc_ok] at bodyRun
      generalize c1HashEquation :
          V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1 rightC1 =
            c1HashResult at bodyRun
      cases c1HashResult with
      | fail error =>
          simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
      | div => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
      | ok parentC1 =>
          try simp only [c1HashEquation, Aeneas.Std.bind_tc_ok] at bodyRun
          generalize c2HashEquation :
              V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2 rightC2 =
                c2HashResult at bodyRun
          cases c2HashResult with
          | fail error =>
              simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok parentC2 =>
              try simp only [nextIndexEquation, c1HashEquation, c2HashEquation,
                Aeneas.Std.bind_tc_ok] at bodyRun
              generalize parentPositionEquation : position >>> 1#i32 =
                parentPositionResult at bodyRun
              cases parentPositionResult with
              | fail error =>
                  simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                    parentPositionEquation, Bind.bind, Aeneas.Std.bind]
                    at bodyRun
              | div =>
                  simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                    parentPositionEquation, Bind.bind, Aeneas.Std.bind]
                    at bodyRun
              | ok parentPosition =>
                  try simp only [nextIndexEquation, c1HashEquation,
                    c2HashEquation, parentPositionEquation,
                    Aeneas.Std.bind_tc_ok] at bodyRun
                  generalize pushEquation : alloc.vec.Vec.push scratch
                      (parentPosition, parentC1, parentC2) = pushResult
                    at bodyRun
                  cases pushResult with
                  | fail error =>
                      simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                        parentPositionEquation, pushEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | div =>
                      simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                        parentPositionEquation, pushEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | ok pushed =>
                      simp [nextIndexEquation, c1HashEquation, c2HashEquation,
                        parentPositionEquation, pushEquation, if_pos rfl,
                        Bind.bind, Aeneas.Std.bind] at bodyRun
                      rcases bodyRun with ⟨rfl, rfl, rfl⟩
                      exact ⟨paired_continue_step_of_exact_runs hash level
                        scratch pushed nodePos index rightIndex nextIndex
                        position rightPosition parentPosition c1 c2 rightC1
                        rightC2 parentC1 parentC2 rightIndexBound leftExact
                        rightExact rightIndexRun nextIndexEquation positionEven
                        rightPositionRun
                        (u32_shr_one_success_val position parentPosition
                          parentPositionEquation)
                        c1HashEquation c2HashEquation pushEquation⟩

/-- Direct inversion of production's odd-position frontier branch.  The
frontier slice/copy equations identify the disclosed sibling arrays; the two
node calls, parent shift, push, and one-entry cursor advance are taken from
the same successful body equation. -/
theorem exact_inner_body_odd_frontier_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex nodeEnd nextIndex : Std.Usize)
    (position : Std.U32) (c1 c2 : Array Std.U8 26#usize)
    (c1SiblingSlice c2SiblingSlice : Slice Std.U8)
    (c1Sibling c2Sibling : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionOdd : position &&& 1#u32 ≠ 0#u32)
    (nodeEndRun : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        (.ok nodeEnd : Result Std.Usize))
    (frontierRoom : ¬ nodeEnd > Slice.len c1Nodes)
    (c1SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c1SiblingSlice)
    (c1CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c1SiblingSlice = .ok (.Ok c1Sibling))
    (c2SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c2Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c2SiblingSlice)
    (c2CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c2SiblingSlice = .ok (.Ok c2Sibling))
    (nextIndexRun : index + 1#usize =
      (.ok nextIndex : Result Std.Usize))
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at bodyRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at bodyRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at bodyRun
  simp only [if_neg positionOdd] at bodyRun
  rw [nodeEndRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  change (if nodeEnd > Slice.len c1Nodes then _ else _) = _ at bodyRun
  simp only [if_neg frontierRoom] at bodyRun
  rw [c1SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c1CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap] at bodyRun
  rw [c2SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c2CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap] at bodyRun
  rw [nextIndexRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  generalize c1HashEquation :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1Sibling c1 =
        c1HashResult at bodyRun
  cases c1HashResult with
  | fail error => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok parentC1 =>
      try simp only [c1HashEquation, Aeneas.Std.bind_tc_ok] at bodyRun
      generalize c2HashEquation :
          V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2Sibling c2 =
            c2HashResult at bodyRun
      cases c2HashResult with
      | fail error =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | div =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | ok parentC2 =>
          try simp only [c1HashEquation, c2HashEquation,
            Aeneas.Std.bind_tc_ok] at bodyRun
          generalize parentPositionEquation : position >>> 1#i32 =
            parentPositionResult at bodyRun
          cases parentPositionResult with
          | fail error =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok parentPosition =>
              try simp only [c1HashEquation, c2HashEquation,
                parentPositionEquation, Aeneas.Std.bind_tc_ok] at bodyRun
              generalize pushEquation : alloc.vec.Vec.push scratch
                  (parentPosition, parentC1, parentC2) = pushResult at bodyRun
              cases pushResult with
              | fail error =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | div =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | ok pushed =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
                  rcases bodyRun with ⟨rfl, rfl, rfl⟩
                  exact ⟨frontier_odd_continue_step_of_exact_runs hash
                    level scratch pushed nodePos nodeEnd index nextIndex
                    position parentPosition c1 c2 c1Sibling c2Sibling parentC1
                    parentC2
                    (by
                      change index.val < level.val.length at active
                      exact active)
                    leftExact nextIndexRun positionOdd
                    (u32_shr_one_success_val position parentPosition
                      parentPositionEquation)
                    c1HashEquation c2HashEquation pushEquation⟩

/-- Direct inversion of the even frontier branch when no following live
entry exists. -/
theorem exact_inner_body_even_last_frontier_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex rightIndex nodeEnd : Std.Usize)
    (position : Std.U32) (c1 c2 : Array Std.U8 26#usize)
    (c1SiblingSlice c2SiblingSlice : Slice Std.U8)
    (c1Sibling c2Sibling : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightIndexRun : index + 1#usize =
      (.ok rightIndex : Result Std.Usize))
    (noRightEntry : ¬ rightIndex < alloc.vec.Vec.len level)
    (nodeEndRun : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        (.ok nodeEnd : Result Std.Usize))
    (frontierRoom : ¬ nodeEnd > Slice.len c1Nodes)
    (c1SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c1SiblingSlice)
    (c1CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c1SiblingSlice = .ok (.Ok c1Sibling))
    (c2SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c2Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c2SiblingSlice)
    (c2CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c2SiblingSlice = .ok (.Ok c2Sibling))
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at bodyRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at bodyRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at bodyRun
  simp only [if_pos positionEven] at bodyRun
  rw [rightIndexRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, if_neg noRightEntry] at bodyRun
  rw [nodeEndRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  change (if nodeEnd > Slice.len c1Nodes then _ else _) = _ at bodyRun
  simp only [if_neg frontierRoom] at bodyRun
  rw [c1SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c1CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap] at bodyRun
  rw [c2SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c2CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap,
    if_pos positionEven] at bodyRun
  generalize c1HashEquation :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1 c1Sibling =
        c1HashResult at bodyRun
  cases c1HashResult with
  | fail error => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok parentC1 =>
      try simp only [c1HashEquation, Aeneas.Std.bind_tc_ok] at bodyRun
      generalize c2HashEquation :
          V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2 c2Sibling =
            c2HashResult at bodyRun
      cases c2HashResult with
      | fail error =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | div =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | ok parentC2 =>
          try simp only [c1HashEquation, c2HashEquation,
            Aeneas.Std.bind_tc_ok] at bodyRun
          generalize parentPositionEquation : position >>> 1#i32 =
            parentPositionResult at bodyRun
          cases parentPositionResult with
          | fail error =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok parentPosition =>
              try simp only [c1HashEquation, c2HashEquation,
                parentPositionEquation, Aeneas.Std.bind_tc_ok] at bodyRun
              generalize pushEquation : alloc.vec.Vec.push scratch
                  (parentPosition, parentC1, parentC2) = pushResult at bodyRun
              cases pushResult with
              | fail error =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | div =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | ok pushed =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
                  rcases bodyRun with ⟨rfl, rfl, rfl⟩
                  exact ⟨frontier_even_continue_step_of_exact_runs hash
                    level scratch pushed nodePos nodeEnd index rightIndex
                    position parentPosition c1 c2 c1Sibling c2Sibling parentC1
                    parentC2
                    (by
                      change index.val < level.val.length at active
                      exact active)
                    leftExact rightIndexRun positionEven
                    (u32_shr_one_success_val position parentPosition
                      parentPositionEquation)
                    c1HashEquation c2HashEquation pushEquation⟩

/-- Direct inversion of the even frontier branch where a following live
entry exists but is not the adjacent odd sibling. -/
theorem exact_inner_body_even_gap_frontier_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex rightIndex nodeEnd : Std.Usize)
    (position rightPosition expectedRightPosition : Std.U32)
    (c1 c2 rightC1 rightC2 : Array Std.U8 26#usize)
    (c1SiblingSlice c2SiblingSlice : Slice Std.U8)
    (c1Sibling c2Sibling : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightIndexRun : index + 1#usize =
      (.ok rightIndex : Result Std.Usize))
    (rightIndexBound : rightIndex < alloc.vec.Vec.len level)
    (rightEntryRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level rightIndex =
        .ok (rightPosition, rightC1, rightC2))
    (expectedPositionRun : position + 1#u32 =
      (.ok expectedRightPosition : Result Std.U32))
    (notAdjacent : rightPosition ≠ expectedRightPosition)
    (nodeEndRun : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        (.ok nodeEnd : Result Std.Usize))
    (frontierRoom : ¬ nodeEnd > Slice.len c1Nodes)
    (c1SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c1SiblingSlice)
    (c1CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c1SiblingSlice = .ok (.Ok c1Sibling))
    (c2SliceRun :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c2Nodes
        { start := nodePos, «end» := nodeEnd } = .ok c2SiblingSlice)
    (c2CopyRun :
      core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
        c2SiblingSlice = .ok (.Ok c2Sibling))
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at bodyRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at bodyRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at bodyRun
  simp only [if_pos positionEven] at bodyRun
  rw [rightIndexRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, if_pos rightIndexBound] at bodyRun
  rw [rightEntryRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [expectedPositionRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  change (if rightPosition = expectedRightPosition then _ else _) = _
    at bodyRun
  simp only [if_neg notAdjacent] at bodyRun
  rw [nodeEndRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  change (if nodeEnd > Slice.len c1Nodes then _ else _) = _ at bodyRun
  simp only [if_neg frontierRoom] at bodyRun
  rw [c1SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c1CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap] at bodyRun
  rw [c2SliceRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok] at bodyRun
  rw [c2CopyRun] at bodyRun
  simp only [Aeneas.Std.bind_tc_ok, core.result.Result.unwrap,
    if_pos positionEven] at bodyRun
  generalize c1HashEquation :
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c1 c1Sibling =
        c1HashResult at bodyRun
  cases c1HashResult with
  | fail error => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [c1HashEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok parentC1 =>
      try simp only [c1HashEquation, Aeneas.Std.bind_tc_ok] at bodyRun
      generalize c2HashEquation :
          V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash c2 c2Sibling =
            c2HashResult at bodyRun
      cases c2HashResult with
      | fail error =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | div =>
          simp [c1HashEquation, c2HashEquation, Bind.bind, Aeneas.Std.bind]
            at bodyRun
      | ok parentC2 =>
          try simp only [c1HashEquation, c2HashEquation,
            Aeneas.Std.bind_tc_ok] at bodyRun
          generalize parentPositionEquation : position >>> 1#i32 =
            parentPositionResult at bodyRun
          cases parentPositionResult with
          | fail error =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [c1HashEquation, c2HashEquation, parentPositionEquation,
                Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok parentPosition =>
              try simp only [c1HashEquation, c2HashEquation,
                parentPositionEquation, Aeneas.Std.bind_tc_ok] at bodyRun
              generalize pushEquation : alloc.vec.Vec.push scratch
                  (parentPosition, parentC1, parentC2) = pushResult at bodyRun
              cases pushResult with
              | fail error =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | div =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
              | ok pushed =>
                  simp [c1HashEquation, c2HashEquation,
                    parentPositionEquation, pushEquation, Bind.bind,
                    Aeneas.Std.bind] at bodyRun
                  rcases bodyRun with ⟨rfl, rfl, rfl⟩
                  exact ⟨frontier_even_continue_step_of_exact_runs hash
                    level scratch pushed nodePos nodeEnd index rightIndex
                    position parentPosition c1 c2 c1Sibling c2Sibling parentC1
                    parentC2
                    (by
                      change index.val < level.val.length at active
                      exact active)
                    leftExact rightIndexRun positionEven
                    (u32_shr_one_success_val position parentPosition
                      parentPositionEquation)
                    c1HashEquation c2HashEquation pushEquation⟩

/-- The odd frontier dispatcher obtains every slice/copy/cursor equation by
case analysis of the translated body.  Thus callers need only provide the
live entry read and its odd parity, both of which come from the immutable
level. -/
theorem exact_inner_body_odd_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex : Std.Usize)
    (position : Std.U32) (c1 c2 : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionOdd : position &&& 1#u32 ≠ 0#u32)
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  have reducedRun := bodyRun
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at reducedRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at reducedRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at reducedRun
  simp only [if_neg positionOdd] at reducedRun
  generalize nodeEndEquation : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        nodeEndResult at reducedRun
  cases nodeEndResult with
  | fail error =>
      simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | div => simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | ok nodeEnd =>
      try simp only [nodeEndEquation, Aeneas.Std.bind_tc_ok] at reducedRun
      change (if nodeEnd > Slice.len c1Nodes then _ else _) = _
        at reducedRun
      by_cases frontierTooShort : nodeEnd > Slice.len c1Nodes
      · simp only [if_pos frontierTooShort] at reducedRun
        simp at reducedRun
      · simp only [if_neg frontierTooShort] at reducedRun
        generalize c1SliceEquation :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
              { start := nodePos, «end» := nodeEnd } = c1SliceResult
          at reducedRun
        cases c1SliceResult with
        | fail error =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | div =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | ok c1SiblingSlice =>
            try simp only [c1SliceEquation, Aeneas.Std.bind_tc_ok] at reducedRun
            generalize c1CopyEquation :
                core.array.TryFromArrayCopySlice.try_from 26#usize
                core.marker.CopyU8 c1SiblingSlice = c1CopyResult
              at reducedRun
            cases c1CopyResult with
            | fail error =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | div =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | ok c1CopyOutput =>
                try simp only [c1CopyEquation, Aeneas.Std.bind_tc_ok] at reducedRun
                cases c1CopyOutput with
                | Err error =>
                    simp [core.result.Result.unwrap, Bind.bind,
                      Aeneas.Std.bind] at reducedRun
                | Ok c1Sibling =>
                    simp only [core.result.Result.unwrap,
                      Aeneas.Std.bind_tc_ok] at reducedRun
                    generalize c2SliceEquation :
                        core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                          c2Nodes { start := nodePos, «end» := nodeEnd } =
                            c2SliceResult at reducedRun
                    cases c2SliceResult with
                    | fail error =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | div =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | ok c2SiblingSlice =>
                        try simp only [c2SliceEquation, Aeneas.Std.bind_tc_ok]
                          at reducedRun
                        generalize c2CopyEquation :
                            core.array.TryFromArrayCopySlice.try_from 26#usize
                              core.marker.CopyU8 c2SiblingSlice = c2CopyResult
                          at reducedRun
                        cases c2CopyResult with
                        | fail error =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | div =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | ok c2CopyOutput =>
                            try simp only [c2CopyEquation, Aeneas.Std.bind_tc_ok]
                              at reducedRun
                            cases c2CopyOutput with
                            | Err error =>
                                simp [core.result.Result.unwrap, Bind.bind,
                                  Aeneas.Std.bind] at reducedRun
                            | Ok c2Sibling =>
                                simp only [core.result.Result.unwrap,
                                  Aeneas.Std.bind_tc_ok] at reducedRun
                                generalize nextIndexEquation :
                                    index + 1#usize = nextIndexResult
                                  at reducedRun
                                cases nextIndexResult with
                                | fail error =>
                                    simp [nextIndexEquation, Bind.bind,
                                      Aeneas.Std.bind] at reducedRun
                                | div =>
                                    simp [nextIndexEquation, Bind.bind,
                                      Aeneas.Std.bind] at reducedRun
                                | ok nextIndex =>
                                    exact
                                      exact_inner_body_odd_frontier_cont_yields_step
                                        hash c1Nodes c2Nodes level scratch
                                        outputScratch nodePos outputNodePos
                                        index outputIndex nodeEnd nextIndex
                                        position c1 c2 c1SiblingSlice
                                        c2SiblingSlice c1Sibling c2Sibling
                                        active leftIndexRun leftExact positionOdd
                                        nodeEndEquation frontierTooShort
                                        c1SliceEquation c1CopyEquation
                                        c2SliceEquation c2CopyEquation
                                        nextIndexEquation bodyRun

/-- The corresponding dispatcher for an even entry with no following live
entry. -/
theorem exact_inner_body_even_last_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex rightIndex : Std.Usize)
    (position : Std.U32) (c1 c2 : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightIndexRun : index + 1#usize =
      (.ok rightIndex : Result Std.Usize))
    (noRightEntry : ¬ rightIndex < alloc.vec.Vec.len level)
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  have reducedRun := bodyRun
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at reducedRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at reducedRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at reducedRun
  simp only [if_pos positionEven] at reducedRun
  rw [rightIndexRun] at reducedRun
  simp only [Aeneas.Std.bind_tc_ok, if_neg noRightEntry] at reducedRun
  generalize nodeEndEquation : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        nodeEndResult at reducedRun
  cases nodeEndResult with
  | fail error =>
      simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | div => simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | ok nodeEnd =>
      try simp only [nodeEndEquation, Aeneas.Std.bind_tc_ok] at reducedRun
      change (if nodeEnd > Slice.len c1Nodes then _ else _) = _
        at reducedRun
      by_cases frontierTooShort : nodeEnd > Slice.len c1Nodes
      · simp only [if_pos frontierTooShort] at reducedRun
        simp at reducedRun
      · simp only [if_neg frontierTooShort] at reducedRun
        generalize c1SliceEquation :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
              { start := nodePos, «end» := nodeEnd } = c1SliceResult
          at reducedRun
        cases c1SliceResult with
        | fail error =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | div =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | ok c1SiblingSlice =>
            try simp only [c1SliceEquation, Aeneas.Std.bind_tc_ok] at reducedRun
            generalize c1CopyEquation :
                core.array.TryFromArrayCopySlice.try_from 26#usize
                core.marker.CopyU8 c1SiblingSlice = c1CopyResult
              at reducedRun
            cases c1CopyResult with
            | fail error =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | div =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | ok c1CopyOutput =>
                try simp only [c1CopyEquation, Aeneas.Std.bind_tc_ok] at reducedRun
                cases c1CopyOutput with
                | Err error =>
                    simp [core.result.Result.unwrap, Bind.bind,
                      Aeneas.Std.bind] at reducedRun
                | Ok c1Sibling =>
                    simp only [core.result.Result.unwrap,
                      Aeneas.Std.bind_tc_ok] at reducedRun
                    generalize c2SliceEquation :
                        core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                          c2Nodes { start := nodePos, «end» := nodeEnd } =
                            c2SliceResult at reducedRun
                    cases c2SliceResult with
                    | fail error =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | div =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | ok c2SiblingSlice =>
                        try simp only [c2SliceEquation, Aeneas.Std.bind_tc_ok]
                          at reducedRun
                        generalize c2CopyEquation :
                            core.array.TryFromArrayCopySlice.try_from 26#usize
                              core.marker.CopyU8 c2SiblingSlice = c2CopyResult
                          at reducedRun
                        cases c2CopyResult with
                        | fail error =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | div =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | ok c2CopyOutput =>
                            try simp only [c2CopyEquation, Aeneas.Std.bind_tc_ok]
                              at reducedRun
                            cases c2CopyOutput with
                            | Err error =>
                                simp [core.result.Result.unwrap, Bind.bind,
                                  Aeneas.Std.bind] at reducedRun
                            | Ok c2Sibling =>
                                exact
                                  exact_inner_body_even_last_frontier_cont_yields_step
                                    hash c1Nodes c2Nodes level scratch
                                    outputScratch nodePos outputNodePos index
                                    outputIndex rightIndex nodeEnd position c1
                                    c2 c1SiblingSlice c2SiblingSlice c1Sibling
                                    c2Sibling active leftIndexRun leftExact
                                    positionEven rightIndexRun noRightEntry
                                    nodeEndEquation frontierTooShort
                                    c1SliceEquation c1CopyEquation
                                    c2SliceEquation c2CopyEquation bodyRun

/-- The dispatcher for an even entry followed by a non-adjacent live entry. -/
theorem exact_inner_body_even_gap_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex rightIndex : Std.Usize)
    (position rightPosition expectedRightPosition : Std.U32)
    (c1 c2 rightC1 rightC2 : Array Std.U8 26#usize)
    (active : index < alloc.vec.Vec.len level)
    (leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2))
    (leftExact : (position, c1, c2) = level.val[index.val]!)
    (positionEven : position &&& 1#u32 = 0#u32)
    (rightIndexRun : index + 1#usize =
      (.ok rightIndex : Result Std.Usize))
    (rightIndexBound : rightIndex < alloc.vec.Vec.len level)
    (rightEntryRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level rightIndex =
        .ok (rightPosition, rightC1, rightC2))
    (expectedPositionRun : position + 1#u32 =
      (.ok expectedRightPosition : Result Std.U32))
    (notAdjacent : rightPosition ≠ expectedRightPosition)
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  have reducedRun := bodyRun
  unfold
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    at reducedRun
  simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
    at reducedRun
  change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at reducedRun
  simp only [if_pos positionEven] at reducedRun
  rw [rightIndexRun] at reducedRun
  simp only [Aeneas.Std.bind_tc_ok, if_pos rightIndexBound] at reducedRun
  rw [rightEntryRun] at reducedRun
  simp only [Aeneas.Std.bind_tc_ok] at reducedRun
  rw [expectedPositionRun] at reducedRun
  simp only [Aeneas.Std.bind_tc_ok] at reducedRun
  change (if rightPosition = expectedRightPosition then _ else _) = _
    at reducedRun
  simp only [if_neg notAdjacent] at reducedRun
  generalize nodeEndEquation : nodePos +
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        nodeEndResult at reducedRun
  cases nodeEndResult with
  | fail error =>
      simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | div => simp [nodeEndEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
  | ok nodeEnd =>
      try simp only [nodeEndEquation, Aeneas.Std.bind_tc_ok] at reducedRun
      change (if nodeEnd > Slice.len c1Nodes then _ else _) = _
        at reducedRun
      by_cases frontierTooShort : nodeEnd > Slice.len c1Nodes
      · simp only [if_pos frontierTooShort] at reducedRun
        simp at reducedRun
      · simp only [if_neg frontierTooShort] at reducedRun
        generalize c1SliceEquation :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c1Nodes
              { start := nodePos, «end» := nodeEnd } = c1SliceResult
          at reducedRun
        cases c1SliceResult with
        | fail error =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | div =>
            simp [c1SliceEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
        | ok c1SiblingSlice =>
            try simp only [c1SliceEquation, Aeneas.Std.bind_tc_ok] at reducedRun
            generalize c1CopyEquation :
                core.array.TryFromArrayCopySlice.try_from 26#usize
                core.marker.CopyU8 c1SiblingSlice = c1CopyResult
              at reducedRun
            cases c1CopyResult with
            | fail error =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | div =>
                simp [c1CopyEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
            | ok c1CopyOutput =>
                try simp only [c1CopyEquation, Aeneas.Std.bind_tc_ok] at reducedRun
                cases c1CopyOutput with
                | Err error =>
                    simp [core.result.Result.unwrap, Bind.bind,
                      Aeneas.Std.bind] at reducedRun
                | Ok c1Sibling =>
                    simp only [core.result.Result.unwrap,
                      Aeneas.Std.bind_tc_ok] at reducedRun
                    generalize c2SliceEquation :
                        core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                          c2Nodes { start := nodePos, «end» := nodeEnd } =
                            c2SliceResult at reducedRun
                    cases c2SliceResult with
                    | fail error =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | div =>
                        simp [c2SliceEquation, Bind.bind, Aeneas.Std.bind]
                          at reducedRun
                    | ok c2SiblingSlice =>
                        try simp only [c2SliceEquation, Aeneas.Std.bind_tc_ok]
                          at reducedRun
                        generalize c2CopyEquation :
                            core.array.TryFromArrayCopySlice.try_from 26#usize
                              core.marker.CopyU8 c2SiblingSlice = c2CopyResult
                          at reducedRun
                        cases c2CopyResult with
                        | fail error =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | div =>
                            simp [c2CopyEquation, Bind.bind, Aeneas.Std.bind]
                              at reducedRun
                        | ok c2CopyOutput =>
                            try simp only [c2CopyEquation, Aeneas.Std.bind_tc_ok]
                              at reducedRun
                            cases c2CopyOutput with
                            | Err error =>
                                simp [core.result.Result.unwrap, Bind.bind,
                                  Aeneas.Std.bind] at reducedRun
                            | Ok c2Sibling =>
                                exact
                                  exact_inner_body_even_gap_frontier_cont_yields_step
                                    hash c1Nodes c2Nodes level scratch
                                    outputScratch nodePos outputNodePos index
                                    outputIndex rightIndex nodeEnd position
                                    rightPosition expectedRightPosition c1 c2
                                    rightC1 rightC2 c1SiblingSlice
                                    c2SiblingSlice c1Sibling c2Sibling active
                                    leftIndexRun leftExact positionEven
                                    rightIndexRun rightIndexBound rightEntryRun
                                    expectedPositionRun notAdjacent
                                    nodeEndEquation frontierTooShort
                                    c1SliceEquation c1CopyEquation
                                    c2SliceEquation c2CopyEquation bodyRun

/-- Exhaustive successful-continue inversion for the translated inner body.
No semantic branch premise remains: the immutable level reads, parity,
checked successor, adjacency test, and frontier branch are all selected from
the literal body equation. -/
theorem exact_inner_body_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level scratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (nodePos outputNodePos index outputIndex : Std.Usize)
    (bodyRun :
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level scratch nodePos index =
        .ok (.cont (outputScratch, outputNodePos, outputIndex))) :
    Nonempty (ExactInnerContinueStep hash level scratch nodePos index
      outputScratch outputNodePos outputIndex) := by
  have active : index < alloc.vec.Vec.len level := by
    by_contra inactive
    have impossible := bodyRun
    unfold
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
      at impossible
    simp only [if_neg inactive] at impossible
    simp at impossible
  have indexBound : index.val < level.val.length := by
    change index.val < level.val.length at active
    exact active
  obtain ⟨entry, entryRun, entryValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec level index indexBound)
  rcases entry with ⟨position, c1, c2⟩
  have leftIndexRun :
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice
          AspisV7MerkleK12SourceBridge.GeneratedEntry) level index =
        .ok (position, c1, c2) := by
    rw [alloc.vec.Vec.index_slice_index]
    exact entryRun
  have leftExact : (position, c1, c2) = level.val[index.val]! := by
    rw [entryValue]
    exact (getElem!_pos level.val index.val indexBound).symm
  by_cases positionEven : position &&& 1#u32 = 0#u32
  · have reducedRun := bodyRun
    unfold
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
      at reducedRun
    simp only [if_pos active, leftIndexRun, Aeneas.Std.bind_tc_ok, lift]
      at reducedRun
    change (if position &&& 1#u32 = 0#u32 then _ else _) = _ at reducedRun
    simp only [if_pos positionEven] at reducedRun
    generalize rightIndexEquation : index + 1#usize = rightIndexResult
      at reducedRun
    cases rightIndexResult with
    | fail error =>
        simp [rightIndexEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
    | div =>
        simp [rightIndexEquation, Bind.bind, Aeneas.Std.bind] at reducedRun
    | ok rightIndex =>
        try simp only [rightIndexEquation, Aeneas.Std.bind_tc_ok] at reducedRun
        by_cases rightIndexBound : rightIndex < alloc.vec.Vec.len level
        · have rightIndexBoundNat :
              rightIndex.val < level.val.length := by
            change rightIndex.val < level.val.length at rightIndexBound
            exact rightIndexBound
          obtain ⟨rightEntry, rightEntryRunUsize, rightEntryValue⟩ :=
            Aeneas.Std.WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec level rightIndex
                rightIndexBoundNat)
          rcases rightEntry with ⟨rightPosition, rightC1, rightC2⟩
          have rightEntryRun :
              alloc.vec.Vec.index
                (core.slice.index.SliceIndexUsizeSlice
                  AspisV7MerkleK12SourceBridge.GeneratedEntry) level
                  rightIndex = .ok (rightPosition, rightC1, rightC2) := by
            rw [alloc.vec.Vec.index_slice_index]
            exact rightEntryRunUsize
          have rightExact : (rightPosition, rightC1, rightC2) =
              level.val[rightIndex.val]! := by
            rw [rightEntryValue]
            exact (getElem!_pos level.val rightIndex.val rightIndexBoundNat).symm
          simp only [if_pos rightIndexBound, rightEntryRun,
            Aeneas.Std.bind_tc_ok] at reducedRun
          generalize expectedPositionEquation : position + 1#u32 =
              expectedPositionResult at reducedRun
          cases expectedPositionResult with
          | fail error =>
              simp [expectedPositionEquation, Bind.bind, Aeneas.Std.bind]
                at reducedRun
          | div =>
              simp [expectedPositionEquation, Bind.bind, Aeneas.Std.bind]
                at reducedRun
          | ok expectedRightPosition =>
              try simp only [expectedPositionEquation, Aeneas.Std.bind_tc_ok]
                at reducedRun
              by_cases adjacent : rightPosition = expectedRightPosition
              · subst expectedRightPosition
                exact exact_inner_body_paired_cont_yields_step hash c1Nodes
                  c2Nodes level scratch outputScratch nodePos outputNodePos
                  index outputIndex rightIndex position rightPosition c1 c2
                  rightC1 rightC2 active leftIndexRun leftExact positionEven
                  rightIndexEquation rightIndexBound rightEntryRun rightExact
                  expectedPositionEquation bodyRun
              · exact exact_inner_body_even_gap_cont_yields_step hash
                  c1Nodes c2Nodes level scratch outputScratch nodePos
                  outputNodePos index outputIndex rightIndex position
                  rightPosition expectedRightPosition c1 c2 rightC1 rightC2
                  active leftIndexRun leftExact positionEven rightIndexEquation
                  rightIndexBound rightEntryRun expectedPositionEquation
                  adjacent bodyRun
        · exact exact_inner_body_even_last_cont_yields_step hash c1Nodes
            c2Nodes level scratch outputScratch nodePos outputNodePos index
            outputIndex rightIndex position c1 c2 active leftIndexRun
            leftExact positionEven rightIndexEquation rightIndexBound bodyRun
  · exact exact_inner_body_odd_cont_yields_step hash c1Nodes c2Nodes level
      scratch outputScratch nodePos outputNodePos index outputIndex position c1
      c2 active leftIndexRun leftExact positionEven bodyRun

/-- Constructive conversion of a generic translated inner-loop trace whose
terminal pending flag is `none`.  Keeping the source start and result generic
gives the structural recursion a variable index at every constructor. -/
noncomputable def exact_inner_control_flow_trace_to_indexed_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    {start : AspisV7MerkleK12SourceBridge.GeneratedLevel × Std.Usize ×
      Std.Usize}
    {result : AspisV7MerkleK12SourceBridge.GeneratedLevel × Std.Usize ×
      Option Bool}
    (trace : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (AspisV7MerkleK12SourceBridge.exactInnerBody hash c1Nodes c2Nodes level)
      start result)
    (resultNone : result.2.2 = none) :
    ExactInnerIndexedTrace hash level start.2.2 start.1 result.1 := by
  induction trace with
  | @done start result bodyRun =>
      rcases start with ⟨scratch, nodePos, index⟩
      rcases result with ⟨final, finalNodePos, pending⟩
      cases pending with
      | some accepted => cases resultNone
      | none =>
        change
          V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
              hash c1Nodes c2Nodes level scratch nodePos index =
            .ok (.done (final, finalNodePos, none)) at bodyRun
        obtain ⟨exhausted, scratchExact, _⟩ :=
          exact_inner_body_done_none_is_exhausted hash c1Nodes c2Nodes level
            scratch final nodePos index finalNodePos bodyRun
        subst final
        exact ExactInnerIndexedTrace.done scratch exhausted
  | @cont start next result bodyRun tail inductionHypothesis =>
      rcases start with ⟨scratch, nodePos, index⟩
      rcases next with ⟨nextScratch, nextNodePos, nextIndex⟩
      change
        V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
            hash c1Nodes c2Nodes level scratch nodePos index =
          .ok (.cont (nextScratch, nextNodePos, nextIndex)) at bodyRun
      let step := Classical.choice
        (exact_inner_body_cont_yields_step hash c1Nodes c2Nodes level scratch
          nextScratch nodePos nextNodePos index nextIndex bodyRun)
      exact step.prepend (inductionHypothesis resultNone)

/-- Complete conversion of the finite generic source-control-flow trace into
the cursor-indexed Merkle edge trace.  The terminal case is exact exhaustion;
each continue case uses the exhaustive translated-body inversion above. -/
theorem exact_inner_control_flow_trace_yields_indexed_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level initialScratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (initialNodePos outputNodePos initialIndex : Std.Usize)
    (trace : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (AspisV7MerkleK12SourceBridge.exactInnerBody hash c1Nodes c2Nodes level)
      (initialScratch, initialNodePos, initialIndex)
      (outputScratch, outputNodePos, none)) :
    Nonempty (ExactInnerIndexedTrace hash level initialIndex initialScratch
      outputScratch) :=
  ⟨exact_inner_control_flow_trace_to_indexed_trace hash c1Nodes c2Nodes level
    trace rfl⟩

/-- Cursor erasure is constructive.  The exact source index increments prove
that the indexed trace consumes precisely the corresponding list suffix. -/
noncomputable def ExactInnerIndexedTrace.toEdgeTrace
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {level : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    {index : Std.Usize}
    {scratch final : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    (trace : ExactInnerIndexedTrace hash level index scratch final) :
    AspisV7MerkleK12TraversalBridge.ExactInnerEdgeTrace hash
      (level.val.drop index.val) scratch final := by
  induction trace with
  | done scratch exhausted =>
      simpa [List.drop_eq_nil_iff.mpr exhausted] using
        (AspisV7MerkleK12TraversalBridge.ExactInnerEdgeTrace.done
          (hash := hash) scratch)
  | @frontier index nextIndex scratch pushed final child parent indexBound
      childExact nextIndexExact edge pushRun tail inductionHypothesis =>
      have remainingExact :
          level.val.drop index.val = child :: level.val.drop nextIndex.val := by
        rw [list_drop_eq_getElem_cons level.val index.val indexBound]
        rw [← childExact, nextIndexExact]
      rw [remainingExact]
      exact AspisV7MerkleK12TraversalBridge.ExactInnerEdgeTrace.frontier
        edge pushRun inductionHypothesis
  | @paired index nextIndex scratch pushed final left right parent
      rightIndexBound leftExact rightExact nextIndexExact leftEdge rightEdge
      pushRun tail inductionHypothesis =>
      have remainingExact : level.val.drop index.val =
          left :: right :: level.val.drop nextIndex.val := by
        rw [list_drop_eq_two_getElem_cons level.val index.val rightIndexBound]
        rw [← leftExact, ← rightExact, nextIndexExact]
      rw [remainingExact]
      exact AspisV7MerkleK12TraversalBridge.ExactInnerEdgeTrace.paired
        leftEdge rightEdge pushRun inductionHypothesis

/-- Starting from production's zero cursor consumes the whole immutable level
and yields the edge-covering list trace used to construct one paired hash
round. -/
theorem exact_inner_control_flow_trace_yields_edge_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level initialScratch outputScratch :
      AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (initialNodePos outputNodePos : Std.Usize)
    (trace : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (AspisV7MerkleK12SourceBridge.exactInnerBody hash c1Nodes c2Nodes level)
      (initialScratch, initialNodePos, 0#usize)
      (outputScratch, outputNodePos, none)) :
    Nonempty (AspisV7MerkleK12TraversalBridge.ExactInnerEdgeTrace hash
      level.val initialScratch outputScratch) := by
  let indexed := Classical.choice
    (exact_inner_control_flow_trace_yields_indexed_trace hash c1Nodes c2Nodes
      level initialScratch outputScratch initialNodePos outputNodePos 0#usize
      trace)
  exact ⟨by simpa using indexed.toEdgeTrace⟩

#print axioms exact_inner_body_active_cannot_done_none
#print axioms exact_inner_body_done_none_is_exhausted
#print axioms list_drop_eq_getElem_cons
#print axioms list_drop_eq_two_getElem_cons
#print axioms frontier_even_continue_step_of_exact_runs
#print axioms frontier_odd_continue_step_of_exact_runs
#print axioms paired_continue_step_of_exact_runs
#print axioms exact_inner_body_paired_cont_yields_step
#print axioms exact_inner_body_odd_frontier_cont_yields_step
#print axioms exact_inner_body_even_last_frontier_cont_yields_step
#print axioms exact_inner_body_even_gap_frontier_cont_yields_step
#print axioms exact_inner_body_odd_cont_yields_step
#print axioms exact_inner_body_even_last_cont_yields_step
#print axioms exact_inner_body_even_gap_cont_yields_step
#print axioms exact_inner_body_cont_yields_step
#print axioms exact_inner_control_flow_trace_yields_indexed_trace
#print axioms exact_inner_control_flow_trace_yields_edge_trace
#print axioms ExactInnerIndexedTrace.toEdgeTrace
#print axioms u32_shr_one_i32_val
#print axioms testBit_zero_false_of_and_one_eq_zero
#print axioms testBit_zero_true_of_and_one_ne_zero

end AspisV7MerkleK12InnerTraceBridge
