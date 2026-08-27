import PoolV1TreeAppendOneBridge
import AspisFormal.Pool.IncrementalMerkleV1

/-!
# Pool V1 production carry trace to abstract appendCarry

This file factors the representation argument away from the translated Rust
control-flow proof. `modelFrom` reads the concrete frontier from the low bit
up, while `concreteCarry` is the list-level image of the exact source trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1TreeAppendOneAbstractBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated
open PoolV1TreeAppendOneSourceBridge
open AspisPool.IncrementalMerkleV1

abbrev Digest := Array Std.U32 8#usize

def modelFrom (cursor : Nat) (frontier : List Digest)
    (level : Nat) : Nat → List (Option Digest)
  | 0 => []
  | fuel + 1 =>
      (if cursor % 2 = 1 then some frontier[level]! else none) ::
        modelFrom (cursor / 2) frontier (level + 1) fuel

theorem modelFrom_length (cursor : Nat) (frontier : List Digest)
    (level fuel : Nat) :
    (modelFrom cursor frontier level fuel).length = fuel := by
  induction fuel generalizing cursor level with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp [modelFrom, inductionHypothesis]

theorem modelFrom_getElem
    (cursor : Nat) (frontier : List Digest) (level fuel index : Nat)
    (indexBound : index < fuel) :
    (modelFrom cursor frontier level fuel)[index]'(by
      rw [modelFrom_length]
      exact indexBound) =
      if cursor.testBit index then
        some frontier[level + index]!
      else
        none := by
  induction index generalizing cursor level fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [modelFrom, Nat.testBit_zero]
  | succ index inductionHypothesis =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [modelFrom, List.getElem_cons_succ]
          rw [inductionHypothesis (cursor := cursor / 2)
            (level := level + 1) (fuel := fuel) (by omega)]
          rw [← Nat.testBit_add_one cursor index]
          (congr 3; omega)

/-- The concrete cursor/frontier representation is definitionally the same
least-significant-bit model used by the Pool genesis and history invariant
bridge. -/
def modelFrontier (cursor : Nat) (frontier : List Digest) :
    List (Option Digest) :=
  (List.range 20).map fun level =>
    if cursor.testBit level then some frontier[level]! else none

theorem modelFrom_zero_twenty_eq_modelFrontier
    (cursor : Nat) (frontier : List Digest) :
    modelFrom cursor frontier 0 20 = modelFrontier cursor frontier := by
  apply List.ext_getElem
  · simp [modelFrom_length, modelFrontier]
  · intro index leftBound rightBound
    rw [modelFrom_getElem cursor frontier 0 20 index leftBound]
    simp [modelFrontier]

inductive ConcreteCarryResult where
  | more (frontier : List Digest)
  | full (root : Digest)

def concreteCarry (parent : Digest → Digest → Digest)
    (empty : List Digest) (cursor : Nat) (frontier : List Digest)
    (carry : Digest) (level : Nat) : Nat → ConcreteCarryResult
  | 0 => .full carry
  | fuel + 1 =>
      if cursor % 2 = 1 then
        concreteCarry parent empty (cursor / 2)
          (frontier.set level empty[level]!)
          (parent frontier[level]! carry) (level + 1) fuel
      else
        .more (frontier.set level carry)

theorem modelFrom_set_below
    (cursor : Nat) (frontier : List Digest) (level fuel changed : Nat)
    (value : Digest) (below : changed < level) :
    modelFrom cursor (frontier.set changed value) level fuel =
      modelFrom cursor frontier level fuel := by
  induction fuel generalizing cursor level with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [modelFrom]
      rw [List.set_getElem!_ne _ _ _ _ (by omega)]
      rw [inductionHypothesis (cursor := cursor / 2)
        (level := level + 1) (by omega)]

theorem appendCarry_modelFrom_exact
    (parent : Digest → Digest → Digest)
    (empty : List Digest) (cursor : Nat) (frontier : List Digest)
    (carry : Digest) (level fuel : Nat)
    (bound : level + fuel ≤ frontier.length) :
    match concreteCarry parent empty cursor frontier carry level fuel with
    | .more updated =>
        appendCarry parent carry (modelFrom cursor frontier level fuel) =
          .more (modelFrom (cursor + 1) updated level fuel)
    | .full root =>
        appendCarry parent carry (modelFrom cursor frontier level fuel) =
          .full root := by
  induction fuel generalizing cursor frontier carry level with
  | zero => simp [concreteCarry, modelFrom, appendCarry]
  | succ fuel inductionHypothesis =>
      by_cases odd : cursor % 2 = 1
      · simp only [concreteCarry, modelFrom, odd, if_pos, appendCarry]
        rw [← modelFrom_set_below (cursor / 2) frontier (level + 1)
          fuel level empty[level]! (by omega)]
        have recursive := inductionHypothesis
          (cursor := cursor / 2)
          (frontier := frontier.set level empty[level]!)
          (carry := parent frontier[level]! carry)
          (level := level + 1)
          (bound := by rw [List.length_set]; omega)
        cases result : concreteCarry parent empty (cursor / 2)
            (frontier.set level empty[level]!)
            (parent frontier[level]! carry) (level + 1) fuel with
        | more updated =>
            rw [result] at recursive
            simp only at recursive ⊢
            rw [recursive]
            have nextEven : (cursor + 1) % 2 = 0 := by omega
            have nextHalf : (cursor + 1) / 2 = cursor / 2 + 1 := by omega
            simp only [nextEven, if_false, nextHalf, zero_ne_one]
        | full root =>
            rw [result] at recursive
            simp only at recursive ⊢
            rw [recursive]
      · have even : cursor % 2 = 0 := by omega
        have nextOdd : (cursor + 1) % 2 = 1 := by omega
        have nextHalf : (cursor + 1) / 2 = cursor / 2 := by omega
        have indexBound : level < frontier.length := by omega
        simp only [concreteCarry, modelFrom, even, if_false, appendCarry,
          nextOdd, if_pos, nextHalf, zero_ne_one]
        rw [List.set_getElem!_eq _ _ _ _ ⟨indexBound, rfl⟩]
        rw [modelFrom_set_below (cursor / 2) frontier
          (level + 1) fuel level carry (by omega)]

def finalizedTraceResult (state : CarryState) : ConcreteCarryResult :=
  if state.2.2.val = 20 then
    .full state.2.1
  else
    .more (state.1.val.set state.2.2.val state.2.1)

theorem CarryTrace.concreteCarry_exact
    {parent : Digest → Digest → Digest}
    {self : GeneratedValidatedTree} {leafIndex : Std.U64}
    {before final : CarryState}
    (trace : CarryTrace parent self leafIndex before final)
    (levelBound : before.2.2.val ≤ 20) :
    concreteCarry parent self.empty.val
      (leafIndex.val >>> before.2.2.val) before.1.val before.2.1
      before.2.2.val (20 - before.2.2.val) =
        finalizedTraceResult final := by
  induction trace with
  | @terminal state terminal =>
      rcases state with ⟨frontier, carry, level⟩
      change level.val ≤ 20 at levelBound
      change 20 ≤ level.val ∨
        ∃ shifted : Std.U64, level.val < 20 ∧
          leafIndex >>> level = .ok shifted ∧
          shifted &&& 1#u64 ≠ 1#u64 at terminal
      change concreteCarry parent self.empty.val
        (leafIndex.val >>> level.val) frontier.val carry level.val
        (20 - level.val) = finalizedTraceResult (frontier, carry, level)
      rcases terminal with depth | ⟨shifted, levelLt, shiftRun, bitNotOne⟩
      · have levelEq : level.val = 20 := by omega
        simp [concreteCarry, finalizedTraceResult, levelEq]
      · have quotientNotOdd :
            (leafIndex.val >>> level.val) % 2 ≠ 1 := by
          intro odd
          exact bitNotOne
            ((carry_bit_one_iff_shifted_quotient_odd leafIndex shifted level
              levelLt shiftRun).2 odd)
        have quotientEven : (leafIndex.val >>> level.val) % 2 = 0 := by
          have modBound := Nat.mod_lt (leafIndex.val >>> level.val) (by omega : 0 < 2)
          omega
        have remaining : 20 - level.val = (19 - level.val) + 1 := by omega
        rw [remaining]
        simp [concreteCarry, finalizedTraceResult, quotientEven,
          show level.val ≠ 20 by omega]
  | @step before next final oneStep rest inductionHypothesis =>
      rcases before with ⟨frontier, carry, level⟩
      rcases oneStep with
        ⟨levelLt, shifted, shiftRun, bitOne, left, leftEq,
          emptyAtLevel, emptyEq, nextLevel, nextLevelVal, afterEq⟩
      change level.val ≤ 20 at levelBound
      change level.val < 20 at levelLt
      change leafIndex >>> level = .ok shifted at shiftRun
      change nextLevel.val = level.val + 1 at nextLevelVal
      change next =
        (frontier.set level emptyAtLevel, parent left carry, nextLevel) at afterEq
      subst next
      have nextBound : nextLevel.val ≤ 20 := by omega
      have quotientOdd : (leafIndex.val >>> level.val) % 2 = 1 :=
        (carry_bit_one_iff_shifted_quotient_odd leafIndex shifted level
          levelLt shiftRun).1 bitOne
      have remaining : 20 - level.val = (19 - level.val) + 1 := by omega
      have nextRemaining : 20 - nextLevel.val = 19 - level.val := by omega
      have frontierIndex : level.val < frontier.val.length := by
        simpa [frontier.property] using levelLt
      have emptyIndex : level.val < self.empty.val.length := by
        simpa [self.empty.property] using (show level.val < 21 by omega)
      have leftBang : frontier.val[level.val]! = left := by
        rw [← List.Inhabited_getElem_eq_getElem! frontier.val level.val frontierIndex]
        exact leftEq.symm
      have emptyBang : self.empty.val[level.val]! = emptyAtLevel := by
        rw [← List.Inhabited_getElem_eq_getElem! self.empty.val level.val emptyIndex]
        exact emptyEq.symm
      rw [remaining]
      simp only [concreteCarry, quotientOdd, if_pos]
      have recursive := inductionHypothesis nextBound
      simpa [Array.set_val_eq, nextLevelVal, nextRemaining,
        Nat.shiftRight_succ, leftBang, emptyBang] using recursive

theorem translated_append_loop_implies_abstract_appendCarry
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (leaf : Digest)
    (final : CarryState)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self leafIndex frontier leaf 0#usize = .ok final) :
    match finalizedTraceResult final with
    | .more updated =>
        appendCarry parent leaf
            (modelFrom leafIndex.val frontier.val 0 20) =
          .more (modelFrom (leafIndex.val + 1) updated 0 20)
    | .full root =>
        appendCarry parent leaf
            (modelFrom leafIndex.val frontier.val 0 20) = .full root := by
  have loopSpec := append_loop_has_recursive_source_trace
    parent parentExact self leafIndex (frontier, leaf, 0#usize)
  rw [run] at loopSpec
  simp only [WP.spec_ok] at loopSpec
  have concreteExact :=
    PoolV1TreeAppendOneAbstractBridge.CarryTrace.concreteCarry_exact
      loopSpec (by norm_num)
  have concreteExact0 :
      concreteCarry parent self.empty.val leafIndex.val frontier.val leaf
        0 20 = finalizedTraceResult final := by
    simpa using concreteExact
  have abstractExact := appendCarry_modelFrom_exact parent self.empty.val
    leafIndex.val frontier.val leaf 0 20 (by simp [frontier.property])
  rw [concreteExact0] at abstractExact
  exact abstractExact

/-- Literal translated carry-loop success, stated in the exact range/test-bit
frontier representation consumed by `PoolTreeHistoryInvariantV1`. -/
theorem translated_append_loop_implies_modelFrontier_appendCarry
    (parent : Digest → Digest → Digest)
    (parentExact : ParentCallbackExact parent)
    (self : GeneratedValidatedTree)
    (leafIndex : Std.U64)
    (frontier : Array Digest 20#usize)
    (leaf : Digest)
    (final : CarryState)
    (run :
      aspis_statement.pool_v1.incremental_merkle.ValidatedIncrementalMerkleTreeV1.append_one_loop
          self leafIndex frontier leaf 0#usize = .ok final) :
    match finalizedTraceResult final with
    | .more updated =>
        appendCarry parent leaf (modelFrontier leafIndex.val frontier.val) =
          .more (modelFrontier (leafIndex.val + 1) updated)
    | .full root =>
        appendCarry parent leaf (modelFrontier leafIndex.val frontier.val) =
          .full root := by
  simpa only [modelFrom_zero_twenty_eq_modelFrontier] using
    translated_append_loop_implies_abstract_appendCarry parent parentExact
      self leafIndex frontier leaf final run

#print axioms modelFrom_zero_twenty_eq_modelFrontier
#print axioms modelFrom_set_below
#print axioms appendCarry_modelFrom_exact
#print axioms CarryTrace.concreteCarry_exact
#print axioms translated_append_loop_implies_abstract_appendCarry
#print axioms translated_append_loop_implies_modelFrontier_appendCarry

end PoolV1TreeAppendOneAbstractBridge
