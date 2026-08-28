import V7BinaryFrontierLoopBridge
import Init.Data.List.Nat.Perm

/-!
# Pure insertion-sort model for the production frontier helper

The translated Rust loop shifts predecessors to the right and writes the saved
key once its insertion position is found.  The final list is the same as the
adjacent-swap `bubbleLeft` model below.  This file proves the model's sorted
prefix and permutation properties independently of the translated source.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7BinaryFrontierSource

set_option autoImplicit false

namespace V7BinaryFrontierSortModel

def swapWithPrevious (values : List Std.U32) (position : Nat) : List Std.U32 :=
  (values.set position values[position - 1]!).set (position - 1)
    values[position]!

@[simp] theorem swapWithPrevious_length
    (values : List Std.U32) (position : Nat) :
    (swapWithPrevious values position).length = values.length := by
  simp [swapWithPrevious]

def bubbleLeft : List Std.U32 → Nat → List Std.U32
  | values, 0 => values
  | values, position + 1 =>
      if position + 1 < values.length then
        if values[position + 1]! < values[position]! then
          bubbleLeft (swapWithPrevious values (position + 1)) position
        else values
      else values
termination_by _ position => position

private theorem inserted_prefix_pairwise
    (before after : List Std.U32) (key : Std.U32)
    (sorted : (before ++ after).Pairwise (.≤.))
    (beforeKey : ∀ x ∈ before, x ≤ key)
    (keyAfter : ∀ y ∈ after, key < y) :
    (before ++ key :: after).Pairwise (.≤.) := by
  rw [List.pairwise_append] at sorted ⊢
  rcases sorted with ⟨beforeSorted, afterSorted, cross⟩
  refine ⟨beforeSorted, ?_, ?_⟩
  · simp only [List.pairwise_cons]
    exact ⟨fun y member => (keyAfter y member).le, afterSorted⟩
  · intro x xMember y yMember
    rcases List.mem_cons.mp yMember with equality | yMember
    · subst y
      exact beforeKey x xMember
    · exact cross x xMember y yMember

private theorem pairwise_before_le_key_of_last
    (before : List Std.U32) (key : Std.U32)
    (sorted : before.Pairwise (.≤.))
    (nonempty : before ≠ [])
    (lastKey : before.getLast nonempty ≤ key) :
    ∀ x ∈ before, x ≤ key := by
  intro x member
  have xLast : x ≤ before.getLast nonempty := by
    have decomposition := List.dropLast_concat_getLast nonempty
    rw [← decomposition] at member sorted
    rcases List.mem_append.mp member with inInit | isLast
    · exact sorted.rel_of_mem_append inInit (by simp)
    · have equality : x = before.getLast nonempty := by simpa using isLast
      simpa [equality]
  exact xLast.trans lastKey

private def BubbleInv (original : List Std.U32) (target : Nat)
    (current : List Std.U32) (position : Nat) : Prop :=
  ∃ before after key suffix,
    before.length = position ∧
    before.length + after.length = target ∧
    original = (before ++ after) ++ key :: suffix ∧
    current = (before ++ key :: after) ++ suffix ∧
    (before ++ after).Pairwise (· ≤ ·) ∧
    ∀ value ∈ after, key < value

private theorem bubbleInv_initial
    (values : List Std.U32) (target : Nat)
    (targetBound : target < values.length)
    (prefixSorted : (values.take target).Pairwise (· ≤ ·)) :
    BubbleInv values target values target := by
  refine ⟨values.take target, [], values[target], values.drop (target + 1),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt targetBound)]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt targetBound)]
  · calc
      values = values.take (target + 1) ++ values.drop (target + 1) :=
        (List.take_append_drop (target + 1) values).symm
      _ = (values.take target ++ []) ++ values[target] ::
          values.drop (target + 1) := by
        rw [List.take_succ_eq_append_getElem targetBound]
        simp
  · calc
      values = values.take (target + 1) ++ values.drop (target + 1) :=
        (List.take_append_drop (target + 1) values).symm
      _ = (values.take target ++ values[target] :: []) ++
          values.drop (target + 1) := by
        rw [List.take_succ_eq_append_getElem targetBound]
  · simpa
  · simp

private theorem bubbleInv_active_bounds
    {original current : List Std.U32} {target position : Nat}
    (invariant : BubbleInv original target current position) :
    position ≤ target ∧ target < current.length := by
  rcases invariant with ⟨before, after, key, suffix, positionExact,
    targetExact, originalExact, currentExact, sorted, keyAfter⟩
  constructor
  · omega
  · rw [currentExact]
    simp only [List.length_append, List.length_cons]
    omega

private theorem adjacent_set_exact
    (before : List Std.U32) (previous key : Std.U32)
    (after : List Std.U32) :
    let values := before ++ previous :: key :: after
    (values.set (before.length + 1) previous).set before.length key =
      before ++ key :: previous :: after := by
  simp

private theorem bubbleInv_swap
    {original current : List Std.U32} {target position : Nat}
    (invariant : BubbleInv original target current position)
    (positive : 0 < position)
    (less : current[position]! < current[position - 1]!) :
    let swapped :=
      (current.set position current[position - 1]!).set (position - 1)
        current[position]!
    BubbleInv original target swapped (position - 1) := by
  rcases invariant with ⟨before, after, key, suffix, positionExact,
    targetExact, originalExact, currentExact, sorted, keyAfter⟩
  have beforeNonempty : before ≠ [] := by
    intro empty
    subst before
    simp at positionExact
    omega
  let init := before.dropLast
  let previous := before.getLast beforeNonempty
  have beforeDecomposition : init ++ [previous] = before :=
    List.dropLast_concat_getLast beforeNonempty
  have positionInit : position = init.length + 1 := by
    rw [← positionExact, ← beforeDecomposition]
    simp [init]
  have currentDecomposition :
      current = init ++ previous :: key :: (after ++ suffix) := by
    rw [currentExact, ← beforeDecomposition]
    simp [List.append_assoc]
  have keyRead : current[position]! = key := by
    rw [currentDecomposition, positionInit]
    simp
  have previousRead : current[position - 1]! = previous := by
    rw [currentDecomposition, positionInit]
    simp
  have keyPrevious : key < previous := by
    simpa only [keyRead, previousRead] using less
  refine ⟨init, previous :: after, key, suffix, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [← targetExact, ← beforeDecomposition]
    simp
    omega
  · rw [originalExact, ← beforeDecomposition]
    simp only [List.append_assoc, List.singleton_append]
  · rw [positionInit, currentDecomposition]
    have keyAt :
        (init ++ previous :: key :: (after ++ suffix))[init.length + 1]! =
          key := by simp
    have previousAt :
        (init ++ previous :: key :: (after ++ suffix))[init.length + 1 - 1]! =
          previous := by simp
    rw [keyAt, previousAt, Nat.add_sub_cancel]
    simpa only [List.append_assoc, List.cons_append] using
      (adjacent_set_exact init previous key (after ++ suffix))
  · rw [← beforeDecomposition] at sorted
    simpa only [List.append_assoc, List.singleton_append] using sorted
  · intro value member
    rcases List.mem_cons.mp member with equality | member
    · subst value
      exact keyPrevious
    · exact keyAfter value member

private theorem bubbleInv_done_prefix_sorted
    {original current : List Std.U32} {target position : Nat}
    (invariant : BubbleInv original target current position)
    (done : position = 0 ∨
      current[position - 1]! ≤ current[position]!) :
    (current.take (target + 1)).Pairwise (· ≤ ·) := by
  rcases invariant with ⟨before, after, key, suffix, positionExact,
    targetExact, originalExact, currentExact, sorted, keyAfter⟩
  have prefixTake : current.take (target + 1) = before ++ key :: after := by
    rw [currentExact]
    have lengthExact : (before ++ key :: after).length = target + 1 := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [← lengthExact, List.take_left]
  rw [prefixTake]
  apply inserted_prefix_pairwise before after key sorted
  · rcases done with zero | boundary
    · have empty : before = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [empty]
    · by_cases beforeEmpty : before = []
      · simp [beforeEmpty]
      · have positionLength : position = before.length := positionExact.symm
        have keyRead : current[position]! = key := by
          rw [currentExact, positionLength]
          simp
        let init := before.dropLast
        let previous := before.getLast beforeEmpty
        have beforeDecomposition : init ++ [previous] = before :=
          List.dropLast_concat_getLast beforeEmpty
        have positionInit : position = init.length + 1 := by
          rw [positionLength, ← beforeDecomposition]
          simp [init]
        have lastRead : current[position - 1]! = previous := by
          rw [currentExact, ← beforeDecomposition, positionInit]
          simp [List.append_assoc]
        exact pairwise_before_le_key_of_last before key
          (List.pairwise_append.mp sorted).1 beforeEmpty
          (by simpa only [previous, lastRead, keyRead] using boundary)
  · exact keyAfter

private theorem bubbleInv_perm
    {original current : List Std.U32} {target position : Nat}
    (invariant : BubbleInv original target current position) :
    current.Perm original := by
  rcases invariant with ⟨before, after, key, suffix, positionExact,
    targetExact, originalExact, currentExact, sorted, keyAfter⟩
  rw [currentExact, originalExact]
  have move : List.Perm (key :: after) (after ++ [key]) := by
    simpa using
      (List.perm_append_comm : List.Perm ([key] ++ after) (after ++ [key]))
  simpa only [List.append_assoc, List.singleton_append] using
    List.Perm.append_right suffix (List.Perm.append_left before move)

private theorem bubbleLeft_reaches_done
    {original current : List Std.U32} {target position : Nat}
    (invariant : BubbleInv original target current position) :
    ∃ finalPosition,
      BubbleInv original target (bubbleLeft current position) finalPosition ∧
      (finalPosition = 0 ∨
        (bubbleLeft current position)[finalPosition - 1]! ≤
          (bubbleLeft current position)[finalPosition]!) := by
  induction position generalizing current with
  | zero =>
      refine ⟨0, ?_, Or.inl rfl⟩
      simpa only [bubbleLeft] using invariant
  | succ previous ih =>
      have bounds := bubbleInv_active_bounds invariant
      have active : previous + 1 < current.length := by omega
      rw [bubbleLeft, if_pos active]
      by_cases less : current[previous + 1]! < current[previous]!
      · rw [if_pos less]
        have nextInvariant :
            BubbleInv original target
              (swapWithPrevious current (previous + 1)) previous := by
          simpa only [swapWithPrevious, Nat.add_sub_cancel] using
            (bubbleInv_swap invariant (by omega) less)
        exact ih nextInvariant
      · rw [if_neg less]
        refine ⟨previous + 1, invariant, Or.inr ?_⟩
        simp only [Nat.add_sub_cancel]
        exact le_of_not_gt less

theorem bubbleLeft_sorted_prefix
    (values : List Std.U32) (target : Nat)
    (targetBound : target < values.length)
    (prefixSorted : (values.take target).Pairwise (· ≤ ·)) :
    ((bubbleLeft values target).take (target + 1)).Pairwise (· ≤ ·) := by
  obtain ⟨finalPosition, invariant, done⟩ :=
    bubbleLeft_reaches_done
      (bubbleInv_initial values target targetBound prefixSorted)
  exact bubbleInv_done_prefix_sorted invariant done

theorem bubbleLeft_perm
    (values : List Std.U32) (target : Nat)
    (targetBound : target < values.length)
    (prefixSorted : (values.take target).Pairwise (· ≤ ·)) :
    (bubbleLeft values target).Perm values := by
  obtain ⟨finalPosition, invariant, done⟩ :=
    bubbleLeft_reaches_done
      (bubbleInv_initial values target targetBound prefixSorted)
  exact bubbleInv_perm invariant

@[simp] theorem bubbleLeft_length
    (values : List Std.U32) (position : Nat) :
    (bubbleLeft values position).length = values.length := by
  induction position generalizing values with
  | zero => simp only [bubbleLeft]
  | succ previous ih =>
      rw [bubbleLeft]
      split
      · split
        · rw [ih, swapWithPrevious_length]
        · rfl
      · rfl

#print axioms bubbleLeft_sorted_prefix
#print axioms bubbleLeft_perm
#print axioms bubbleLeft_length

end V7BinaryFrontierSortModel
