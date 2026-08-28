import V7FirstCompactFrontierBodyBridge

/-!
# Exact translated windows-loop frontier sum

This file lifts the literal translated body theorem through Aeneas' generic
`loop`.  Its target is the ordered, duplicate-free list already established by
the preceding production validation loop.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7FirstCompactSource

set_option autoImplicit false

namespace V7FirstCompactFrontierLoopBridge

def adjacentXorLogSum : List Std.U32 → Nat
  | left :: right :: rest =>
      Nat.log2 (Nat.xor left.val right.val) +
        adjacentXorLogSum (right :: rest)
  | _ => 0
termination_by values => values.length

theorem translated_windows_loop_exact
    (remaining : List Std.U32)
    (iterator : core.slice.iter.Windows Std.U32)
    (expanded : Std.Usize)
    (widthExact : iterator.width.val = 2)
    (remainingExact : iterator.slice.val.drop iterator.index = remaining)
    (distinct : remaining.Pairwise (fun left right => left.val ≠ right.val))
    (headroom : expanded.val + adjacentXorLogSum remaining ≤ Std.Usize.max) :
    ∃ output : Std.Usize,
      v6_onefold.binary_frontier_nodes_loop2 iterator expanded = .ok output ∧
      output.val = expanded.val + adjacentXorLogSum remaining := by
  cases remaining with
  | nil =>
      have stop : iterator.slice.val.length < iterator.index + iterator.width.val := by
        rw [widthExact]
        have lengthDrop := congrArg List.length remainingExact
        simp at lengthDrop
        omega
      have nextNone :
          core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
              iterator = .ok (none, iterator) := by
        unfold
          core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
        rw [if_neg (by omega)]
      have bodyDone :
          v6_onefold.binary_frontier_nodes_loop2.body iterator expanded =
            .ok (.done expanded) := by
        unfold v6_onefold.binary_frontier_nodes_loop2.body
        rw [nextNone]
        rfl
      refine ⟨expanded, ?_, by simp [adjacentXorLogSum]⟩
      simpa only [v6_onefold.binary_frontier_nodes_loop2, loop.eq_def,
        bodyDone]
  | cons left tail =>
      cases tail with
      | nil =>
          have stop : iterator.slice.val.length < iterator.index + iterator.width.val := by
            rw [widthExact]
            have lengthDrop := congrArg List.length remainingExact
            simp at lengthDrop
            omega
          have nextNone :
              core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
                  iterator = .ok (none, iterator) := by
            unfold
              core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
            rw [if_neg (by omega)]
          have bodyDone :
              v6_onefold.binary_frontier_nodes_loop2.body iterator expanded =
                .ok (.done expanded) := by
            unfold v6_onefold.binary_frontier_nodes_loop2.body
            rw [nextNone]
            rfl
          refine ⟨expanded, ?_, by simp [adjacentXorLogSum]⟩
          simpa only [v6_onefold.binary_frontier_nodes_loop2, loop.eq_def,
            bodyDone]
      | cons right rest =>
          let next : core.slice.iter.Windows Std.U32 :=
            { iterator with index := iterator.index + 1 }
          let pair := core.slice.iter.Windows.windowAt iterator.slice
            iterator.index iterator.width.val
          have canContinue :
              iterator.index + iterator.width.val ≤ iterator.slice.val.length := by
            rw [widthExact]
            have lengthDrop := congrArg List.length remainingExact
            simp at lengthDrop
            omega
          have nextExact :
              core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
                  iterator = .ok (some pair, next) := by
            unfold
              core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
            rw [if_pos canContinue]
          have pairValue : pair.val = [left, right] := by
            simp [pair, core.slice.iter.Windows.windowAt, widthExact,
              remainingExact]
          have pairZero : Slice.index_usize pair 0#usize = .ok left := by
            simp [Slice.index_usize, pairValue]
          have pairOne : Slice.index_usize pair 1#usize = .ok right := by
            simp [Slice.index_usize, pairValue]
          have headDistinct : left.val ≠ right.val := by
            exact List.rel_of_pairwise_cons distinct (by simp)
          have xorNonzero : Nat.xor left.val right.val ≠ 0 := by
            simpa [Nat.xor_eq_zero_iff] using headDistinct
          have remainingNext :
              next.slice.val.drop next.index = right :: rest := by
            simp [next]
            rw [List.drop_add_one_eq_tail_drop, remainingExact]
            rfl
          have distinctNext :
              (right :: rest).Pairwise
                (fun a b => a.val ≠ b.val) := by
            simpa using distinct.tail
          have expandedHeadroom :
              expanded.val + Nat.log2 (Nat.xor left.val right.val) +
                  adjacentXorLogSum (right :: rest) ≤ Std.Usize.max := by
            simpa [adjacentXorLogSum, Nat.add_assoc] using headroom
          have bodyHeadroom :
              expanded.val + Nat.log2 (Nat.xor left.val right.val) ≤
                Std.Usize.max := by
            omega
          obtain ⟨bodyExpanded, bodySuccess, bodyValue⟩ :=
            V7FirstCompactFrontierBodyBridge.source_frontier_body_succeeds_exact_log2
              iterator next pair left right expanded nextExact pairZero pairOne
              xorNonzero bodyHeadroom
          have recursiveHeadroom :
              bodyExpanded.val + adjacentXorLogSum (right :: rest) ≤
                Std.Usize.max := by
            rw [bodyValue]
            exact expandedHeadroom
          obtain ⟨output, loopSuccess, outputValue⟩ :=
            translated_windows_loop_exact (right :: rest) next bodyExpanded
              widthExact remainingNext distinctNext recursiveHeadroom
          refine ⟨output, ?_, ?_⟩
          · unfold v6_onefold.binary_frontier_nodes_loop2
            rw [loop.eq_def]
            simp only
            rw [bodySuccess]
            exact loopSuccess
          · rw [adjacentXorLogSum]
            rw [outputValue, bodyValue]
            omega
termination_by remaining.length
decreasing_by simp_all

#print axioms translated_windows_loop_exact

end V7FirstCompactFrontierLoopBridge
