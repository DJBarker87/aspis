import V7BinaryFrontierSortSourceBridge
import AspisFormal.K1.V7Tag73Q16PointwiseFrontierBridge
import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Literal binary-frontier source to the exact K1.3 semantic recurrence

This module specializes the translated production helper to Tag-73's fixed
`q = 16`, depth-18 query schedule.  It constructs the exact Rust array from
the semantic injection, proves that production sorting returns the canonical
increasing schedule, and identifies the returned adjacent-XOR expression with
the maintained semantic frontier theorem.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace V7BinaryFrontierK13Integration

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73PointwiseFrontierXor
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16PointwiseFrontierBridge
open V7BinaryFrontierSource
open V7BinaryFrontierLoopBridge
open V7BinaryFrontierSortSourceBridge

noncomputable section

private theorem query_position_u32_bound
    (schedule : QuerySchedule) (slot : Fin 16) :
    (schedule.positions slot).val < 2 ^ UScalarTy.U32.numBits := by
  have positionBound := (schedule.positions slot).isLt
  rw [UScalarTy.U32_numBits_eq]
  omega

/-- The exact fixed Rust array consumed by `binary_frontier_nodes`. -/
def queryScheduleArray (schedule : QuerySchedule) :
    Array Std.U32 16#usize :=
  ⟨List.ofFn (fun slot : Fin 16 =>
      Std.U32.ofNatCore (schedule.positions slot).val
        (query_position_u32_bound schedule slot)), by simp⟩

theorem query_schedule_array_nodup (schedule : QuerySchedule) :
    (queryScheduleArray schedule).val.Nodup := by
  apply List.nodup_ofFn.mpr
  intro left right equality
  apply schedule.positions.injective
  apply Fin.ext
  have values := congrArg UScalar.val equality
  simpa [queryScheduleArray, Std.U32.ofNatCore_val_eq] using values

theorem query_schedule_array_bounded (schedule : QuerySchedule) :
    ∀ value ∈ (queryScheduleArray schedule).val,
      value.val < 2 ^ 18 := by
  intro value membership
  rw [queryScheduleArray] at membership
  simp only [List.mem_ofFn] at membership
  obtain ⟨slot, valueExact⟩ := membership
  subst value
  simpa [Std.U32.ofNatCore_val_eq] using (schedule.positions slot).isLt

theorem query_schedule_array_values_toFinset (schedule : QuerySchedule) :
    ((queryScheduleArray schedule).val.map UScalar.val).toFinset =
      queryPositionNatFinset schedule.positions := by
  unfold queryPositionNatFinset queryPositionFinset
  rw [Finset.map_map, Fin.univ_map_def]
  apply Finset.ext
  intro position
  simp [queryScheduleArray, Std.U32.ofNatCore_val_eq]

private theorem sorted_values_pairwise
    {Q : Std.Usize} {values : Array Std.U32 Q}
    (sorted : values.val.Pairwise (· ≤ ·)) :
    (values.val.map UScalar.val).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact sorted.imp (fun relation => by simpa using relation)

private theorem sorted_values_nodup
    {Q : Std.Usize} {values : Array Std.U32 Q}
    (distinct : values.val.Pairwise
      (fun left right => left.val ≠ right.val)) :
    (values.val.map UScalar.val).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_map]
  exact distinct

/-- Any translated sorted permutation of the operational q16 array is the
exact canonical increasing position list used by the semantic theorem. -/
theorem translated_sorted_values_eq_semantic_sorted
    (schedule : QuerySchedule) (sorted : Array Std.U32 16#usize)
    (post : OuterSortPost (queryScheduleArray schedule).val sorted) :
    sorted.val.map UScalar.val = sortedQueryPositions schedule.positions := by
  have distinct := sorted_output_pairwise_distinct
    (queryScheduleArray schedule) sorted (query_schedule_array_nodup schedule)
    post.perm
  have valuesSorted := sorted_values_pairwise post.sorted
  have valuesNodup := sorted_values_nodup distinct
  have canonical :=
    (List.toFinset_sort (· ≤ ·) valuesNodup).2 valuesSorted
  have finsetExact : (sorted.val.map UScalar.val).toFinset =
      queryPositionNatFinset schedule.positions := by
    calc
      (sorted.val.map UScalar.val).toFinset =
          ((queryScheduleArray schedule).val.map UScalar.val).toFinset := by
        apply Finset.ext
        intro position
        simpa using (post.perm.map UScalar.val).mem_iff
      _ = queryPositionNatFinset schedule.positions :=
        query_schedule_array_values_toFinset schedule
  rw [finsetExact] at canonical
  exact canonical.symm

private theorem adjacent_xor_log_sum_from_map_val
    (previous : Std.U32) (rest : List Std.U32) :
    adjacentXorLogSum (previous :: rest) =
      adjacentXorSumFrom previous.val (rest.map UScalar.val) := by
  induction rest generalizing previous with
  | nil => simp [adjacentXorLogSum, adjacentXorSumFrom]
  | cons next tail inductionHypothesis =>
      simp only [adjacentXorLogSum, adjacentXorSumFrom, List.map_cons]
      rw [inductionHypothesis next]

theorem adjacent_xor_log_sum_map_val (values : List Std.U32) :
    adjacentXorLogSum values = adjacentXorSum (values.map UScalar.val) := by
  cases values with
  | nil => simp [adjacentXorLogSum, adjacentXorSum]
  | cons first rest =>
      simp only [adjacentXorSum, List.map_cons]
      exact adjacent_xor_log_sum_from_map_val first rest

/-- Executable source-facing frontier value.  Failure maps to zero only so
the function is total; the q16 theorem proves that the failure arm is
unreachable for every operational schedule. -/
def translatedFrontierNodes (schedule : QuerySchedule) : Nat :=
  match v6_onefold.binary_frontier_nodes (queryScheduleArray schedule) 18#u8 with
  | .ok (.Ok output) => output.val
  | _ => 0

/-- The literal translated Rust helper computes exactly the maintained K1.3
semantic frontier recurrence for every operational Tag-73 schedule. -/
theorem translated_frontier_nodes_eq_semantic (schedule : QuerySchedule) :
    translatedFrontierNodes schedule =
      semanticFrontierNodes schedule.positions := by
  obtain ⟨sorted, output, sourceRun, post, outputValue⟩ :=
    translated_binary_frontier_q16_exact (queryScheduleArray schedule)
      (query_schedule_array_nodup schedule)
      (query_schedule_array_bounded schedule)
  have sortedExact :=
    translated_sorted_values_eq_semantic_sorted schedule sorted post
  have adjacentExact := adjacent_xor_log_sum_map_val sorted.val
  unfold translatedFrontierNodes
  rw [sourceRun]
  rw [semantic_frontier_eq_sorted_adjacent_xor]
  rw [← sortedExact, ← adjacentExact]
  norm_num at outputValue ⊢
  exact outputValue

#print axioms query_schedule_array_nodup
#print axioms query_schedule_array_bounded
#print axioms translated_sorted_values_eq_semantic_sorted
#print axioms adjacent_xor_log_sum_map_val
#print axioms translated_frontier_nodes_eq_semantic

end

end V7BinaryFrontierK13Integration
