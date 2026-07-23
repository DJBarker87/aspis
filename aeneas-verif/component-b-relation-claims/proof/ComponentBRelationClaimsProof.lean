import ComponentBRelationClaimsGenerated
import MultilinearEvalPortableCapstones

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace aspis_prover.ComponentBRelationClaimsProof

open aspis_prover.MultilinearEvalProofs
open AspisV5ComponentADeployedTerminalApplicability

abbrev GeneratedQM31 := aspis_core.field.QM31
abbrev ExactQM31 := aspis_prover.MultilinearEvalProofs.ExactQM31

local instance : Inhabited GeneratedQM31 := ⟨aspis_core.field.QM31.ZERO⟩

private theorem generated_zero_canonical :
    GeneratedCanonicalQM31 aspis_core.field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    aspis_core.field.QM31.ZERO]

private theorem generated_zero_exact :
    generatedQm31ToExact aspis_core.field.QM31.ZERO = (0 : ExactQM31) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        aspis_core.field.QM31.ZERO]

def exactSliceEntry (values : Slice GeneratedQM31) (index : Nat) : ExactQM31 :=
  generatedQm31ToExact values.val[index]!

private theorem exactSliceEntry_eq
    (values : Slice GeneratedQM31) (index : Nat)
    (hindex : index < values.val.length) :
    exactSliceEntry values index = generatedQm31ToExact values.val[index] := by
  unfold exactSliceEntry
  congr 1
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem slice_index_run
    (values : Slice GeneratedQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val] := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem vec_index_run
    (values : alloc.vec.Vec GeneratedQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice GeneratedQM31) values index =
      ok values.val[index.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  simpa [valueEq] using run

private theorem wrapping_succ_exact
    (index : Std.Usize) (hindex : index.val < 1024) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have one : (1#usize : Std.Usize).val = 1 := rfl
  rw [one]
  apply Nat.mod_eq_of_lt
  have room : 1025 < UScalar.size .Usize := by
    have h := (1025#usize).hSize
    scalar_tac
  omega

/-- The source-extracted dense terminal loop is the exact row-ordered dot
product.  This theorem is arbitrary in the canonical message and covector;
it does not assume the Component-B layout. -/
theorem extracted_terminal_loop_exact
    (message : alloc.vec.Vec GeneratedQM31)
    (terminalCovector : Slice GeneratedQM31)
    (messageLength : message.val.length = 1024)
    (covectorLength : terminalCovector.val.length = 1024)
    (messageCanonical : GeneratedCanonicalQM31List message.val)
    (covectorCanonical : GeneratedCanonicalQM31List terminalCovector.val)
    (terminal : GeneratedQM31) (terminalCanonical : GeneratedCanonicalQM31 terminal)
    (row : Std.Usize) (rowBound : row.val ≤ 1024) :
    ∃ out,
      v5_mask.split_layer_zero.evaluate_component_b_relation_claims_loop
          terminalCovector message terminal row = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact terminal +
        ∑ index ∈ Finset.Ico row.val 1024,
          exactSliceEntry terminalCovector index *
            generatedQm31ToExact message.val[index]! := by
  have messageLenScalar : alloc.vec.Vec.len message = 1024#usize := by
    apply UScalar.val_eq_imp
    simpa using messageLength
  have covectorLenScalar : terminalCovector.len = 1024#usize := by
    apply UScalar.val_eq_imp
    simpa [Slice.len_val] using covectorLength
  unfold v5_mask.split_layer_zero.evaluate_component_b_relation_claims_loop
  by_cases more : row.val < 1024
  · have rowMessage : row.val < message.val.length := by omega
    have rowCovector : row.val < terminalCovector.val.length := by omega
    have moreScalar : row < 1024#usize := more
    rw [messageLenScalar, if_pos moreScalar, covectorLenScalar,
      if_pos moreScalar]
    have covectorRead := slice_index_run terminalCovector row rowCovector
    have messageRead := vec_index_run message row rowMessage
    rw [covectorRead, messageRead]
    simp only [bind_tc_ok]
    have covectorAtCanonical :
        GeneratedCanonicalQM31 terminalCovector.val[row.val] :=
      covectorCanonical _ (List.getElem_mem rowCovector)
    have messageAtCanonical : GeneratedCanonicalQM31 message.val[row.val] :=
      messageCanonical _ (List.getElem_mem rowMessage)
    obtain ⟨product, productRun, productCanonical, productExact⟩ :=
      generated_qm31_mul_corresponds
        terminalCovector.val[row.val] message.val[row.val]
        covectorAtCanonical messageAtCanonical
    rw [productRun]
    simp only [bind_tc_ok]
    obtain ⟨nextTerminal, addRun, nextCanonical, nextExact⟩ :=
      generated_qm31_add_corresponds terminal product
        terminalCanonical productCanonical
    rw [addRun]
    simp only [bind_tc_ok, lift]
    let nextRow := Std.Usize.wrapping_add row 1#usize
    have nextRowValue : nextRow.val = row.val + 1 :=
      wrapping_succ_exact row more
    have nextBound : nextRow.val ≤ 1024 := by omega
    obtain ⟨out, loopRun, outCanonical, outExact⟩ :=
      extracted_terminal_loop_exact message terminalCovector
        messageLength covectorLength messageCanonical covectorCanonical
        nextTerminal nextCanonical nextRow nextBound
    rw [show Std.Usize.wrapping_add row 1#usize = nextRow from rfl, loopRun]
    refine ⟨out, rfl, outCanonical, ?_⟩
    rw [outExact, nextExact, productExact]
    rw [← exactSliceEntry_eq terminalCovector row.val rowCovector]
    have messageBang : message.val[row.val]! = message.val[row.val] := by
      apply List.getElem!_of_getElem?
      simp [rowMessage]
    rw [← messageBang]
    rw [nextRowValue]
    let summand := fun index ↦
      exactSliceEntry terminalCovector index *
        generatedQm31ToExact message.val[index]!
    have split := Finset.sum_Ico_consecutive summand
      (Nat.le_succ row.val) (show row.val + 1 ≤ 1024 by omega)
    have singleton :
        ∑ index ∈ Finset.Ico row.val (row.val + 1), summand index =
          summand row.val := by
      rw [Finset.sum_Ico_succ_top (Nat.le_refl row.val)]
      simp
    rw [← split, singleton]
    change generatedQm31ToExact terminal + summand row.val +
        ∑ index ∈ Finset.Ico (row.val + 1) 1024, summand index =
      generatedQm31ToExact terminal +
        (summand row.val +
          ∑ index ∈ Finset.Ico (row.val + 1) 1024, summand index)
    ring
  · have done : row.val = 1024 := by omega
    have doneScalar : ¬ row < (1024#usize) := by
      simp [done]
    rw [messageLenScalar, if_neg doneScalar]
    refine ⟨terminal, rfl, terminalCanonical, ?_⟩
    simp [done]
termination_by 1024 - row.val
decreasing_by
  rw [nextRowValue]
  omega

private theorem array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize} (values : Array T N)
    (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have actualBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hElem : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, hElem] using run

private theorem array_update_run
    {T : Type} {N : Std.Usize} (values : Array T N)
    (index : Std.Usize) (value : T) (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨updated, run, updatedEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [updatedEq] using run

/-- The production helper selects the second committed C2 message. -/
def generatedComponentBMessage
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize) :
    alloc.vec.Vec GeneratedQM31 :=
  c2Messages.val[(1#usize).val]!

/-- One of the three fixed transcript points consumed by the helper. -/
def generatedRelationPoint
    (points : Array (Array GeneratedQM31 10#usize) 3#usize)
    (index : Std.Usize) : Slice GeneratedQM31 :=
  Array.to_slice points.val[index.val]!

private theorem generatedRelationPoint_length
    (points : Array (Array GeneratedQM31 10#usize) 3#usize)
    (index : Std.Usize) :
    (generatedSliceValues (generatedRelationPoint points index)).length = 10 := by
  simp [generatedRelationPoint, generatedSliceValues, Array.to_slice]

def generatedClaimsArray
    (out0 out1 out2 terminal : GeneratedQM31) :
    Array GeneratedQM31 4#usize :=
  ((((Array.repeat 4#usize aspis_core.field.QM31.ZERO).set 0#usize out0).set
      1#usize out1).set 2#usize out2).set 3#usize terminal

/-- End-to-end execution of the source-extracted Component-B consumer.

The selected coefficients are literally `c2_messages[1]`; the three point
slots remain in source order 0, 1, 2; and slot 3 is the row-ordered terminal
dot.  No caller-supplied lane selector or abstract evaluator appears in this
statement. -/
theorem extracted_component_b_relation_claims_exact
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize)
    (points : Array (Array GeneratedQM31 10#usize) 3#usize)
    (terminalCovector : Slice GeneratedQM31)
    (messageLength : (generatedComponentBMessage c2Messages).val.length = 1024)
    (covectorLength : terminalCovector.val.length = 1024)
    (messageCanonical :
      GeneratedCanonicalQM31List (generatedComponentBMessage c2Messages).val)
    (point0Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 0#usize).val)
    (point1Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 1#usize).val)
    (point2Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 2#usize).val)
    (covectorCanonical : GeneratedCanonicalQM31List terminalCovector.val) :
    ∃ out0 out1 out2 terminal,
      v5_mask.split_layer_zero.evaluate_component_b_relation_claims
          c2Messages points terminalCovector =
        ok (generatedClaimsArray out0 out1 out2 terminal) ∧
      GeneratedCanonicalQM31 out0 ∧
      GeneratedCanonicalQM31 out1 ∧
      GeneratedCanonicalQM31 out2 ∧
      GeneratedCanonicalQM31 terminal ∧
      generatedQm31ToExact out0 =
        multilinearEvalValue
          (maintainedPointOfGeneratedSlice (generatedRelationPoint points 0#usize)
            (generatedRelationPoint_length points 0#usize))
          (maintainedMessageOfGeneratedQm31Slice
            (alloc.vec.Vec.deref (generatedComponentBMessage c2Messages))
            messageLength) ∧
      generatedQm31ToExact out1 =
        multilinearEvalValue
          (maintainedPointOfGeneratedSlice (generatedRelationPoint points 1#usize)
            (generatedRelationPoint_length points 1#usize))
          (maintainedMessageOfGeneratedQm31Slice
            (alloc.vec.Vec.deref (generatedComponentBMessage c2Messages))
            messageLength) ∧
      generatedQm31ToExact out2 =
        multilinearEvalValue
          (maintainedPointOfGeneratedSlice (generatedRelationPoint points 2#usize)
            (generatedRelationPoint_length points 2#usize))
          (maintainedMessageOfGeneratedQm31Slice
            (alloc.vec.Vec.deref (generatedComponentBMessage c2Messages))
            messageLength) ∧
      generatedQm31ToExact terminal =
        ∑ row ∈ Finset.Ico 0 1024,
          exactSliceEntry terminalCovector row *
            generatedQm31ToExact
              (generatedComponentBMessage c2Messages).val[row]! := by
  let message := generatedComponentBMessage c2Messages
  let coefficients := alloc.vec.Vec.deref message
  let point0 := generatedRelationPoint points 0#usize
  let point1 := generatedRelationPoint points 1#usize
  let point2 := generatedRelationPoint points 2#usize
  have point0Length := generatedRelationPoint_length points 0#usize
  have point1Length := generatedRelationPoint_length points 1#usize
  have point2Length := generatedRelationPoint_length points 2#usize
  obtain ⟨out0, run0, out0Canonical, out0Exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (extracted_extension_entrypoint_maintained_mle_unconditional
      coefficients point0 point0Length messageLength messageCanonical
      point0Canonical)
  obtain ⟨out1, run1, out1Canonical, out1Exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (extracted_extension_entrypoint_maintained_mle_unconditional
      coefficients point1 point1Length messageLength messageCanonical
      point1Canonical)
  obtain ⟨out2, run2, out2Canonical, out2Exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (extracted_extension_entrypoint_maintained_mle_unconditional
      coefficients point2 point2Length messageLength messageCanonical
      point2Canonical)
  obtain ⟨terminal, terminalRun, terminalCanonical, terminalExact⟩ :=
    extracted_terminal_loop_exact message terminalCovector messageLength
      covectorLength messageCanonical covectorCanonical
      aspis_core.field.QM31.ZERO generated_zero_canonical 0#usize (by decide)
  have c2Read := array_index_run c2Messages 1#usize (by decide)
  have point0Read := array_index_run points 0#usize (by decide)
  have point1Read := array_index_run points 1#usize (by decide)
  have point2Read := array_index_run points 2#usize (by decide)
  have update0 := array_update_run
    (Array.repeat 4#usize aspis_core.field.QM31.ZERO) 0#usize out0 (by decide)
  have update1 := array_update_run
    ((Array.repeat 4#usize aspis_core.field.QM31.ZERO).set 0#usize out0)
      1#usize out1 (by decide)
  have update2 := array_update_run
    (((Array.repeat 4#usize aspis_core.field.QM31.ZERO).set 0#usize out0).set
      1#usize out1) 2#usize out2 (by decide)
  have update3 := array_update_run
    ((((Array.repeat 4#usize aspis_core.field.QM31.ZERO).set 0#usize out0).set
      1#usize out1).set 2#usize out2) 3#usize terminal (by decide)
  dsimp [coefficients, point0, point1, point2, message,
    generatedComponentBMessage, generatedRelationPoint] at run0 run1 run2 terminalRun
  refine ⟨out0, out1, out2, terminal, ?_, out0Canonical, out1Canonical,
    out2Canonical, terminalCanonical, ?_, ?_, ?_, ?_⟩
  · unfold v5_mask.split_layer_zero.evaluate_component_b_relation_claims
    rw [c2Read]
    simp only [bind_tc_ok]
    rw [point0Read]
    simp only [lift, bind_tc_ok]
    rw [run0]
    simp only [bind_tc_ok]
    rw [update0]
    simp only [bind_tc_ok]
    rw [point1Read]
    simp only [bind_tc_ok]
    rw [run1]
    simp only [bind_tc_ok]
    rw [update1]
    simp only [bind_tc_ok]
    rw [point2Read]
    simp only [bind_tc_ok]
    rw [run2]
    simp only [bind_tc_ok]
    rw [update2]
    simp only [bind_tc_ok]
    rw [terminalRun]
    simp only [bind_tc_ok]
    simpa [generatedClaimsArray,
      v5_mask.split_layer_zero.V5_RELATION_POINT_CLAIMS] using update3
  · simpa [coefficients, point0, message] using out0Exact
  · simpa [coefficients, point1, message] using out1Exact
  · simpa [coefficients, point2, message] using out2Exact
  · simpa [generated_zero_exact] using terminalExact

/-- Concrete non-vacuity: the authentic helper executes successfully on the
canonical all-zero committed messages, points, and terminal covector. -/
theorem extracted_component_b_relation_claims_zero_nonvacuous :
    ∃ (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize)
      (points : Array (Array GeneratedQM31 10#usize) 3#usize)
      (terminalCovector : Slice GeneratedQM31)
      (out : Array GeneratedQM31 4#usize),
      v5_mask.split_layer_zero.evaluate_component_b_relation_claims
          c2Messages points terminalCovector = ok out := by
  let zeroVec : alloc.vec.Vec GeneratedQM31 :=
    ⟨List.replicate 1024 aspis_core.field.QM31.ZERO, by
      have bound := (1024#usize).hSize
      simp only [List.length_replicate]
      scalar_tac⟩
  let zeroPoint : Array GeneratedQM31 10#usize :=
    Array.repeat 10#usize aspis_core.field.QM31.ZERO
  let c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize :=
    ⟨[zeroVec, zeroVec, zeroVec], by decide⟩
  let points : Array (Array GeneratedQM31 10#usize) 3#usize :=
    ⟨[zeroPoint, zeroPoint, zeroPoint], by decide⟩
  let terminalCovector : Slice GeneratedQM31 :=
    ⟨List.replicate 1024 aspis_core.field.QM31.ZERO, by
      have bound := (1024#usize).hSize
      simp only [List.length_replicate]
      scalar_tac⟩
  have zeroCanonical (count : Nat) :
      GeneratedCanonicalQM31List
        (List.replicate count aspis_core.field.QM31.ZERO) := by
    intro value member
    simp only [List.mem_replicate] at member
    exact member.2 ▸ generated_zero_canonical
  have messageLength :
      (generatedComponentBMessage c2Messages).val.length = 1024 := by
    change (List.replicate 1024 aspis_core.field.QM31.ZERO).length = 1024
    simp only [List.length_replicate]
  have messageCanonical :
      GeneratedCanonicalQM31List
        (generatedComponentBMessage c2Messages).val := by
    change GeneratedCanonicalQM31List
      (List.replicate 1024 aspis_core.field.QM31.ZERO)
    exact zeroCanonical 1024
  have point0Canonical :
      GeneratedCanonicalQM31List
        (generatedRelationPoint points 0#usize).val := by
    change GeneratedCanonicalQM31List
      (List.replicate 10 aspis_core.field.QM31.ZERO)
    exact zeroCanonical 10
  have point1Canonical :
      GeneratedCanonicalQM31List
        (generatedRelationPoint points 1#usize).val := by
    change GeneratedCanonicalQM31List
      (List.replicate 10 aspis_core.field.QM31.ZERO)
    exact zeroCanonical 10
  have point2Canonical :
      GeneratedCanonicalQM31List
        (generatedRelationPoint points 2#usize).val := by
    change GeneratedCanonicalQM31List
      (List.replicate 10 aspis_core.field.QM31.ZERO)
    exact zeroCanonical 10
  have covectorLength : terminalCovector.val.length = 1024 := by
    change (List.replicate 1024 aspis_core.field.QM31.ZERO).length = 1024
    simp only [List.length_replicate]
  have covectorCanonical :
      GeneratedCanonicalQM31List terminalCovector.val := by
    change GeneratedCanonicalQM31List
      (List.replicate 1024 aspis_core.field.QM31.ZERO)
    exact zeroCanonical 1024
  obtain ⟨out0, out1, out2, terminal, run, _⟩ :=
    extracted_component_b_relation_claims_exact c2Messages points
      terminalCovector messageLength covectorLength messageCanonical
      point0Canonical point1Canonical point2Canonical covectorCanonical
  exact ⟨c2Messages, points, terminalCovector,
    generatedClaimsArray out0 out1 out2 terminal, run⟩

#print axioms extracted_terminal_loop_exact
#print axioms extracted_component_b_relation_claims_exact
#print axioms extracted_component_b_relation_claims_zero_nonvacuous

end aspis_prover.ComponentBRelationClaimsProof
