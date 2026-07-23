import RuntimeFourRoundLaterRelease
import RuntimeLaterReleasedMaintainedBridge
import RuntimeScheduleCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFourRoundLaterMaintained

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimeFourRoundLaterRelease
open ComponentCRuntimeLaterReleasedMaintainedBridge
open ComponentCRuntimeLaterRoundLoopCorrespondence
open ComponentCRuntimeScheduleProof

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize

private theorem array3_eq_entries
    {T : Type*} [Inhabited T] (values : Array T 3#usize) :
    values = Array.make 3#usize
      [values.val[0]!, values.val[1]!, values.val[2]!] := by
  rcases values with ⟨values, hlength⟩
  apply Subtype.ext
  simp only [Array.make]
  rcases values with _ | ⟨v0, values⟩
  · simp at hlength
  rcases values with _ | ⟨v1, values⟩
  · simp at hlength
  rcases values with _ | ⟨v2, values⟩
  · simp at hlength
  rcases values with _ | ⟨v3, values⟩
  · rfl
  · simp at hlength

/-- The three actual source-authentic later vectors are exactly the maintained
`later{1,2,3}ReadMap` families once the generated query words and folded
vectors are decoded.  Counts, traversal order, slot order, vector lengths,
and reconstruction of the fixed-size outer array are conclusions.

The remaining hypotheses are deliberately pointwise field-decoding facts;
they are discharged by the generated codeword-tower adapter rather than by a
second traversal premise. -/
theorem generated_four_round_later_release_matches_maintained
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (base : DeployedRuntimeSchedule F K)
    (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (c : Coefficients K)
    (view : RawQM31 → K)
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31)
    (later0 later1Out later2Out later3Out later4 : RuntimeLater)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (htrace0 : ComponentCRuntimeRoundDeepControlFlow.GeneratedRuntimeRoundTrace
      schedule relation0 relation1 folded0 folded1 later0 later1Out
      tables0 tables1 0#usize)
    (htrace1 : ComponentCRuntimeRoundDeepControlFlow.GeneratedRuntimeRoundTrace
      schedule relation1 relation2 folded1 folded2 later1Out later2Out
      tables1 tables2 1#usize)
    (htrace2 : ComponentCRuntimeRoundDeepControlFlow.GeneratedRuntimeRoundTrace
      schedule relation2 relation3 folded2 folded3 later2Out later3Out
      tables2 tables3 2#usize)
    (htrace3 : ComponentCRuntimeRoundDeepControlFlow.GeneratedRuntimeRoundTrace
      schedule relation3 relation4 folded3 folded4 later3Out later4
      tables3 tables4 3#usize)
    (hfibres0 : schedule.later_fibres.val[0]! = later1 indices)
    (hfibres1 : schedule.later_fibres.val[1]! = later2 indices)
    (hfibres2 : schedule.later_fibres.val[2]! = later3 indices)
    (hempty0 : later0.val[0]!.val = [])
    (hempty1 : later0.val[1]!.val = [])
    (hempty2 : later0.val[2]!.val = [])
    (hread0 : ∀ fibre ∈ (later1 indices).val,
      4 * fibre.val + 4 ≤ folded1.val.length)
    (hread1 : ∀ fibre ∈ (later2 indices).val,
      4 * fibre.val + 4 ≤ folded2.val.length)
    (hread2 : ∀ fibre ∈ (later3 indices).val,
      4 * fibre.val + 4 ≤ folded3.val.length)
    (hcapacity0 : 4 * (later1 indices).val.length ≤ Std.Usize.max)
    (hcapacity1 : 4 * (later2 indices).val.length ≤ Std.Usize.max)
    (hcapacity2 : 4 * (later3 indices).val.length ≤ Std.Usize.max)
    (hfolded1 : ∀ row : Fin layer1Symbols,
      view folded1.val[row.val]! =
        layer1Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row)
    (hfolded2 : ∀ row : Fin layer2Symbols,
      view folded2.val[row.val]! =
        layer2Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row)
    (hfolded3 : ∀ row : Fin layer3Symbols,
      view folded3.val[row.val]! =
        layer3Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc c row) :
    let rt := withGeneratedLaterFibres base indices hrange
    later4 = Array.make 3#usize
        [later4.val[0]!, later4.val[1]!, later4.val[2]!] ∧
      later4.val[0]!.val.length = 4 * rt.later1Count ∧
      later4.val[1]!.val.length = 4 * rt.later2Count ∧
      later4.val[2]!.val.length = 4 * rt.later3Count ∧
      (∀ (index : Fin rt.later1Count) (slot : Fin 4),
        view (later4.val[0]!.val[4 * index.val + slot.val]!) =
          later1ReadMap (decodeFriSchedule rt) enc c (index, slot)) ∧
      (∀ (index : Fin rt.later2Count) (slot : Fin 4),
        view (later4.val[1]!.val[4 * index.val + slot.val]!) =
          later2ReadMap (decodeFriSchedule rt) enc c (index, slot)) ∧
      ∀ (index : Fin rt.later3Count) (slot : Fin 4),
        view (later4.val[2]!.val[4 * index.val + slot.val]!) =
          later3ReadMap (decodeFriSchedule rt) enc c (index, slot) := by
  dsimp only
  have hreleased := generated_four_round_later_release_exact
    schedule relation0 relation1 relation2 relation3 relation4
    folded0 folded1 folded2 folded3 folded4
    later0 later1Out later2Out later3Out later4
    tables0 tables1 tables2 tables3 tables4
    (later1 indices) (later2 indices) (later3 indices)
    htrace0 htrace1 htrace2 htrace3 hfibres0 hfibres1 hfibres2
    hempty0 hempty1 hempty2 hread0 hread1 hread2
    hcapacity0 hcapacity1 hcapacity2
  have hfamily1 := released_fibres_prefix_decodes_to_readFibres
    view (alloc.vec.Vec.deref folded1) (later1 indices) layer2Symbols
    (withGeneratedLaterFibres base indices hrange).later1Fibre
    (layer1Map (decodeFriSchedule
      (withGeneratedLaterFibres base indices hrange)) enc c)
    (fun index => by
      rw [withGeneratedLaterFibres_later1Fibre]
      simp) hfolded1
  have hfamily2 := released_fibres_prefix_decodes_to_readFibres
    view (alloc.vec.Vec.deref folded2) (later2 indices) layer3Symbols
    (withGeneratedLaterFibres base indices hrange).later2Fibre
    (layer2Map (decodeFriSchedule
      (withGeneratedLaterFibres base indices hrange)) enc c)
    (fun index => by
      rw [withGeneratedLaterFibres_later2Fibre]
      simp) hfolded2
  have hfamily3 := released_fibres_prefix_decodes_to_readFibres
    view (alloc.vec.Vec.deref folded3) (later3 indices) layer4Symbols
    (withGeneratedLaterFibres base indices hrange).later3Fibre
    (layer3Map (decodeFriSchedule
      (withGeneratedLaterFibres base indices hrange)) enc c)
    (fun index => by
      rw [withGeneratedLaterFibres_later3Fibre]
      simp) hfolded3
  refine ⟨array3_eq_entries later4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreleased.1, releasedFibresPrefix_length]
    rw [withGeneratedLaterFibres_later1Count]
  · rw [hreleased.2.1, releasedFibresPrefix_length]
    rw [withGeneratedLaterFibres_later2Count]
  · rw [hreleased.2.2, releasedFibresPrefix_length]
    rw [withGeneratedLaterFibres_later3Count]
  · intro index slot
    rw [hreleased.1]
    change _ = (readFibres
      (withGeneratedLaterFibres base indices hrange).later1Fibre)
        ((layer1Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc) c)
        (index, slot)
    exact hfamily1 index slot
  · intro index slot
    rw [hreleased.2.1]
    change _ = (readFibres
      (withGeneratedLaterFibres base indices hrange).later2Fibre)
        ((layer2Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc) c)
        (index, slot)
    exact hfamily2 index slot
  · intro index slot
    rw [hreleased.2.2]
    change _ = (readFibres
      (withGeneratedLaterFibres base indices hrange).later3Fibre)
        ((layer3Map (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange)) enc) c)
        (index, slot)
    exact hfamily3 index slot

#print axioms generated_four_round_later_release_matches_maintained

end aspis_prover.ComponentCRuntimeFourRoundLaterMaintained
