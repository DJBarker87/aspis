import V5RelationLinkedAccumulatorTraversal
import V5RelationFullSourceProof

/-!
# Public bridge between the relation-driver and linked accumulator snapshots

The complete relation-driver extraction and the complete accumulator-helper
extraction contain duplicate structural copies of `WeightComponent` and
`WeightAccumulator`.  The generated external definition of `fold` already
maps between those copies.  This file makes that structural map public and
proves that a successful driver-side fold is the same successful linked fold.
-/

namespace AspisV5RelationFullLinkedAccumulatorBridge

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedSupportedFold
open AspisV5RelationLinkedAccumulatorTraversal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev FullComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent
abbrev LinkedComponent :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
abbrev LinkedWeights :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator

deriving instance Inhabited for
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent

def componentToLinked : FullComponent → LinkedComponent
  | .Geometric scale step => .Geometric scale step
  | .Multilinear scale point => .Multilinear scale point
  | .Tensor scale factors => .Tensor scale factors
  | .Product scale pairs => .Product scale pairs
  | .Dense values => .Dense values
  | .Grouped64x16 rows values width => .Grouped64x16 rows values width
  | .Grouped64x16BinaryDeferred rows masks first values =>
      .Grouped64x16BinaryDeferred rows masks first values
  | .Grouped128x16 rows values width => .Grouped128x16 rows values width

def componentFromLinked : LinkedComponent → FullComponent
  | .Geometric scale step => .Geometric scale step
  | .Multilinear scale point => .Multilinear scale point
  | .Tensor scale factors => .Tensor scale factors
  | .Product scale pairs => .Product scale pairs
  | .Dense values => .Dense values
  | .Grouped64x16 rows values width => .Grouped64x16 rows values width
  | .Grouped64x16BinaryDeferred rows masks first values =>
      .Grouped64x16BinaryDeferred rows masks first values
  | .Grouped128x16 rows values width => .Grouped128x16 rows values width

def weightsToLinked (weights : FullWeights) : LinkedWeights :=
  { log_len := weights.log_len
    components :=
      ⟨weights.components.val.map componentToLinked,
        by simpa using weights.components.property⟩ }

def weightsFromLinked (weights : LinkedWeights) : FullWeights :=
  { log_len := weights.log_len
    components :=
      ⟨weights.components.val.map componentFromLinked,
        by simpa using weights.components.property⟩ }

@[simp] theorem componentFromTo (component : FullComponent) :
    componentFromLinked (componentToLinked component) = component := by
  cases component <;> rfl

@[simp] theorem componentToFrom (component : LinkedComponent) :
    componentToLinked (componentFromLinked component) = component := by
  cases component <;> rfl

@[simp] theorem weightsFromTo (weights : FullWeights) :
    weightsFromLinked (weightsToLinked weights) = weights := by
  cases weights with
  | mk logLen components =>
    simp only [weightsToLinked, weightsFromLinked]
    congr 1
    apply Subtype.ext
    simp [Function.comp_def]

@[simp] theorem weightsToFrom (weights : LinkedWeights) :
    weightsToLinked (weightsFromLinked weights) = weights := by
  cases weights with
  | mk logLen components =>
    simp only [weightsToLinked, weightsFromLinked]
    congr 1
    apply Subtype.ext
    simp [Function.comp_def]

private theorem getElemBangEqGetElem
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (bound : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [bound]

theorem weightsToLinked_component
    (weights : FullWeights) (index : Nat)
    (bound : index < weights.components.val.length) :
    (weightsToLinked weights).components.val[index]! =
      componentToLinked weights.components.val[index]! := by
  change (List.map componentToLinked weights.components.val)[index]! =
    componentToLinked weights.components.val[index]!
  have sourceBang :
      weights.components.val[index]! = weights.components.val[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  have mapBound :
      index < (List.map componentToLinked weights.components.val).length := by
    simpa using bound
  have mapBang :
      (List.map componentToLinked weights.components.val)[index]! =
        (List.map componentToLinked weights.components.val)[index] := by
    exact getElemBangEqGetElem _ index mapBound
  have actualMap :
      (List.map componentToLinked weights.components.val)[index] =
        componentToLinked weights.components.val[index] := by
    rw [List.getElem_map]
  exact mapBang.trans (actualMap.trans (congrArg componentToLinked sourceBang.symm))

/-- The generated complete-driver external body calls exactly the linked
accumulator fold and maps its result back structurally. -/
theorem fullFoldSuccessImpliesLinkedFold
    (weights output : FullWeights) (alpha : RawQM31)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        (weightsToLinked weights) alpha = .ok (weightsToLinked output) := by
  unfold aspis_core.sumcheck.WeightAccumulator.fold
    at success
  generalize linkedRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        _ alpha = linkedResult at success
  cases linkedResult with
  | fail error => simp at success
  | div => simp at success
  | ok folded =>
    simp only [bind_tc_ok, Result.ok.injEq] at success
    change
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
          (weightsToLinked weights) alpha = .ok folded at linkedRun
    change weightsFromLinked folded = output at success
    subst output
    simpa using linkedRun

/-- A successful complete-driver fold preserves the component count.  This
is the driver-facing consequence of the exact linked fold traversal. -/
theorem fullFoldSuccessPreservesComponentLength
    (weights output : FullWeights) (alpha : RawQM31)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    output.components.val.length = weights.components.val.length := by
  have linkedRun := fullFoldSuccessImpliesLinkedFold weights output alpha success
  have linkedLength := foldSuccessPreservesComponentLength
    (weightsToLinked weights) (weightsToLinked output) alpha linkedRun
  simpa [weightsToLinked] using linkedLength

/-- Driver-facing form of the exact pointwise traversal theorem. -/
theorem fullFoldSuccessExposesLinkedComponent
    (weights output : FullWeights) (alpha : RawQM31)
    (target : Nat) (targetBound : target < weights.components.val.length)
    (targetReleased :
      ReleasedComponent (componentToLinked weights.components.val[target]!))
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold
          weights alpha = .ok output) :
    ∃ (alpha2 alpha3 : RawQM31)
        (preparedAlpha preparedAlpha2 :
          V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
        (componentOut : LinkedComponent) (folded : LinkedWeights),
      V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha = .ok alpha2 ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha = .ok preparedAlpha ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          alpha2 = .ok preparedAlpha2 ∧
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
          preparedAlpha alpha2 = .ok alpha3 ∧
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (componentToLinked weights.components.val[target]!) weights.log_len
          alpha alpha2 alpha3 preparedAlpha preparedAlpha2 =
        .ok (none, componentOut) ∧
      componentToLinked output.components.val[target]! = componentOut ∧
      ReleasedComponent componentOut := by
  have linkedRun := fullFoldSuccessImpliesLinkedFold weights output alpha success
  have inputLength :
      (weightsToLinked weights).components.val.length =
        weights.components.val.length := by
    simp [weightsToLinked]
  have linkedTargetBound :
      target < (weightsToLinked weights).components.val.length := by
    simpa [inputLength] using targetBound
  have linkedInputCell := weightsToLinked_component weights target targetBound
  have linkedReleased :
      ReleasedComponent
        (weightsToLinked weights).components.val[target]! := by
    rw [linkedInputCell]
    exact targetReleased
  obtain ⟨alpha2, alpha3, preparedAlpha, preparedAlpha2, componentOut,
      folded, squareRun, prepareRun, prepare2Run, alpha3Run, _dispatchRun,
      componentRun, outputCell, outputReleased, _logRun⟩ :=
    foldSuccessExposesComponent (weightsToLinked weights)
      (weightsToLinked output) alpha target linkedTargetBound linkedReleased
      linkedRun
  have linkedLength := foldSuccessPreservesComponentLength
    (weightsToLinked weights) (weightsToLinked output) alpha linkedRun
  have outputBound : target < output.components.val.length := by
    have linkedOutputBound :
        target < (weightsToLinked output).components.val.length := by
      rw [linkedLength]
      exact linkedTargetBound
    simpa [weightsToLinked] using linkedOutputBound
  have linkedOutputCell := weightsToLinked_component output target outputBound
  refine ⟨alpha2, alpha3, preparedAlpha, preparedAlpha2, componentOut, folded,
    squareRun, prepareRun, prepare2Run, alpha3Run, ?_, ?_, outputReleased⟩
  · have callEq := congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component weights.log_len alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2)
      linkedInputCell
    exact callEq.symm.trans (by simpa [weightsToLinked] using componentRun)
  · exact linkedOutputCell.symm.trans outputCell

#print axioms fullFoldSuccessImpliesLinkedFold
#print axioms fullFoldSuccessPreservesComponentLength
#print axioms fullFoldSuccessExposesLinkedComponent

end AspisV5RelationFullLinkedAccumulatorBridge
