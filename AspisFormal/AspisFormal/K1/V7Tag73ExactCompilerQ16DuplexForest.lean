import AspisFormal.K1.V7Tag73ExactCompilerQ16BranchReplayLift

/-!
# Canonical exact-compiler q16 duplex forest

Every used output and advance coordinate is copied from the checked literal
candidate execution.  Unused rectangle cells are deterministic padding and
are never consumed by the branch plan.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16DuplexForest

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates

noncomputable section

noncomputable def exactOperationalQ16DuplexForest
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : TotalQ16DuplexForest :=
  (fun counter block =>
    if beforeSelected : counter.val ≤
        (exactOperationalTape input).search.selectedCounter.val then
      let coordinates := exactOperationalQ16BranchCoordinates input counter
        beforeSelected
      if used : block.val < coordinates.outputs.length then
        coordinates.outputs[block.val]
      else zeroBytes 32
    else zeroBytes 32,
   fun counter block =>
    if beforeSelected : counter.val ≤
        (exactOperationalTape input).search.selectedCounter.val then
      let coordinates := exactOperationalQ16BranchCoordinates input counter
        beforeSelected
      if used : block.val < coordinates.advances.length then
        coordinates.advances[block.val]
      else zeroBytes 32
    else zeroBytes 32)

theorem exact_operational_q16_duplex_output_used
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val)
    (index : Nat)
    (used : index <
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).outputs.length)
    (indexCap : index < 8) :
    (exactOperationalQ16DuplexForest input).1 counter ⟨index, indexCap⟩ =
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).outputs[index] := by
  change (if h : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val then
      let coordinates := exactOperationalQ16BranchCoordinates input counter h
      if used : index < coordinates.outputs.length then
        coordinates.outputs[index]
      else zeroBytes 32
    else zeroBytes 32) = _
  rw [dif_pos beforeSelected]
  have used' : index <
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).outputs.length := used
  rw [dif_pos used']

theorem exact_operational_q16_duplex_advance_used
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val)
    (index : Nat)
    (used : index <
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).advances.length)
    (indexCap : index < 8) :
    (exactOperationalQ16DuplexForest input).2 counter ⟨index, indexCap⟩ =
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).advances[index] := by
  change (if h : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val then
      let coordinates := exactOperationalQ16BranchCoordinates input counter h
      if used : index < coordinates.advances.length then
        coordinates.advances[index]
      else zeroBytes 32
    else zeroBytes 32) = _
  rw [dif_pos beforeSelected]
  have used' : index <
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).advances.length := used
  rw [dif_pos used']

/-- The exact source branch reads precisely its canonical duplex list. -/
theorem exact_operational_q16_branch_duplex_pairs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    let coordinates := exactOperationalQ16BranchCoordinates input counter
      beforeSelected
    let branch := schedulerNativeQ16BranchOfSpec
      (exactOperationalQ16InitialDigest input)
      { counter := counter
        outcome := (exactOperationalTape input).search.outcome counter }
    q16BranchDuplexPairs branch (exactOperationalQ16DuplexForest input) =
      coordinates.outputs.zip coordinates.advances := by
  let coordinates := exactOperationalQ16BranchCoordinates input counter
    beforeSelected
  let branch := schedulerNativeQ16BranchOfSpec
    (exactOperationalQ16InitialDigest input)
    { counter := counter
      outcome := (exactOperationalTape input).search.outcome counter }
  apply List.ext_getElem
  · rw [q16_branch_duplex_pairs_length, List.length_zip]
    rw [coordinates.advancesLength, Nat.min_self]
    exact coordinates.outputsLength.symm
  · intro index leftBound rightBound
    unfold q16BranchDuplexPairs
    rw [List.getElem_ofFn, List.getElem_zip]
    have outputBound : index < coordinates.outputs.length := by
      simpa [branch, schedulerNativeQ16BranchOfSpec,
        coordinates.outputsLength] using leftBound
    have advanceBound : index < coordinates.advances.length := by
      rw [coordinates.advancesLength]
      exact outputBound
    have indexCap : index < 8 := Nat.lt_of_lt_of_le outputBound (by
      rw [coordinates.outputsLength]
      exact candidate_outcome_blocks_cap
        ((exactOperationalTape input).search.outcome counter))
    apply Prod.ext
    · exact exact_operational_q16_duplex_output_used input counter
        beforeSelected index outputBound indexCap
    · exact exact_operational_q16_duplex_advance_used input counter
        beforeSelected index advanceBound indexCap

/-- The output half of the canonical duplex forest is the exact successful
first-cap-203 forest of the accepted source execution. -/
theorem exact_operational_q16_duplex_forest_succeeds
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    q16DigestForestSucceeds (exactOperationalQ16DuplexForest input).1 := by
  apply scheduler_native_q16_source_plan_realizes_successful_forest
    (exactOperationalQ16InitialDigest input)
    (exactOperationalTape input).search
    (exactOperationalQ16DuplexForest input) frontierExact
  intro counter beforeSelected
  let coordinates := exactOperationalQ16BranchCoordinates input counter
    beforeSelected
  have pairsExact := exact_operational_q16_branch_duplex_pairs input counter
    beforeSelected
  have outputsExact :
      q16BranchOutputBlocks
          (schedulerNativeQ16BranchOfSpec
            (exactOperationalQ16InitialDigest input)
            { counter := counter
              outcome := (exactOperationalTape input).search.outcome counter })
          (exactOperationalQ16DuplexForest input) = coordinates.outputs := by
    unfold q16BranchOutputBlocks
    rw [pairsExact]
    apply List.ext_getElem
    · rw [List.length_map, List.length_zip, coordinates.advancesLength,
        Nat.min_self]
    · intro index leftBound rightBound
      rw [List.getElem_map, List.getElem_zip]
  rw [outputsExact]
  exact coordinates.decoded

#print axioms exact_operational_q16_branch_duplex_pairs
#print axioms exact_operational_q16_duplex_forest_succeeds

end

end AspisK1.V7Tag73ExactCompilerQ16DuplexForest
