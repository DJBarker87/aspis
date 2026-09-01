import AspisFormal.K1.V7Tag73Q16DigestDrawReindex
import AspisFormal.K1.V7Tag73Q16RawENNRealProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore

/-!
# Successful Tag-73 q16 digest forests

The deployed q16 scan receives sixty-four cloned candidate branches, each
with eight full SHA-256 blocks available to its bounded sampler.  This file
identifies the successful subtype of that full digest forest with exactly:

* all discarded high fourteen bits; and
* the first admitted cap-203 schedule sample counted by the finite q16 proof.

Consequently conditioning on scan success introduces no bias beyond the
already-proved first-success law.  This is a finite representation theorem;
SHA-256/random-oracle security remains an explicit external boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16SuccessfulForestBridge

open MeasureTheory
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73HiddenTapeAveraging

noncomputable section

def HasFirstAdmittedForest {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (forest : Fin candidateCount → Raw) : Prop :=
  ∃ sample : FirstAdmittedSample output admitted candidateCount,
    sample.2.1.2 = forest

theorem firstAdmittedAt_unique
    {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat)
    (firstCounter secondCounter : Fin candidateCount)
    (forest : Fin candidateCount → Raw)
    (firstResult secondResult : Result)
    (firstAdmitted : admitted firstResult)
    (secondAdmitted : admitted secondResult)
    (first : FirstAdmittedAt output admitted candidateCount firstResult
      (firstCounter, forest))
    (second : FirstAdmittedAt output admitted candidateCount secondResult
      (secondCounter, forest)) :
    firstCounter = secondCounter ∧ firstResult = secondResult := by
  have notFirstBefore : ¬ firstCounter.val < secondCounter.val := by
    intro before
    exact (second.1 firstCounter before firstResult firstAdmitted) first.2
  have notSecondBefore : ¬ secondCounter.val < firstCounter.val := by
    intro before
    exact (first.1 secondCounter before secondResult secondAdmitted) second.2
  have counterEq : firstCounter = secondCounter := by
    apply Fin.ext
    exact Nat.le_antisymm (Nat.le_of_not_gt notSecondBefore)
      (Nat.le_of_not_gt notFirstBefore)
  subst secondCounter
  have firstOutput : output (forest firstCounter) = some firstResult := by
    simpa using first.2
  have secondOutput : output (forest firstCounter) = some secondResult := by
    simpa using second.2
  exact ⟨rfl, Option.some.inj (firstOutput.symm.trans secondOutput)⟩

theorem firstAdmittedSample_eq_of_forest_eq
    {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat)
    (first second : FirstAdmittedSample output admitted candidateCount)
    (forestEq : first.2.1.2 = second.2.1.2) :
    first = second := by
  rcases first with ⟨firstResult, firstTrace⟩
  rcases second with ⟨secondResult, secondTrace⟩
  change firstTrace.1.2 = secondTrace.1.2 at forestEq
  let commonForest := firstTrace.1.2
  have secondForest : secondTrace.1.2 = commonForest := forestEq.symm
  have secondAt : FirstAdmittedAt output admitted candidateCount
      secondResult.1 (secondTrace.1.1, commonForest) := by
    rw [← secondForest]
    exact secondTrace.2
  have unique := firstAdmittedAt_unique output admitted candidateCount
    firstTrace.1.1 secondTrace.1.1 commonForest firstResult.1 secondResult.1
    firstResult.2 secondResult.2 (by simpa [commonForest] using firstTrace.2)
    secondAt
  have resultEq : firstResult = secondResult := Subtype.ext unique.2
  subst secondResult
  have traceEq : firstTrace = secondTrace := by
    apply Subtype.ext
    apply Prod.ext unique.1
    exact forestEq
  subst secondTrace
  rfl

def successfulDrawForestEquiv
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) :
    {forest : Fin candidateCount → Raw //
      HasFirstAdmittedForest output admitted candidateCount forest} ≃
      FirstAdmittedSample output admitted candidateCount where
  toFun forest := Classical.choose forest.2
  invFun sample := ⟨sample.2.1.2, ⟨sample, rfl⟩⟩
  left_inv forest := by
    apply Subtype.ext
    exact Classical.choose_spec forest.2
  right_inv sample := by
    let witness : HasFirstAdmittedForest output admitted candidateCount
        sample.2.1.2 := ⟨sample, rfl⟩
    have chosenForest :
        (Classical.choose witness).2.1.2 = sample.2.1.2 :=
      Classical.choose_spec witness
    apply firstAdmittedSample_eq_of_forest_eq output admitted candidateCount
    exact chosenForest

def q16DigestForestSucceeds (forest : Q16CandidateDigestForest) : Prop :=
  HasFirstAdmittedForest q16CandidateOutput SemanticCap203Admitted 64
    (deployedQ16DrawForest forest)

abbrev SuccessfulQ16DigestForest :=
  {forest : Q16CandidateDigestForest // q16DigestForestSucceeds forest}

abbrev SuccessfulQ16Coordinates :=
  Q16CandidateHighForest ×
    FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64

def successfulQ16DigestForestEquiv :
    SuccessfulQ16DigestForest ≃ SuccessfulQ16Coordinates where
  toFun forest :=
    ((q16CandidateDigestForestEquiv forest.1).2,
      successfulDrawForestEquiv q16CandidateOutput SemanticCap203Admitted 64
        ⟨(q16CandidateDigestForestEquiv forest.1).1, forest.2⟩)
  invFun coordinates :=
    let draws :=
      (successfulDrawForestEquiv q16CandidateOutput SemanticCap203Admitted 64
        ).symm coordinates.2
    ⟨q16CandidateDigestForestEquiv.symm (draws.1, coordinates.1), by
      simpa [q16DigestForestSucceeds, deployedQ16DrawForest] using draws.2⟩
  left_inv forest := by
    apply Subtype.ext
    apply q16CandidateDigestForestEquiv.injective
    apply Prod.ext
    · simpa [q16DigestForestSucceeds, deployedQ16DrawForest] using
        (Classical.choose_spec forest.2)
    · simp
  right_inv coordinates := by
    apply Prod.ext
    · simp
    · have restored := (successfulDrawForestEquiv q16CandidateOutput
        SemanticCap203Admitted 64).apply_symm_apply coordinates.2
      simpa using restored

def q16SuccessfulCoordinatesBadEvent (bad : Finset (Fin 262144)) :
    Set SuccessfulQ16Coordinates :=
  {coordinates | coordinates.2 ∈ q16FirstAdmittedBadEvent bad}

theorem q16_successful_coordinates_bad_measure_le_semantic_choose
    [Nonempty
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)]
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (PMF.uniformOfFintype SuccessfulQ16Coordinates).toOuterMeasure
        (q16SuccessfulCoordinatesBadEvent bad) ≤
      (Nat.choose 9557 16 : ENNReal) /
        (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
          ENNReal) := by
  apply uniform_product_event_probability_le_of_every_slice_le
  intro high
  have sliceEq :
      productEventFstSlice (q16SuccessfulCoordinatesBadEvent bad) high =
        q16FirstAdmittedBadEvent bad := by
    ext sample
    rfl
  rw [sliceEq]
  exact q16_first_cap203_bad_measure_le_semantic_choose bad badCard
    reference traceExists

/-- Residual-dependent q16 conditioning for one uniform compiler tape.  The
bad consistency set may depend on every answer outside the complete q16
digest forest, while every slice retains the same exact raw bound. -/
theorem uniform_tape_dependent_q16_event_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Tape ≃ Residual × Q16CandidateDigestForest)
    (bad : Residual → Finset (Fin 262144))
    (badCard : ∀ residual, (bad residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent q16DigestForestSucceeds (fun residual =>
        successfulQ16DigestForestEquiv ⁻¹'
          q16SuccessfulCoordinatesBadEvent (bad residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (Nat.choose 9557 16 : ENNReal) /
        (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
          ENNReal) := by
  classical
  let sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64 := ⟨reference, Classical.choice traceExists⟩
  letI : Nonempty (FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) := ⟨sample⟩
  let successfulCoordinates : SuccessfulQ16Coordinates :=
    (Classical.choice inferInstance, sample)
  letI : Nonempty SuccessfulQ16Coordinates := ⟨successfulCoordinates⟩
  letI : Nonempty SuccessfulQ16DigestForest :=
    ⟨successfulQ16DigestForestEquiv.symm successfulCoordinates⟩
  apply uniform_tape_dependent_successful_event_probability_le
    q16DigestForestSucceeds coordinates successfulQ16DigestForestEquiv
    (fun residual => q16SuccessfulCoordinatesBadEvent (bad residual))
    ((Nat.choose 9557 16 : ENNReal) /
      (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
        ENNReal))
  · intro residual
    exact q16_successful_coordinates_bad_measure_le_semantic_choose
      (bad residual) (badCard residual) reference traceExists
  · exact covered

/-- Hidden-tape averaging of the exact residual-dependent q16 bridge. -/
theorem exact_compiler_dependent_q16_event_probability_le
    {HiddenTape Residual : Type} [Fintype HiddenTape]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (coordinates : HiddenTape →
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures ≃
          Residual × Q16CandidateDigestForest)
    (bad : HiddenTape → Residual → Finset (Fin 262144))
    (badCard : ∀ hidden residual, (bad hidden residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (HiddenTape ×
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape
        AspisK1.V7Tag73TranscriptSchedule.Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent q16DigestForestSucceeds
          (fun residual => successfulQ16DigestForestEquiv ⁻¹'
            q16SuccessfulCoordinatesBadEvent (bad hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (Nat.choose 9557 16 : ENNReal) /
        (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
          ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_q16_event_probability_le
    (coordinates hidden) (bad hidden) (badCard hidden) reference traceExists
    (jointEventSlice event hidden) (covered hidden)

end

#print axioms firstAdmittedAt_unique
#print axioms firstAdmittedSample_eq_of_forest_eq
#print axioms successfulDrawForestEquiv
#print axioms successfulQ16DigestForestEquiv
#print axioms q16_successful_coordinates_bad_measure_le_semantic_choose
#print axioms uniform_tape_dependent_q16_event_probability_le
#print axioms exact_compiler_dependent_q16_event_probability_le

end AspisK1.V7Tag73Q16SuccessfulForestBridge
