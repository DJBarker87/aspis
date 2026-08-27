import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Complete duplex causal probability for one ordinary Tag-73 challenge

An ordinary QM31 challenge retains its complete bounded-rejection path and
the four independent duplex-advance answers.  These values may influence a
future prover response, so the causal experiment keeps all of them in a
nuisance skeleton and separates only the returned uniform QM31 value.

This is the ordinary-challenge analogue of the nonzero-gamma factorization.
It is used for the one-fold alpha contribution to K1.3 and does not divide by
any grinding work.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73CompleteCausalOrdinaryProbability

open MeasureTheory
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

abbrev Tag73OrdinaryAdvanceDigestGhosts := Fin 4 → Digest256

abbrev SuccessfulTag73DuplexOrdinaryAttempt :=
  SuccessfulTag73RawStream × Tag73OrdinaryAdvanceDigestGhosts

abbrev Tag73CompleteOrdinarySamplerSkeleton :=
  Tag73OrdinarySamplerSkeleton × Tag73OrdinaryAdvanceDigestGhosts

def successfulDuplexOrdinaryValue
    (sample : SuccessfulTag73DuplexOrdinaryAttempt) : QM31Exact :=
  tag73FourLimbsToExact (successfulTag73Values sample.1)

/-- Exact decomposition retaining the whole rejection/advance nuisance and
isolating the returned ordinary QM31 value. -/
def successfulDuplexOrdinaryFactorization :
    SuccessfulTag73DuplexOrdinaryAttempt ≃
      Tag73CompleteOrdinarySamplerSkeleton × QM31Exact :=
  (Equiv.prodCongr successfulOrdinaryRawFactorization
      (Equiv.refl Tag73OrdinaryAdvanceDigestGhosts)).trans
    { toFun := fun pair =>
        ((pair.1.1, pair.2), tag73FourLimbsToExact pair.1.2)
      invFun := fun pair =>
        ((pair.1.1, tag73FourLimbsToExact.symm pair.2), pair.1.2)
      left_inv := by intro pair; simp
      right_inv := by intro pair; simp }

@[simp] theorem successfulDuplexOrdinaryFactorization_value
    (sample : SuccessfulTag73DuplexOrdinaryAttempt) :
    (successfulDuplexOrdinaryFactorization sample).2 =
      successfulDuplexOrdinaryValue sample := by
  rfl

theorem successful_duplex_ordinary_factorization_law :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).map
        successfulDuplexOrdinaryFactorization =
      PMF.uniformOfFintype
        (Tag73CompleteOrdinarySamplerSkeleton × QM31Exact) := by
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv
    successfulDuplexOrdinaryFactorization

def completeOrdinaryDependentEvent
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact) :
    Set (Tag73CompleteOrdinarySamplerSkeleton × QM31Exact) :=
  {pair | pair.2 ∈ target pair.1}

def completeOrdinaryEventSlice
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton) : Set QM31Exact :=
  {value | value ∈ target skeleton}

def duplexOrdinaryDependentEvent
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact) :
    Set SuccessfulTag73DuplexOrdinaryAttempt :=
  successfulDuplexOrdinaryFactorization ⁻¹'
    completeOrdinaryDependentEvent target

theorem uniform_ordinary_target_probability_exact
    (target : Finset QM31Exact) :
    (PMF.uniformOfFintype QM31Exact).toOuterMeasure
        {value | value ∈ target} =
      (target.card : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, qm31Exact_card]
  congr 1
  norm_cast
  exact Fintype.card_coe target

theorem complete_ordinary_dependent_probability_le
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat) (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype
      (Tag73CompleteOrdinarySamplerSkeleton × QM31Exact)).toOuterMeasure
        (completeOrdinaryDependentEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_product_event_probability_le_of_every_slice_le
  intro skeleton
  rw [show productEventFstSlice (completeOrdinaryDependentEvent target)
      skeleton = {value | value ∈ target skeleton} by rfl]
  rw [uniform_ordinary_target_probability_exact]
  gcongr
  exact_mod_cast targetCap skeleton

/-- Complete causal ordinary-challenge bound.  The target may depend on every
rejection-path and duplex-advance answer, but not on the isolated returned
QM31 value. -/
theorem duplex_ordinary_dependent_probability_le
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat) (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (duplexOrdinaryDependentEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (duplexOrdinaryDependentEvent target) =
      ((PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).map
        successfulDuplexOrdinaryFactorization).toOuterMeasure
          (completeOrdinaryDependentEvent target) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
    _ = (PMF.uniformOfFintype
          (Tag73CompleteOrdinarySamplerSkeleton × QM31Exact)).toOuterMeasure
            (completeOrdinaryDependentEvent target) := by
      rw [successful_duplex_ordinary_factorization_law]
    _ ≤ _ := complete_ordinary_dependent_probability_le target cap targetCap

/-- Separate a total ordinary raw sampler region from an arbitrary residual
compiler context.  The residual may choose the complete nuisance-dependent
target, while the returned ordinary value remains the isolated uniform
factor. -/
theorem uniform_tape_dependent_ordinary_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (target : Residual →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ residual skeleton, (target residual skeleton).card ≤ cap)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹'
          duplexOrdinaryDependentEvent (target residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  let successfulEvent : Residual → Set {a : Total // success a} :=
    fun residual => successfulCoordinates ⁻¹'
      duplexOrdinaryDependentEvent (target residual)
  let dependentEvent : Set (Residual × Total) :=
    dependentSuccessfulSubtypeEvent success successfulEvent
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹' dependentEvent) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = (PMF.uniformOfFintype (Residual × Total)).toOuterMeasure
          dependentEvent := by
      calc
        _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure
              dependentEvent := by rw [PMF.toOuterMeasure_map_apply]
        _ = _ := by
          rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ ≤ _ := by
      apply uniform_product_event_probability_le_of_every_slice_le
      intro residual
      calc
        (PMF.uniformOfFintype Total).toOuterMeasure
            (productEventFstSlice dependentEvent residual) =
          (PMF.uniformOfFintype Total).toOuterMeasure
            (successfulSubtypeEvent success (successfulEvent residual)) := by
              rw [show dependentEvent =
                dependentSuccessfulSubtypeEvent success successfulEvent by rfl,
                productEventFstSlice_dependentSuccessfulSubtypeEvent]
        _ ≤ (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
              (successfulEvent residual) :=
          uniform_successful_subtype_event_probability_le success
            (successfulEvent residual)
        _ = (PMF.uniformOfFintype
              SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
                (duplexOrdinaryDependentEvent (target residual)) := by
          calc
            _ = ((PMF.uniformOfFintype {a : Total // success a}).map
                  successfulCoordinates).toOuterMeasure
                    (duplexOrdinaryDependentEvent (target residual)) := by
                rw [PMF.toOuterMeasure_map_apply]
            _ = _ := by
              rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
                successfulCoordinates]
        _ ≤ _ := duplex_ordinary_dependent_probability_le
          (target residual) cap (targetCap residual)

/-- Average the exact alpha-source coordinate/inclusion bridge over the
compiler's arbitrary hidden tape. -/
theorem exact_compiler_dependent_ordinary_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape Digest256
        freshExposures ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (target : HiddenTape → Residual →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (HiddenTape ×
      AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape Digest256
        freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            duplexOrdinaryDependentEvent (target hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_ordinary_event_probability_le success
    (coordinates hidden) successfulCoordinates (target hidden) cap
    (targetCap hidden) (jointEventSlice event hidden) (covered hidden)

end


#print axioms successfulDuplexOrdinaryFactorization
#print axioms successful_duplex_ordinary_factorization_law
#print axioms uniform_ordinary_target_probability_exact
#print axioms duplex_ordinary_dependent_probability_le
#print axioms uniform_tape_dependent_ordinary_event_probability_le
#print axioms exact_compiler_dependent_ordinary_event_probability_le

end AspisK1.V7Tag73CompleteCausalOrdinaryProbability
