import AspisFormal.K1.V7Tag73HiddenTapeAveraging
import AspisFormal.V5ComponentCRejectionSampler
import AspisFormal.V5RankOneOpeningHiding

/-!
# Generic finite successful-sampler conditioning

This module contains only the finite-measure conditioning lemmas shared by
the Tag-73 q16 and gamma analyses.  It deliberately has no circle-decoding or
K1.4 import: a q16 build must not elaborate the correlated-agreement stack
merely to reuse generic uniform-product accounting.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73SuccessfulSamplerConditioningBridge

open MeasureTheory

noncomputable section

/-- Restrict an event on a successful subtype back to the total sampler
space. -/
def successfulSubtypeEvent
    {A : Type} (success : A → Prop)
    (event : Set {a : A // success a}) : Set A :=
  {a | ∃ h : success a, (⟨a, h⟩ : {a : A // success a}) ∈ event}

def successfulSubtypeEventEquiv
    {A : Type} (success : A → Prop)
    (event : Set {a : A // success a}) :
    {a : A // a ∈ successfulSubtypeEvent success event} ≃
      {a : {a : A // success a} // a ∈ event} where
  toFun a := ⟨⟨a.1, Classical.choose a.2⟩, Classical.choose_spec a.2⟩
  invFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl

/-- Conditioning a finite uniform sampler on a nonempty successful subset can
only increase the probability of an event contained in that subset. -/
theorem uniform_successful_subtype_event_probability_le
    {A : Type} [Fintype A] [Nonempty A]
    (success : A → Prop) [DecidablePred success]
    [Nonempty {a : A // success a}]
    (event : Set {a : A // success a}) :
    (PMF.uniformOfFintype A).toOuterMeasure
        (successfulSubtypeEvent success event) ≤
      (PMF.uniformOfFintype {a : A // success a}).toOuterMeasure event := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (successfulSubtypeEventEquiv success event)]
  gcongr
  exact Fintype.card_subtype_le success

/-- A fixed coordinate equivalence can expose the total sampler region and an
independent residual tape.  Any event covered by a successful sampler event
inherits the latter's conditional probability bound. -/
theorem uniform_tape_event_probability_le_successful_sampler_event
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Total × Residual)
    (event : Set Tape)
    (successfulEvent : Set {a : Total // success a})
    (covered : event ⊆ coordinates ⁻¹'
      (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent)) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
        successfulEvent := by
  classical
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹'
            (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent)) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure
          (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = (PMF.uniformOfFintype (Total × Residual)).toOuterMeasure
          (Prod.fst ⁻¹' successfulSubtypeEvent success successfulEvent) := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ = ((PMF.uniformOfFintype (Total × Residual)).map Prod.fst).toOuterMeasure
          (successfulSubtypeEvent success successfulEvent) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = (PMF.uniformOfFintype Total).toOuterMeasure
          (successfulSubtypeEvent success successfulEvent) := by
      rw [AspisV5ComponentCRejectionSampler.uniform_prod_map_fst]
    _ ≤ (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
          successfulEvent :=
      uniform_successful_subtype_event_probability_le success successfulEvent

/-! ## Residual-dependent causal contexts -/

/-- A product event sliced at a fixed first coordinate. -/
def productEventFstSlice
    {Residual Total : Type} (event : Set (Residual × Total))
    (residual : Residual) : Set Total :=
  {total | (residual, total) ∈ event}

/-- A residual-indexed family of events on the successful subtype, embedded
back into the total product experiment. -/
def dependentSuccessfulSubtypeEvent
    {Residual Total : Type} (success : Total → Prop)
    (event : Residual → Set {a : Total // success a}) :
    Set (Residual × Total) :=
  {pair | ∃ h : success pair.2, ⟨pair.2, h⟩ ∈ event pair.1}

@[simp] theorem productEventFstSlice_dependentSuccessfulSubtypeEvent
    {Residual Total : Type} (success : Total → Prop)
    (event : Residual → Set {a : Total // success a})
    (residual : Residual) :
    productEventFstSlice (dependentSuccessfulSubtypeEvent success event)
        residual =
      successfulSubtypeEvent success (event residual) := by
  rfl

/-- Uniformly sample the residual context, then uniformly sample the total raw
sampler region. -/
def uniformProductJointLaw
    (Residual Total : Type) [Fintype Residual] [Nonempty Residual]
    [Fintype Total] [Nonempty Total] : PMF (Residual × Total) :=
  (PMF.uniformOfFintype Residual).bind fun residual =>
    (PMF.uniformOfFintype Total).map fun total => (residual, total)

theorem uniformProductJointLaw_eq_uniform
    (Residual Total : Type) [Fintype Residual] [Nonempty Residual]
    [Fintype Total] [Nonempty Total] :
    uniformProductJointLaw Residual Total =
      PMF.uniformOfFintype (Residual × Total) := by
  classical
  ext pair
  rw [uniformProductJointLaw, PMF.bind_apply]
  rw [tsum_eq_single pair.1]
  · rw [PMF.map_apply, tsum_eq_single pair.2]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply,
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
        Fintype.card_prod, Nat.cast_mul]
      exact (ENNReal.mul_inv
        (a := (Fintype.card Residual : ENNReal))
        (b := (Fintype.card Total : ENNReal))
        (Or.inl (Nat.cast_ne_zero.mpr
          (Fintype.card_ne_zero : Fintype.card Residual ≠ 0)))
        (Or.inl (ENNReal.natCast_ne_top (Fintype.card Residual)))).symm
    · intro total totalNe
      rw [if_neg]
      intro equal
      exact totalNe (congrArg Prod.snd equal).symm
  · intro residual residualNe
    have mappedZero :
        (PMF.uniformOfFintype Total).map
            (fun total => (residual, total)) pair = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro total
      rw [if_neg]
      intro equal
      exact residualNe (congrArg Prod.fst equal).symm
    rw [mappedZero, mul_zero]

theorem uniform_product_event_probability_eq_weighted_slices
    {Residual Total : Type} [Fintype Residual] [Nonempty Residual]
    [Fintype Total] [Nonempty Total]
    (event : Set (Residual × Total)) :
    (PMF.uniformOfFintype (Residual × Total)).toOuterMeasure event =
      ∑' residual : Residual,
        (PMF.uniformOfFintype Residual) residual *
          (PMF.uniformOfFintype Total).toOuterMeasure
            (productEventFstSlice event residual) := by
  rw [← uniformProductJointLaw_eq_uniform Residual Total]
  unfold uniformProductJointLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro residual
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem uniform_product_event_probability_le_of_every_slice_le
    {Residual Total : Type} [Fintype Residual] [Nonempty Residual]
    [Fintype Total] [Nonempty Total]
    (event : Set (Residual × Total)) (bound : ENNReal)
    (sliceBound : ∀ residual,
      (PMF.uniformOfFintype Total).toOuterMeasure
        (productEventFstSlice event residual) ≤ bound) :
    (PMF.uniformOfFintype (Residual × Total)).toOuterMeasure event ≤
      bound := by
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' residual : Residual,
        (PMF.uniformOfFintype Residual) residual *
          (PMF.uniformOfFintype Total).toOuterMeasure
            (productEventFstSlice event residual)) ≤
        ∑' residual : Residual,
          (PMF.uniformOfFintype Residual) residual * bound := by
      exact ENNReal.tsum_le_tsum fun residual =>
        mul_le_mul_left' (sliceBound residual)
          ((PMF.uniformOfFintype Residual) residual)
    _ = (∑' residual : Residual,
          (PMF.uniformOfFintype Residual) residual) * bound := by
      exact ENNReal.tsum_mul_right
    _ = bound := by rw [PMF.tsum_coe, one_mul]

/-- Generic residual-dependent conditioning bridge.  A source equivalence
separates a total raw sampler from the rest of the compiler tape; each
residual context may choose a different event on the successful subtype. -/
theorem uniform_tape_dependent_successful_event_probability_le
    {Tape Total Residual Successful : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    [Fintype Successful] [Nonempty Successful]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates : {a : Total // success a} ≃ Successful)
    (successfulEvent : Residual → Set Successful)
    (bound : ENNReal)
    (successfulBound : ∀ residual,
      (PMF.uniformOfFintype Successful).toOuterMeasure
        (successfulEvent residual) ≤ bound)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹' successfulEvent residual)) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤ bound := by
  let subtypeEvent : Residual → Set {a : Total // success a} :=
    fun residual => successfulCoordinates ⁻¹' successfulEvent residual
  let dependentEvent : Set (Residual × Total) :=
    dependentSuccessfulSubtypeEvent success subtypeEvent
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
            (successfulSubtypeEvent success (subtypeEvent residual)) := by
              rw [show dependentEvent =
                dependentSuccessfulSubtypeEvent success subtypeEvent by rfl,
                productEventFstSlice_dependentSuccessfulSubtypeEvent]
        _ ≤ (PMF.uniformOfFintype {a : Total // success a}).toOuterMeasure
              (subtypeEvent residual) :=
          uniform_successful_subtype_event_probability_le success
            (subtypeEvent residual)
        _ = (PMF.uniformOfFintype Successful).toOuterMeasure
              (successfulEvent residual) := by
          calc
            _ = ((PMF.uniformOfFintype {a : Total // success a}).map
                  successfulCoordinates).toOuterMeasure
                    (successfulEvent residual) := by
                rw [PMF.toOuterMeasure_map_apply]
            _ = _ := by
              rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
                successfulCoordinates]
        _ ≤ bound := successfulBound residual

end

#print axioms uniform_successful_subtype_event_probability_le
#print axioms uniform_tape_event_probability_le_successful_sampler_event
#print axioms uniformProductJointLaw_eq_uniform
#print axioms uniform_product_event_probability_le_of_every_slice_le
#print axioms uniform_tape_dependent_successful_event_probability_le

end AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
