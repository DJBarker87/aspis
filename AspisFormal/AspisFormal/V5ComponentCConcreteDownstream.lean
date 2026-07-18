import AspisFormal.V5ComponentCDirectHiding
import AspisFormal.V5ComponentCRelationRowLinearity

/-!
# v5 Component C: one concrete fixed downstream schedule

`V5ComponentCDirectHiding` fixes the Component-C word space and the complete
FRI/later/final evaluator, but accepts the 36 relation rows as a supplied
linear map.  `V5ComponentCRelationRowLinearity` constructs those rows from the
exact two-OOD-plus-seven-coefficient arithmetic.  This leaf joins the two:
the downstream map is literally

`concreteF schedule.fri enc (relationRows schedule.relation)`.

The schedule type itself requires the relation coefficient-fold challenges
to equal the FRI fold challenges.  A mismatched pair is therefore not an
input to the theorem.  There is no C-DEC, transport, rank, fixed-256, or
canonical-padding premise.

The physical Rust relation tail is not stored in the logical 36-row order.
It contains 58 QM31 fields: four circle-point coordinates, six line points,
eight OOD values, eight OOD mixes, 28 polynomial coefficients, and four final
coefficients.  This leaf defines the exact extraction permutation and leaves
both byte decoding and executable correspondence as a named unproved seam.
-/

namespace AspisV5ComponentCConcreteDownstream

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5ComponentCDirectHiding
open AspisV5ComponentCPreCProjection
open AspisV5ComponentCPreCProjectionMixed
open AspisV5ComponentCUnconditionedComposition
open AspisV5MixedFieldComposition

/-- The single Component-C word type, disambiguating the identically reduced
aliases exported by the relation and FRI leaves. -/
abbrev CWord (K : Type*) :=
  AspisV5ComponentCConcreteFoldLinearity.Coefficients K

/-! ## One schedule and one downstream map -/

section Schedule

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- A complete fixed Component-C public schedule.  Equality of the four
relation and FRI alphas is a type-level admission condition, not an optional
premise that a caller may forget. -/
structure CompleteFixedSchedule where
  fri : FixedSchedule F K
  relation : FixedRelationSchedule K
  alphas_agree : relation.alpha = fri.alpha

variable {F K}

/-- The complete schedule discharges the previously named alpha-agreement
interface by construction. -/
theorem relationAndFriAlphasAgree (schedule : CompleteFixedSchedule F K) :
    AspisV5ComponentCRelationRowLinearity.UnmetDeployment.RelationAndFriAlphasAgree
      schedule.relation schedule.fri :=
  schedule.alphas_agree

/-- **The concrete direct downstream map.**  No relation-row linear map is an
argument: it is constructed from the relation schedule. -/
def concreteDownstream (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) :
    CWord K →ₗ[K] (Fin (fRows schedule.fri) → K) :=
  concreteF schedule.fri enc (relationRows schedule.relation)

@[simp] theorem concreteDownstream_def (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) :
    concreteDownstream schedule enc =
      concreteF schedule.fri enc (relationRows schedule.relation) :=
  rfl

/-! ### Relation-coordinate and order teeth -/

theorem concreteDownstream_relation_ood
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K) (round : Fin 4) (sample : Fin 2) :
    concreteDownstream schedule enc c
        (fTaggedIndexEquiv schedule.fri
          (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))))
      = roundOodRows schedule.relation round c sample := by
  rw [concreteDownstream_def, concreteF_relation_coordinate,
    relationRows_at_ood]

theorem concreteDownstream_relation_polynomial
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K) (round : Fin 4) (degree : Fin 7) :
    concreteDownstream schedule enc c
        (fTaggedIndexEquiv schedule.fri
          (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))))
      = roundPolynomialRows schedule.relation round c degree := by
  rw [concreteDownstream_def, concreteF_relation_coordinate,
    relationRows_at_polynomial]

/-- The logical relation index is round-major: OOD row `sample` has local
flat coordinate `9*round+sample`. -/
theorem logical_ood_index_val (round : Fin 4) (sample : Fin 2) :
    (finProdFinEquiv
      (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))).val
      = 9 * round.val + sample.val := by
  change sample.val + 9 * round.val = 9 * round.val + sample.val
  omega

/-- Polynomial coefficient `degree` follows the two OOD rows in its round. -/
theorem logical_polynomial_index_val (round : Fin 4) (degree : Fin 7) :
    (finProdFinEquiv
      (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))).val
      = 9 * round.val + 2 + degree.val := by
  change (2 + degree.val) + 9 * round.val =
    9 * round.val + 2 + degree.val
  omega

end Schedule

/-! ## Exact extraction from the physical 58-field relation tail -/

def physicalRelationTailFieldCount : Nat := 58
def physicalOodStart : Nat := 10
def physicalMixStart : Nat := 18
def physicalPolynomialStart : Nat := 26
def physicalFinalStart : Nat := 54

theorem physical_relation_tail_inventory :
    physicalOodStart = 4 + 6 ∧
    physicalMixStart = physicalOodStart + 8 ∧
    physicalPolynomialStart = physicalMixStart + 8 ∧
    physicalFinalStart = physicalPolynomialStart + 28 ∧
    physicalRelationTailFieldCount = physicalFinalStart + 4 := by
  decide

/-- Physical field position of one logical relation row in
`V5RealHostArtifact::encode_relation_tail`. -/
def physicalRelationIndex (index : RelationTaggedIndex) :
    Fin physicalRelationTailFieldCount :=
  match index.2 with
  | .inl sample =>
      ⟨physicalOodStart + 2 * index.1.val + sample.val, by
        simp only [physicalRelationTailFieldCount, physicalOodStart]
        omega⟩
  | .inr degree =>
      ⟨physicalPolynomialStart + 7 * index.1.val + degree.val, by
        simp only [physicalRelationTailFieldCount, physicalPolynomialStart]
        omega⟩

@[simp] theorem physicalRelationIndex_ood_val (round : Fin 4) (sample : Fin 2) :
    (physicalRelationIndex (round, .inl sample)).val =
      10 + 2 * round.val + sample.val :=
  rfl

@[simp] theorem physicalRelationIndex_polynomial_val
    (round : Fin 4) (degree : Fin 7) :
    (physicalRelationIndex (round, .inr degree)).val =
      26 + 7 * round.val + degree.val :=
  rfl

/-- Reorder the witness-dependent fields from the physical Rust tail into the
logical 36-row map consumed by `concreteF`.  Public points, public OOD mixes,
and final coefficients are intentionally skipped. -/
def reorderPhysicalRelationTail {K : Type*}
    (tail : Fin physicalRelationTailFieldCount → K) : RelationIndex → K :=
  fun logical =>
    tail (physicalRelationIndex (relationTaggedIndexEquiv.symm logical))

theorem reorderPhysicalRelationTail_ood {K : Type*}
    (tail : Fin physicalRelationTailFieldCount → K)
    (round : Fin 4) (sample : Fin 2) :
    reorderPhysicalRelationTail tail
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))
      = tail (physicalRelationIndex (round, .inl sample)) := by
  have hindex : relationTaggedIndexEquiv.symm
      (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
      (round, .inl sample) := by
    unfold relationTaggedIndexEquiv
    apply Prod.ext
    · rfl
    · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
  simp only [reorderPhysicalRelationTail, hindex]

theorem reorderPhysicalRelationTail_polynomial {K : Type*}
    (tail : Fin physicalRelationTailFieldCount → K)
    (round : Fin 4) (degree : Fin 7) :
    reorderPhysicalRelationTail tail
        (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))
      = tail (physicalRelationIndex (round, .inr degree)) := by
  have hindex : relationTaggedIndexEquiv.symm
      (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
      (round, .inr degree) := by
    unfold relationTaggedIndexEquiv
    apply Prod.ext
    · rfl
    · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
  simp only [reorderPhysicalRelationTail, hindex]

/-! ## Complete direct hiding specialization -/

section DirectHiding

variable {F K FA MA MH SB PB VA VH VB TB U : Type*}
variable [Field F] [Field K] [Algebra F K] [Field FA]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup U] [Module K U]
variable [DecidableEq K] [Fintype K]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- Direct hiding with both previously abstract downstream choices removed:
the complete schedule fixes the four common alphas and constructs all 36
relation rows before `concreteF` adds the schedule-sized later/final rows.
The hypotheses are exactly those of the direct capstone; none is duplicated
or weakened. -/
theorem concrete_downstream_complete_joint_hiding
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → CWord K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → CWord K)
    (ell : CWord K →ₗ[K] K) (E : CWord K →ₗ[K] U)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      MixedOuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (hrows₁ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁)
    (hrows₂ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂) :
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E
          (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E
          (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  exact direct_componentC_complete_joint_hiding
    schedule.fri enc (relationRows schedule.relation)
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
    ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂

end DirectHiding

section SuccessfulDirectHiding

variable {F K FA MA MH SB PB VA VH VB TB U : Type*}
variable [Field F] [Field K] [Algebra F K] [Field FA]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup U] [Module K U]
variable [Fintype K]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- Strongest concrete downstream theorem: all 36 relation rows are fixed by
the complete schedule and Component C is drawn from the successful executable
sampler law.  Its hypotheses are verbatim those of
`direct_componentC_complete_joint_hiding_successful_sampler`; only the free
relation-map parameter has been eliminated. -/
theorem concrete_downstream_complete_joint_hiding_successful_sampler
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → CWord K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → CWord K)
    (ell : CWord K →ₗ[K] K) (E : CWord K →ₗ[K] U)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      MixedOuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (hrows₁ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁)
    (hrows₂ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1)
    (successfulFreeLaw : PMF (AspisV5ComponentCSamplerKernel.FreeCoordinates K))
    (rustEncode : AspisV5ComponentCSamplerKernel.FreeCoordinates K →
      LinearMap.ker ell)
    (hfree : AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform
      successfulFreeLaw)
    (hencode : AspisV5ComponentCSamplerKernel.RustEncoderMatchesKernelEquiv
      ell pivot hpivot rustEncode) :
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell successfulFreeLaw
          rustEncode E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell successfulFreeLaw
          rustEncode E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  classical
  exact direct_componentC_complete_joint_hiding_successful_sampler
    schedule.fri enc (relationRows schedule.relation)
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
    ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂
    pivot hpivot successfulFreeLaw rustEncode hfree hencode

end SuccessfulDirectHiding

/-! ## Honest deployment seams -/

namespace UnmetDeployment

variable {F K Bytes : Type*} [Field F] [Field K] [Algebra F K]

/-- Canonical QM31 decoding plus the exact non-contiguous field extraction
above maps the physical Rust relation tail to the model's 36 rows.  Definition
only; no theorem in this file proves it. -/
def PhysicalRustRelationTailCorresponds
    (schedule : CompleteFixedSchedule F K)
    (rustTailBytes : CWord K → Bytes)
    (decodeTail : Bytes → Fin physicalRelationTailFieldCount → K) : Prop :=
  ∀ c, reorderPhysicalRelationTail (decodeTail (rustTailBytes c)) =
    relationRows schedule.relation c

/-- Rust's base-field constant `M31_QUARTER` embeds to the inverse of four
used by `accumulateChunkLinear`.  This code/constant correspondence is named
separately rather than hidden inside the full-row seam. -/
def M31QuarterCorresponds
    (rustM31Quarter : F) : Prop :=
  algebraMap F K rustM31Quarter = (4 : K)⁻¹

/-- Complete model-side downstream equality for Rust's actual `1023`-column
F-matrix domain.  The load-bearing `encodeFree` map is the
free-coordinate-to-kernel embedding implemented by
`V5ComponentCLane::encode_free_coordinates`; omitting it would incorrectly
identify the deployed matrix with the raw `1024`-coefficient reference map.
The output includes relation rows, deduplicated later rows and final
coefficients; physical byte layout and the quarter constant remain separate
obligations. -/
def RustConcreteDownstreamCorresponds
    (schedule : CompleteFixedSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustDownstream : FreeCoordinateVector K →
      Fin (fRows schedule.fri) → K) : Prop :=
  ∀ free, rustDownstream free =
    concreteDownstream schedule enc (encodeFree free)

end UnmetDeployment

/-! ## Axiom audit -/

#print axioms relationAndFriAlphasAgree
#print axioms concreteDownstream_def
#print axioms concreteDownstream_relation_ood
#print axioms concreteDownstream_relation_polynomial
#print axioms logical_ood_index_val
#print axioms logical_polynomial_index_val
#print axioms physical_relation_tail_inventory
#print axioms physicalRelationIndex_ood_val
#print axioms physicalRelationIndex_polynomial_val
#print axioms reorderPhysicalRelationTail_ood
#print axioms reorderPhysicalRelationTail_polynomial
#print axioms concrete_downstream_complete_joint_hiding
#print axioms concrete_downstream_complete_joint_hiding_successful_sampler
#print axioms UnmetDeployment.PhysicalRustRelationTailCorresponds
#print axioms UnmetDeployment.M31QuarterCorresponds
#print axioms UnmetDeployment.RustConcreteDownstreamCorresponds

end AspisV5ComponentCConcreteDownstream
