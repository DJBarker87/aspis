import AspisFormal.V5ComponentCConcreteDownstream
import AspisFormal.V5ComponentCRejectionSampler

/-!
# v5 Component C: direct hiding from the bounded `u32` sampler

This leaf substitutes the exact finite rejection-sampling experiment into the
strongest concrete Component-C downstream theorem.  The successful free law
is literally `successfulComponentCFreeCoordinateLaw e`: a uniform
preallocated family of `u32` words, conditioned once on all 4092 bounded
calls succeeding, projected to low 31 bits, decoded through the supplied
four-limb equivalence, and encoded into `ker ell` by the literal
`componentCEncoderEquiv`.

Consequently the theorem below has no abstract Component-C sampler-law or
encoder premise.  The rejection-sampler theorem discharges both interfaces.

## Honest ceiling

This remains a finite ideal/HVZK-side theorem.  It deliberately retains the
outer A/H/B surjectivity hypotheses and the two deployed-shaped
`MixedDeployedProjectionCorrespondence` premises.  It does not assert any of
the imported deployment seams: production PRG/CSPRNG pseudorandomness,
variable-consumption stopping-time correspondence, the Rust low31 operation,
QM31 limb order/codec, executable downstream code/model equality, PCS
binding, Fiat--Shamir/RO compilation, or salted-Merkle/hash assumptions.
Those remain separate named obligations; none is discharged here.
-/

namespace AspisV5ComponentCBlockSamplerDirectHiding

open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDirectHiding
open AspisV5ComponentCPreCProjection
open AspisV5ComponentCPreCProjectionMixed
open AspisV5ComponentCUnconditionedComposition
open AspisV5MixedFieldComposition
open AspisV5ComponentCRejectionSampler

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

/-- Strongest finite direct-hiding theorem currently available for Component
C.  The concrete successful law comes from the literal whole-`u32`
conditioning experiment, and the encoder is the exact pivot-correction linear
equivalence.  Thus no abstract C sampler or C encoder hypothesis remains. -/
theorem concrete_downstream_complete_joint_hiding_conditioned_u32_sampler
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
    (e : QM31Limbs ≃ K) :
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell
          (successfulComponentCFreeCoordinateLaw e)
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
            ell pivot hpivot)
          E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell
          (successfulComponentCFreeCoordinateLaw e)
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
            ell pivot hpivot)
          E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  classical
  exact concrete_downstream_complete_joint_hiding_successful_sampler
    schedule enc LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
    ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂
    pivot hpivot (successfulComponentCFreeCoordinateLaw e)
    (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)
    (successfulComponentCFreeCoordinateLaw_isIndependentUniform e)
    (by rfl)

/-! ## Axiom audit -/

#print axioms concrete_downstream_complete_joint_hiding_conditioned_u32_sampler

end AspisV5ComponentCBlockSamplerDirectHiding
