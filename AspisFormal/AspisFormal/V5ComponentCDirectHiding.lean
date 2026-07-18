import AspisFormal.V5ComponentCPreCProjectionMixed
import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5ComponentCSamplerKernel

/-!
# v5 Component C: direct schedule-indexed hiding composition

This leaf assembles the direct Component-C route from three independently
checked pieces:

* the exact deployed pre-C projection (one combined `ell` scalar and eighteen
  per-lane `E` rows);
* the concrete fixed-challenge circle/line/coefficient folds; and
* the exact uniform-on-`ker ell` pivot-sampler law.

The downstream map is literally
`concreteF schedule enc relationRows`.  Its codomain has the production
schedule's deduplicated size `fRows schedule`; no fixed 256-row convention is
used.  Since the unconditioned Component-C theorem accepts every linear
downstream map, this composition needs no C-DEC premise, rank certificate, or
circle-to-GRS/arity-four transport theorem.

The main theorem is still a mathematical hiding theorem, not a deployed-ZK
claim.  Rust byte/model correspondence, outer-source independence, terminal
PCS compatibility, transcript/compiler assumptions, and hash/commitment
assumptions are named below and deliberately left unproved.
-/

namespace AspisV5ComponentCDirectHiding

open AspisV5ComponentCPreCProjection
open AspisV5ComponentCPreCProjectionMixed
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCSamplerKernel
open AspisV5ComponentCUnconditionedComposition
open AspisV5MixedFieldComposition

/-! ## Direct mathematical capstone -/

section DirectCapstone

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

/-- **Direct schedule-indexed Component-C hiding.**

The C mask word is exactly `Fin 1024 -> K`.  The downstream view is the
concrete public-schedule linear map assembled from the encoder, the four
deployed fold layers, schedule-deduplicated authenticated parent reads, the
four coefficient folds, and the supplied linear relation rows.

All hypotheses are mathematical A/H/B hiding or exact released-row
correspondence hypotheses.  In particular there is no hypothesis about
C-DEC, a `(76+256)` rank, a circle/GRS transport, or canonical padding. -/
theorem direct_componentC_complete_joint_hiding
    (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → Coefficients K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → Coefficients K)
    (ell : Coefficients K →ₗ[K] K) (E : Coefficients K →ₗ[K] U)
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
          (concreteF schedule enc relationRows) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E
          (concreteF schedule enc relationRows) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  exact conditional_complete_joint_hiding_mixed_fields_of_preC_rows
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
    ell E (concreteF schedule enc relationRows) gamma hgamma
    publishedInactive decodeConditionedRows hrows₁ hrows₂

end DirectCapstone

/-! ## Successful Rust-sampler law reduces to the ideal kernel law -/

section SuccessfulSampler

variable {K U Y V : Type*} [Field K] [Fintype K] [DecidableEq K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup Y] [Module K Y]

/-- The same inner Component-C view as `unconditionedCJointKernel`, but fed
by the law obtained from the successful Rust free-coordinate sampler and its
executable pivot encoder.  It models the successful branch only. -/
noncomputable def successfulSamplerJointKernel
    (ell : Coefficients K →ₗ[K] K)
    (successfulFreeLaw : PMF (FreeCoordinates K))
    (rustEncode : FreeCoordinates K → LinearMap.ker ell)
    (E : Coefficients K →ₗ[K] U) (Fmap : Coefficients K →ₗ[K] Y)
    (gamma : K) (visible : V) (preC : Coefficients K) : PMF (V × U × Y) :=
  (successfulEncodedLaw successfulFreeLaw rustEncode).map
    fun c : LinearMap.ker ell =>
      (visible, E ((c : LinearMap.ker ell) : Coefficients K),
        Fmap (preC + gamma ^ 18 •
          ((c : LinearMap.ker ell) : Coefficients K)))

/-- The two explicit sampler interfaces rewrite the successful executable
sampler experiment to the ideal uniform-kernel experiment used by the direct
capstone.  Both premises are consumed by
`samplerUniformOnKerEll_of_exact_interfaces`; neither is decorative. -/
theorem successfulSamplerJointKernel_eq_ideal
    (ell : Coefficients K →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1)
    (successfulFreeLaw : PMF (FreeCoordinates K))
    (rustEncode : FreeCoordinates K → LinearMap.ker ell)
    (hfree : SuccessfulFreeCoordinatesAreIndependentUniform successfulFreeLaw)
    (hencode : RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode)
    (E : Coefficients K →ₗ[K] U) (Fmap : Coefficients K →ₗ[K] Y)
    (gamma : K) (visible : V) (preC : Coefficients K) :
    successfulSamplerJointKernel ell successfulFreeLaw rustEncode
        E Fmap gamma visible preC
      = unconditionedCJointKernel ell E Fmap gamma visible preC := by
  have huniform := samplerUniformOnKerEll_of_exact_interfaces
    ell pivot hpivot successfulFreeLaw rustEncode hfree hencode
  rw [AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces.SamplerUniformOnKerEll]
    at huniform
  simp only [successfulSamplerJointKernel, unconditionedCJointKernel]
  rw [huniform]
  rfl

end SuccessfulSampler

/-! ## Full direct law with the successful executable sampler -/

section SuccessfulDirectCapstone

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

/-- The complete direct theorem with the Component-C coin drawn from the
successful executable sampler law rather than mentioning an ideal kernel
sampler in its statement.  The proof uses both sampler interfaces to rewrite
each inner law to the ideal direct capstone, applies that capstone, then
rewrites back. -/
theorem direct_componentC_complete_joint_hiding_successful_sampler
    (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → Coefficients K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → Coefficients K)
    (ell : Coefficients K →ₗ[K] K) (E : Coefficients K →ₗ[K] U)
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
    (successfulFreeLaw : PMF (FreeCoordinates K))
    (rustEncode : FreeCoordinates K → LinearMap.ker ell)
    (hfree : SuccessfulFreeCoordinatesAreIndependentUniform successfulFreeLaw)
    (hencode : RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode) :
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell successfulFreeLaw
          rustEncode E (concreteF schedule enc relationRows) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell successfulFreeLaw
          rustEncode E (concreteF schedule enc relationRows) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  classical
  let rho := PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)
  let Fmap := concreteF schedule enc relationRows
  let visible₁ := mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
  let visible₂ := mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
  let preC₁ := fun sample => preCWord gamma (semantic₁ sample)
    (hcopy₁ sample) (componentB₁ sample)
  let preC₂ := fun sample => preCWord gamma (semantic₂ sample)
    (hcopy₂ sample) (componentB₂ sample)
  have hleft :
      rho.bind (fun sample => successfulSamplerJointKernel ell
        successfulFreeLaw rustEncode E Fmap gamma (visible₁ sample)
          (preC₁ sample))
        = rho.bind (fun sample => unconditionedCJointKernel ell E Fmap gamma
          (visible₁ sample) (preC₁ sample)) := by
    apply congrArg (fun kernel => rho.bind kernel)
    funext sample
    exact successfulSamplerJointKernel_eq_ideal ell pivot hpivot
      successfulFreeLaw rustEncode hfree hencode E Fmap gamma
      (visible₁ sample) (preC₁ sample)
  have hright :
      rho.bind (fun sample => successfulSamplerJointKernel ell
        successfulFreeLaw rustEncode E Fmap gamma (visible₂ sample)
          (preC₂ sample))
        = rho.bind (fun sample => unconditionedCJointKernel ell E Fmap gamma
          (visible₂ sample) (preC₂ sample)) := by
    apply congrArg (fun kernel => rho.bind kernel)
    funext sample
    exact successfulSamplerJointKernel_eq_ideal ell pivot hpivot
      successfulFreeLaw rustEncode hfree hencode E Fmap gamma
      (visible₂ sample) (preC₂ sample)
  have hideal := direct_componentC_complete_joint_hiding
    schedule enc relationRows LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
    ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂
  change rho.bind (fun sample => successfulSamplerJointKernel ell
      successfulFreeLaw rustEncode E Fmap gamma (visible₁ sample) (preC₁ sample))
    = rho.bind (fun sample => successfulSamplerJointKernel ell
      successfulFreeLaw rustEncode E Fmap gamma (visible₂ sample) (preC₂ sample))
  exact hleft.trans (hideal.trans hright.symm)

end SuccessfulDirectCapstone

/-! ## Honest deployment boundary

These definitions name the remaining edges.  This namespace contains no
theorem asserting that a Rust artifact, transcript, PCS, or hash satisfies
them.
-/

namespace UnmetDeployment

variable {F K FA MA MH SB PB VA VH VB TB U Run Bytes Transcript HashState : Type*}
variable [Field F] [Field K] [Algebra F K] [Field FA]

/-- The four outer sources decode to the independent product-uniform law used
by the mixed-field capstone.  This owns entropy generation, domain
separation, bounded-abort conditioning, and independence from Component C. -/
def OuterSourcesAreIndependentUniform
    [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]
    [Nonempty MA] [Nonempty MH] [Nonempty SB] [Nonempty PB]
    (rustOuterLaw : PMF (MixedOuterSample MA MH SB PB)) : Prop :=
  rustOuterLaw = PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)

/-- Stronger joint-source seam: the decoded outer coins and the successful
Component-C free coordinates have exactly the product law used by the proof.
This states both outer uniformity and independence from the C source, instead
of relying on either as prose. -/
def OuterAndCFreeSourcesAreIndependentUniform
    [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]
    [Nonempty MA] [Nonempty MH] [Nonempty SB] [Nonempty PB]
    (rustJointLaw : PMF
      (MixedOuterSample MA MH SB PB × FreeCoordinates K))
    (successfulFreeLaw : PMF (FreeCoordinates K)) : Prop :=
  rustJointLaw =
    (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
      (fun outer => successfulFreeLaw.map (fun free => (outer, free)))

/-- The accepted Rust run's schedule, encoder, relation evaluator and exact
deduplicated row order decode to `concreteF`.  This is stronger than a
same-language test and deliberately remains an interface. -/
def RustScheduleEncoderRelationCorrespondence
    (schedule : FixedSchedule F K)
    (rustF : Coefficients K → Fin (fRows schedule) → K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) : Prop :=
  AspisV5ComponentCConcreteFoldLinearity.UnmetDeployment.RustFixedScheduleCorrespondence
    schedule rustF enc relationRows

/-- The accepted terminal opening uses the same final codeword coordinate and
four-coefficient tensor represented by the concrete fold model. -/
def DeployedTerminalPCSCompatible
    (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) : Prop :=
  TerminalPCSCompatible schedule enc

/-- Released bytes are an injective serialization of the exact mixed outer
view, C `E` rows, and schedule-sized `concreteF` rows in theorem order. -/
def RustDirectSerializationCorrespondence
    (schedule : FixedSchedule F K)
    (decode : Bytes → MixedOuterVisible VA VH SB TB VB × U ×
      (Fin (fRows schedule) → K))
    (released : Run → Bytes)
    (abstractView : Run → MixedOuterVisible VA VH SB TB VB × U ×
      (Fin (fRows schedule) → K)) : Prop :=
  Function.Injective decode ∧ ∀ run, decode (released run) = abstractView run

/-- Fiat--Shamir/BCS compilation edge: commitments precede the public
schedule and nonzero `gamma`, and the compiler's programmed-RO simulator
transports the proved public-coin law to the adaptive transcript law. -/
def FiatShamirCompilerCorrespondence
    (commitPrefix : Transcript → HashState)
    (scheduleOf : Transcript → FixedSchedule F K)
    (gammaOf : Transcript → K)
    (compiledSimulationValid : Transcript → Prop) : Prop :=
  (∀ transcript, gammaOf transcript ≠ 0) ∧
  (∀ t₁ t₂, commitPrefix t₁ = commitPrefix t₂ →
    scheduleOf t₁ = scheduleOf t₂ ∧ gammaOf t₁ = gammaOf t₂) ∧
  ∀ transcript, compiledSimulationValid transcript

/-- Hash/Merkle edge required by the compiler theorem.  No statement about
SHA-256 is proved here. -/
def HashAndCommitmentAssumptions
    (binding hashHiding randomOracle : HashState → Prop) : Prop :=
  (∀ state, binding state) ∧ (∀ state, hashHiding state) ∧
    ∀ state, randomOracle state

end UnmetDeployment

/-! ## Axiom audit -/

#print axioms direct_componentC_complete_joint_hiding
#print axioms successfulSamplerJointKernel
#print axioms successfulSamplerJointKernel_eq_ideal
#print axioms direct_componentC_complete_joint_hiding_successful_sampler
#print axioms UnmetDeployment.OuterSourcesAreIndependentUniform
#print axioms UnmetDeployment.OuterAndCFreeSourcesAreIndependentUniform
#print axioms UnmetDeployment.RustScheduleEncoderRelationCorrespondence
#print axioms UnmetDeployment.DeployedTerminalPCSCompatible
#print axioms UnmetDeployment.RustDirectSerializationCorrespondence
#print axioms UnmetDeployment.FiatShamirCompilerCorrespondence
#print axioms UnmetDeployment.HashAndCommitmentAssumptions

end AspisV5ComponentCDirectHiding
