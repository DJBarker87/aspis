import AspisFormal.V5InactiveClaimDeployedCorrespondence
import AspisFormal.V5DeployedCarriedInvariant

/-!
# Component-B parameterized read-law factorization

The Component-B algebra supplies the shared-pivot read shape
`AspisV5InactiveClaimJointHiding.sharedPivotView_pmf_indep`, proved in model:
one uniform pivot scalar feeds the authenticated terminal opening, the carried
copy-inactive claim, and the residual released view, and the joint law is
computed exactly (`sharedPivotView_law`).  One gap between deployed artefacts
and any HVZK application was the capstone-v2 correspondence premise
`hCarriedB`, packaged in `V5DeployedCarriedInvariant` as a witness-difference
certificate: a legal-difference space `ΔB`, a spanning generator list, and
per-generator kernel checks.  That module records that no executable `ΔB`
exists in the deployed Rust, so its interface
(`UnmetDeployment.DeployedCarriedCertificateInterface`) has no deployed
artefact to consume today.

This file studies an alternative conditional interface: the
deployed serialized B-lane reads — terminal opening, carried inactive claim,
residual view, as functions of the one sampled pivot scalar — are exactly the
`sharedPivotView` shape at the transcribed deployed terminal covector, with
pivot direction `k = e₉₉₃` and unit inactive coefficient `inactive k = 1`.
Stated as the named interface `DeployedBLaneReadsAreSharedPivotView`, the
following parameterized consequences hold in the model:

1. **Exact parameterized read-law factorization** (the legacy theorem name is
   `deployed_bLane_reads_witness_free_law`).
   Given the interface, the deployed B-lane read law equals the law of the
   explicit sampler `simulatedBLaneReads t r₀ slope`, which draws one uniform
   scalar.  Its three parameters are
   the authenticated terminal value `t`, the residual intercept
   `r₀ = released m − inactive m • released e₉₉₃`, and the slope
   `released e₉₉₃`.

2. **The old premise becomes a parameter equality**
   (`intercept_eq_correctedReleased`,
   `deployed_bLane_reads_pmf_indep`).  The intercept `r₀` is literally
   `correctedReleased inactive released e₉₉₃ m` of
   `V5DeployedCarriedInvariant` at `inactive e₉₉₃ = 1`, and pairwise
   indistinguishability of two deployed runs needs exactly equality of their
   intercepts — the verbatim `hCarriedB` shape.  That equality remains an
   explicit condition of the pairwise law.  This file does not prove that
   `t` or `r₀` is public, witness-independent, or available to an HVZK
   simulator at the required transcript time.

3. **The parameters are exactly what the reads reveal**
   (`deployed_bLane_reads_reveal_intercept`).  Pushing the deployed read law
   through the discriminator returns the point mass at the intercept — the
   transported `sharedPivotViewShape_map_discriminator` of
   `V5DeployedCarriedInvariant`.  This is an after-the-fact factorization of
   the released read triple; it is not a proof that those parameters can be
   generated from the public statement before simulating the view.

4. **Serialization corollary** (legacy name
   `deployed_bLane_bytes_witness_free_law`).  Any byte encoding of the read
   triple inherits the same parameterized law by data
   processing; exactness and position of the deployed encoding stay with the
   named serialization premises of
   `V5InactiveClaimDeployedCorrespondence` (Question 3 there), untouched.

5. **Model non-vacuity** (`interface_nonvacuous`,
   `hvzk_reduction_nonvacuous`).  The interface and pairwise implication fire
   on a synthetic shared-pivot read function using the transcribed terminal
   covector.  This does not instantiate the deployed serializer.

## Why the interface is minimal

* The pivot-kernel fact `terminal e₉₉₃ = 0` is NOT a conjunct: it is proved
  for the transcribed covector
  (`AspisV5InactiveClaimJointHiding.terminalDotFunctional_pivot_eq_zero`, the
  row-993 weight-zero theorem) and consumed silently.
* No `gammaB ≠ 0` bound is a conjunct: the unit-mask premise
  `DeployedInactiveCovectorIsUnitAtPivotRow` — reused from
  `V5InactiveClaimDeployedCorrespondence`, where its Rust content is
  documented (the binary copy-inactive row mask sets row 993 with coefficient
  one) — supplies `inactive e₉₉₃ = 1 ≠ 0` outright.
* Pivot freshness `released e₉₉₃ = 0` is NOT assumed, matching the recorded
  deployed evidence against it (the released claims table's `eq` covectors
  read row 993; see Question 2 of `V5InactiveClaimDeployedCorrespondence`):
  the exact law keeps the correlation through the public slope
  `released e₉₉₃` instead of assuming it away.
* No legal-difference space, no generator list, no span condition, and no
  kernel-containment certificate appear: the fixed-schedule Δ machinery is
  not consumed anywhere in this file.

## Relation to `V5DeployedCarriedInvariant`

That module does not already cover this reduction.  It transcribes the
`sharedPivotView` shape (`sharedPivotViewShape`, definitionally equal to the
model's `sharedPivotView`) only as the codomain of its discriminator and
negative tests, and its deployed interface is the Δ-based
`DeployedCarriedCertificateInterface`, which additionally demands the
`ΔB`-span and generator-check artefacts that the deployed Rust does not
contain.  What it does contribute is reused here and cited: the corrected
map `correctedReleased` (the intercept, item 2) and the discriminator
theorem (item 3).  The smallest piece that was missing — and that this file
names — is the per-read conjunct itself: `∀ p, deployedReads p =
sharedPivotView (terminalDotFunctional point scale) inactive released
(basis pivotRow 1) m p`, together with the unit-mask premise.  Discharging
it is a code-transcription obligation against the deployed serializer
(`V5StructuredBLane::encode` writes the pivot at row 993; the read surfaces
are inventoried in the two correspondence modules), not a linear-algebra
obligation; nothing in this repository proves it, and this file does not
claim it.

Scope: everything proved here is finite linear algebra and uniform-`PMF`
reasoning over the transcribed layout.  Commitment binding, transcript
ordering, and byte-position exactness remain the named obligations of
`V5SumcheckTranscriptBinding` and `V5InactiveClaimDeployedCorrespondence`.
Additionally, a complete HVZK reduction still must prove that the parameters
`t` and `r₀` used by this factorization are equal across the compared witness
experiments and are publicly simulatable at the appropriate transcript point.
-/

open scoped ENNReal

namespace AspisV5InactiveClaimHVZKReduction

open AspisV5CompactTerminal
open AspisV5InactiveClaimJointHiding
open AspisV5InactiveClaimDeployedCorrespondence

variable {K : Type*} [Field K]

/-! ## 1. The parameterized normal form and named interface -/

/-- The parameterized B-lane read normal form: draw one uniform scalar `c`, output
the pinned terminal value, the scalar itself as the carried claim, and the
affine residual `r₀ + c • slope`.  A mask assignment does not appear after
the three parameters are supplied, but `t` and `intercept` may themselves
depend on the witness.  This definition does not prove they are public or
simulatable. -/
def simulatedBLaneReads {V : Type*} [AddCommGroup V] [Module K V]
    (t : K) (intercept slope : V) : K → K × K × V :=
  fun c => (t, c, intercept + c • slope)

/-- **The minimal named deployed interface of the B-terminal HVZK leg.**  The
deployed serialized B-lane reads — the decoded (terminal opening, carried
inactive claim, residual view) triple as a function of the sampled pivot
scalar — are exactly the `sharedPivotView` shape at the transcribed deployed
terminal covector, with pivot direction `k = e₉₉₃` (`basis pivotRow 1`) and
the deployed released covectors `inactive`, `released`; and the copy-inactive
covector reads the pivot with unit coefficient (the reused binary-mask
premise `DeployedInactiveCovectorIsUnitAtPivotRow`).  The pivot-kernel fact
is not a conjunct: it is proved for the transcribed covector.  Nothing in
this repository discharges either conjunct for the deployed byte stream; the
first is the per-read code-transcription obligation, the second the binary
row-mask bind. -/
def DeployedBLaneReadsAreSharedPivotView {V : Type*} [AddCommGroup V]
    [Module K V] (deployedReads : K → K × K × V) (point : Round → K)
    (scale : K) (inactive : (Row → K) →ₗ[K] K)
    (released : (Row → K) →ₗ[K] V) (m : Row → K) : Prop :=
  (∀ p : K, deployedReads p
      = sharedPivotView (terminalDotFunctional point scale) inactive released
          (basis pivotRow 1) m p)
    ∧ DeployedInactiveCovectorIsUnitAtPivotRow inactive

/-! ## 2. The conditional theorems -/

section Conditional

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **Conditional theorem, parameterized exact-law form.**  Given the interface, the
deployed B-lane read law factors through `simulatedBLaneReads` at the
parameters `t` (authenticated terminal value),
`r₀ = released m − inactive m • released e₉₉₃` (residual intercept), and
`released e₉₉₃` (slope).  The witness may enter through `(t, r₀)`; the theorem
does not show these parameters are equal between witnesses or available from
the public statement. -/
theorem deployed_bLane_reads_witness_free_law [Fintype K]
    (deployedReads : K → K × K × V) (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (m : Row → K)
    (h : DeployedBLaneReadsAreSharedPivotView deployedReads point scale
      inactive released m)
    (t : K) (hm : terminalDotFunctional point scale m = t) :
    (PMF.uniformOfFintype K).map deployedReads
      = (PMF.uniformOfFintype K).map
          (simulatedBLaneReads t
            (released m - inactive m • released (basis pivotRow 1))
            (released (basis pivotRow 1))) := by
  obtain ⟨hreads, hunit⟩ := h
  have hone : inactive (basis pivotRow 1) = 1 := hunit
  rw [funext hreads,
    sharedPivotView_law (terminalDotFunctional point scale) inactive released
      (basis pivotRow 1) m t (terminalDotFunctional_pivot_eq_zero point scale)
      (by rw [hone]; exact one_ne_zero) hm]
  congr 1
  funext c
  simp only [simulatedBLaneReads, hone, inv_one, one_mul]

/-- The normal form's intercept is the corrected released value of
`V5DeployedCarriedInvariant` at the unit pivot coefficient: the object the
capstone-v2 premise `hCarriedB` constrains is exactly this parameter. -/
theorem intercept_eq_correctedReleased
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (m : Row → K)
    (hunit : DeployedInactiveCovectorIsUnitAtPivotRow inactive) :
    released m - inactive m • released (basis pivotRow 1)
      = AspisV5DeployedCarriedInvariant.correctedReleased inactive released
          (basis pivotRow 1) m := by
  have hone : inactive (basis pivotRow 1) = 1 := hunit
  rw [AspisV5DeployedCarriedInvariant.correctedReleased_apply, hone, inv_one,
    one_mul]

/-- **Conditional theorem, pairwise equality form.**  Two deployed runs whose
reads satisfy the interface, whose authenticated terminal values agree, and
whose residual intercepts agree have identical read laws.  The intercept
equality is the verbatim `hCarriedB` shape at `inactive e₉₉₃ = 1`.  Equality
of `t` and the intercept is assumed here, not derived from public
simulatability or witness independence. -/
theorem deployed_bLane_reads_pmf_indep [Fintype K]
    (reads₁ reads₂ : K → K × K × V) (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (m₁ m₂ : Row → K)
    (h₁ : DeployedBLaneReadsAreSharedPivotView reads₁ point scale inactive
      released m₁)
    (h₂ : DeployedBLaneReadsAreSharedPivotView reads₂ point scale inactive
      released m₂)
    (t : K) (hm₁ : terminalDotFunctional point scale m₁ = t)
    (hm₂ : terminalDotFunctional point scale m₂ = t)
    (hintercept : released m₁ - inactive m₁ • released (basis pivotRow 1)
      = released m₂ - inactive m₂ • released (basis pivotRow 1)) :
    (PMF.uniformOfFintype K).map reads₁
      = (PMF.uniformOfFintype K).map reads₂ := by
  rw [deployed_bLane_reads_witness_free_law reads₁ point scale inactive
      released m₁ h₁ t hm₁,
    deployed_bLane_reads_witness_free_law reads₂ point scale inactive
      released m₂ h₂ t hm₂,
    hintercept]

/-- **The released triple determines its intercept.**  Pushing the deployed
read law through the discriminator returns the point mass at the intercept.
This after-the-fact recoverability does not show that an HVZK simulator knows
the intercept before producing the triple.  The identity is transported from
`AspisV5DeployedCarriedInvariant.sharedPivotViewShape_map_discriminator`. -/
theorem deployed_bLane_reads_reveal_intercept [Fintype K]
    (deployedReads : K → K × K × V) (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (m : Row → K)
    (h : DeployedBLaneReadsAreSharedPivotView deployedReads point scale
      inactive released m) :
    ((PMF.uniformOfFintype K).map deployedReads).map
        (fun view => view.2.2 - view.2.1 • released (basis pivotRow 1))
      = PMF.pure (released m - inactive m • released (basis pivotRow 1)) := by
  obtain ⟨hreads, hunit⟩ := h
  have hone : inactive (basis pivotRow 1) = 1 := hunit
  have hfun : (fun view : K × K × V =>
        view.2.2 - view.2.1 • released (basis pivotRow 1))
      = fun view : K × K × V =>
          view.2.2 - ((inactive (basis pivotRow 1))⁻¹ * view.2.1)
            • released (basis pivotRow 1) := by
    funext view
    rw [hone, inv_one, one_mul]
  have hshape : sharedPivotView (terminalDotFunctional point scale) inactive
        released (basis pivotRow 1) m
      = AspisV5DeployedCarriedInvariant.sharedPivotViewShape
          (terminalDotFunctional point scale) inactive released
          (basis pivotRow 1) m := rfl
  rw [funext hreads, hfun, hshape,
    AspisV5DeployedCarriedInvariant.sharedPivotViewShape_map_discriminator
      (terminalDotFunctional point scale) inactive released (basis pivotRow 1)
      m (by rw [hone]; exact one_ne_zero),
    ← intercept_eq_correctedReleased inactive released m hunit]

/-- **Serialization corollary.**  Any byte encoding of the read triple
inherits the parameterized law by data processing.  Whether the deployed wire
bytes are such an encoding of exactly this triple is the serialization
obligation recorded in `V5InactiveClaimDeployedCorrespondence`; it is not
consumed or discharged here. -/
theorem deployed_bLane_bytes_witness_free_law [Fintype K] {Bytes : Type*}
    (encodeReads : K × K × V → Bytes)
    (deployedReads : K → K × K × V) (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (m : Row → K)
    (h : DeployedBLaneReadsAreSharedPivotView deployedReads point scale
      inactive released m)
    (t : K) (hm : terminalDotFunctional point scale m = t) :
    (PMF.uniformOfFintype K).map (fun p => encodeReads (deployedReads p))
      = (PMF.uniformOfFintype K).map
          (fun c => encodeReads (simulatedBLaneReads t
            (released m - inactive m • released (basis pivotRow 1))
            (released (basis pivotRow 1)) c)) := by
  have hlaw := deployed_bLane_reads_witness_free_law deployedReads point scale
    inactive released m h t hm
  calc (PMF.uniformOfFintype K).map (fun p => encodeReads (deployedReads p))
      = ((PMF.uniformOfFintype K).map deployedReads).map encodeReads :=
        (PMF.map_comp _ _ _).symm
    _ = ((PMF.uniformOfFintype K).map
          (simulatedBLaneReads t
            (released m - inactive m • released (basis pivotRow 1))
            (released (basis pivotRow 1)))).map encodeReads := by rw [hlaw]
    _ = (PMF.uniformOfFintype K).map
          (fun c => encodeReads (simulatedBLaneReads t
            (released m - inactive m • released (basis pivotRow 1))
            (released (basis pivotRow 1)) c)) := PMF.map_comp _ _ _

end Conditional

/-! ## 3. Model non-vacuity using the transcribed terminal covector -/

/-- The interface is satisfiable for a synthetic read function at the
transcribed terminal covector: reads are defined as the shared-pivot view itself, with the row-993 projection as
the inactive covector (which satisfies the binary-mask premise) and the
row-994 pad projection as the residual view. -/
theorem interface_nonvacuous (point : Round → K) (scale : K) (m : Row → K) :
    DeployedBLaneReadsAreSharedPivotView
      (sharedPivotView (terminalDotFunctional point scale)
        (LinearMap.proj pivotRow) (LinearMap.proj padRow) (basis pivotRow 1) m)
      point scale (LinearMap.proj pivotRow) (LinearMap.proj padRow) m :=
  ⟨fun _ => rfl, binary_mask_interface_nonvacuous⟩

/-- **Model non-vacuity of the implication.**  At the transcribed terminal
covector, the pairwise conclusion fires for the zero vector and the unit
pivot vector — two witnesses that genuinely differ in their inactive
coordinate — and the two synthetic read laws are equal. -/
theorem hvzk_reduction_nonvacuous [Fintype K] (point : Round → K) (scale : K) :
    (PMF.uniformOfFintype K).map
        (sharedPivotView (terminalDotFunctional point scale)
          (LinearMap.proj pivotRow) (LinearMap.proj padRow) (basis pivotRow 1)
          (0 : Row → K))
      = (PMF.uniformOfFintype K).map
        (sharedPivotView (terminalDotFunctional point scale)
          (LinearMap.proj pivotRow) (LinearMap.proj padRow) (basis pivotRow 1)
          (basis pivotRow 1))
    ∧ (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K) (0 : Row → K)
        ≠ (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K) (basis pivotRow 1) := by
  constructor
  · refine deployed_bLane_reads_pmf_indep _ _ point scale
      (LinearMap.proj pivotRow) (LinearMap.proj padRow) 0 (basis pivotRow 1)
      (interface_nonvacuous point scale 0)
      (interface_nonvacuous point scale (basis pivotRow 1)) 0 (map_zero _)
      (terminalDotFunctional_pivot_eq_zero point scale) ?_
    have hpad : (basis pivotRow (1 : K)) padRow = 0 := by
      simp [basis, show padRow ≠ pivotRow from by decide]
    simp [LinearMap.proj_apply, hpad]
  · have h0 : (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K) (0 : Row → K)
        = 0 := map_zero _
    have h1 : (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K) (basis pivotRow 1)
        = 1 := by simp [LinearMap.proj_apply, basis]
    rw [h0, h1]
    exact zero_ne_one

/-! ## Axiom audit -/

#print axioms simulatedBLaneReads
#print axioms DeployedBLaneReadsAreSharedPivotView
#print axioms deployed_bLane_reads_witness_free_law
#print axioms intercept_eq_correctedReleased
#print axioms deployed_bLane_reads_pmf_indep
#print axioms deployed_bLane_reads_reveal_intercept
#print axioms deployed_bLane_bytes_witness_free_law
#print axioms interface_nonvacuous
#print axioms hvzk_reduction_nonvacuous

end AspisV5InactiveClaimHVZKReduction
