import AspisFormal.V5ComponentCEmatModel
import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# v5 Component C: exact kernel sampler law

This leaf closes the finite algebra and probability statement behind
`V5ComponentCLane::encode_free_coordinates`:

* `1023` free field coordinates are inserted away from one pivot row;
* the pivot is the unique correction making the atomic inactive functional
  vanish;
* a unit pivot coefficient makes this map a linear equivalence from
  `K^1023` onto `ker ell`; and
* the image of the joint uniform law on the `1023` free coordinates is
  exactly the uniform law on `ker ell`.

The linear equivalence itself is the already kernel-checked
`pivotEncoderEquiv` from `V5ComponentCEmatModel`; this file adds the exact
`PMF` transfer and packages the deployment seams without re-proving the
linear algebra.

## Honest deployment ceiling

Rust obtains each `QM31` coordinate from four bounded M31 rejection samplers.
This file does **not** pretend that a deterministic word source is random and
does not erase the possible `MaskSampleExhausted` result.  Its Rust-facing
capstone is explicitly conditional on two named interfaces:

1. the successful free-coordinate law is the joint product-uniform law; and
2. the Rust encoder, including row order and pivot selection, is the linear
   equivalence modelled here.

Discharging (1) requires a concrete entropy game for the raw words, their
independence/domain separation, the 31-bit mask, the `< 2^31-1` acceptance
test, all bounded retries, and conditioning on success.  Discharging (2)
requires the Rust/Lean row-table and QM31 representation correspondence.
Neither is asserted in this file.  In particular, this leaf makes no claim
about `V5FixtureRng`, an OS RNG, a PRG, or production entropy.
-/

namespace AspisV5ComponentCSamplerKernel

open AspisV5ComponentCEmatModel
open AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces

/-- The exact number of independently requested Component-C field
coordinates in the Rust sampler. -/
abbrev freeCoordinateCount : Nat := 1023

/-- The ideal free-coordinate space requested by the Rust loop. -/
abbrev FreeCoordinates (K : Type*) := Fin freeCoordinateCount → K

section ExactSampler

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The exact pivot-correction equivalence, re-exported under the sampler
name.  Its forward function is `pivotEncoder ell pivot`; its codomain is the
kernel subtype, so membership is part of the value rather than a premise. -/
def componentCEncoderEquiv (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) :
    FreeCoordinates K ≃ₗ[K] LinearMap.ker ell :=
  pivotEncoderEquiv ell pivot hpivot

omit [Fintype K] [DecidableEq K] in
/-- The sampler encoder is a bijection onto the whole inactive-functional
kernel.  No rank or cardinality premise is assumed. -/
theorem componentCEncoder_bijective (ell : (Fin 1024 → K) →ₗ[K] K)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    Function.Bijective (componentCEncoderEquiv ell pivot hpivot) :=
  (componentCEncoderEquiv ell pivot hpivot).bijective

omit [Fintype K] [DecidableEq K] in
/-- The forward sampler map is literally the pivot encoder used by the
linear-algebra model. -/
theorem componentCEncoder_apply_coe (ell : (Fin 1024 → K) →ₗ[K] K)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1)
    (free : FreeCoordinates K) :
    ((componentCEncoderEquiv ell pivot hpivot free : LinearMap.ker ell) :
        Fin 1024 → K) = pivotEncoder ell pivot free :=
  rfl

/-- Exact ideal law for mutually independent uniform free coordinates.  For
a finite field, the uniform law on the full function space is precisely the
joint product-uniform law; no coordinate is derived from another. -/
noncomputable def idealFreeCoordinateLaw : PMF (FreeCoordinates K) :=
  PMF.uniformOfFintype (FreeCoordinates K)

/-- Ideal successful Component-C sampler law obtained by applying the exact
pivot encoder to the ideal free-coordinate law. -/
noncomputable def idealKernelSamplerLaw
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) : PMF (LinearMap.ker ell) :=
  (idealFreeCoordinateLaw (K := K)).map (componentCEncoderEquiv ell pivot hpivot)

/-- **Exact sampler theorem.** Uniform independent free coordinates, followed
by the derived-pivot encoder, induce exactly the uniform distribution on the
entire kernel. -/
theorem idealKernelSamplerLaw_eq_uniform
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) :
    idealKernelSamplerLaw ell pivot hpivot =
      PMF.uniformOfFintype (LinearMap.ker ell) := by
  exact AspisV5RankOneOpeningHiding.uniform_map_linearEquiv
    (componentCEncoderEquiv ell pivot hpivot)

/-- Converse tooth: because the pivot encoder is an equivalence, it cannot
turn a non-uniform free-coordinate law into the uniform kernel law.  Thus the
joint-uniform source premise is mathematically load-bearing, rather than a
decorative assumption in the Rust-facing capstone. -/
theorem freeCoordinateLaw_eq_uniform_of_encodedLaw_eq_uniform
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1)
    (freeLaw : PMF (FreeCoordinates K))
    (h : freeLaw.map (componentCEncoderEquiv ell pivot hpivot) =
      PMF.uniformOfFintype (LinearMap.ker ell)) :
    freeLaw = idealFreeCoordinateLaw := by
  let e := componentCEncoderEquiv ell pivot hpivot
  have hmap := congrArg (fun law : PMF (LinearMap.ker ell) => law.map e.symm) h
  have hleft : (freeLaw.map e).map e.symm = freeLaw := by
    rw [PMF.map_comp]
    have hfun : (e.symm : LinearMap.ker ell → FreeCoordinates K) ∘
        (e : FreeCoordinates K → LinearMap.ker ell) = id := by
      funext free
      exact e.symm_apply_apply free
    rw [hfun, PMF.map_id]
  have hright : (PMF.uniformOfFintype (LinearMap.ker ell)).map e.symm =
      idealFreeCoordinateLaw := by
    exact AspisV5RankOneOpeningHiding.uniform_map_linearEquiv e.symm
  exact hleft ▸ hright ▸ hmap

/-- Exact iff form: the encoded kernel law is uniform precisely when the
1023-coordinate input law is joint-uniform. -/
theorem encodedLaw_eq_uniform_iff_freeLaw_eq_uniform
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1)
    (freeLaw : PMF (FreeCoordinates K)) :
    freeLaw.map (componentCEncoderEquiv ell pivot hpivot) =
        PMF.uniformOfFintype (LinearMap.ker ell) ↔
      freeLaw = idealFreeCoordinateLaw := by
  constructor
  · exact freeCoordinateLaw_eq_uniform_of_encodedLaw_eq_uniform
      ell pivot hpivot freeLaw
  · intro h
    rw [h]
    exact idealKernelSamplerLaw_eq_uniform ell pivot hpivot

/-- Named deployment interface: the law of the 1023 free QM31 values,
conditioned on the Rust bounded sampler returning success, is the exact joint
uniform law.  This is where raw-word entropy, rejection retries, independence,
and the success conditioning belong. -/
def SuccessfulFreeCoordinatesAreIndependentUniform
    (successfulFreeLaw : PMF (FreeCoordinates K)) : Prop :=
  successfulFreeLaw = idealFreeCoordinateLaw

/-- Named deployment interface: the executable Rust encoder has exactly the
same pivot, non-pivot row enumeration, QM31 arithmetic and output values as
the kernel equivalence. -/
def RustEncoderMatchesKernelEquiv
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1)
    (rustEncode : FreeCoordinates K → LinearMap.ker ell) : Prop :=
  rustEncode = componentCEncoderEquiv ell pivot hpivot

/-- The law produced by a supplied successful free-coordinate law and a
supplied executable encoder.  This deliberately models only the successful
branch; it does not erase or bound `MaskSampleExhausted`. -/
noncomputable def successfulEncodedLaw
    {ell : (Fin 1024 → K) →ₗ[K] K}
    (successfulFreeLaw : PMF (FreeCoordinates K))
    (rustEncode : FreeCoordinates K → LinearMap.ker ell) :
    PMF (LinearMap.ker ell) :=
  successfulFreeLaw.map rustEncode

/-- Rust-facing conditional capstone.  Both deployment interfaces are used:
the first fixes the source law, and the second fixes the executable encoder.
The conclusion is the existing `SamplerUniformOnKerEll` obligation used by
the Component-C hiding capstones. -/
theorem samplerUniformOnKerEll_of_exact_interfaces
    (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1)
    (successfulFreeLaw : PMF (FreeCoordinates K))
    (rustEncode : FreeCoordinates K → LinearMap.ker ell)
    (hfree : SuccessfulFreeCoordinatesAreIndependentUniform successfulFreeLaw)
    (hencode : RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode) :
    SamplerUniformOnKerEll ell
      (successfulEncodedLaw successfulFreeLaw rustEncode) := by
  rw [SuccessfulFreeCoordinatesAreIndependentUniform] at hfree
  rw [RustEncoderMatchesKernelEquiv] at hencode
  rw [SamplerUniformOnKerEll, successfulEncodedLaw, hfree, hencode]
  exact idealKernelSamplerLaw_eq_uniform ell pivot hpivot

end ExactSampler

/-! ## Concrete non-vacuity over a finite field -/

namespace NonVacuity

/-- A finite-field demo pivot. -/
def z2Pivot : Fin 1024 := 0

/-- A finite-field demo inactive functional: projection at the pivot. -/
def z2Ell : (Fin 1024 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj z2Pivot

/-- The demo functional has the required unit pivot coefficient. -/
theorem z2Ell_pivot : z2Ell (Pi.single z2Pivot 1) = 1 := by
  simp [z2Ell, z2Pivot]

/-- The exact uniform-kernel theorem has a concrete finite-field instance;
its hypotheses are not vacuous. -/
theorem z2_idealKernelSamplerLaw_eq_uniform :
    idealKernelSamplerLaw z2Ell z2Pivot z2Ell_pivot =
      PMF.uniformOfFintype (LinearMap.ker z2Ell) :=
  idealKernelSamplerLaw_eq_uniform z2Ell z2Pivot z2Ell_pivot

/-- Degenerate non-unit-pivot functional used to show that the unit pivot
coefficient is essential. -/
def z2ZeroEll : (Fin 1024 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := 0

/-- Negative tooth: with zero pivot coefficient, the same placement/correction
formula is not onto the kernel.  The missing vector is the unit vector at the
pivot itself. -/
theorem zeroPivotEncoder_not_surjective :
    ¬ Function.Surjective (pivotEncoder z2ZeroEll z2Pivot) := by
  intro hsurj
  obtain ⟨free, hfree⟩ := hsurj (Pi.single z2Pivot (1 : ZMod 2))
  have hpivot := congrFun hfree z2Pivot
  rw [pivotEncoder_apply_pivot] at hpivot
  simp [z2ZeroEll, z2Pivot] at hpivot

end NonVacuity

/-! ## Axiom audit -/

#print axioms componentCEncoderEquiv
#print axioms componentCEncoder_bijective
#print axioms componentCEncoder_apply_coe
#print axioms idealFreeCoordinateLaw
#print axioms idealKernelSamplerLaw
#print axioms idealKernelSamplerLaw_eq_uniform
#print axioms freeCoordinateLaw_eq_uniform_of_encodedLaw_eq_uniform
#print axioms encodedLaw_eq_uniform_iff_freeLaw_eq_uniform
#print axioms SuccessfulFreeCoordinatesAreIndependentUniform
#print axioms RustEncoderMatchesKernelEquiv
#print axioms successfulEncodedLaw
#print axioms samplerUniformOnKerEll_of_exact_interfaces
#print axioms NonVacuity.z2Ell_pivot
#print axioms NonVacuity.z2_idealKernelSamplerLaw_eq_uniform
#print axioms NonVacuity.zeroPivotEncoder_not_surjective

end AspisV5ComponentCSamplerKernel
