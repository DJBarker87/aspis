import AspisFormal.V5ComponentCAffineCoupling

/-!
# v5 Component C: sample-aware unconditioned composition

This file composes the unconditioned Component-C coupling with the intended
outer A/B sampler shape.  An outer sample `s` is drawn from `rho`; Component C
is then drawn uniformly from the whole space `ker ell` and releases

    (visible s, E c, F (preC s + gamma^18 * c)).

The A/B coupling is a measure-preserving equivalence `tau` of the outer sample
space.  Pointwise equality of the visible value, `ell preC`, and `E preC`
after reindexing lets
`componentC_unconditioned_joint_law_of_matched_residuals` identify the two
inner laws.  The outer laws are then equal by reindexing `rho` through `tau`.

There is no fixed released value, filter, fibre disintegration, rank, or
surjectivity premise.  The candidate Rust pre-C word, uniform sampler,
serialization, and Fiat--Shamir transcript correspondences remain named,
unproved implementation interfaces below.  Consequently this file is not a deployed zero-knowledge
claim.
-/

open scoped ENNReal

namespace AspisV5ComponentCUnconditionedComposition

open AspisV5ComponentCAffineCoupling

variable {K M U Y S V : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-! ## The intended unconditioned sampler shape -/

/-- For one outer A/B sample, sample Component C uniformly from the whole
relation kernel and release the outer visible value, the C lane's own
`E`-coordinate, and the post-combination `F`-view. -/
noncomputable def unconditionedCJointKernel
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (gamma : K) (visible : V) (preC : M) : PMF (V × U × Y) :=
  (PMF.uniformOfFintype (LinearMap.ker ell)).map
    fun c : LinearMap.ker ell =>
      (visible, E ((c : LinearMap.ker ell) : M),
        F (preC + gamma ^ 18 • ((c : LinearMap.ker ell) : M)))

/-- Pointwise leaf: matched visible, `ell`, and `E` residuals identify the two
unconditioned inner Component-C laws. -/
theorem unconditionedCJointKernel_eq_of_match
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0)
    (visible₁ visible₂ : V) (preC₁ preC₂ : M)
    (hvisible : visible₁ = visible₂)
    (hell : ell preC₁ = ell preC₂) (hE : E preC₁ = E preC₂) :
    unconditionedCJointKernel ell E F gamma visible₁ preC₁
      = unconditionedCJointKernel ell E F gamma visible₂ preC₂ := by
  have hC := componentC_unconditioned_joint_law_of_matched_residuals
    ell E F hgamma hell hE
  unfold unconditionedCJointKernel
  rw [hvisible]
  have hlift := congrArg
    (fun q : PMF (U × Y) => q.map (fun z => (visible₂, z.1, z.2))) hC
  simpa only [PMF.map_comp, Function.comp_def] using hlift

/-- **Full sample-aware unconditioned Component-C composition.**

The left and right experiments both draw from the literal outer law `rho` and
then uniformly from all of `ker ell`.  The proof first applies the
unconditioned Component-C theorem at each outer sample and then reindexes the
second outer experiment through the measure-preserving equivalence `tau`.
Every hypothesis is load-bearing; concrete failures appear below. -/
theorem sampleAware_unconditioned_componentC_joint_law
    [DecidableEq K] [Fintype M]
    (rho : PMF S) (tau : S ≃ S) (hmeasure : rho.map tau = rho)
    (preC₁ preC₂ : S → M) (visible₁ visible₂ : S → V)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0)
    (hvisible : ∀ s, visible₁ s = visible₂ (tau s))
    (hell : ∀ s, ell (preC₁ s) = ell (preC₂ (tau s)))
    (hE : ∀ s, E (preC₁ s) = E (preC₂ (tau s))) :
    rho.bind (fun s =>
        unconditionedCJointKernel ell E F gamma (visible₁ s) (preC₁ s))
      = rho.bind (fun s =>
          unconditionedCJointKernel ell E F gamma (visible₂ s) (preC₂ s)) := by
  let Q₁ : S → PMF (V × U × Y) := fun s =>
    unconditionedCJointKernel ell E F gamma (visible₁ s) (preC₁ s)
  let Q₂ : S → PMF (V × U × Y) := fun s =>
    unconditionedCJointKernel ell E F gamma (visible₂ s) (preC₂ s)
  have hkernel : ∀ s, Q₁ s = Q₂ (tau s) := by
    intro s
    exact unconditionedCJointKernel_eq_of_match ell E F hgamma
      (visible₁ s) (visible₂ (tau s)) (preC₁ s) (preC₂ (tau s))
      (hvisible s) (hell s) (hE s)
  change rho.bind Q₁ = rho.bind Q₂
  calc
    rho.bind Q₁ = rho.bind (Q₂ ∘ (tau : S → S)) := by
      apply congrArg (fun q : S → PMF (V × U × Y) => rho.bind q)
      funext s
      exact hkernel s
    _ = (rho.map tau).bind Q₂ := (PMF.bind_map rho tau Q₂).symm
    _ = rho.bind Q₂ := by rw [hmeasure]

/-! ## Honest candidate-implementation interfaces -/

namespace UnmetDeployment

/-- The modeled pre-C word is the exact word a candidate Rust implementation
must produce by its
gamma-combination on the same outer sample.  Definition only; no theorem in
this file proves it. -/
def RustPreCCorrespondence {Run Sample : Type*}
    (runOfSample : Sample → Run) (rustPreC : Run → M)
    (leanPreC : Sample → M) : Prop :=
  ∀ s, leanPreC s = rustPreC (runOfSample s)

/-- Decoding a candidate Rust Component-C sampler gives exactly the uniform
law on the whole Lean kernel `ker ell`.  Definition only. -/
def RustUniformKernelSamplerCorrespondence {Sample RustCoin : Type*}
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (rustCoins : Sample → PMF RustCoin)
    (decodeMask : Sample → RustCoin → LinearMap.ker ell) : Prop :=
  ∀ s, (rustCoins s).map (decodeMask s) =
    PMF.uniformOfFintype (LinearMap.ker ell)

/-- The bytes released by a candidate run are exactly the serialization of
the abstract triple used by `unconditionedCJointKernel`, in the same
coordinate order.  This is a code-to-model edge, not merely a codec
round-trip.  Definition only. -/
def RustSerializationCorrespondence {Run Bytes : Type*}
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y) (gamma : K)
    (releasedBytes : Run → LinearMap.ker ell → Bytes)
    (serialize : V → U → Y → Bytes) (visible : Run → V) (preC : Run → M) :
    Prop :=
  ∀ run c, releasedBytes run c =
    serialize (visible run) (E ((c : LinearMap.ker ell) : M))
      (F (preC run + gamma ^ 18 • ((c : LinearMap.ker ell) : M)))

/-- A candidate implementation's transcript fixes the same outer reindexing, schedule, and
nonzero `gamma` before the Component-C sample is used, and derives the same
challenge on both the Rust and Lean sides.  This explicitly fences the
Fiat--Shamir/compiler edge; it is not proved here. -/
def FiatShamirCorrespondence {Transcript Schedule Sample : Type*}
    (pinnedSchedule : Schedule) (pinnedGamma : K)
    (tau : Sample ≃ Sample) (rustReindex leanReindex : Sample → Sample)
    (rustTranscript leanTranscript : Sample → Transcript)
    (scheduleOf : Transcript → Schedule) (gammaOf : Transcript → K)
    (CommittedBeforeComponentCSample : Transcript → Prop) : Prop :=
  pinnedGamma ≠ 0 ∧ ∀ s,
    CommittedBeforeComponentCSample (rustTranscript s)
      ∧ CommittedBeforeComponentCSample (leanTranscript s)
      ∧ rustReindex s = tau s
      ∧ leanReindex s = tau s
      ∧ scheduleOf (rustTranscript s) = pinnedSchedule
      ∧ scheduleOf (leanTranscript s) = pinnedSchedule
      ∧ gammaOf (rustTranscript s) = pinnedGamma
      ∧ gammaOf (leanTranscript s) = pinnedGamma

end UnmetDeployment

/-! ## Non-vacuity and load-bearing negative tests -/

/-- All hypotheses of the full theorem are simultaneously satisfiable in a
nonempty finite model. -/
theorem sampleAware_unconditioned_hypotheses_instantiable :
    ∃ (rho : PMF Unit) (tau : Unit ≃ Unit)
        (preC₁ preC₂ : Unit → ZMod 2) (visible₁ visible₂ : Unit → Unit),
      rho.map tau = rho
        ∧ (1 : ZMod 2) ≠ 0
        ∧ (∀ s, visible₁ s = visible₂ (tau s))
        ∧ (∀ s, (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₁ s)
            = (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₂ (tau s)))
        ∧ (∀ s, (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₁ s)
            = (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₂ (tau s))) := by
  refine ⟨PMF.pure (), Equiv.refl Unit, (fun _ => 0), (fun _ => 0),
    (fun _ => ()), (fun _ => ()), ?_, one_ne_zero, ?_, ?_, ?_⟩
  · exact PMF.map_id (PMF.pure ())
  · intro s
    rfl
  · intro s
    rfl
  · intro s
    rfl

/-- Without outer measure preservation, all pointwise matching premises can
hold while the complete laws differ.  Here `tau` swaps the two outer samples
but `rho` is the point mass at `0`; the released visible coordinate exposes
the failed reindexing. -/
theorem measurePreservation_is_loadBearing :
    let rho : PMF (Fin 2) := PMF.pure 0
    let tau : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    let preC : Fin 2 → ZMod 2 := fun _ => 0
    let visible₁ : Fin 2 → Fin 2 := fun s => s
    let visible₂ : Fin 2 → Fin 2 := fun s => tau s
    rho.map tau ≠ rho
      ∧ (1 : ZMod 2) ≠ 0
      ∧ (∀ s, visible₁ s = visible₂ (tau s))
      ∧ (∀ s, (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC s)
          = (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC (tau s)))
      ∧ (∀ s, (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC s)
          = (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC (tau s)))
      ∧ rho.bind (fun s => unconditionedCJointKernel
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 (visible₁ s) (preC s))
        ≠ rho.bind (fun s => unconditionedCJointKernel
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 (visible₂ s) (preC s)) := by
  dsimp
  refine ⟨?_, one_ne_zero, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [PMF.pure_map, Equiv.swap_apply_left] at h
    have h0 := congrArg (fun q : PMF (Fin 2) => q 0) h
    simp [PMF.pure_apply] at h0
  · intro s
    fin_cases s <;> rfl
  · intro s
    rfl
  · intro s
    rfl
  · intro h
    have hp := congrArg (fun q : PMF (Fin 2 × ZMod 2 × ZMod 2) =>
      q.map Prod.fst) h
    simp only [PMF.pure_bind, unconditionedCJointKernel, PMF.map_comp,
      Function.comp_def] at hp
    have hone :
        (PMF.uniformOfFintype
          (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))).map
            (fun _ => (1 : Fin 2)) = PMF.pure 1 := by
      simpa [Function.const_def] using
        (PMF.map_const
          (PMF.uniformOfFintype
            (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))
          (1 : Fin 2))
    have hswap :
        (fun _ : LinearMap.ker
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) =>
            (Equiv.swap (0 : Fin 2) 1) 0) = fun _ => (1 : Fin 2) := by
      funext c
      exact Equiv.swap_apply_left 0 1
    rw [hswap, hone] at hp
    have hp0 := congrArg (fun q : PMF (Fin 2) => q 0) hp
    simp [PMF.pure_apply] at hp0

/-- The `ell` residual invariant is load-bearing.  With `ell = id`, the
Component-C mask space is trivial.  Dropping only the `ell` equality lets the
downstream identity evaluator distinguish pre-C words `0` and `1`, even
though measure preservation, visible matching, and `E` matching all hold. -/
theorem ellInvariant_is_loadBearing :
    let rho : PMF Unit := PMF.pure ()
    let preC₁ : Unit → ZMod 2 := fun _ => 0
    let preC₂ : Unit → ZMod 2 := fun _ => 1
    let visible : Unit → Unit := fun _ => ()
    rho.map (Equiv.refl Unit) = rho
      ∧ (1 : ZMod 2) ≠ 0
      ∧ (∀ s, visible s = visible ((Equiv.refl Unit) s))
      ∧ ¬ (∀ s,
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₁ s)
            = (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₂ s))
      ∧ (∀ s, (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₁ s)
          = (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) (preC₂ s))
      ∧ rho.bind (fun s => unconditionedCJointKernel
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          1 (visible s) (preC₁ s))
        ≠ rho.bind (fun s => unconditionedCJointKernel
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          1 (visible s) (preC₂ s)) := by
  dsimp
  refine ⟨PMF.map_id (PMF.pure ()), one_ne_zero, ?_, ?_, ?_, ?_⟩
  · intro s
    rfl
  · intro h
    have h01 := h ()
    have h01' : (0 : ZMod 2) = 1 := by
      simpa only [LinearMap.id_apply] using h01
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) h01'
  · intro s
    rfl
  · intro h
    have hp := congrArg (fun q : PMF (Unit × ZMod 2 × ZMod 2) =>
      q.map (fun z => z.2.2)) h
    simp only [PMF.pure_bind, unconditionedCJointKernel, PMF.map_comp,
      Function.comp_def] at hp
    have hker : ∀ c : LinearMap.ker
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2), (c : ZMod 2) = 0 :=
      fun c => LinearMap.mem_ker.mp c.2
    simp_rw [hker] at hp
    simp only [one_pow, smul_zero, add_zero, LinearMap.id_apply] at hp
    have hzero :
        (PMF.uniformOfFintype
          (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))).map
            (fun _ => (0 : ZMod 2)) = PMF.pure 0 := by
      simpa [Function.const_def] using
        (PMF.map_const
          (PMF.uniformOfFintype
            (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))
          (0 : ZMod 2))
    have hone :
        (PMF.uniformOfFintype
          (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))).map
            (fun _ => (1 : ZMod 2)) = PMF.pure 1 := by
      simpa [Function.const_def] using
        (PMF.map_const
          (PMF.uniformOfFintype
            (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))
          (1 : ZMod 2))
    rw [hzero, hone] at hp
    have hp0 := congrArg (fun q : PMF (ZMod 2) => q 0) hp
    rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
      if_neg (by decide)] at hp0
    exact one_ne_zero hp0

#print axioms unconditionedCJointKernel
#print axioms unconditionedCJointKernel_eq_of_match
#print axioms sampleAware_unconditioned_componentC_joint_law
#print axioms UnmetDeployment.RustPreCCorrespondence
#print axioms UnmetDeployment.RustUniformKernelSamplerCorrespondence
#print axioms UnmetDeployment.RustSerializationCorrespondence
#print axioms UnmetDeployment.FiatShamirCorrespondence
#print axioms sampleAware_unconditioned_hypotheses_instantiable
#print axioms measurePreservation_is_loadBearing
#print axioms ellInvariant_is_loadBearing

end AspisV5ComponentCUnconditionedComposition
