import AspisFormal.V5ComponentCResidualReduction

/-!
# v5 A/B-to-C residual bridge

This file supplies the generic, sample-aware composition lemma missing between
the Component-A/Component-B view-matching arguments and Component C's
conditioned hiding theorem.

An A/B simulator reindexes its joint sample by an equivalence `tau : S ≃ S`.
The reindexing must preserve the actual A/B sample law `rho`.  For every sample
`s`, the pre-C word in the first run is compared with the pre-C word in the
second run at `tau s`.  The bridge hypothesis requires those two words to agree
under both the copy-inactive functional `ell` and the 76-coordinate
conditioning map `E`.  This puts their difference in
`ker ell ⊓ ker E`, so the existing Component-C theorem supplies a conditioned
mask-fibre law equality pointwise.  Binding those pointwise laws over `rho`
then gives the fixed-`e` conditional skew-product joint law, including an
arbitrary A/B-visible view that is itself invariant under `tau`.

This is still not a deployed v5 hiding theorem.  In particular, nothing here
identifies the abstract pre-C words with the Rust gamma-combination, constructs
the A/B reindexing, or proves that the deployed 72 layer-zero openings and four
per-lane claims (whose fourth claim uses `v5_structured_terminal_covector`)
agree after that reindexing.  `UnmetDeployment.RustPreCBridge` names the exact
Rust-side pre-C equation and pins it to one common schedule and gamma; it is a
definition only and is not proved here.  The intended C sampler is uniform on
`ker ell`, not drawn directly from one fixed `E`-fibre.  This file does not
uncondition the fixed-`e` theorem: the exact missing mixture identity is named
by `UnmetDeployment.UniformKerFibreDisintegration` and remains unproved here.
-/

open scoped ENNReal BigOperators

namespace AspisV5ABToCResidualBridge

open AspisV5ComponentCResidualReduction

variable {K M U Y S V : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-- The sample-aware A/B-to-C residual invariant.

The second run is evaluated at the measure-preserving reindexing `tau s`, not
at the original sample `s`.  Both equalities use the same `ell` and `E`; a
caller cannot silently change the C schedule between the two sides. -/
def ABToCResidualInvariant (tau : S ≃ S) (preC₁ preC₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) : Prop :=
  ∀ s, ell (preC₁ s) = ell (preC₂ (tau s))
    ∧ E (preC₁ s) = E (preC₂ (tau s))

/-- A sample-aware residual invariant puts every reindexed word difference in
the exact conditioned mask space. -/
theorem reindexed_sub_mem_ker_inf_ker (tau : S ≃ S) (preC₁ preC₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (hinvariant : ABToCResidualInvariant tau preC₁ preC₂ ell E) (s : S) :
    preC₂ (tau s) - preC₁ s ∈ LinearMap.ker ell ⊓ LinearMap.ker E :=
  sub_mem_ker_inf_ker ell E (hinvariant s).1 (hinvariant s).2

/-- The Component-C mask fibre after the 76 conditioned coordinates have been
fixed to `e`. -/
abbrev ConditionedMaskFibre (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (e : U) :=
  {c : LinearMap.ker ell // E.domRestrict (LinearMap.ker ell) c = e}

/-- For one A/B sample, draw Component C uniformly from its conditioned fibre
and release the A/B-visible value, the fixed conditioned coordinate `e`, and
the post-combination `F`-view.  The definition evaluates `E` on the sampled
mask rather than hard-coding `e`; membership in the fibre proves that the
released coordinate is exactly `e`. -/
noncomputable def conditionedCJointKernel [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (gamma : K) (e : U) [Nonempty (ConditionedMaskFibre ell E e)]
    (visible : V) (x : M) : PMF (V × U × Y) :=
  (PMF.uniformOfFintype (ConditionedMaskFibre ell E e)).map
      fun c : ConditionedMaskFibre ell E e =>
    (visible, E ((c : LinearMap.ker ell) : M),
      F (x + gamma ^ 18 • ((c : LinearMap.ker ell) : M)))

/-- Pointwise bridge: matching `ell`, `E`, and the A/B-visible value makes the
whole conditioned Component-C kernel equal after the A/B reindexing.

This is the pointwise leaf form for a caller that already owns a concrete
sample `s`.  All three hypotheses are used: the residual invariant supplies
the two C-side equalities, `hvisible` preserves the jointly released A/B view,
and `hgamma` makes the `gamma^18` mask action invertible. -/
theorem conditionedCJointKernel_eq_of_reindexed_match
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (tau : S ≃ S) (preC₁ preC₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) (e : U)
    [Nonempty (ConditionedMaskFibre ell E e)]
    (visible₁ visible₂ : S → V)
    (hinvariant : ABToCResidualInvariant tau preC₁ preC₂ ell E)
    (hvisible : ∀ s, visible₁ s = visible₂ (tau s)) (s : S) :
    conditionedCJointKernel ell E F gamma e (visible₁ s) (preC₁ s)
      = conditionedCJointKernel ell E F gamma e
          (visible₂ (tau s)) (preC₂ (tau s)) := by
  have hC := full_fold_decoupling_of_matched_normalized_residuals
    ell E F hgamma (hinvariant s).1 (hinvariant s).2 e
  have hconditioned : ∀ c : ConditionedMaskFibre ell E e,
      E ((c : LinearMap.ker ell) : M) = e := by
    intro c
    simpa only [LinearMap.domRestrict_apply] using c.2
  unfold conditionedCJointKernel
  simp_rw [hconditioned]
  rw [hvisible s]
  have hlift := congrArg
    (fun q : PMF Y => q.map (fun y => (visible₂ (tau s), e, y))) hC
  simpa only [PMF.map_comp, Function.comp_def] using hlift

/-- **Sample-aware skew-product bridge.**

If `tau` preserves the actual A/B sampler `rho`, the pointwise residual
invariant and visible-view equality integrate to an equality of the complete
joint laws.  The left law draws `s ← rho` and then a conditioned C mask for
the first pre-C word; the right law independently spells the same experiment
for the second pre-C word.  The proof first applies the pointwise C theorem,
then reindexes the outer `rho` bind by `tau`.

The equality `rho.map tau = rho` is deliberately explicit: bijectivity of
`tau` alone does not preserve a nonuniform sampler.

This theorem is conditional on one fixed released value `e`.  It is not the
unconditioned law of the intended sampler, which samples uniformly from all of
`ker ell`; applying it there also requires the fibre-disintegration interface
named below. -/
theorem sampleAware_conditioned_joint_law
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (rho : PMF S) (tau : S ≃ S) (hmeasure : rho.map tau = rho)
    (preC₁ preC₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) (e : U)
    [Nonempty (ConditionedMaskFibre ell E e)]
    (visible₁ visible₂ : S → V)
    (hinvariant : ABToCResidualInvariant tau preC₁ preC₂ ell E)
    (hvisible : ∀ s, visible₁ s = visible₂ (tau s)) :
    rho.bind (fun s =>
        conditionedCJointKernel ell E F gamma e (visible₁ s) (preC₁ s))
      = rho.bind (fun s =>
          conditionedCJointKernel ell E F gamma e (visible₂ s) (preC₂ s)) := by
  let Q₁ : S → PMF (V × U × Y) := fun s =>
    conditionedCJointKernel ell E F gamma e (visible₁ s) (preC₁ s)
  let Q₂ : S → PMF (V × U × Y) := fun s =>
    conditionedCJointKernel ell E F gamma e (visible₂ s) (preC₂ s)
  have hkernel : ∀ s, Q₁ s = Q₂ (tau s) := by
    intro s
    exact conditionedCJointKernel_eq_of_reindexed_match tau preC₁ preC₂
      ell E F hgamma e visible₁ visible₂ hinvariant hvisible s
  change rho.bind Q₁ = rho.bind Q₂
  calc
    rho.bind Q₁ = rho.bind (Q₂ ∘ (tau : S → S)) := by
      apply congrArg (fun q : S → PMF (V × U × Y) => rho.bind q)
      funext s
      exact hkernel s
    _ = (rho.map tau).bind Q₂ := (PMF.bind_map rho tau Q₂).symm
    _ = rho.bind Q₂ := by rw [hmeasure]

/-! ## The exact pre-Component-C lane composition -/

/-- The nineteen-lane word immediately before Component C is added.  The
sixteen semantic lanes occupy powers `gamma^0` through `gamma^15`, Hcopy
occupies `gamma^16`, and Component B occupies `gamma^17`. -/
def preCWord (gamma : K) (semantic : Fin 16 → M) (hcopy componentB : M) : M :=
  (∑ j : Fin 16, gamma ^ (j : ℕ) • semantic j)
    + gamma ^ 16 • hcopy + gamma ^ 17 • componentB

/-- Every linear released functional commutes with the exact pre-C lane
composition. -/
theorem map_preCWord (L : M →ₗ[K] U) (gamma : K)
    (semantic : Fin 16 → M) (hcopy componentB : M) :
    L (preCWord gamma semantic hcopy componentB) =
      (∑ j : Fin 16, gamma ^ (j : ℕ) • L (semantic j))
        + gamma ^ 16 • L hcopy + gamma ^ 17 • L componentB := by
  simp [preCWord]

/-- If all nineteen pre-C lane contributions agree under one linear map at
one common `gamma`, their combined pre-C words agree under that map.  This is
the algebraic reason the Component-C `E` invariant is not a second,
independent rank target after the same 76 lane views have already been
matched. -/
theorem map_preCWord_eq_of_lane_matches (L : M →ₗ[K] U) (gamma : K)
    (semantic₁ semantic₂ : Fin 16 → M)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ : M)
    (hsemantic : ∀ j, L (semantic₁ j) = L (semantic₂ j))
    (hhcopy : L hcopy₁ = L hcopy₂)
    (hcomponentB : L componentB₁ = L componentB₂) :
    L (preCWord gamma semantic₁ hcopy₁ componentB₁) =
      L (preCWord gamma semantic₂ hcopy₂ componentB₂) := by
  rw [map_preCWord, map_preCWord]
  simp_rw [hsemantic, hhcopy, hcomponentB]

/-- Sample-aware composition of the two invariants consumed by Component C.
It is enough to match every semantic lane, Hcopy and Component B under the
same deployed `ell` and `E` maps after the A/B sample reindexing. -/
theorem residualInvariant_of_lane_matches
    (rhoReindex : S ≃ S) (gamma : K)
    (semantic₁ semantic₂ : S → Fin 16 → M)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (hellSemantic : ∀ s j,
      ell (semantic₁ s j) = ell (semantic₂ (rhoReindex s) j))
    (hellHcopy : ∀ s, ell (hcopy₁ s) = ell (hcopy₂ (rhoReindex s)))
    (hellB : ∀ s,
      ell (componentB₁ s) = ell (componentB₂ (rhoReindex s)))
    (hESemantic : ∀ s j, E (semantic₁ s j) = E (semantic₂ (rhoReindex s) j))
    (hEHcopy : ∀ s, E (hcopy₁ s) = E (hcopy₂ (rhoReindex s)))
    (hEB : ∀ s, E (componentB₁ s) = E (componentB₂ (rhoReindex s))) :
    ABToCResidualInvariant rhoReindex
      (fun s => preCWord gamma (semantic₁ s) (hcopy₁ s) (componentB₁ s))
      (fun s => preCWord gamma (semantic₂ s) (hcopy₂ s) (componentB₂ s))
      ell E := by
  intro s
  exact ⟨
    map_preCWord_eq_of_lane_matches ell gamma
      (semantic₁ s) (semantic₂ (rhoReindex s))
      (hcopy₁ s) (hcopy₂ (rhoReindex s))
      (componentB₁ s) (componentB₂ (rhoReindex s))
      (hellSemantic s) (hellHcopy s) (hellB s),
    map_preCWord_eq_of_lane_matches E gamma
      (semantic₁ s) (semantic₂ (rhoReindex s))
      (hcopy₁ s) (hcopy₂ (rhoReindex s))
      (componentB₁ s) (componentB₂ (rhoReindex s))
      (hESemantic s) (hEHcopy s) (hEB s)⟩

/-- Deployment-shaped composition.  Component B need not make each semantic
lane's inactive value agree separately.  It is enough that the one released,
gamma-combined inactive claim agrees after reindexing; matching the actual
76-coordinate `E` view of every pre-C lane then supplies the second
invariant.  This is the form an affine B pivot pad can instantiate. -/
theorem residualInvariant_of_combined_inactive_and_E_lane_matches
    (rhoReindex : S ≃ S) (gamma : K)
    (semantic₁ semantic₂ : S → Fin 16 → M)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ : S → M)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (hcombinedInactive : ∀ s,
      ell (preCWord gamma (semantic₁ s) (hcopy₁ s) (componentB₁ s)) =
        ell (preCWord gamma (semantic₂ (rhoReindex s))
          (hcopy₂ (rhoReindex s)) (componentB₂ (rhoReindex s))))
    (hESemantic : ∀ s j, E (semantic₁ s j) = E (semantic₂ (rhoReindex s) j))
    (hEHcopy : ∀ s, E (hcopy₁ s) = E (hcopy₂ (rhoReindex s)))
    (hEB : ∀ s, E (componentB₁ s) = E (componentB₂ (rhoReindex s))) :
    ABToCResidualInvariant rhoReindex
      (fun s => preCWord gamma (semantic₁ s) (hcopy₁ s) (componentB₁ s))
      (fun s => preCWord gamma (semantic₂ s) (hcopy₂ s) (componentB₂ s))
      ell E := by
  intro s
  exact ⟨hcombinedInactive s,
    map_preCWord_eq_of_lane_matches E gamma
      (semantic₁ s) (semantic₂ (rhoReindex s))
      (hcopy₁ s) (hcopy₂ (rhoReindex s))
      (componentB₁ s) (componentB₂ (rhoReindex s))
      (hESemantic s) (hEHcopy s) (hEB s)⟩

/-! ## Honest deployment interface -/

namespace UnmetDeployment

/-- **UNRESOLVED Rust↔Lean pre-C bridge (not proved).**

For every A/B sample, both the Rust run and its Lean model must use the same
pinned transcript schedule and the same nonzero lane-combination challenge
`gamma`.  The modeled pre-C word must be the real Rust pre-C word, and that
word must be exactly

`sum_(j<16) gamma^j * semantic_j + gamma^16 * Hcopy + gamma^17 * B`.

Component C is intentionally absent: its lane is added later with coefficient
`gamma^18`.  The pinned schedule is also the schedule of the 72 authenticated
layer-zero positions and the four per-lane claims; the fourth claim is the
current structured functional `v5_structured_terminal_covector`, not the
rejected older dense covector.  No theorem in this file establishes any of
these equalities for Rust bytes. -/
def RustPreCBridge {Schedule Run Sample : Type*}
    (pinnedSchedule : Schedule) (pinnedGamma : K)
    (runOfSample : Sample → Run)
    (scheduleOf : Run → Schedule) (gammaOf : Run → K)
    (leanScheduleOf : Sample → Schedule) (leanGammaOf : Sample → K)
    (rustPreC : Run → M) (leanPreC : Sample → M)
    (semantic : Run → Fin 16 → M) (hcopy componentB : Run → M) : Prop :=
  pinnedGamma ≠ 0
    ∧ ∀ s,
      scheduleOf (runOfSample s) = pinnedSchedule
        ∧ leanScheduleOf s = pinnedSchedule
        ∧ gammaOf (runOfSample s) = pinnedGamma
        ∧ leanGammaOf s = pinnedGamma
        ∧ leanPreC s = rustPreC (runOfSample s)
        ∧ rustPreC (runOfSample s)
          = (∑ j : Fin 16, pinnedGamma ^ (j : ℕ) • semantic (runOfSample s) j)
            + pinnedGamma ^ 16 • hcopy (runOfSample s)
            + pinnedGamma ^ 17 • componentB (runOfSample s)

/-- **UNRESOLVED unconditioning interface (not proved).**

A candidate Rust sampler must draw uniformly from `ker ell`.  To lift the
fixed-`e` theorem above, its law must be disintegrated as: first draw the
released coordinate `e` from the pushforward under `E`, then draw from the
conditional law on that fibre.  The second conjunct pins each supported
conditional law to the literal `PMF.filter` conditional of the uniform kernel
law.  `uniform_conditioned_eq_uniform_fibre` in the imported Component-C file
then identifies that conditional with the uniform subtype law consumed by
`sampleAware_conditioned_joint_law`.

This is a definition only.  Neither this file nor `RustPreCBridge` proves that
the deployed sampler, serializer, and fixed-schedule experiment realise this
mixture, and no unconditioned deployed hiding conclusion is exported. -/
def UniformKerFibreDisintegration [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (conditionedLaw : U → PMF (LinearMap.ker ell)) : Prop :=
  let uniformKer := PMF.uniformOfFintype (LinearMap.ker ell)
  let coordinateLaw := uniformKer.map (E.domRestrict (LinearMap.ker ell))
  uniformKer = coordinateLaw.bind conditionedLaw
    ∧ ∀ e, e ∈ coordinateLaw.support →
      ∃ h : ∃ c ∈ {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e}, c ∈ uniformKer.support,
        conditionedLaw e = uniformKer.filter
          {c : LinearMap.ker ell | E.domRestrict (LinearMap.ker ell) c = e} h

end UnmetDeployment

/-! ## Non-vacuity and a negative test -/

/-- The sample-aware invariant is satisfiable on a nonempty finite field and
sample space.  This checks that its two conjuncts and the reindexing shape are
not contradictory. -/
theorem residualInvariant_nonvacuous :
    ABToCResidualInvariant (Equiv.refl Unit)
      (fun _ : Unit => (0 : ZMod 2)) (fun _ : Unit => (0 : ZMod 2))
      (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
      (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) := by
  intro s
  exact ⟨rfl, rfl⟩

/-- All load-bearing kinds of premise of the skew-product theorem are
simultaneously satisfiable: a measure-preserving reindexing, the residual
invariant, visible-view invariance, a nonzero gamma, and an inhabited
conditioned fibre. -/
theorem sampleAware_bridge_hypotheses_instantiable :
    ∃ (rho : PMF Unit) (tau : Unit ≃ Unit)
        (preC₁ preC₂ : Unit → ZMod 2) (visible₁ visible₂ : Unit → Unit),
      rho.map tau = rho
        ∧ ABToCResidualInvariant tau preC₁ preC₂
            (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
            (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        ∧ (∀ s, visible₁ s = visible₂ (tau s))
        ∧ (1 : ZMod 2) ≠ 0
        ∧ Nonempty (ConditionedMaskFibre
            (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
            (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 0) := by
  refine ⟨PMF.pure (), Equiv.refl Unit, (fun _ => 0), (fun _ => 0),
    (fun _ => ()), (fun _ => ()), ?_, residualInvariant_nonvacuous, ?_,
    one_ne_zero, ?_⟩
  · exact PMF.map_id (PMF.pure ())
  · intro s
    rfl
  · exact ⟨⟨0, by change (0 : ZMod 2) = 0; rfl⟩⟩

/-- The residual invariant is a real restriction, not a proposition that holds
for arbitrary pre-C words: even under the identity sample reindexing, words
`0` and `1` fail the `ell = id` conjunct. -/
theorem residualInvariant_not_automatic :
    ¬ ABToCResidualInvariant (Equiv.refl Unit)
      (fun _ : Unit => (0 : ZMod 2)) (fun _ : Unit => (1 : ZMod 2))
      (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
      (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) := by
  intro h
  have h01 : (0 : ZMod 2) = 1 := by simpa using (h ()).1
  exact zero_ne_one h01

/-- Bijectivity alone does not preserve an arbitrary A/B sampler.  Swapping
the two points of `Fin 2` moves the point mass at `0` to the point mass at `1`,
so the explicit `rho.map tau = rho` premise cannot be dropped. -/
theorem measurePreservation_not_automatic :
    (PMF.pure (0 : Fin 2)).map (Equiv.swap 0 1) ≠ PMF.pure 0 := by
  intro h
  rw [PMF.pure_map, Equiv.swap_apply_left] at h
  have h1 := congrArg (fun p : PMF (Fin 2) => p 1) h
  simp [PMF.pure_apply] at h1

#print axioms ABToCResidualInvariant
#print axioms reindexed_sub_mem_ker_inf_ker
#print axioms ConditionedMaskFibre
#print axioms conditionedCJointKernel
#print axioms conditionedCJointKernel_eq_of_reindexed_match
#print axioms sampleAware_conditioned_joint_law
#print axioms preCWord
#print axioms map_preCWord
#print axioms map_preCWord_eq_of_lane_matches
#print axioms residualInvariant_of_lane_matches
#print axioms residualInvariant_of_combined_inactive_and_E_lane_matches
#print axioms UnmetDeployment.RustPreCBridge
#print axioms UnmetDeployment.UniformKerFibreDisintegration
#print axioms residualInvariant_nonvacuous
#print axioms sampleAware_bridge_hypotheses_instantiable
#print axioms residualInvariant_not_automatic
#print axioms measurePreservation_not_automatic

end AspisV5ABToCResidualBridge
