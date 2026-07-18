import AspisFormal.V5ComponentBTriangularHiding
import AspisFormal.V5ComponentCUnconditionedComposition

/-!
# v5 conditional hiding capstone, version 3

This file composes the current abstract hiding pieces with their real
dependency structure:

* Component A is an affine view hidden by a uniform linear mask;
* Hcopy is a second affine view hidden by an independent uniform linear mask;
* Component B uses the triangular law from
  `V5ComponentBTriangularHiding`: its masked 271-coordinate state is matched
  first, its structured terminal is a deterministic function of that matched
  state, and its pads cover only the independent 76-coordinate residual view;
* Component C is sampled uniformly from the whole relation kernel and is
  composed through
  `sampleAware_unconditioned_componentC_joint_law`.

The outer sample is the uniform law on the product

`MA × MH × SB × PB`.

An explicit product translation matches the A view, Hcopy view, and the full
triangular B view pointwise.  In particular, no translation direction and no
rank premise is allocated to the B terminal.

The bridge into Component C is deliberately explicit.  The caller supplies
one deterministic projection of the matched outer visible tuple for the
published gamma-combined inactive claim, and one for `E(preC)`, together with
run-by-run correspondence equalities.  Pointwise outer-view equality then
implies equality under both `ell` and `E`; these are exactly the residual
premises consumed by the unconditioned Component-C theorem.

This is an abstract, conditional capstone.  It does not prove that the Rust
maps, rank certificates, samplers, transcript, compiler, or serialized bytes
instantiate the model.  Those edges are named as unproved propositions in
`UnmetDeployment`.  Therefore this file must not be cited as a deployed
zero-knowledge proof.
-/

open scoped ENNReal

namespace AspisV5ConditionalHidingCapstoneV3

open AspisV5ComponentBTriangularHiding
  AspisV5ComponentCUnconditionedComposition
  AspisV5RankOneOpeningHiding

/-! ## Outer product sample and visible tuple -/

/-- Independent outer coins: Component A, Hcopy, Component-B state, and
Component-B pads-plus-pivot. -/
abbrev OuterSample (MA MH SB PB : Type*) := MA × MH × SB × PB

/-- Everything visible before Component C is sampled.  The last three
coordinates are the one triangular Component-B view: masked state,
deterministic terminal, and independent residual view. -/
abbrev OuterVisible (VA VH SB TB VB : Type*) := VA × VH × SB × TB × VB

variable {K MA MH SB PB VA VH VB TB MC U Y : Type*}
variable [Field K]
variable [AddCommGroup MA] [Module K MA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VA] [Module K VA]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup MC] [Module K MC]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup Y] [Module K Y]

/-- The complete outer visible tuple for one run.  Its Component-B suffix is
literally `triangularView`, so the terminal cannot be silently split off as an
independent target. -/
def outerVisible
    (LA : MA →ₗ[K] VA) (wA : VA)
    (LH : MH →ₗ[K] VH) (wH : VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wBS : SB) (wBV : VB) :
    OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB :=
  fun sample =>
    (wA + LA sample.1,
      wH + LH sample.2.1,
      triangularView terminalB RB AB wBS wBV
        (sample.2.2.1, sample.2.2.2))

/-! ## Explicit outer translation -/

/-- Translate all four independent outer coin components. -/
def outerTranslationEquiv (dA : MA) (dH : MH) (dS : SB) (dP : PB) :
    OuterSample MA MH SB PB ≃ OuterSample MA MH SB PB where
  toFun sample :=
    (sample.1 + dA, sample.2.1 + dH,
      sample.2.2.1 + dS, sample.2.2.2 + dP)
  invFun sample :=
    (sample.1 - dA, sample.2.1 - dH,
      sample.2.2.1 - dS, sample.2.2.2 - dP)
  left_inv sample := by
    rcases sample with ⟨a, h, s, p⟩
    simp
  right_inv sample := by
    rcases sample with ⟨a, h, s, p⟩
    simp

@[simp]
theorem outerTranslationEquiv_apply
    (dA : MA) (dH : MH) (dS : SB) (dP : PB)
    (sample : OuterSample MA MH SB PB) :
    outerTranslationEquiv dA dH dS dP sample =
      (sample.1 + dA, sample.2.1 + dH,
        sample.2.2.1 + dS, sample.2.2.2 + dP) :=
  rfl

/-- Surjectivity of the three genuinely independent released maps constructs
all shifts.  There is no terminal-map premise. -/
theorem exists_outer_shifts
    (LA : MA →ₗ[K] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB) :
    ∃ dA dH dP,
      LA dA = wA₂ - wA₁
        ∧ LH dH = wH₂ - wH₁
        ∧ AB dP = wBV₂ - wBV₁ - RB (wBS₂ - wBS₁) := by
  obtain ⟨dA, hdA⟩ := hLA (wA₂ - wA₁)
  obtain ⟨dH, hdH⟩ := hLH (wH₂ - wH₁)
  obtain ⟨dP, hdP⟩ := hAB (wBV₂ - wBV₁ - RB (wBS₂ - wBS₁))
  exact ⟨dA, dH, dP, hdA, hdH, hdP⟩

/-- Pointwise equality of the complete outer visible tuple after the product
translation.  The Component-B suffix is discharged by
`triangularView_translate`, including its terminal as a deterministic image
of the matched masked state. -/
theorem outerVisible_translate
    (LA : MA →ₗ[K] VA) (LH : MH →ₗ[K] VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (dA : MA) (hdA : LA dA = wA₂ - wA₁)
    (dH : MH) (hdH : LH dH = wH₂ - wH₁)
    (dP : PB)
    (hdP : AB dP = wBV₂ - wBV₁ - RB (wBS₂ - wBS₁))
    (sample : OuterSample MA MH SB PB) :
    outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
        (outerTranslationEquiv dA dH (wBS₂ - wBS₁) dP sample)
      = outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample := by
  apply Prod.ext
  · simp only [outerVisible, outerTranslationEquiv_apply, map_add, hdA]
    abel_nf
  · apply Prod.ext
    · simp only [outerVisible, outerTranslationEquiv_apply, map_add, hdH]
      abel_nf
    · exact triangularView_translate terminalB RB AB wBS₁ wBS₂ wBV₁ wBV₂
        dP hdP (sample.2.2.1, sample.2.2.2)

/-- Function-level form of the pointwise visible coupling. -/
theorem outerVisible_comp_translation
    (LA : MA →ₗ[K] VA) (LH : MH →ₗ[K] VH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (dA : MA) (hdA : LA dA = wA₂ - wA₁)
    (dH : MH) (hdH : LH dH = wH₂ - wH₁)
    (dP : PB)
    (hdP : AB dP = wBV₂ - wBV₁ - RB (wBS₂ - wBS₁)) :
    outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ ∘
        outerTranslationEquiv dA dH (wBS₂ - wBS₁) dP
      = outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ := by
  funext sample
  exact outerVisible_translate LA LH terminalB RB AB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    dA hdA dH hdH dP hdP sample

section FiniteOuter

variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- Every explicit product translation preserves the uniform outer law. -/
theorem outer_uniform_preserved
    (dA : MA) (dH : MH) (dS : SB) (dP : PB) :
    (PMF.uniformOfFintype (OuterSample MA MH SB PB)).map
        (outerTranslationEquiv dA dH dS dP)
      = PMF.uniformOfFintype (OuterSample MA MH SB PB) :=
  uniform_map_equiv (outerTranslationEquiv dA dH dS dP)

end FiniteOuter

/-! ## The explicit residual-projection bridge -/

/-- For one run, both Component-C residual coordinates are deterministic
projections of the already released outer visible tuple.  The first function
is the published gamma-combined inactive claim; the second is the released
`E(preC)` coordinate. -/
def ResidualsAreVisibleProjections
    (visible : OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB)
    (preC : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (publishedE : OuterVisible VA VH SB TB VB → U) : Prop :=
  ∀ sample,
    ell (preC sample) = publishedInactive (visible sample)
      ∧ E (preC sample) = publishedE (visible sample)

omit [AddCommGroup MA] [Module K MA]
  [AddCommGroup MH] [Module K MH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup PB] [Module K PB]
  [AddCommGroup VA] [Module K VA]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup VB] [Module K VB] in
/-- Matching the complete outer visible tuple transports both residual
coordinates through their shared deterministic projections. -/
theorem residual_invariants_of_visible_projections
    (tau : OuterSample MA MH SB PB ≃ OuterSample MA MH SB PB)
    (visible₁ visible₂ :
      OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB)
    (preC₁ preC₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (publishedE : OuterVisible VA VH SB TB VB → U)
    (hvisible : ∀ sample, visible₁ sample = visible₂ (tau sample))
    (hprojection₁ : ResidualsAreVisibleProjections visible₁ preC₁ ell E
      publishedInactive publishedE)
    (hprojection₂ : ResidualsAreVisibleProjections visible₂ preC₂ ell E
      publishedInactive publishedE) :
    ∀ sample,
      ell (preC₁ sample) = ell (preC₂ (tau sample))
        ∧ E (preC₁ sample) = E (preC₂ (tau sample)) := by
  intro sample
  exact ⟨
    (hprojection₁ sample).1 |>.trans
      ((congrArg publishedInactive (hvisible sample)).trans
        (hprojection₂ (tau sample)).1.symm),
    (hprojection₁ sample).2 |>.trans
      ((congrArg publishedE (hvisible sample)).trans
        (hprojection₂ (tau sample)).2.symm)⟩

/-! ## Conditional complete joint-law capstone -/

section Capstone

variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- **Conditional complete-view hiding, v3.**

The three surjectivity premises construct one outer product translation.  The
two projection correspondences turn pointwise equality of the full outer view
into the `ell` and `E` invariants required by the unconditioned Component-C
theorem.  The conclusion is equality of the complete joint law: outer visible
tuple, Component-C `E` coordinate, and downstream `F` view.

No deployment claim is made by this implication. -/
theorem conditional_complete_joint_hiding_v3
    (LA : MA →ₗ[K] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (preC₁ preC₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (publishedE : OuterVisible VA VH SB TB VB → U)
    (hprojection₁ : ResidualsAreVisibleProjections
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      preC₁ ell E publishedInactive publishedE)
    (hprojection₂ : ResidualsAreVisibleProjections
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      preC₂ ell E publishedInactive publishedE) :
    (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preC₁ sample))
      = (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preC₂ sample)) := by
  obtain ⟨dA, dH, dP, hdA, hdH, hdP⟩ :=
    exists_outer_shifts LA hLA LH hLH RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
  let shift := outerTranslationEquiv dA dH (wBS₂ - wBS₁) dP
  let tau := shift.symm
  let visible₁ := outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁
  let visible₂ := outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂
  have hmeasure :
      (PMF.uniformOfFintype (OuterSample MA MH SB PB)).map tau
        = PMF.uniformOfFintype (OuterSample MA MH SB PB) :=
    uniform_map_equiv tau
  have hvisible : ∀ sample, visible₁ sample = visible₂ (tau sample) := by
    intro sample
    have hpoint := outerVisible_translate LA LH terminalB RB AB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      dA hdA dH hdH dP hdP (tau sample)
    change visible₁ sample = visible₂ (tau sample)
    simpa only [tau, shift, Equiv.apply_symm_apply] using hpoint
  have hresidual := residual_invariants_of_visible_projections
    tau visible₁ visible₂ preC₁ preC₂ ell E publishedInactive publishedE
    hvisible hprojection₁ hprojection₂
  exact sampleAware_unconditioned_componentC_joint_law
    (PMF.uniformOfFintype (OuterSample MA MH SB PB)) tau hmeasure
    preC₁ preC₂ visible₁ visible₂ ell E F hgamma hvisible
    (fun sample => (hresidual sample).1)
    (fun sample => (hresidual sample).2)

end Capstone

/-! ## Non-vacuity and a projection-premise failure -/

namespace Model

abbrev F₂ := ZMod 2
abbrev Sample := OuterSample F₂ F₂ F₂ F₂
abbrev Visible := OuterVisible F₂ F₂ F₂ F₂ F₂

def terminal : F₂ → F₂ := id

def view (w : F₂) : Sample → Visible :=
  outerVisible (LinearMap.id : F₂ →ₗ[F₂] F₂) w
    (LinearMap.id : F₂ →ₗ[F₂] F₂) w terminal
    (LinearMap.id : F₂ →ₗ[F₂] F₂)
    (LinearMap.id : F₂ →ₗ[F₂] F₂) w w

def preC (w : F₂) : Sample → F₂ := fun sample => (view w sample).1

def projection : Visible → F₂ := fun visible => visible.1

theorem projection_correspondence (w : F₂) :
    ResidualsAreVisibleProjections (view w) (preC w)
      (LinearMap.id : F₂ →ₗ[F₂] F₂)
      (LinearMap.id : F₂ →ₗ[F₂] F₂) projection projection := by
  intro sample
  exact ⟨rfl, rfl⟩

/-- Every capstone premise is simultaneously satisfiable while all four outer
witness contributions change. -/
theorem capstone_v3_nonvacuous :
    (PMF.uniformOfFintype Sample).bind
        (fun sample => unconditionedCJointKernel
          (LinearMap.id : F₂ →ₗ[F₂] F₂)
          (LinearMap.id : F₂ →ₗ[F₂] F₂)
          (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
          (view 0 sample) (preC 0 sample))
      = (PMF.uniformOfFintype Sample).bind
        (fun sample => unconditionedCJointKernel
          (LinearMap.id : F₂ →ₗ[F₂] F₂)
          (LinearMap.id : F₂ →ₗ[F₂] F₂)
          (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
          (view 1 sample) (preC 1 sample)) :=
  conditional_complete_joint_hiding_v3
    (LinearMap.id : F₂ →ₗ[F₂] F₂) (fun x => ⟨x, rfl⟩)
    (LinearMap.id : F₂ →ₗ[F₂] F₂) (fun x => ⟨x, rfl⟩)
    terminal (LinearMap.id : F₂ →ₗ[F₂] F₂)
    (LinearMap.id : F₂ →ₗ[F₂] F₂) (fun x => ⟨x, rfl⟩)
    0 1 0 1 0 1 0 1
    (preC 0) (preC 1)
    (LinearMap.id : F₂ →ₗ[F₂] F₂)
    (LinearMap.id : F₂ →ₗ[F₂] F₂)
    (LinearMap.id : F₂ →ₗ[F₂] F₂)
    1 one_ne_zero projection projection
    (projection_correspondence 0) (projection_correspondence 1)

/-- A constant outer visible tuple for the premise-deletion test. -/
def constantVisible : Sample → Visible := fun _ => (0, 0, 0, 0, 0)

/-- A witness-dependent pre-C word hidden from `constantVisible`. -/
def constantPreC (w : F₂) : Sample → F₂ := fun _ => w

/-- With `ell = id`, the C kernel is trivial, so the downstream projection of
the negative experiment is the point mass at its pre-C word. -/
theorem negative_downstream_law (w : F₂) :
    ((PMF.uniformOfFintype Sample).bind
      (fun sample => unconditionedCJointKernel
        (LinearMap.id : F₂ →ₗ[F₂] F₂)
        (0 : F₂ →ₗ[F₂] F₂)
        (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
        (constantVisible sample) (constantPreC w sample))).map
          (fun output : Visible × F₂ × F₂ => output.2.2)
      = PMF.pure w := by
  rw [PMF.map_bind]
  have hinner : ∀ sample : Sample,
      (unconditionedCJointKernel
        (LinearMap.id : F₂ →ₗ[F₂] F₂)
        (0 : F₂ →ₗ[F₂] F₂)
        (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
        (constantVisible sample) (constantPreC w sample)).map
          (fun output : Visible × F₂ × F₂ => output.2.2)
        = PMF.pure w := by
    intro sample
    unfold unconditionedCJointKernel
    rw [PMF.map_comp]
    have hker : ∀ c : LinearMap.ker
        (LinearMap.id : F₂ →ₗ[F₂] F₂), (c : F₂) = 0 :=
      fun c => LinearMap.mem_ker.mp c.2
    have hfun :
        ((fun output : Visible × F₂ × F₂ => output.2.2) ∘
          fun c : LinearMap.ker (LinearMap.id : F₂ →ₗ[F₂] F₂) =>
            (constantVisible sample,
              (0 : F₂ →ₗ[F₂] F₂) (c : F₂),
              (LinearMap.id : F₂ →ₗ[F₂] F₂)
                (constantPreC w sample +
                  (1 : F₂) ^ 18 • (c : F₂))))
          = fun _ => w := by
      funext c
      simp [constantPreC, hker c]
    rw [hfun]
    change (PMF.uniformOfFintype
      (LinearMap.ker (LinearMap.id : F₂ →ₗ[F₂] F₂))).map
        (Function.const _ w) = PMF.pure w
    exact PMF.map_const _ _
  simp_rw [hinner]
  exact PMF.bind_const _ _

/-- The published-inactive projection premise is load-bearing.  The two runs
have identical outer visible tuples and identical `E = 0` residuals, but no
single deterministic published-inactive projection can represent pre-C words
`0` and `1`; correspondingly, their complete C joint laws differ. -/
theorem visible_projection_premise_is_loadBearing :
    (¬ ∃ publishedInactive : Visible → F₂,
      ResidualsAreVisibleProjections constantVisible (constantPreC 0)
          (LinearMap.id : F₂ →ₗ[F₂] F₂) (0 : F₂ →ₗ[F₂] F₂)
          publishedInactive (fun _ => 0)
        ∧ ResidualsAreVisibleProjections constantVisible (constantPreC 1)
          (LinearMap.id : F₂ →ₗ[F₂] F₂) (0 : F₂ →ₗ[F₂] F₂)
          publishedInactive (fun _ => 0))
      ∧ (PMF.uniformOfFintype Sample).bind
          (fun sample => unconditionedCJointKernel
            (LinearMap.id : F₂ →ₗ[F₂] F₂)
            (0 : F₂ →ₗ[F₂] F₂)
            (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
            (constantVisible sample) (constantPreC 0 sample))
        ≠ (PMF.uniformOfFintype Sample).bind
          (fun sample => unconditionedCJointKernel
            (LinearMap.id : F₂ →ₗ[F₂] F₂)
            (0 : F₂ →ₗ[F₂] F₂)
            (LinearMap.id : F₂ →ₗ[F₂] F₂) 1
            (constantVisible sample) (constantPreC 1 sample)) := by
  constructor
  · rintro ⟨publishedInactive, hzero, hone⟩
    have hz := (hzero (0 : Sample)).1
    have ho := (hone (0 : Sample)).1
    change (0 : F₂) = publishedInactive (constantVisible 0) at hz
    change (1 : F₂) = publishedInactive (constantVisible 0) at ho
    have h01 : (0 : F₂) = 1 := by
      exact hz.trans ho.symm
    exact zero_ne_one h01
  · intro hlaw
    have hprojected := congrArg
      (fun q : PMF (Visible × F₂ × F₂) =>
        q.map (fun output => output.2.2)) hlaw
    rw [negative_downstream_law 0, negative_downstream_law 1] at hprojected
    have hvalue := congrArg (fun q : PMF F₂ => q 0) hprojected
    rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
      if_neg (by decide)] at hvalue
    exact one_ne_zero hvalue

end Model

/-! ## Explicit unmet deployment interfaces -/

namespace UnmetDeployment

/-- The frozen Rust matrices are exactly the abstract A, Hcopy, and B-pad
maps, and their audited rank certificates imply the three surjectivity
premises consumed by the capstone. -/
def FrozenRankAndLinearMapCorrespondence
    (LA leanA rustA : MA →ₗ[K] VA)
    (LH leanH rustH : MH →ₗ[K] VH)
    (AB leanB rustB : PB →ₗ[K] VB) : Prop :=
  LA = leanA ∧ leanA = rustA ∧ Function.Surjective LA
    ∧ LH = leanH ∧ leanH = rustH ∧ Function.Surjective LH
    ∧ AB = leanB ∧ leanB = rustB ∧ Function.Surjective AB

/-- The deployed Component-B state coordinates, residual map, pad map, and
structured terminal evaluator equal the one triangular model used here. -/
def RustTriangularBViewCorrespondence
    (modelView rustView :
      OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB) : Prop :=
  modelView = rustView

/-- The decoded deployed outer sampler is the independent uniform product
law used by the theorem. -/
def RustOuterSamplerIsIndependentUniform
    [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]
    (rustSampler : PMF (OuterSample MA MH SB PB)) : Prop :=
  rustSampler = PMF.uniformOfFintype (OuterSample MA MH SB PB)

/-- The published combined inactive claim and the candidate `E(preC)` value
are exactly the two common deterministic projections required by both runs.
This interface is currently uninstantiated because the deployed Component-C
map does not yet exist. -/
def RustPublishedResidualProjectionCorrespondence
    (visible₁ visible₂ :
      OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB)
    (preC₁ preC₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (publishedE : OuterVisible VA VH SB TB VB → U) : Prop :=
  ResidualsAreVisibleProjections visible₁ preC₁ ell E
      publishedInactive publishedE
    ∧ ResidualsAreVisibleProjections visible₂ preC₂ ell E
      publishedInactive publishedE

/-- The Lean pre-C words and the candidate `ell`, `E`, and `F` maps agree
extensionally with the decoded maps evaluated by a Rust prover/verifier on
the pinned schedule.  Byte-level decoding is a separate serialization
interface.  This is an uninstantiated interface, not a claim that production
currently contains Component C. -/
def RustPreCAndCMapsCorrespondence
    (leanPreC rustPreC : OuterSample MA MH SB PB → MC)
    (leanEll rustEll : MC →ₗ[K] K)
    (leanE rustE : MC →ₗ[K] U) (leanF rustF : MC →ₗ[K] Y) : Prop :=
  leanPreC = rustPreC ∧ leanEll = rustEll ∧ leanE = rustE ∧ leanF = rustF

/-- For every outer sample, the candidate Rust Component-C coins decode to
the same uniform kernel law used by `unconditionedCJointKernel`.  The
per-sample quantifier is the conditional-uniformity/independence premise; a
single marginal equality would not suffice.  This interface is currently
uninstantiated. -/
def RustComponentCKernelSamplerIsUniform
    [DecidableEq K] [Fintype MC] {RustCoin : Type*}
    (ell : MC →ₗ[K] K)
    (rustCoins : OuterSample MA MH SB PB → PMF RustCoin)
    (decodeMask : OuterSample MA MH SB PB → RustCoin → LinearMap.ker ell) : Prop :=
  ∀ sample, (rustCoins sample).map (decodeMask sample) =
    PMF.uniformOfFintype (LinearMap.ker ell)

/-- The transcript/compiler fixes the same nonzero gamma, the same outer
translation, and the same commitment-before-challenge absorb ordering in both
runs.  Both the abstract and Rust reindexing functions are equated to `tau`. -/
def FiatShamirCompilerCorrespondence
    {Transcript Prefix Schedule : Type*}
    (CommitBeforeChallenge :
      (Transcript → Transcript) → (Transcript → K) → Prop)
    (abstractAbsorb rustAbsorb : Transcript → Transcript)
    (prefixOf : Transcript → Prefix)
    (scheduleOf : Transcript → Schedule) (gammaOf : Transcript → K)
    (tau : OuterSample MA MH SB PB ≃ OuterSample MA MH SB PB)
    (abstractReindex rustReindex :
      OuterSample MA MH SB PB → OuterSample MA MH SB PB)
    (t₁ t₂ : Transcript) (pinnedSchedule : Schedule) (pinnedGamma : K) : Prop :=
  CommitBeforeChallenge abstractAbsorb gammaOf
    ∧ abstractAbsorb = rustAbsorb
    ∧ abstractReindex = tau ∧ rustReindex = tau
    ∧ prefixOf t₁ = prefixOf t₂
    ∧ scheduleOf t₁ = pinnedSchedule ∧ scheduleOf t₂ = pinnedSchedule
    ∧ gammaOf t₁ = pinnedGamma ∧ gammaOf t₂ = pinnedGamma
    ∧ pinnedGamma ≠ 0

/-- The candidate Rust bytes are exactly serialization of the complete joint
tuple returned by `unconditionedCJointKernel`, with no omitted coordinate and
with the actual `ker ell` sample type.  This interface is currently
uninstantiated. -/
def RustCompleteSerializationCorrespondence
    {Bytes : Type*}
    (ell : MC →ₗ[K] K)
    (abstractOutput : OuterSample MA MH SB PB →
      LinearMap.ker ell → OuterVisible VA VH SB TB VB × U × Y)
    (serialize : (OuterVisible VA VH SB TB VB × U × Y) → Bytes)
    (rustBytes : OuterSample MA MH SB PB →
      LinearMap.ker ell → Bytes) : Prop :=
  ∀ sample c, rustBytes sample c = serialize (abstractOutput sample c)

/-- Computational commitment binding, hash/RO behavior, and the compiler
reduction are external assumptions rather than finite-linear-algebra facts. -/
def ComputationalBindingHashAndCompilerAssumptions
    (CommitmentBinding HashRandomOracle CompilerSound : Prop) : Prop :=
  CommitmentBinding ∧ HashRandomOracle ∧ CompilerSound

end UnmetDeployment

#print axioms outerTranslationEquiv_apply
#print axioms exists_outer_shifts
#print axioms outerVisible_translate
#print axioms outerVisible_comp_translation
#print axioms outer_uniform_preserved
#print axioms ResidualsAreVisibleProjections
#print axioms residual_invariants_of_visible_projections
#print axioms conditional_complete_joint_hiding_v3
#print axioms Model.projection_correspondence
#print axioms Model.capstone_v3_nonvacuous
#print axioms Model.negative_downstream_law
#print axioms Model.visible_projection_premise_is_loadBearing
#print axioms UnmetDeployment.FrozenRankAndLinearMapCorrespondence
#print axioms UnmetDeployment.RustTriangularBViewCorrespondence
#print axioms UnmetDeployment.RustOuterSamplerIsIndependentUniform
#print axioms UnmetDeployment.RustPublishedResidualProjectionCorrespondence
#print axioms UnmetDeployment.RustPreCAndCMapsCorrespondence
#print axioms UnmetDeployment.RustComponentCKernelSamplerIsUniform
#print axioms UnmetDeployment.FiatShamirCompilerCorrespondence
#print axioms UnmetDeployment.RustCompleteSerializationCorrespondence
#print axioms UnmetDeployment.ComputationalBindingHashAndCompilerAssumptions

end AspisV5ConditionalHidingCapstoneV3
