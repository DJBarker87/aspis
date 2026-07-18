import AspisFormal.V5ComponentCPreCProjection
import AspisFormal.V5MixedFieldComposition

/-!
# v5 Component C: exact pre-C projections at the deployed field boundary

`V5ComponentCPreCProjection` proves the eighteen-lane gamma-combination
identities over the Component-C field.  `V5MixedFieldComposition` proves the
complete hiding theorem with Component-A coins and views over a separate base
field.  This leaf joins those two results without putting a QM31-module
structure on the M31 Component-A spaces.

The deployment-facing seam follows the actual wire: one released
gamma-combined inactive scalar, plus eighteen released per-lane `E` rows.  In
the deployed instantiation it owns the M31-to-QM31 lift of the Component-A
rows, the Rust row order, the byte codec, and the evaluator correspondence.
It never asks a decoder to manufacture eighteen per-lane inactive values.

There is no extension-field surjectivity claim.  `LA` remains `FA`-linear;
only Hcopy, B, C, gamma, `ell`, `E`, and `F` are over `K`.
-/

namespace AspisV5ComponentCPreCProjectionMixed

open AspisV5ComponentCPreCProjection
open AspisV5MixedFieldComposition
open AspisV5ComponentCUnconditionedComposition

/-! ## Exact mixed-visible row seam -/

variable {FA K MA MH SB PB VA VH VB TB MC U : Type*}
variable [Field K]
variable [AddCommGroup MC] [Module K MC]
variable [AddCommGroup U] [Module K U]

/-- Strong abstract mixed correspondence exposing both `ell` and `E` per
lane.  It is retained as an algebraic lemma, but the deployed wrapper below
uses `MixedDeployedProjectionCorrespondence` because the wire exposes only
one combined inactive scalar. -/
def MixedReleasedRowsCorrespondence
    (visible : MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (decodeRows : MixedOuterVisible VA VH SB TB VB → PreCReleasedRows K U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U)
    (semantic : MixedOuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : MixedOuterSample MA MH SB PB → MC) : Prop :=
  ReleasedRowsCorrespondence visible decodeRows ell E semantic hcopy componentB

/-- One exact mixed row correspondence supplies both residual projections
consumed by the mixed-field capstone. -/
theorem mixedResidualsAreVisibleProjections_of_released_rows
    (visible : MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (decodeRows : MixedOuterVisible VA VH SB TB VB → PreCReleasedRows K U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (gamma : K)
    (semantic : MixedOuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : MixedOuterSample MA MH SB PB → MC)
    (hrows : MixedReleasedRowsCorrespondence visible decodeRows ell E
      semantic hcopy componentB) :
    MixedResidualsAreVisibleProjections visible
      (fun sample => preCWord gamma (semantic sample)
        (hcopy sample) (componentB sample))
      ell E (projectedInactive gamma ∘ decodeRows)
      (projectedConditioned gamma ∘ decodeRows) := by
  intro sample
  exact residual_projection_pair_of_released_rows visible decodeRows ell E gamma
    semantic hcopy componentB hrows sample

/-- The deployed-shaped mixed seam: one already-combined inactive scalar and
eighteen per-lane conditioned rows.  No `K`-module structure is imposed on
the Component-A head. -/
def MixedDeployedProjectionCorrespondence
    (visible : MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      MixedOuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (gamma : K)
    (semantic : MixedOuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : MixedOuterSample MA MH SB PB → MC) : Prop :=
  DeployedProjectionCorrespondence visible publishedInactive
    decodeConditionedRows ell E gamma semantic hcopy componentB

/-- The deployed-shaped mixed correspondence supplies the same two exact
residual equalities consumed by the mixed-field capstone. -/
theorem mixedResidualsAreVisibleProjections_of_deployed_rows
    (visible : MixedOuterSample MA MH SB PB → MixedOuterVisible VA VH SB TB VB)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      MixedOuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (gamma : K)
    (semantic : MixedOuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : MixedOuterSample MA MH SB PB → MC)
    (hrows : MixedDeployedProjectionCorrespondence visible publishedInactive
      decodeConditionedRows ell E gamma semantic hcopy componentB) :
    MixedResidualsAreVisibleProjections visible
      (fun sample => preCWord gamma (semantic sample)
        (hcopy sample) (componentB sample))
      ell E publishedInactive
      (projectedConditionedRows gamma ∘ decodeConditionedRows) := by
  intro sample
  exact residual_projection_pair_of_deployed_rows visible publishedInactive
    decodeConditionedRows ell E gamma semantic hcopy componentB hrows sample

/-! ## Complete mixed-field wrapper -/

section CompleteWrapper

variable {Y : Type*}
variable [Field FA]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup Y] [Module K Y]
variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- The mixed-field hiding capstone with its abstract residual projections
replaced by the actual deployed wire shape: one combined inactive scalar and
eighteen per-lane conditioned rows.

In particular `LA : MA →ₗ[FA] VA`: this theorem neither creates a `K`-module
on `MA`/`VA` nor strengthens M31-rational surjectivity to QM31 surjectivity.
The downstream Component-C map `F` remains an arbitrary `K`-linear map. -/
theorem conditional_complete_joint_hiding_mixed_fields_of_preC_rows
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
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
        (fun sample => unconditionedCJointKernel ell E F gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample))) := by
  exact conditional_complete_joint_hiding_mixed_fields
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    (fun sample => preCWord gamma (semantic₁ sample)
      (hcopy₁ sample) (componentB₁ sample))
    (fun sample => preCWord gamma (semantic₂ sample)
      (hcopy₂ sample) (componentB₂ sample))
    ell E F gamma hgamma
    publishedInactive
    (projectedConditionedRows gamma ∘ decodeConditionedRows)
    (mixedResidualsAreVisibleProjections_of_deployed_rows
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁ hrows₁)
    (mixedResidualsAreVisibleProjections_of_deployed_rows
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂ hrows₂)

end CompleteWrapper

/-! ## A genuinely two-field non-vacuity and a row-seam tooth -/

namespace Model

abbrev FA₂ := ZMod 2
abbrev K₃ := ZMod 3
abbrev Sample := MixedOuterSample FA₂ K₃ K₃ K₃
abbrev Visible := MixedOuterVisible FA₂ K₃ K₃ K₃ K₃

def semantic : Sample → SemanticLane → K₃ := fun _ _ => 0
def hcopy : Sample → K₃ := fun _ => 0
def componentB : Sample → K₃ := fun sample => sample.2.1

def visible : Sample → Visible := fun sample =>
  (sample.1, sample.2.1, sample.2.2.1, sample.2.2.1, sample.2.2.2)

def decodeRows : Visible → PreCReleasedRows K₃ K₃ := fun output =>
  preCReleasedRows (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃) (fun _ => 0) 0 output.2.1

/-- The exact row seam is satisfiable while Component A and Component C use
different fields (`ZMod 2` and `ZMod 3`). -/
theorem mixed_row_correspondence_nonvacuous :
    MixedReleasedRowsCorrespondence visible decodeRows
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) semantic hcopy componentB := by
  intro sample
  rfl

def badDecodeRows : Visible → PreCReleasedRows K₃ K₃ := fun _ =>
  preCReleasedRows (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (LinearMap.id : K₃ →ₗ[K₃] K₃) (fun _ => 0) 0 0

/-- A decoder that erases the B-lane row cannot satisfy the correspondence.
Thus the code/model seam is load-bearing rather than decorative. -/
theorem mixed_row_correspondence_is_loadBearing :
    ¬ MixedReleasedRowsCorrespondence visible badDecodeRows
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) semantic hcopy componentB := by
  intro h
  have hbad := h (0, 1, 0, 0)
  have hcomponent := congrArg (fun rows => rows.componentB.inactive) hbad
  norm_num [badDecodeRows, visible, componentB, preCReleasedRows,
    laneReleasedRows] at hcomponent

def publishedInactive : Visible → K₃ := fun output => output.2.1

def decodeConditionedRows : Visible → PreCConditionedRows K₃ := fun output =>
  preCConditionedRows (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (fun _ => 0) 0 output.2.1

/-- The deployed-shaped seam is satisfiable over genuinely different A/C
fields and exposes exactly one combined inactive scalar plus conditioned
rows. -/
theorem mixed_deployed_projection_nonvacuous :
    MixedDeployedProjectionCorrespondence visible publishedInactive
      decodeConditionedRows
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) 1
      semantic hcopy componentB := by
  constructor
  · intro sample
    simp [preCWord, publishedInactive, visible, semantic, hcopy, componentB]
  · intro sample
    rfl

def badPublishedInactive : Visible → K₃ := fun _ => 0

/-- Replacing the one combined inactive scalar by an unrelated value breaks
the deployed correspondence even when all conditioned rows are exact. -/
theorem mixed_deployed_combined_inactive_is_loadBearing :
    ¬ MixedDeployedProjectionCorrespondence visible badPublishedInactive
      decodeConditionedRows
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) 1
      semantic hcopy componentB := by
  intro h
  have bad := h.1 (0, 1, 0, 0)
  norm_num [CombinedInactiveCorrespondence, preCWord, badPublishedInactive,
    visible, semantic, hcopy, componentB] at bad

def badDecodeConditionedRows : Visible → PreCConditionedRows K₃ := fun _ =>
  preCConditionedRows (LinearMap.id : K₃ →ₗ[K₃] K₃)
    (fun _ => 0) 0 0

/-- Erasing the B-lane conditioned row independently breaks the deployed
correspondence while the combined inactive scalar remains exact. -/
theorem mixed_deployed_conditioned_rows_are_loadBearing :
    ¬ MixedDeployedProjectionCorrespondence visible publishedInactive
      badDecodeConditionedRows
      (LinearMap.id : K₃ →ₗ[K₃] K₃)
      (LinearMap.id : K₃ →ₗ[K₃] K₃) 1
      semantic hcopy componentB := by
  intro h
  have bad := h.2 (0, 1, 0, 0)
  have hcomponent := congrArg (fun rows => rows.componentB) bad
  norm_num [ConditionedRowsCorrespondence, badDecodeConditionedRows,
    visible, componentB, preCConditionedRows] at hcomponent

end Model

#print axioms mixedResidualsAreVisibleProjections_of_released_rows
#print axioms MixedDeployedProjectionCorrespondence
#print axioms mixedResidualsAreVisibleProjections_of_deployed_rows
#print axioms conditional_complete_joint_hiding_mixed_fields_of_preC_rows
#print axioms Model.mixed_row_correspondence_nonvacuous
#print axioms Model.mixed_row_correspondence_is_loadBearing
#print axioms Model.mixed_deployed_projection_nonvacuous
#print axioms Model.mixed_deployed_combined_inactive_is_loadBearing
#print axioms Model.mixed_deployed_conditioned_rows_are_loadBearing

end AspisV5ComponentCPreCProjectionMixed
