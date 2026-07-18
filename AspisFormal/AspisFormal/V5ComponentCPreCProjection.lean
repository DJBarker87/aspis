import AspisFormal.V5ConditionalHidingCapstoneV3

/-!
# v5 Component C: exact projections of the pre-C gamma combination

The word entering Component C is the gamma combination of exactly eighteen
already-committed lanes:

* semantic lanes `0..15`, with coefficients `gamma^0 .. gamma^15`;
* Hcopy, with coefficient `gamma^16`;
* Component B, with coefficient `gamma^17`.

Component C itself is the nineteenth lane, with coefficient `gamma^18`, and
does not occur in `preCWord` below.

This leaf proves the elementary but deployment-critical fact that applying the
inactive functional `ell` or the conditioned 76-row map `E` to `preCWord` is
exactly linear in the eighteen lanes.  Its deployed bridge follows the real
wire: one already-combined inactive scalar and eighteen released per-lane `E`
rows.  It never asks the decoder for unavailable per-lane inactive values.

The semantic lanes are modelled *after* their canonical M31-to-QM31 lift into
the common word module.  Identifying that lift, the 76 row order, the decoded
bytes, the Rust evaluator, and the sampler with this model remains the named
`DeployedProjectionCorrespondence` code/model edge.  This file proves no such
edge.

There is deliberately no circle/GRS transport, C-DEC or rank certificate,
Fiat--Shamir or random-oracle claim, commitment assumption, or Rust theorem in
this file.  The downstream map `F` in the capstone wrapper remains an arbitrary
linear map.
-/

open scoped BigOperators

namespace AspisV5ComponentCPreCProjection

open AspisV5ConditionalHidingCapstoneV3
open AspisV5ComponentCUnconditionedComposition

/-- The sixteen semantic lanes occupy gamma powers `0..15`. -/
abbrev SemanticLane := Fin 16

/-- The deployed conditioned Component-C view has exactly 76 rows. -/
abbrev ConditionedRow := Fin 76

/-- The exact 76-row conditioned-view codomain. -/
abbrev ConditionedView (K : Type*) := ConditionedRow → K

/-- A kernel tooth pinning the conditioned row count. -/
theorem conditionedRow_card : Fintype.card ConditionedRow = 76 := by decide

/-- Abstract pair of one lane's inactive and conditioned coordinates.  This
stronger tuple is useful algebraically but is not the deployed wire shape. -/
structure LaneReleasedRows (K U : Type*) where
  inactive : K
  conditioned : U

/-- The released row data for all eighteen pre-C lanes, in the deployed lane
partition.  This is a mathematical row tuple, not a byte decoder. -/
structure PreCReleasedRows (K U : Type*) where
  semantic : SemanticLane → LaneReleasedRows K U
  hcopy : LaneReleasedRows K U
  componentB : LaneReleasedRows K U

/-- The deployed wire releases only the conditioned `E` row for each pre-C
lane.  It releases one already-combined inactive scalar, not eighteen
per-lane inactive values. -/
structure PreCConditionedRows (U : Type*) where
  semantic : SemanticLane → U
  hcopy : U
  componentB : U

/-- Deployment-sized specialisation of one lane's released rows. -/
abbrev DeployedLaneReleasedRows (K : Type*) :=
  LaneReleasedRows K (ConditionedView K)

/-- Deployment-sized specialisation of the full pre-C released tuple. -/
abbrev DeployedPreCReleasedRows (K : Type*) :=
  PreCReleasedRows K (ConditionedView K)

/-- Deployment-sized specialization of the eighteen conditioned rows. -/
abbrev DeployedPreCConditionedRows (K : Type*) :=
  PreCConditionedRows (ConditionedView K)

section Algebra

variable {K M U : Type*} [Field K]
variable [AddCommGroup M] [Module K M]
variable [AddCommGroup U] [Module K U]

/-- Apply the two relevant linear maps to one lane word. -/
def laneReleasedRows (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (word : M) : LaneReleasedRows K U :=
  ⟨ell word, E word⟩

/-- Apply `ell` and `E` separately to every lane of the pre-C partition. -/
def preCReleasedRows (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (semantic : SemanticLane → M) (hcopy componentB : M) :
    PreCReleasedRows K U where
  semantic lane := laneReleasedRows ell E (semantic lane)
  hcopy := laneReleasedRows ell E hcopy
  componentB := laneReleasedRows ell E componentB

/-- Apply `E` separately to the eighteen pre-C lanes, without manufacturing
per-lane inactive values that are absent from the deployed wire. -/
def preCConditionedRows (E : M →ₗ[K] U)
    (semantic : SemanticLane → M) (hcopy componentB : M) :
    PreCConditionedRows U where
  semantic lane := E (semantic lane)
  hcopy := E hcopy
  componentB := E componentB

/-- Exact eighteen-lane word before the `gamma^18 * C` term is added. -/
def preCWord (gamma : K) (semantic : SemanticLane → M)
    (hcopy componentB : M) : M :=
  (∑ lane, gamma ^ lane.val • semantic lane)
    + gamma ^ 16 • hcopy
    + gamma ^ 17 • componentB

/-- Deterministic projection of released per-lane rows to the published
gamma-combined inactive coordinate. -/
def projectedInactive (gamma : K) (rows : PreCReleasedRows K U) : K :=
  (∑ lane, gamma ^ lane.val * (rows.semantic lane).inactive)
    + gamma ^ 16 * rows.hcopy.inactive
    + gamma ^ 17 * rows.componentB.inactive

/-- Deterministic projection of released per-lane rows to `E(preCWord)`. -/
def projectedConditioned (gamma : K) (rows : PreCReleasedRows K U) : U :=
  (∑ lane, gamma ^ lane.val • (rows.semantic lane).conditioned)
    + gamma ^ 16 • rows.hcopy.conditioned
    + gamma ^ 17 • rows.componentB.conditioned

/-- Deterministic projection of the eighteen actually released per-lane `E`
rows. -/
def projectedConditionedRows (gamma : K) (rows : PreCConditionedRows U) : U :=
  (∑ lane, gamma ^ lane.val • rows.semantic lane)
    + gamma ^ 16 • rows.hcopy
    + gamma ^ 17 • rows.componentB

/-- The combined inactive claim is exactly the same gamma combination of the
eighteen per-lane inactive values. -/
theorem ell_preCWord (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (gamma : K) (semantic : SemanticLane → M) (hcopy componentB : M) :
    ell (preCWord gamma semantic hcopy componentB)
      = projectedInactive gamma
          (preCReleasedRows ell E semantic hcopy componentB) := by
  simp [preCWord, projectedInactive, preCReleasedRows, laneReleasedRows]

/-- The conditioned view is exactly the same gamma combination of the
eighteen per-lane conditioned views. -/
theorem E_preCWord (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (gamma : K) (semantic : SemanticLane → M) (hcopy componentB : M) :
    E (preCWord gamma semantic hcopy componentB)
      = projectedConditioned gamma
          (preCReleasedRows ell E semantic hcopy componentB) := by
  simp [preCWord, projectedConditioned, preCReleasedRows, laneReleasedRows]

/-- Deployed-shaped conditioned identity: the same theorem using only the
eighteen `E` rows that are present on the wire. -/
theorem E_preCWord_conditioned_rows (E : M →ₗ[K] U)
    (gamma : K) (semantic : SemanticLane → M) (hcopy componentB : M) :
    E (preCWord gamma semantic hcopy componentB)
      = projectedConditionedRows gamma
          (preCConditionedRows E semantic hcopy componentB) := by
  simp [preCWord, projectedConditionedRows, preCConditionedRows]

end Algebra

/-! ## The explicit code/model row seam -/

section RowCorrespondence

variable {K M U S V : Type*} [Field K]
variable [AddCommGroup M] [Module K M]
variable [AddCommGroup U] [Module K U]

/-- Strong abstract correspondence exposing both `ell` and `E` per lane.
The deployed wire does not expose these eighteen inactive values; direct
deployment wrappers below use `DeployedProjectionCorrespondence` instead. -/
def ReleasedRowsCorrespondence
    (visible : S → V) (decodeRows : V → PreCReleasedRows K U)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) : Prop :=
  ∀ sample, decodeRows (visible sample)
    = preCReleasedRows ell E (semantic sample) (hcopy sample) (componentB sample)

/-- Exact deployed correspondence for the one released gamma-combined
inactive scalar. -/
def CombinedInactiveCorrespondence
    (visible : S → V) (publishedInactive : V → K)
    (ell : M →ₗ[K] K) (gamma : K)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) : Prop :=
  ∀ sample,
    ell (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
      = publishedInactive (visible sample)

/-- Exact deployed correspondence for the eighteen released per-lane `E`
rows. -/
def ConditionedRowsCorrespondence
    (visible : S → V) (decodeConditionedRows : V → PreCConditionedRows U)
    (E : M →ₗ[K] U)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) : Prop :=
  ∀ sample, decodeConditionedRows (visible sample)
    = preCConditionedRows E (semantic sample) (hcopy sample) (componentB sample)

/-- The exact deployed projection seam.  Its two conjuncts correspond to the
wire's one combined inactive scalar and its eighteen per-lane conditioned
rows; it contains no per-lane inactive coordinate. -/
def DeployedProjectionCorrespondence
    (visible : S → V) (publishedInactive : V → K)
    (decodeConditionedRows : V → PreCConditionedRows U)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (gamma : K)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) : Prop :=
  CombinedInactiveCorrespondence visible publishedInactive ell gamma
      semantic hcopy componentB
    ∧ ConditionedRowsCorrespondence visible decodeConditionedRows E
      semantic hcopy componentB

/-- The row-correspondence interface is non-vacuous: exposing the mathematical
row tuple itself and decoding by the identity satisfies it definitionally. -/
theorem releasedRowsCorrespondence_self
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) :
    ReleasedRowsCorrespondence
      (fun sample => preCReleasedRows ell E (semantic sample)
        (hcopy sample) (componentB sample))
      id ell E semantic hcopy componentB := by
  intro sample
  rfl

/-- The deployed-shaped seam is non-vacuous: directly expose its one combined
scalar and eighteen conditioned rows. -/
theorem deployedProjectionCorrespondence_self
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (gamma : K)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M) :
    DeployedProjectionCorrespondence
      (fun sample =>
        (ell (preCWord gamma (semantic sample) (hcopy sample) (componentB sample)),
          preCConditionedRows E (semantic sample) (hcopy sample) (componentB sample)))
      Prod.fst Prod.snd ell E gamma semantic hcopy componentB := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- One exact row correspondence discharges both residual equalities used by
the Component-C unconditioned coupling. -/
theorem residual_projection_pair_of_released_rows
    (visible : S → V) (decodeRows : V → PreCReleasedRows K U)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (gamma : K)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M)
    (hrows : ReleasedRowsCorrespondence visible decodeRows ell E
      semantic hcopy componentB) :
    ∀ sample,
      ell (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
          = projectedInactive gamma (decodeRows (visible sample))
        ∧ E (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
          = projectedConditioned gamma (decodeRows (visible sample)) := by
  intro sample
  rw [hrows sample]
  exact ⟨ell_preCWord ell E gamma _ _ _, E_preCWord ell E gamma _ _ _⟩

/-- The exact deployed seam supplies both residual equalities without
requiring or reconstructing eighteen per-lane inactive values. -/
theorem residual_projection_pair_of_deployed_rows
    (visible : S → V) (publishedInactive : V → K)
    (decodeConditionedRows : V → PreCConditionedRows U)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (gamma : K)
    (semantic : S → SemanticLane → M) (hcopy componentB : S → M)
    (hrows : DeployedProjectionCorrespondence visible publishedInactive
      decodeConditionedRows ell E gamma semantic hcopy componentB) :
    ∀ sample,
      ell (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
          = publishedInactive (visible sample)
        ∧ E (preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
          = projectedConditionedRows gamma
              (decodeConditionedRows (visible sample)) := by
  intro sample
  refine ⟨hrows.1 sample, ?_⟩
  rw [hrows.2 sample]
  exact E_preCWord_conditioned_rows E gamma _ _ _

end RowCorrespondence

/-! ## Bridge to the v3 capstone -/

section CapstoneBridge

variable {K MA MH SB PB VA VH VB TB MC U : Type*}
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

omit [AddCommGroup MA] [Module K MA]
  [AddCommGroup MH] [Module K MH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup PB] [Module K PB]
  [AddCommGroup VA] [Module K VA]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup VB] [Module K VB] in
/-- Specialise the exact row identity to the precise projection interface
consumed by `V5ConditionalHidingCapstoneV3`. -/
theorem residualsAreVisibleProjections_of_released_rows
    (visible : OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB)
    (decodeRows : OuterVisible VA VH SB TB VB → PreCReleasedRows K U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (gamma : K)
    (semantic : OuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : OuterSample MA MH SB PB → MC)
    (hrows : ReleasedRowsCorrespondence visible decodeRows ell E
      semantic hcopy componentB) :
    ResidualsAreVisibleProjections visible
      (fun sample => preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
      ell E (projectedInactive gamma ∘ decodeRows)
      (projectedConditioned gamma ∘ decodeRows) := by
  intro sample
  simpa only [Function.comp_apply] using
    residual_projection_pair_of_released_rows visible decodeRows ell E gamma
      semantic hcopy componentB hrows sample

omit [AddCommGroup MA] [Module K MA]
  [AddCommGroup MH] [Module K MH]
  [AddCommGroup SB] [Module K SB]
  [AddCommGroup PB] [Module K PB]
  [AddCommGroup VA] [Module K VA]
  [AddCommGroup VH] [Module K VH]
  [AddCommGroup VB] [Module K VB] in
/-- Deployed-shaped bridge: the published inactive projection is the one
combined scalar already on the wire, while the conditioned projection is
derived from the eighteen released `E` rows. -/
theorem residualsAreVisibleProjections_of_deployed_rows
    (visible : OuterSample MA MH SB PB → OuterVisible VA VH SB TB VB)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      OuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (gamma : K)
    (semantic : OuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy componentB : OuterSample MA MH SB PB → MC)
    (hrows : DeployedProjectionCorrespondence visible publishedInactive
      decodeConditionedRows ell E gamma semantic hcopy componentB) :
    ResidualsAreVisibleProjections visible
      (fun sample => preCWord gamma (semantic sample) (hcopy sample) (componentB sample))
      ell E publishedInactive
      (projectedConditionedRows gamma ∘ decodeConditionedRows) := by
  intro sample
  simpa only [Function.comp_apply] using
    residual_projection_pair_of_deployed_rows visible publishedInactive
      decodeConditionedRows ell E gamma semantic hcopy componentB hrows sample

end CapstoneBridge

/-! ## Complete wrapper: exact lane rows feed the v3 theorem -/

section CompleteWrapper

variable {K MA MH SB PB VA VH VB TB MC Y : Type*}
variable [Field K]
variable [AddCommGroup MA] [Module K MA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VA] [Module K VA]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup MC] [Module K MC]
variable [AddCommGroup Y] [Module K Y]
variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- The v3 capstone with its two abstract residual-projection hypotheses
replaced by exact per-lane row correspondences.  `F` remains arbitrary and no
fold transport or C-DEC premise appears. -/
theorem conditional_complete_joint_hiding_v3_of_preC_rows
    (LA : MA →ₗ[K] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : OuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] ConditionedView K) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (decodeRows : OuterVisible VA VH SB TB VB → DeployedPreCReleasedRows K)
    (hrows₁ : ReleasedRowsCorrespondence
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      decodeRows ell E semantic₁ hcopy₁ componentB₁)
    (hrows₂ : ReleasedRowsCorrespondence
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      decodeRows ell E semantic₂ hcopy₂ componentB₂) :
    (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample) (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample) (hcopy₂ sample) (componentB₂ sample))) := by
  exact conditional_complete_joint_hiding_v3
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    (fun sample => preCWord gamma (semantic₁ sample)
      (hcopy₁ sample) (componentB₁ sample))
    (fun sample => preCWord gamma (semantic₂ sample)
      (hcopy₂ sample) (componentB₂ sample))
    ell E F gamma hgamma
    (projectedInactive gamma ∘ decodeRows)
    (projectedConditioned gamma ∘ decodeRows)
    (residualsAreVisibleProjections_of_released_rows
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      decodeRows ell E gamma semantic₁ hcopy₁ componentB₁ hrows₁)
    (residualsAreVisibleProjections_of_released_rows
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      decodeRows ell E gamma semantic₂ hcopy₂ componentB₂ hrows₂)

end CompleteWrapper

/-! ## Deployed-shaped complete wrapper -/

section DeployedCompleteWrapper

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
variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- The v3 capstone with the deployed wire shape: one combined inactive
scalar and eighteen conditioned rows.  Both residual equalities remain exact. -/
theorem conditional_complete_joint_hiding_v3_of_deployed_preC_rows
    (LA : MA →ₗ[K] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : OuterSample MA MH SB PB → SemanticLane → MC)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      OuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (hrows₁ : DeployedProjectionCorrespondence
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁)
    (hrows₂ : DeployedProjectionCorrespondence
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂) :
    (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample) (hcopy₁ sample) (componentB₁ sample)))
      = (PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample) (hcopy₂ sample) (componentB₂ sample))) := by
  exact conditional_complete_joint_hiding_v3
    LA hLA LH hLH terminalB RB AB hAB
    wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
    (fun sample => preCWord gamma (semantic₁ sample)
      (hcopy₁ sample) (componentB₁ sample))
    (fun sample => preCWord gamma (semantic₂ sample)
      (hcopy₂ sample) (componentB₂ sample))
    ell E F gamma hgamma publishedInactive
    (projectedConditionedRows gamma ∘ decodeConditionedRows)
    (residualsAreVisibleProjections_of_deployed_rows
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁ hrows₁)
    (residualsAreVisibleProjections_of_deployed_rows
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂ hrows₂)

end DeployedCompleteWrapper

/-! ## Load-bearing negative models -/

namespace Negative

abbrev F2 := ZMod 2
abbrev Sample := OuterSample F2 F2 F2 F2
abbrev Visible := OuterVisible F2 F2 F2 F2 F2

def zeroVisible : Sample → Visible := fun _ => (0, 0, 0, 0, 0)
def onePreC : Sample → F2 := fun _ => 1
def zeroProjection : Visible → F2 := fun _ => 0

/-- If the published inactive projection is not tied to the pre-C word, the
first residual-projection premise can fail. -/
theorem inactive_projection_is_loadBearing :
    ¬ ResidualsAreVisibleProjections zeroVisible onePreC
      (LinearMap.id : F2 →ₗ[F2] F2) (0 : F2 →ₗ[F2] F2)
      zeroProjection zeroProjection := by
  intro h
  have bad := (h (0, 0, 0, 0)).1
  simp [onePreC, zeroProjection] at bad

/-- Independently, if the published conditioned projection is not tied to
the pre-C word, the second residual-projection premise can fail. -/
theorem conditioned_projection_is_loadBearing :
    ¬ ResidualsAreVisibleProjections zeroVisible onePreC
      (0 : F2 →ₗ[F2] F2) (LinearMap.id : F2 →ₗ[F2] F2)
      zeroProjection zeroProjection := by
  intro h
  have bad := (h (0, 0, 0, 0)).2
  simp [onePreC, zeroProjection] at bad

def oneSemantic : Sample → SemanticLane → F2 :=
  fun _ lane => if lane = 0 then 1 else 0

def zeroLane : Sample → F2 := fun _ => 0

def goodConditionedRows : Visible → PreCConditionedRows F2 := fun _ =>
  preCConditionedRows (LinearMap.id : F2 →ₗ[F2] F2)
    (oneSemantic (0, 0, 0, 0)) 0 0

def badConditionedRows : Visible → PreCConditionedRows F2 := fun _ =>
  preCConditionedRows (LinearMap.id : F2 →ₗ[F2] F2)
    (fun _ => 0) 0 0

/-- The single combined inactive scalar is independently load-bearing in the
deployed-shaped seam. -/
theorem deployed_combined_inactive_is_loadBearing :
    ¬ DeployedProjectionCorrespondence zeroVisible zeroProjection
      goodConditionedRows (LinearMap.id : F2 →ₗ[F2] F2)
      (LinearMap.id : F2 →ₗ[F2] F2) 1 oneSemantic zeroLane zeroLane := by
  intro h
  have bad := h.1 (0, 0, 0, 0)
  norm_num [CombinedInactiveCorrespondence, zeroVisible, zeroProjection,
    preCWord, oneSemantic, zeroLane] at bad

/-- The eighteen conditioned rows are independently load-bearing in the
deployed-shaped seam. -/
theorem deployed_conditioned_rows_are_loadBearing :
    ¬ DeployedProjectionCorrespondence zeroVisible (fun _ => 1)
      badConditionedRows (LinearMap.id : F2 →ₗ[F2] F2)
      (LinearMap.id : F2 →ₗ[F2] F2) 1 oneSemantic zeroLane zeroLane := by
  intro h
  have bad := h.2 (0, 0, 0, 0)
  have hsemantic := congrArg (fun rows => rows.semantic 0) bad
  norm_num [ConditionedRowsCorrespondence, badConditionedRows,
    preCConditionedRows, oneSemantic, zeroVisible] at hsemantic

end Negative

#print axioms ell_preCWord
#print axioms E_preCWord
#print axioms E_preCWord_conditioned_rows
#print axioms conditionedRow_card
#print axioms CombinedInactiveCorrespondence
#print axioms ConditionedRowsCorrespondence
#print axioms DeployedProjectionCorrespondence
#print axioms residual_projection_pair_of_released_rows
#print axioms residual_projection_pair_of_deployed_rows
#print axioms releasedRowsCorrespondence_self
#print axioms deployedProjectionCorrespondence_self
#print axioms residualsAreVisibleProjections_of_released_rows
#print axioms residualsAreVisibleProjections_of_deployed_rows
#print axioms conditional_complete_joint_hiding_v3_of_preC_rows
#print axioms conditional_complete_joint_hiding_v3_of_deployed_preC_rows
#print axioms Negative.inactive_projection_is_loadBearing
#print axioms Negative.conditioned_projection_is_loadBearing
#print axioms Negative.deployed_combined_inactive_is_loadBearing
#print axioms Negative.deployed_conditioned_rows_are_loadBearing

end AspisV5ComponentCPreCProjection
