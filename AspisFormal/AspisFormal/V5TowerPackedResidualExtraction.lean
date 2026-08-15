import AspisFormal.V5ConstraintLaneBatching

/-!
# Extracting base-field residuals from V5 tower packing

At Boolean trace rows, each raw constraint residual is an M31 value.  The
production evaluator groups four such values into one QM31 value using the
fixed tower basis `(1, i, u, i*u)`.  This packing is injective on four
base-field values even though no map from four arbitrary QM31 values to one
QM31 value could be injective.

This file proves the basis algebra and the exact selector-isolation step.  A
separate source correspondence must identify Rust's `qm31_pack_base4` and row
selector implementation with the basis and selector functions supplied here.
-/

namespace AspisV5TowerPackedResidualExtraction

open Module
open AspisV5ConstraintLaneBatching
open AspisV5FriConcreteEncoderApplicability

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Pack four base-field values into an extension field through a chosen
basis.  The deployed instance is the QM31 tower basis `(1, i, u, i*u)`. -/
noncomputable def towerPack
    (basis : Basis (Fin 4) F K) (values : Fin 4 → F) : K :=
  basis.equivFun.symm values

@[simp]
theorem towerPack_zero (basis : Basis (Fin 4) F K) :
    towerPack basis (0 : Fin 4 → F) = 0 := by
  simp [towerPack]

/-- Basis packing is injective on four base-field coordinates. -/
theorem towerPack_injective (basis : Basis (Fin 4) F K) :
    Function.Injective (towerPack basis) := by
  exact basis.equivFun.symm.injective

theorem towerPack_eq_zero_iff
    (basis : Basis (Fin 4) F K) (values : Fin 4 → F) :
    towerPack basis values = 0 ↔ ∀ lane, values lane = 0 := by
  constructor
  · intro packedZero lane
    have valuesZero : values = 0 :=
      towerPack_injective basis (packedZero.trans (towerPack_zero basis).symm)
    exact congrFun valuesZero lane
  · intro allZero
    have : values = 0 := funext allZero
    simp [this]

/-! ## Boolean-row selector isolation -/

/-- Packed residual polynomial evaluated through an arbitrary row-selector
family. -/
noncomputable def selectedPackedResidual
    {Row Point Group : Type*} [Fintype Row]
    (basis : Basis (Fin 4) F K)
    (selector : Point → Row → F)
    (residual : Row → Group → Fin 4 → F)
    (point : Point) (group : Group) : K :=
  ∑ row, selector point row • towerPack basis (residual row group)

/-- A selector family is exact on the designated Boolean point for every
row. -/
def SelectsExactRow
    {Row Point : Type*} [DecidableEq Row]
    (selector : Point → Row → F) (pointOfRow : Row → Point) : Prop :=
  ∀ row selected,
    selector (pointOfRow row) selected = if selected = row then 1 else 0

theorem selectedPackedResidual_at_exact_row
    {Row Point Group : Type*} [Fintype Row] [DecidableEq Row]
    (basis : Basis (Fin 4) F K)
    (selector : Point → Row → F) (pointOfRow : Row → Point)
    (exact : SelectsExactRow selector pointOfRow)
    (residual : Row → Group → Fin 4 → F)
    (row : Row) (group : Group) :
    selectedPackedResidual basis selector residual (pointOfRow row) group =
      towerPack basis (residual row group) := by
  classical
  simp [selectedPackedResidual, exact row]

/-- If every exactly selected packed row is zero, every underlying base-field
residual is zero. -/
theorem all_residuals_zero_of_selected_packed_zero
    {Row Point Group : Type*} [Fintype Row] [DecidableEq Row]
    (basis : Basis (Fin 4) F K)
    (selector : Point → Row → F) (pointOfRow : Row → Point)
    (exact : SelectsExactRow selector pointOfRow)
    (residual : Row → Group → Fin 4 → F)
    (selectedZero : ∀ row group,
      selectedPackedResidual basis selector residual (pointOfRow row) group = 0) :
    ∀ row group lane, residual row group lane = 0 := by
  intro row group lane
  have packedZero : towerPack basis (residual row group) = 0 := by
    rw [← selectedPackedResidual_at_exact_row basis selector pointOfRow exact]
    exact selectedZero row group
  exact (towerPack_eq_zero_iff basis (residual row group)).mp packedZero lane

/-! ## Composition with the exact twenty-five-lane theta batch -/

/-- Base-field residual groups which become the four Poseidon and twenty
semantic QM31 lanes at one Boolean row.  The copy lane is already an extension
field value because its own `lambda`/`chi` batching is a separate event. -/
structure ConstraintRowResiduals where
  poseidon : Fin 4 → Fin 4 → F
  semantic : Fin 20 → Fin 4 → F
  copy : K

noncomputable def ConstraintRowResiduals.laneVector
    (basis : Basis (Fin 4) F K)
    (row : ConstraintRowResiduals (F := F) (K := K)) :
    ConstraintLane → K :=
  constraintLaneVector
    (fun group => towerPack basis (row.poseidon group))
    (fun group => towerPack basis (row.semantic group))
    row.copy

/-- Once the exact theta-batching polynomial is identically zero, tower-basis
injectivity gives every raw Poseidon and semantic residual, plus the copy
lane, individually. -/
theorem all_row_residuals_zero_of_theta_polynomial_zero
    (basis : Basis (Fin 4) F K)
    (row : ConstraintRowResiduals (F := F) (K := K))
    (polynomialZero : monomialPolynomial (row.laneVector basis) = 0) :
    (∀ group lane, row.poseidon group lane = 0) ∧
      (∀ group lane, row.semantic group lane = 0) ∧
      row.copy = 0 := by
  have lanesZero := all_source_lanes_zero_of_polynomial_eq_zero
    (fun group => towerPack basis (row.poseidon group))
    (fun group => towerPack basis (row.semantic group))
    row.copy polynomialZero
  constructor
  · intro group lane
    exact (towerPack_eq_zero_iff basis (row.poseidon group)).mp
      (lanesZero.1 group) lane
  constructor
  · intro group lane
    exact (towerPack_eq_zero_iff basis (row.semantic group)).mp
      (lanesZero.2.1 group) lane
  · exact lanesZero.2.2

/-- Exact code/model boundary for the deployed packing and Boolean selector
implementations.  It is deliberately extensional and contains no security
claim. -/
structure RustTowerPackingAndSelectorMatches
    {Row Point : Type*} [DecidableEq Row]
    (basis : Basis (Fin 4) F K)
    (rustPack : (Fin 4 → F) → K)
    (rustSelector : Point → Row → F)
    (pointOfRow : Row → Point) : Prop where
  pack : rustPack = towerPack basis
  selector : SelectsExactRow rustSelector pointOfRow

#print axioms towerPack_injective
#print axioms towerPack_eq_zero_iff
#print axioms selectedPackedResidual_at_exact_row
#print axioms all_residuals_zero_of_selected_packed_zero
#print axioms all_row_residuals_zero_of_theta_polynomial_zero

end AspisV5TowerPackedResidualExtraction
