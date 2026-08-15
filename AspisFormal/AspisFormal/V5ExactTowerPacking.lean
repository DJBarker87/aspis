import AspisFormal.V5ComponentCQM31TowerExact
import AspisFormal.V5TowerPackedResidualExtraction

/-!
# The exact four-coordinate basis used by the V5 tower packer

The release Rust function `qm31_pack_base4` places four M31 values in the
literal QM31 fields `(c0.a, c0.b, c1.a, c1.b)`.  This file gives those same
four coordinates a concrete linear-basis interpretation.  It therefore
connects the exact tower representation to the generic injective-packing
theorems in `V5TowerPackedResidualExtraction` without a caller-chosen basis.

The Rust-to-Lean extraction proving that the release function returns these
coordinates lives in `aeneas-verif/v5-tower-pack-20260815`.
-/

namespace AspisV5ExactTowerPacking

open Module
open AspisV5ComponentCQM31TowerExact
open AspisV5TowerPackedResidualExtraction

/-- The four literal QM31 coordinates in Rust field order. -/
def exactTowerCoordinates (value : QM31Exact) : Fin 4 → M31Exact :=
  ![value.re.re, value.re.im, value.im.re, value.im.im]

/-- Assemble four M31 coordinates as `(c0.a,c0.b,c1.a,c1.b)`. -/
def exactTowerSynthesis (values : Fin 4 → M31Exact) : QM31Exact :=
  ⟨⟨values 0, values 1⟩, ⟨values 2, values 3⟩⟩

@[simp]
theorem exactTowerSynthesis_coordinates (value : QM31Exact) :
    exactTowerSynthesis (exactTowerCoordinates value) = value := by
  ext <;> rfl

@[simp]
theorem exactTowerCoordinates_synthesis (values : Fin 4 → M31Exact) :
    exactTowerCoordinates (exactTowerSynthesis values) = values := by
  funext lane
  fin_cases lane <;> rfl

/-- Coordinate projection is an M31-linear equivalence. -/
noncomputable def exactTowerCoordinateEquiv :
    QM31Exact ≃ₗ[M31Exact] (Fin 4 → M31Exact) where
  toFun := exactTowerCoordinates
  invFun := exactTowerSynthesis
  left_inv := exactTowerSynthesis_coordinates
  right_inv := exactTowerCoordinates_synthesis
  map_add' left right := by
    funext lane
    fin_cases lane <;> rfl
  map_smul' scalar value := by
    funext lane
    fin_cases lane <;> rfl

/-- The deployed `(1,i,u,i*u)` M31 basis of QM31. -/
noncomputable def deployedTowerBasis : Basis (Fin 4) M31Exact QM31Exact :=
  Basis.ofEquivFun exactTowerCoordinateEquiv

/-- Generic basis packing at the deployed basis is literal Rust field-order
assembly. -/
@[simp]
theorem towerPack_deployedTowerBasis (values : Fin 4 → M31Exact) :
    towerPack deployedTowerBasis values = exactTowerSynthesis values := by
  rfl

/-- The pure function described by the extracted Rust theorem is exactly the
generic basis-packing function. -/
theorem exactTowerSynthesis_eq_towerPack :
    exactTowerSynthesis = towerPack deployedTowerBasis := by
  funext values
  exact (towerPack_deployedTowerBasis values).symm

/-- Consequently the deployed basis pack is injective on all four M31
coordinates. -/
theorem deployedTowerPack_injective :
    Function.Injective (towerPack deployedTowerBasis) :=
  towerPack_injective deployedTowerBasis

/-- Once a source proof supplies the exact row-selector equation, the generic
packing-and-selector boundary is discharged with no further packing premise. -/
theorem packingAndSelectorMatches_of_selector
    {Row Point : Type*} [DecidableEq Row]
    (rustSelector : Point → Row → M31Exact)
    (pointOfRow : Row → Point)
    (selectorExact : SelectsExactRow rustSelector pointOfRow) :
    RustTowerPackingAndSelectorMatches deployedTowerBasis exactTowerSynthesis
      rustSelector pointOfRow := by
  exact ⟨exactTowerSynthesis_eq_towerPack, selectorExact⟩

#print axioms exactTowerSynthesis_coordinates
#print axioms exactTowerCoordinates_synthesis
#print axioms towerPack_deployedTowerBasis
#print axioms exactTowerSynthesis_eq_towerPack
#print axioms deployedTowerPack_injective
#print axioms packingAndSelectorMatches_of_selector

end AspisV5ExactTowerPacking
