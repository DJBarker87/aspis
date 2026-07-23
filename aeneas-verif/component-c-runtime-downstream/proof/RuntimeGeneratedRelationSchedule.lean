import RuntimeRelationRoundOodSemantics
import RuntimeRelationRoundPolynomialSemantics
import AspisFormal.V5ComponentCDownstreamDeployed
import RuntimeMaintainedRoundSelectors

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeGeneratedRelationSchedule

open aspis_prover
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimeCoefficientFoldCorrespondence
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeMaterializedRelationArithmetic
open ComponentCRuntimeRelationRoundOodSemantics
open ComponentCRuntimeRelationRoundPolynomialSemantics
open AspisV5ComponentCDownstreamDeployed

abbrev RawQM31 := aspis_core.field.QM31
abbrev BaseField := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ComponentCRuntimeCoefficientFoldCorrespondence.instInhabitedRawQM31

def oodPairValue (w : OodPairWitness) : Fin 2 → RawQM31 :=
  ![w.value0, w.value1]

def oodPairTable (w : OodPairWitness) : Fin 2 → alloc.vec.Vec RawQM31 :=
  ![w.table0, w.table1]

/-- The twelve materialized weight tables returned by the four authentic
relation rounds. -/
structure FourRoundGeneratedTables where
  ood0 : OodPairWitness
  ood1 : OodPairWitness
  ood2 : OodPairWitness
  ood3 : OodPairWitness
  polynomial0 : PolynomialWitness
  polynomial1 : PolynomialWitness
  polynomial2 : PolynomialWitness
  polynomial3 : PolynomialWitness

/-- Replace only the relation-table half of a deployed schedule by the exact
decoded vectors returned by the generated evaluator.  This makes the former
`poly3`/pre-fold table correspondence definitional while preserving the same
alpha and the entire FRI schedule. -/
def withGeneratedRelationTables
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    DeployedRuntimeSchedule BaseField ExtensionField where
  alpha := base.alpha
  ood0 := fun sample => exactSliceVector 1024
    (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample))
  ood1 := fun sample => exactSliceVector 256
    (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample))
  ood2 := fun sample => exactSliceVector 64
    (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample))
  ood3 := fun sample => exactSliceVector 16
    (alloc.vec.Vec.deref (oodPairTable tables.ood3 sample))
  poly0 := exactSliceVector 1024
    (alloc.vec.Vec.deref tables.polynomial0.table)
  poly1 := exactSliceVector 256
    (alloc.vec.Vec.deref tables.polynomial1.table)
  poly2 := exactSliceVector 64
    (alloc.vec.Vec.deref tables.polynomial2.table)
  poly3 := exactSliceVector 16
    (alloc.vec.Vec.deref tables.polynomial3.table)
  circleInv2x := base.circleInv2x
  circleInv2y := base.circleInv2y
  line1Inverse := base.line1Inverse
  line2Inverse := base.line2Inverse
  line3Inverse := base.line3Inverse
  later1Count := base.later1Count
  later2Count := base.later2Count
  later3Count := base.later3Count
  later1Fibre := base.later1Fibre
  later2Fibre := base.later2Fibre
  later3Fibre := base.later3Fibre
  finalX := base.finalX

@[simp] theorem withGeneratedRelationTables_alpha
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (withGeneratedRelationTables base tables).alpha = base.alpha := rfl

@[simp] theorem withGeneratedRelationTables_poly3
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (withGeneratedRelationTables base tables).poly3 =
      exactSliceVector 16
        (alloc.vec.Vec.deref tables.polynomial3.table) := rfl

/-- Exact OOD semantics for one returned pair, after replacing the abstract
schedule table by that returned pair. -/
theorem ood_pair_semantics_matches_generated_table
    (coefficients : alloc.vec.Vec RawQM31)
    (w : OodPairWitness) (n : Nat)
    (coefficientView : Fin n → ExtensionField)
    (hsemantics : OodPairDotSemantics coefficients w)
    (hcoeffLength : coefficients.val.length = n)
    (htable0Length : w.table0.val.length = n)
    (htable1Length : w.table1.val.length = n)
    (hbound : n ≤ 1024)
    (hcoeffCanonical :
      ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
        coefficients.val)
    (htable0Canonical :
      ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
        w.table0.val)
    (htable1Canonical :
      ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
        w.table1.val)
    (hcoefficients :
      exactSliceVector n (alloc.vec.Vec.deref coefficients) = coefficientView) :
    ∀ sample : Fin 2,
      runtimeQM31View (oodPairValue w sample) =
        maintainedSourceDot
          (exactSliceVector n
            (alloc.vec.Vec.deref (oodPairTable w sample)))
          coefficientView := by
  have h := hsemantics n hcoeffLength htable0Length htable1Length hbound
    hcoeffCanonical htable0Canonical htable1Canonical
  rw [hcoefficients] at h
  intro sample
  fin_cases sample
  · change runtimeQM31View w.value0 =
      dotLinear (exactSliceVector n (alloc.vec.Vec.deref w.table0))
        coefficientView
    exact h.1
  · change runtimeQM31View w.value1 =
      dotLinear (exactSliceVector n (alloc.vec.Vec.deref w.table1))
        coefficientView
    exact h.2

/-- Exact polynomial semantics for one returned seven-coordinate message,
against the generated post-OOD table used to produce it. -/
theorem polynomial_semantics_matches_generated_table
    (coefficients : alloc.vec.Vec RawQM31)
    (w : PolynomialWitness) (n : Nat)
    (coefficientView : Fin (4 * n) → ExtensionField)
    (hsemantics : PolynomialSemantics coefficients w)
    (hcoeffLength : coefficients.val.length = 4 * n)
    (htableLength : w.table.val.length = 4 * n)
    (hbound : 4 * n ≤ 1024)
    (hcoeffCanonical :
      ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
        coefficients.val)
    (htableCanonical :
      ComponentCRuntimeMaterializedRelationArithmetic.RuntimeCanonicalList
        w.table.val)
    (hcoefficients :
      exactSliceVector (4 * n) (alloc.vec.Vec.deref coefficients) =
        coefficientView) :
    ∀ degree : Fin 7,
      runtimeQM31View w.polynomial.val[degree.val]! =
        maintainedSourcePolynomial n
          (exactSliceVector (4 * n) (alloc.vec.Vec.deref w.table))
          coefficientView degree := by
  have h := hsemantics n hcoeffLength htableLength hbound
    hcoeffCanonical htableCanonical
  rw [hcoefficients] at h
  intro degree
  change runtimeQM31View w.polynomial.val[degree.val]! =
    polynomialForExtension n
      (exactSliceVector (4 * n) (alloc.vec.Vec.deref w.table))
      coefficientView degree
  exact h.2 degree

#print axioms withGeneratedRelationTables_alpha
#print axioms withGeneratedRelationTables_poly3
#print axioms ood_pair_semantics_matches_generated_table
#print axioms polynomial_semantics_matches_generated_table

end aspis_prover.ComponentCRuntimeGeneratedRelationSchedule
