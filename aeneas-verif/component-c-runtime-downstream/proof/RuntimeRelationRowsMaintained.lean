import RuntimeFourRoundRelationSemantics

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeRelationRowsMaintained

open aspis_prover
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimeFourRoundRelationSemantics
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeGeneratedRelationSchedule
open ComponentCRuntimeMaterializedRelationArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation

local instance : Inhabited RawQM31 :=
  ComponentCRuntimeLaterFibreProof.instInhabitedQM31_runtimeLaterFibreCorrespondence

/-- Exact finite representation facts for the three materialized tables used
by one generated relation round.  The coefficient vector and every table are
named separately; this is not an evaluator-faithfulness premise. -/
structure RoundRelationRepresentation
    (coefficients : alloc.vec.Vec RawQM31)
    (ood : ComponentCRuntimeRelationRoundOodSemantics.OodPairWitness)
    (polynomial :
      ComponentCRuntimeRelationRoundPolynomialSemantics.PolynomialWitness)
    (n : Nat) (coefficientView : Fin (4 * n) -> ExtensionField) where
  coefficient_length : coefficients.val.length = 4 * n
  coefficient_canonical : RuntimeCanonicalList coefficients.val
  coefficient_exact :
    exactSliceVector (4 * n) (alloc.vec.Vec.deref coefficients) =
      coefficientView
  ood0_length : ood.table0.val.length = 4 * n
  ood1_length : ood.table1.val.length = 4 * n
  ood0_canonical : RuntimeCanonicalList ood.table0.val
  ood1_canonical : RuntimeCanonicalList ood.table1.val
  polynomial_length : polynomial.table.val.length = 4 * n
  polynomial_canonical : RuntimeCanonicalList polynomial.table.val

private theorem generated_ood0_table_apply
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood0
        sample =
      exactSliceVector 1024
        (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample)) := rfl

private theorem generated_ood1_table_apply
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood1
        sample =
      exactSliceVector 256
        (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample)) := rfl

private theorem generated_ood2_table_apply
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood2
        sample =
      exactSliceVector 64
        (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample)) := rfl

private theorem generated_ood3_table_apply
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) (sample : Fin 2) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).ood3
        sample =
      exactSliceVector 16
        (alloc.vec.Vec.deref (oodPairTable tables.ood3 sample)) := rfl

private theorem generated_polynomial0_table
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly0 =
      exactSliceVector 1024
        (alloc.vec.Vec.deref tables.polynomial0.table) := rfl

private theorem generated_polynomial1_table
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly1 =
      exactSliceVector 256
        (alloc.vec.Vec.deref tables.polynomial1.table) := rfl

private theorem generated_polynomial2_table
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly2 =
      exactSliceVector 64
        (alloc.vec.Vec.deref tables.polynomial2.table) := rfl

private theorem generated_polynomial3_table
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (tables : FourRoundGeneratedTables) :
    (decodeRelationSchedule (withGeneratedRelationTables base tables)).poly3 =
      exactSliceVector 16
        (alloc.vec.Vec.deref tables.polynomial3.table) := rfl

/-- The exact values released by four generated relation rounds are the
maintained relation rows for the schedule assembled from those same generated
tables.  All remaining hypotheses are concrete length/canonical decoding
facts for finite returned vectors. -/
theorem generated_four_round_relation_rows_match_maintained
    (base : DeployedRuntimeSchedule
      AspisV5ComponentCQM31TowerExact.M31Exact ExtensionField)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (semantics : FourRoundRelationSemantics
      relation0 relation1 relation2 relation3 relation4)
    (c : Coefficients ExtensionField)
    (hround0 : RoundRelationRepresentation relation0.coefficients
      semantics.tables.ood0 semantics.tables.polynomial0 256 c)
    (hround1 : RoundRelationRepresentation relation1.coefficients
      semantics.tables.ood1 semantics.tables.polynomial1 64
      (round1Coefficients
        (decodeRelationSchedule
          (withGeneratedRelationTables base semantics.tables)) c))
    (hround2 : RoundRelationRepresentation relation2.coefficients
      semantics.tables.ood2 semantics.tables.polynomial2 16
      (round2Coefficients
        (decodeRelationSchedule
          (withGeneratedRelationTables base semantics.tables)) c))
    (hround3 : RoundRelationRepresentation relation3.coefficients
      semantics.tables.ood3 semantics.tables.polynomial3 4
      (round3Coefficients
        (decodeRelationSchedule
          (withGeneratedRelationTables base semantics.tables)) c)) :
    let rt := withGeneratedRelationTables base semantics.tables
    (forall (round : Fin 4) (sample : Fin 2),
      runtimeQM31View
          relation4.ood_values.val[round.val]!.val[sample.val]! =
        roundOodRows (decodeRelationSchedule rt) round c sample) /\
    forall (round : Fin 4) (degree : Fin 7),
      runtimeQM31View relation4.sumchecks.val[round.val]!.val[degree.val]! =
        roundPolynomialRows
          (decodeRelationSchedule rt) round c degree := by
  dsimp only
  have hood0 : forall sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood0 sample) =
        dotLinear (exactSliceVector 1024
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood0 sample))) c :=
    ood_pair_semantics_matches_generated_table
      relation0.coefficients semantics.tables.ood0 1024 c
      semantics.ood0_semantics
      (by simpa only [Nat.reduceMul] using hround0.coefficient_length)
      (by simpa only [Nat.reduceMul] using hround0.ood0_length)
      (by simpa only [Nat.reduceMul] using hround0.ood1_length)
      (by norm_num) hround0.coefficient_canonical hround0.ood0_canonical
      hround0.ood1_canonical
      (by simpa only [Nat.reduceMul] using hround0.coefficient_exact)
  have hood1 : forall sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood1 sample) =
        dotLinear (exactSliceVector 256
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood1 sample)))
          (round1Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) :=
    ood_pair_semantics_matches_generated_table
    relation1.coefficients semantics.tables.ood1 256
    (round1Coefficients
      (decodeRelationSchedule
        (withGeneratedRelationTables base semantics.tables)) c)
    semantics.ood1_semantics
    (by simpa only [Nat.reduceMul] using hround1.coefficient_length)
    (by simpa only [Nat.reduceMul] using hround1.ood0_length)
    (by simpa only [Nat.reduceMul] using hround1.ood1_length) (by norm_num)
    hround1.coefficient_canonical hround1.ood0_canonical
    hround1.ood1_canonical
    (by simpa only [Nat.reduceMul] using hround1.coefficient_exact)
  have hood2 : forall sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood2 sample) =
        dotLinear (exactSliceVector 64
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood2 sample)))
          (round2Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) :=
    ood_pair_semantics_matches_generated_table
    relation2.coefficients semantics.tables.ood2 64
    (round2Coefficients
      (decodeRelationSchedule
        (withGeneratedRelationTables base semantics.tables)) c)
    semantics.ood2_semantics
    (by simpa only [Nat.reduceMul] using hround2.coefficient_length)
    (by simpa only [Nat.reduceMul] using hround2.ood0_length)
    (by simpa only [Nat.reduceMul] using hround2.ood1_length) (by norm_num)
    hround2.coefficient_canonical hround2.ood0_canonical
    hround2.ood1_canonical
    (by simpa only [Nat.reduceMul] using hround2.coefficient_exact)
  have hood3 : forall sample : Fin 2,
      runtimeQM31View (oodPairValue semantics.tables.ood3 sample) =
        dotLinear (exactSliceVector 16
          (alloc.vec.Vec.deref (oodPairTable semantics.tables.ood3 sample)))
          (round3Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) :=
    ood_pair_semantics_matches_generated_table
    relation3.coefficients semantics.tables.ood3 16
    (round3Coefficients
      (decodeRelationSchedule
        (withGeneratedRelationTables base semantics.tables)) c)
    semantics.ood3_semantics
    (by simpa only [Nat.reduceMul] using hround3.coefficient_length)
    (by simpa only [Nat.reduceMul] using hround3.ood0_length)
    (by simpa only [Nat.reduceMul] using hround3.ood1_length) (by norm_num)
    hround3.coefficient_canonical hround3.ood0_canonical
    hround3.ood1_canonical
    (by simpa only [Nat.reduceMul] using hround3.coefficient_exact)
  have hpoly0 : forall degree : Fin 7,
      runtimeQM31View
          semantics.tables.polynomial0.polynomial.val[degree.val]! =
        polynomialForExtension 256
          (exactSliceVector 1024
            (alloc.vec.Vec.deref semantics.tables.polynomial0.table)) c degree := by
    simpa only [Nat.reduceMul] using
      polynomial_semantics_matches_generated_table
        relation0.coefficients semantics.tables.polynomial0 256 c
        semantics.polynomial0_semantics hround0.coefficient_length
        hround0.polynomial_length (by norm_num)
        hround0.coefficient_canonical hround0.polynomial_canonical
        hround0.coefficient_exact
  have hpoly1 : forall degree : Fin 7,
      runtimeQM31View
          semantics.tables.polynomial1.polynomial.val[degree.val]! =
        polynomialForExtension 64
          (exactSliceVector 256
            (alloc.vec.Vec.deref semantics.tables.polynomial1.table))
          (round1Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) degree := by
    simpa only [Nat.reduceMul] using
      polynomial_semantics_matches_generated_table
        relation1.coefficients semantics.tables.polynomial1 64
        (round1Coefficients
          (decodeRelationSchedule
            (withGeneratedRelationTables base semantics.tables)) c)
        semantics.polynomial1_semantics hround1.coefficient_length
        hround1.polynomial_length (by norm_num)
        hround1.coefficient_canonical hround1.polynomial_canonical
        hround1.coefficient_exact
  have hpoly2 : forall degree : Fin 7,
      runtimeQM31View
          semantics.tables.polynomial2.polynomial.val[degree.val]! =
        polynomialForExtension 16
          (exactSliceVector 64
            (alloc.vec.Vec.deref semantics.tables.polynomial2.table))
          (round2Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) degree := by
    simpa only [Nat.reduceMul] using
      polynomial_semantics_matches_generated_table
        relation2.coefficients semantics.tables.polynomial2 16
        (round2Coefficients
          (decodeRelationSchedule
            (withGeneratedRelationTables base semantics.tables)) c)
        semantics.polynomial2_semantics hround2.coefficient_length
        hround2.polynomial_length (by norm_num)
        hround2.coefficient_canonical hround2.polynomial_canonical
        hround2.coefficient_exact
  have hpoly3 : forall degree : Fin 7,
      runtimeQM31View
          semantics.tables.polynomial3.polynomial.val[degree.val]! =
        polynomialForExtension 4
          (exactSliceVector 16
            (alloc.vec.Vec.deref semantics.tables.polynomial3.table))
          (round3Coefficients
            (decodeRelationSchedule
              (withGeneratedRelationTables base semantics.tables)) c) degree := by
    simpa only [Nat.reduceMul] using
      polynomial_semantics_matches_generated_table
        relation3.coefficients semantics.tables.polynomial3 4
        (round3Coefficients
          (decodeRelationSchedule
            (withGeneratedRelationTables base semantics.tables)) c)
        semantics.polynomial3_semantics hround3.coefficient_length
        hround3.polynomial_length (by norm_num)
        hround3.coefficient_canonical hround3.polynomial_canonical
        hround3.coefficient_exact
  constructor
  · intro round sample
    have hcases : round.val = 0 ∨ round.val = 1 ∨
        round.val = 2 ∨ round.val = 3 := by omega
    rcases hcases with hround | hround | hround | hround
    · have hr : round = 0 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood0_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_zero, ood0Rows,
        LinearMap.pi_apply]
      rw [generated_ood0_table_apply]
      exact hood0 sample
    · have hr : round = 1 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood1_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_one, Matrix.cons_val_zero,
        ood1Rows, LinearMap.pi_apply, LinearMap.comp_apply]
      rw [generated_ood1_table_apply]
      exact hood1 sample
    · have hr : round = 2 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood2_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, ood2Rows, LinearMap.pi_apply,
        LinearMap.comp_apply]
      rw [generated_ood2_table_apply]
      exact hood2 sample
    · have hr : round = 3 := Fin.eq_of_val_eq hround
      rw [hround, semantics.ood3_match sample, hr]
      simp only [roundOodRows, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons, ood3Rows, LinearMap.pi_apply,
        LinearMap.comp_apply]
      rw [generated_ood3_table_apply]
      exact hood3 sample
  · intro round degree
    have hcases : round.val = 0 ∨ round.val = 1 ∨
        round.val = 2 ∨ round.val = 3 := by omega
    rcases hcases with hround | hround | hround | hround
    · have hr : round = 0 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial0_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_zero,
        polynomial0Rows]
      rw [generated_polynomial0_table]
      exact hpoly0 degree
    · have hr : round = 1 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial1_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_one,
        Matrix.cons_val_zero, polynomial1Rows, LinearMap.comp_apply]
      rw [generated_polynomial1_table]
      exact hpoly1 degree
    · have hr : round = 2 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial2_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, polynomial2Rows, LinearMap.comp_apply]
      rw [generated_polynomial2_table]
      exact hpoly2 degree
    · have hr : round = 3 := Fin.eq_of_val_eq hround
      rw [hround, semantics.polynomial3_match, hr]
      simp only [roundPolynomialRows, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons, polynomial3Rows, LinearMap.comp_apply]
      rw [generated_polynomial3_table]
      exact hpoly3 degree

#print axioms generated_four_round_relation_rows_match_maintained

end aspis_prover.ComponentCRuntimeRelationRowsMaintained
