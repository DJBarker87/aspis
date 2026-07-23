import RuntimePrivateViewControlFlowCurrent
import RuntimeRoundControlFlowCurrent

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace ComponentCRuntimeCanonicalGenerated.RuntimeFourRoundCanonicalityCapstoneCurrent

open ComponentCRuntimeCanonicalGenerated
open RuntimePrivateViewControlFlowCurrent
open RuntimeRelationTableCanonicality
open RuntimeRoundControlFlowCurrent

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
/-- The four exact successful outer runtime rounds establish the twelve-table
canonicality invariant on their final returned table state. -/
theorem generated_four_runtime_rounds_tables_canonical
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31)
    (later0 later1 later2 later3 later4 : RuntimeLater)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (hrun0 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation0 folded0 later0 tables0 0#usize =
        ok (core.result.Result.Ok (), relation1, folded1, later1, tables1))
    (hrun1 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation1 folded1 later1 tables1 1#usize =
        ok (core.result.Result.Ok (), relation2, folded2, later2, tables2))
    (hrun2 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation2 folded2 later2 tables2 2#usize =
        ok (core.result.Result.Ok (), relation3, folded3, later3, tables3))
    (hrun3 :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_round
          schedule relation3 folded3 later3 tables3 3#usize =
        ok (core.result.Result.Ok (), relation4, folded4, later4, tables4)) :
    GeneratedRelationTablesCanonical tables4 := by
  rcases generated_runtime_round_success_decomposes
      schedule relation0 relation1 folded0 folded1 later0 later1
      tables0 tables1 0#usize hrun0 with
    ⟨relationAfter1, tablesAfter1, hrelation0, _, hre1, hte1, _⟩
  rcases generated_runtime_round_success_decomposes
      schedule relation1 relation2 folded1 folded2 later1 later2
      tables1 tables2 1#usize hrun1 with
    ⟨relationAfter2, tablesAfter2, hrelation1, _, hre2, hte2, _⟩
  rcases generated_runtime_round_success_decomposes
      schedule relation2 relation3 folded2 folded3 later2 later3
      tables2 tables3 2#usize hrun2 with
    ⟨relationAfter3, tablesAfter3, hrelation2, _, hre3, hte3, _⟩
  rcases generated_runtime_round_success_decomposes
      schedule relation3 relation4 folded3 folded4 later3 later4
      tables3 tables4 3#usize hrun3 with
    ⟨relationAfter4, tablesAfter4, hrelation3, _, hre4, hte4, _⟩
  subst relationAfter1
  subst tablesAfter1
  subst relationAfter2
  subst tablesAfter2
  subst relationAfter3
  subst tablesAfter3
  subst relationAfter4
  subst tablesAfter4
  exact generated_four_relation_rounds_tables_canonical
    schedule relation0 relation1 relation2 relation3 relation4
    tables0 tables1 tables2 tables3 tables4
    hrelation0 hrelation1 hrelation2 hrelation3

/-- Every successful current public/private Component-C execution returns a
table state whose eight OOD and four polynomial tables are canonical. -/
theorem generated_public_success_returns_canonical_relation_tables
    (schedule : RuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output)) :
    ∃ tables : RuntimeTables, GeneratedRelationTablesCanonical tables := by
  rcases generated_public_success_decomposes
      schedule coefficients codeword expectedInactiveClaim output hrun with
    ⟨tables, relation0, relation1, relation2, relation3, relation4,
      folded0, folded1, folded2, folded3, folded4,
      later0, later1, later2, later3, later4,
      tables0, tables1, tables2, tables3, trace,
      hround0, hround1, hround2, hround3, _, _⟩
  refine ⟨tables, ?_⟩
  exact generated_four_runtime_rounds_tables_canonical
    schedule relation0 relation1 relation2 relation3 relation4
    folded0 folded1 folded2 folded3 folded4
    later0 later1 later2 later3 later4
    tables0 tables1 tables2 tables3 tables
    hround0 hround1 hround2 hround3

#print axioms generated_four_runtime_rounds_tables_canonical
#print axioms generated_public_success_returns_canonical_relation_tables

end ComponentCRuntimeCanonicalGenerated.RuntimeFourRoundCanonicalityCapstoneCurrent
