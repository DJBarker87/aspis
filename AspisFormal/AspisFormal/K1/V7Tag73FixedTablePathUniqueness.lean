import AspisFormal.K1.V7Tag73CheckedRefinementFutureFreePath

/-!
# Uniqueness of a Tag-73 oracle path under one fixed table

`MachineQueryPath` deliberately records only operational query/answer pairs;
on its own it can choose any answer at each query.  The compiler uses such a
path only together with `PathUsesFixedTable`.  This leaf proves that the pair
is deterministic: two paths for the same oracle program backed by the same
first-hit table have exactly the same ordered pairs and returned value.

This is the non-circular alignment primitive needed to compare a checked
fixed-table Tag-73 path with the path reconstructed from the actual scheduler
run.  It assumes neither acceptance, restoration success nor extraction.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FixedTablePathUniqueness

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CheckedRefinementFutureFreePath

noncomputable section

/-- The tail of a table-backed query path is table-backed. -/
theorem path_uses_fixed_table_tail
    (table : FixedOracleTable) (input : ShaInput) (output : ShaOutput)
    (pairs : List (ShaInput × ShaOutput))
    (backed : PathUsesFixedTable table ((input, output) :: pairs)) :
    PathUsesFixedTable table pairs := by
  intro pair member
  exact backed pair (List.mem_cons_of_mem _ member)

/-- The head answer of a table-backed nonempty query path is the table's
literal first-hit answer. -/
theorem path_uses_fixed_table_head
    (table : FixedOracleTable) (input : ShaInput) (output : ShaOutput)
    (pairs : List (ShaInput × ShaOutput))
    (backed : PathUsesFixedTable table ((input, output) :: pairs)) :
    tableLookup table input = some output := by
  exact backed (input, output) (by simp)

/-- One fixed first-hit oracle table makes the operational query path
functional.  Both the complete answer trace and the returned value are
forced; no response-uniqueness or extraction assumption is used. -/
theorem machine_query_path_fixed_table_unique
    {Result : Type*} (table : FixedOracleTable)
    (program : OracleMachine Result)
    (leftPairs rightPairs : List (ShaInput × ShaOutput))
    (leftResult rightResult : Result)
    (left : MachineQueryPath program leftPairs leftResult)
    (right : MachineQueryPath program rightPairs rightResult)
    (leftBacked : PathUsesFixedTable table leftPairs)
    (rightBacked : PathUsesFixedTable table rightPairs) :
    leftPairs = rightPairs ∧ leftResult = rightResult := by
  induction left generalizing rightPairs rightResult with
  | pure result =>
      cases right
      exact ⟨rfl, rfl⟩
  | @query input next output pairs result tail ih =>
      cases right with
      | query _ _ rightOutput rightPairs rightResult rightTail =>
          have leftHead := path_uses_fixed_table_head table input output pairs
            leftBacked
          have rightHead := path_uses_fixed_table_head table input rightOutput
            rightPairs rightBacked
          have outputExact : output = rightOutput := by
            rw [leftHead] at rightHead
            exact Option.some.inj rightHead
          subst rightOutput
          have tailExact := ih rightPairs rightResult rightTail
            (path_uses_fixed_table_tail table input output pairs leftBacked)
            (path_uses_fixed_table_tail table input output rightPairs
              rightBacked)
          exact ⟨congrArg (List.cons (input, output)) tailExact.1,
            tailExact.2⟩

/-- Returned values alone are therefore unique under a fixed table. -/
theorem machine_query_path_fixed_table_result_unique
    {Result : Type*} (table : FixedOracleTable)
    (program : OracleMachine Result)
    (leftPairs rightPairs : List (ShaInput × ShaOutput))
    (leftResult rightResult : Result)
    (left : MachineQueryPath program leftPairs leftResult)
    (right : MachineQueryPath program rightPairs rightResult)
    (leftBacked : PathUsesFixedTable table leftPairs)
    (rightBacked : PathUsesFixedTable table rightPairs) :
    leftResult = rightResult :=
  (machine_query_path_fixed_table_unique table program leftPairs rightPairs
    leftResult rightResult left right leftBacked rightBacked).2

#print axioms path_uses_fixed_table_tail
#print axioms path_uses_fixed_table_head
#print axioms machine_query_path_fixed_table_unique
#print axioms machine_query_path_fixed_table_result_unique

end

end AspisK1.V7Tag73FixedTablePathUniqueness
