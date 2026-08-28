import AspisFormal.K1.V7Tag73CoupledReplayAlignment
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics

/-!
# Operational-oracle table to fixed-table lookup bridge

The translated source/scheduler replay uses `FixedOracleTable`, whereas the
classical-ROM execution stores entries in `OracleState`.  This small bridge
preserves the *first* lookup exactly when the operational table is erased to
the deterministic fixed-table view.  It does not assign a role to a cached
entry, and so remains valid for adversary-first cache population as well.
-/

set_option autoImplicit false

namespace V7FixedTableOracleStateBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73CoupledReplayAlignment

private theorem mapped_first_lookup_preserves_output
    (entries : List AspisK1.V7FsAokExperiment.TableEntry)
    (input : ShaInput) (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : entries.find? (fun candidate => candidate.input = input) = some entry) :
    tableLookup (entries.map fun candidate =>
      ({ input := candidate.input, output := candidate.output } :
        AspisK1.V7Tag73DeterministicRefinement.TableEntry)) input =
      some entry.output := by
  induction entries generalizing entry with
  | nil => simp at found
  | cons head tail ih =>
      by_cases headMatches : head.input = input
      · simp [tableLookup, headMatches] at found ⊢
        cases found
        rfl
      · simp [tableLookup, headMatches] at found ⊢
        simpa [tableLookup, headMatches] using ih entry found

/-- An operational lookup is a lookup with the same answer in the finite
table consumed by the source/semantic replay. -/
theorem fixed_table_of_oracle_state_lookup_of_lookupEntry
    (state : OracleState) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : lookupEntry state input = some entry) :
    tableLookup (fixedTableOfOracleState state) input = some entry.output := by
  unfold lookupEntry at found
  unfold fixedTableOfOracleState
  exact mapped_first_lookup_preserves_output state.table input entry found

/-- Finite source callback coverage stated against the operational ROM table
immediately yields the exact `QueryPairsCoveredByTable` predicate consumed by
the translated q16 trace replay.  The premise is intentionally pair-level:
it neither assumes every SHA input is in the finite table nor attributes the
first insertion to a verifier role. -/
theorem operational_pair_coverage_implies_fixed_table_coverage
    (state : OracleState) (pairs : List (ShaInput × ShaOutput))
    (covered : ∀ pair ∈ pairs, ∃ entry : AspisK1.V7FsAokExperiment.TableEntry,
      lookupEntry state pair.1 = some entry ∧ entry.output = pair.2) :
    AspisK1.V7Tag73ReturnedPlanSemantics.QueryPairsCoveredByTable
      (fixedTableOfOracleState state) pairs := by
  intro pair member
  obtain ⟨entry, found, outputExact⟩ := covered pair member
  rw [← outputExact]
  exact fixed_table_of_oracle_state_lookup_of_lookupEntry state pair.1 entry found

#print axioms mapped_first_lookup_preserves_output
#print axioms fixed_table_of_oracle_state_lookup_of_lookupEntry
#print axioms operational_pair_coverage_implies_fixed_table_coverage

end V7FixedTableOracleStateBridge
