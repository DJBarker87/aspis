import AspisFormal.V5Tag67CandidateTraceExtraction
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5WorkNormalizedApplicabilityRepair
import AspisFormal.V5ComponentCPreProjectionDeployed

/-!
# The exact nineteen-column batching event

The first committed V5 word is the scalar-power combination of nineteen
columns: sixteen M31 trace columns and three QM31 helper columns.  This file
proves fixed-vector algebra and pins the lane order.

* Lean proves the elementary algebra: a fixed nonzero discrepancy between two
  nineteen-column families can be hidden by at most eighteen nonzero values of
  the batching challenge.
The fixed-vector mismatch event must not be unioned over every decoder-list
candidate.  Such a union can be certain when the list contains two distinct
candidates.  The actual proximity event, its curve-decoding theorem, and the
no-list-factor cardinality proof are in `V5Width19CorrelatedAgreement`.

The final section pins the exact `0..15,16,17,18` lane order used by
`CandidateLaneEnsemble`.  It shows precisely when the earlier
`CombinedLaneBindingFailure` is the width-nineteen PCS batching failure; it
does not treat Merkle authentication alone as a proof of code membership.
-/

namespace AspisV5Width19LaneBatchBinding

open Polynomial
open AspisV5ComponentCPreProjectionDeployed
open AspisV5FriConcreteEncoderApplicability
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5WorkNormalizedApplicabilityRepair

variable {K : Type*} [Field K]

/-! ## Fixed-vector degree-eighteen algebra -/

/-- The exact scalar-power combination of nineteen values. -/
def width19Batch (values : Fin 19 -> K) (gamma : K) : K :=
  ∑ lane : Fin 19, values lane * gamma ^ lane.val

@[simp]
theorem eval_monomialPolynomial_width19
    (values : Fin 19 -> K) (gamma : K) :
    (monomialPolynomial values).eval gamma = width19Batch values gamma := by
  simp [monomialPolynomial, width19Batch, Polynomial.eval_finsetSum]

/-- A nonzero nineteen-vector gives a nonzero polynomial. -/
theorem width19Polynomial_ne_zero
    (values : Fin 19 -> K) (hvalues : values ≠ 0) :
    monomialPolynomial values ≠ 0 := by
  intro hzero
  apply hvalues
  apply monomialPolynomial_injective
  simpa [monomialPolynomial] using hzero

/-- The width-nineteen polynomial has degree at most eighteen. -/
theorem width19Polynomial_natDegree_le
    (values : Fin 19 -> K) :
    (monomialPolynomial values).natDegree ≤ 18 := by
  simpa using
    (monomialPolynomial_natDegree_le (K := K) (n := 19) (by decide) values)

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Nonzero batching challenges which hide one fixed nonzero discrepancy. -/
def width19NonzeroCollisionSet (values : Fin 19 -> K) : Finset K :=
  (Finset.univ.erase 0).filter fun gamma => width19Batch values gamma = 0

/-- At most eighteen nonzero challenges hide a fixed nonzero discrepancy. -/
theorem width19_nonzero_collision_card_le
    (values : Fin 19 -> K) (hvalues : values ≠ 0) :
    (width19NonzeroCollisionSet values).card ≤ 18 := by
  let polynomial := monomialPolynomial values
  have hpolynomial : polynomial ≠ 0 := width19Polynomial_ne_zero values hvalues
  have hsubset : (width19NonzeroCollisionSet values).val ⊆ polynomial.roots := by
    intro gamma hgamma
    have hmem : gamma ∈ width19NonzeroCollisionSet values := hgamma
    have hbatch : width19Batch values gamma = 0 := by
      exact (Finset.mem_filter.mp hmem).2
    rw [Polynomial.mem_roots hpolynomial]
    simpa [Polynomial.IsRoot, polynomial] using hbatch
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (width19Polynomial_natDegree_le values)

/-- Exact uniform mass when the released sampler is uniform on `K*`. -/
def uniformWidth19NonzeroCollisionProbability
    (values : Fin 19 -> K) : Rat :=
  (width19NonzeroCollisionSet values).card /
    ((Fintype.card K - 1 : Nat) : Rat)

/-- The elementary fixed-vector collision probability is at most
`18 / (|K|-1)`.  This is not, by itself, the full PCS proximity theorem. -/
theorem uniform_width19_nonzero_collision_probability_le
    (values : Fin 19 -> K) (hvalues : values ≠ 0) :
    uniformWidth19NonzeroCollisionProbability values ≤
      (18 : Rat) / ((Fintype.card K - 1 : Nat) : Rat) := by
  have hfieldNat : 0 < Fintype.card K - 1 := Nat.sub_pos_iff_lt.mpr
    (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance)
  have hfield : (0 : Rat) < ((Fintype.card K - 1 : Nat) : Rat) := by
    exact_mod_cast hfieldNat
  rw [uniformWidth19NonzeroCollisionProbability,
    div_le_div_iff_of_pos_right hfield]
  exact_mod_cast width19_nonzero_collision_card_le values hvalues

end FiniteField

/-! ## Exact V5 lane order -/

abbrev Width19Coefficients (K : Type*) := TotalLane -> Fin 1024 -> K

/-- Read the nineteen coefficient vectors into the semantic/helper partition
used by the candidate-to-spend extraction proof. -/
def ensembleOfWidth19Coefficients
    (gamma : K) (columns : Width19Coefficients K) :
    CandidateLaneEnsemble K where
  gamma := gamma
  semantic := fun lane => columns ⟨lane.val, lane.isLt.trans (by decide)⟩
  hcopy := columns ⟨16, by decide⟩
  componentB := columns ⟨17, by decide⟩
  componentC := columns ⟨18, by decide⟩

/-- Pointwise scalar-power combination of the exact nineteen coefficient
columns. -/
def combineWidth19Coefficients
    (gamma : K) (columns : Width19Coefficients K) : Fin 1024 -> K :=
  (ensembleOfWidth19Coefficients gamma columns).combined

/-- The source construction and the candidate extraction record use exactly
the same combined vector. -/
theorem ensembleOfWidth19Coefficients_combined
    (gamma : K) (columns : Width19Coefficients K) :
    (ensembleOfWidth19Coefficients gamma columns).combined =
      combineWidth19Coefficients gamma columns := by
  rfl

/-- Expanded pointwise form: semantic lanes use powers zero through fifteen,
then Hcopy, B and C use powers sixteen, seventeen and eighteen. -/
theorem combineWidth19Coefficients_apply
    (gamma : K) (columns : Width19Coefficients K) (row : Fin 1024) :
    combineWidth19Coefficients gamma columns row =
      (∑ lane : Fin 16, gamma ^ lane.val *
        columns ⟨lane.val, lane.isLt.trans (by decide)⟩ row) +
      gamma ^ 16 * columns ⟨16, by decide⟩ row +
      gamma ^ 17 * columns ⟨17, by decide⟩ row +
      gamma ^ 18 * columns ⟨18, by decide⟩ row := by
  rw [← ensembleOfWidth19Coefficients_combined]
  exact CandidateLaneEnsemble.combined_apply
    (ensembleOfWidth19Coefficients gamma columns) row

/-- Exact source projection of one candidate record onto the committed
nineteen-column family.  The first two equalities are construction facts; the
last is the substantive PCS/MCA binding statement. -/
structure Width19CandidateProjection
    (gamma : K) (columns : Width19Coefficients K)
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K) : Prop where
  recordLanes : record.lanes = ensembleOfWidth19Coefficients gamma columns
  initialValues : execution.initialValues =
    combineWidth19Coefficients gamma columns

/-- Under the exact width-nineteen projection, the separately named combined
lane failure is impossible. -/
theorem no_combinedLaneBindingFailure_of_width19_projection
    (gamma : K) (columns : Width19Coefficients K)
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K)
    (projection : Width19CandidateProjection gamma columns execution record) :
    ¬ CombinedLaneBindingFailure execution record := by
  intro failure
  apply failure
  rw [projection.recordLanes, ensembleOfWidth19Coefficients_combined,
    projection.initialValues]

/-- Conversely, once the record is known to contain the exact nineteen source
columns, `CombinedLaneBindingFailure` says exactly that the FRI candidate is
not their scalar-power combination. -/
theorem combinedLaneBindingFailure_iff_width19_candidate_mismatch
    (gamma : K) (columns : Width19Coefficients K)
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K)
    (recordLanes : record.lanes =
      ensembleOfWidth19Coefficients gamma columns) :
    CombinedLaneBindingFailure execution record ↔
      combineWidth19Coefficients gamma columns ≠ execution.initialValues := by
  rw [CombinedLaneBindingFailure, recordLanes,
    ensembleOfWidth19Coefficients_combined]

/-! ## Honest statement of the remaining cryptographic step -/

/-- Exact event identity for one fixed candidate schedule.  This definition is
useful for deterministic algebra only.  Its existential union over a decoder
family is not the correlated-agreement rare event and receives no probability
bound from this file. -/
def ExactWidth19BatchEvent
    {Schedule : Type*}
    (event : Schedule -> Prop)
    (gamma : Schedule -> K)
    (columns : Schedule -> Width19Coefficients K)
    (execution : Schedule -> AcceptedCandidateExecution K) : Prop :=
  ∀ schedule,
    event schedule ↔
      combineWidth19Coefficients (gamma schedule) (columns schedule) ≠
        (execution schedule).initialValues

#print axioms eval_monomialPolynomial_width19
#print axioms width19Polynomial_ne_zero
#print axioms width19Polynomial_natDegree_le
#print axioms width19_nonzero_collision_card_le
#print axioms uniform_width19_nonzero_collision_probability_le
#print axioms ensembleOfWidth19Coefficients_combined
#print axioms combineWidth19Coefficients_apply
#print axioms no_combinedLaneBindingFailure_of_width19_projection
#print axioms combinedLaneBindingFailure_iff_width19_candidate_mismatch

end AspisV5Width19LaneBatchBinding
