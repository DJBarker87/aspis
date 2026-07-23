import RuntimePackerCorrespondence
import RuntimeScheduleCorrespondence
import RuntimeValidatedScheduleBridge
import AspisFormal.V5ComponentCDownstreamDeployed

/-!
# Source-authentic Component-C runtime dimension to maintained downstream model

The generated Rust proof closes the runtime dimension and six-segment row
order.  What remains is one explicit deployment interface combining (i) the
transcript-derived deduplicated counts with the supplied maintained schedule
and (ii) the relation/fold arithmetic with `deployedEvaluate`.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeMaintainedBridge

open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimeScheduleProof
open ComponentCRuntimeValidatedScheduleBridge

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The single remaining Component-C runtime deployment interface.

This is deliberately exact, not a `Faithful` slogan: the three scalar
equalities bind the actual deduplicated Rust list lengths to the maintained
schedule, while the function equality is precisely the existing deployed
relation/fold evaluator seam.  The source-authentic row decoder and packer
order are not assumed here; they are proved in `RuntimePackerCorrespondence`. -/
def RustRuntimeScheduleAndArithmeticCorrespondence
    (n0 n1 n2 : Std.Usize)
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K) : Prop :=
  n0.val = rt.later1Count ∧
  n1.val = rt.later2Count ∧
  n2.val = rt.later3Count ∧
  RustDownstreamEvaluatorEqualsDeployed rt encodeFree enc rustEvaluate

/-- The authentic generated row count and the maintained direct-C downstream
map compose under exactly the one named deployment interface above. -/
theorem generated_runtime_dimension_and_direct_model
    (n0 n1 n2 : Std.Usize)
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K)
    (hbounds : RuntimeLaterCountBounds rt)
    (hcorr : RustRuntimeScheduleAndArithmeticCorrespondence
      n0 n1 n2 rt encodeFree enc rustEvaluate) :
    ∃ rows,
      v5_mask.component_c_runtime.component_c_runtime_downstream_rows
          (Array.make 3#usize [n0, n1, n2]) = ok (some rows) ∧
      rows.val = fRows (decodeFriSchedule rt) ∧
      AspisV5ComponentCConcreteDownstream.UnmetDeployment.RustConcreteDownstreamCorresponds
          (decodeSchedule rt) encodeFree enc rustEvaluate := by
  rcases hcorr with ⟨h0, h1, h2, hevaluate⟩
  rcases hbounds with ⟨hb0, hb1, hb2⟩
  have hn0 : n0.val ≤ 18 := by omega
  have hn1 : n1.val ≤ 18 := by omega
  have hn2 : n2.val ≤ 18 := by omega
  obtain ⟨rows, hrun, hrows⟩ :=
    ComponentCRuntimePackerProof.generated_runtime_rows_exact
      n0 n1 n2 hn0 hn1 hn2
  refine ⟨rows, hrun, ?_, ?_⟩
  · rw [hrows, deployed_output_dimension]
    omega
  · exact rustConcreteDownstreamCorresponds_of_deployedMatch
      rt encodeFree enc rustEvaluate hevaluate

/-- The residual is satisfiable for every count-matched supplied schedule:
the maintained evaluator itself is a concrete witness. -/
theorem runtime_schedule_and_arithmetic_correspondence_nonvacuous
    (n0 n1 n2 : Std.Usize)
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (h0 : n0.val = rt.later1Count)
    (h1 : n1.val = rt.later2Count)
    (h2 : n2.val = rt.later3Count) :
    RustRuntimeScheduleAndArithmeticCorrespondence n0 n1 n2 rt encodeFree enc
      (fun free => deployedEvaluate rt enc (encodeFree free)) := by
  exact ⟨h0, h1, h2, rfl⟩

/-- Count binding is load-bearing: changing the first runtime dedup count
while retaining the same maintained schedule falsifies the residual. -/
theorem wrong_first_runtime_count_breaks_correspondence
    (n0 n1 n2 : Std.Usize)
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K)
    (hwrong : n0.val ≠ rt.later1Count) :
    ¬ RustRuntimeScheduleAndArithmeticCorrespondence
      n0 n1 n2 rt encodeFree enc rustEvaluate := by
  intro h
  exact hwrong h.1

/-! ## Source-authentic schedule closure

The following capstone supersedes the three count equalities in
`RustRuntimeScheduleAndArithmeticCorrespondence`: a successful execution of
the generated Rust query derivation supplies the counts and ordered fibres by
construction.  Only the relation/fold evaluator equality remains as an
executable correspondence premise.
-/

/-- A successful source-authentic schedule derivation and the arithmetic-only
correspondence premise compose with the source-authentic runtime row packer.
No transcript count equality or later-fibre ordering is assumed. -/
theorem generated_schedule_dimension_and_direct_model
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (indices : QueryIndices)
    (hrun :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
          queries queryCount = ok (core.result.Result.Ok indices))
    (base : DeployedRuntimeSchedule F K)
    (hrange : GeneratedLaterFibresInRange indices)
    (hcount1 : (later1 indices).length ≤ 18)
    (hcount2 : (later2 indices).length ≤ 18)
    (hcount3 : (later3 indices).length ≤ 18)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K →
        Fin (fRows (decodeFriSchedule
          (withGeneratedLaterFibres base indices hrange))) → K)
    (harithmetic : RustRuntimeArithmeticCorrespondence
      (withGeneratedLaterFibres base indices hrange)
      encodeFree enc rustEvaluate) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount = ok (core.result.Result.Ok indices) /\
    ∃ rows,
      v5_mask.component_c_runtime.component_c_runtime_downstream_rows
          (Array.make 3#usize
            [alloc.vec.Vec.len (later1 indices),
             alloc.vec.Vec.len (later2 indices),
             alloc.vec.Vec.len (later3 indices)]) = ok (some rows) /\
      rows.val = fRows (decodeFriSchedule
        (withGeneratedLaterFibres base indices hrange)) /\
      AspisV5ComponentCConcreteDownstream.UnmetDeployment.RustConcreteDownstreamCorresponds
        (decodeSchedule (withGeneratedLaterFibres base indices hrange))
        encodeFree enc rustEvaluate := by
  refine ⟨hrun, ?_⟩
  apply generated_runtime_dimension_and_direct_model
  · exact ⟨hcount1, hcount2, hcount3⟩
  · exact ⟨by simp, by simp, by simp, harithmetic⟩

/-! ## Executable schedule-validation closure

The preceding historical capstone exposes the range and three q18 count facts
as premises.  The source now checks those facts at the schedule boundary; the
following theorem consumes the three generated validator successes instead.
-/

/-- Source-authentic query derivation plus source-authentic schedule
validation leaves only the relation/fold arithmetic correspondence.  There is
no free range or count premise in this capstone. -/
theorem generated_validated_schedule_dimension_and_direct_model
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (indices : QueryIndices)
    (hderive :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
          queries queryCount = ok (core.result.Result.Ok indices))
    (base : DeployedRuntimeSchedule F K)
    (haccept : GeneratedLaterValidatorsAccept indices)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K →
        Fin (fRows (decodeFriSchedule
          (withValidatedLaterFibres base indices haccept))) → K)
    (harithmetic : RustRuntimeArithmeticCorrespondence
      (withValidatedLaterFibres base indices haccept)
      encodeFree enc rustEvaluate) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount = ok (core.result.Result.Ok indices) ∧
    ∃ rows,
      v5_mask.component_c_runtime.component_c_runtime_downstream_rows
          (Array.make 3#usize
            [alloc.vec.Vec.len (later1 indices),
             alloc.vec.Vec.len (later2 indices),
             alloc.vec.Vec.len (later3 indices)]) = ok (some rows) ∧
      rows.val = fRows (decodeFriSchedule
        (withValidatedLaterFibres base indices haccept)) ∧
      AspisV5ComponentCConcreteDownstream.UnmetDeployment.RustConcreteDownstreamCorresponds
        (decodeSchedule (withValidatedLaterFibres base indices haccept))
        encodeFree enc rustEvaluate := by
  refine ⟨hderive, ?_⟩
  apply generated_runtime_dimension_and_direct_model
  · exact withValidatedLaterFibres_count_bounds base indices haccept
  · exact ⟨by simp, by simp, by simp, harithmetic⟩

#print axioms generated_runtime_dimension_and_direct_model
#print axioms runtime_schedule_and_arithmetic_correspondence_nonvacuous
#print axioms wrong_first_runtime_count_breaks_correspondence
#print axioms generated_schedule_dimension_and_direct_model
#print axioms generated_validated_schedule_dimension_and_direct_model

end aspis_prover.ComponentCRuntimeMaintainedBridge
