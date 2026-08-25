import AspisFormal.K1.V7Tag73RefinementExecutionBridge
import AspisFormal.K1.V7Tag73UniformOracleBoundary
import AspisFormal.K1.V7Tag73PlainRawError

/-!
# Audit of the q16 term in the full-256 target coefficient

The constant `1088` is an exact *query-call* ceiling for the complete q16
candidate forest.  Those calls belong in the global fresh/query budget `Q`.
They are not automatically 1088 new bad-output targets at every fresh
exposure.

This module separates the two roles formally.

* The existing operational refinement theorem constructs the exact q16 cloned
  forest deterministically from every successful work-erased refinement.
  Hence an `adaptiveQ16QueryDagForestFailure` event is empty on the sample type
  of such successful refinements.
* A causal tree may choose an arbitrary continuation after seeing the current
  answer while its current target set is empty.  Adaptive branching itself
  therefore adds zero targets.
* Removing the q16 rectangle gives the exact reduced coefficient
  `Q + choose(Q,2) + P*Q`.

This does not prove that every deployed accepting execution is a successful
work-erased refinement.  Until that source/acceptance-to-refinement bridge is
proved, removing the q16 failure event from the end-to-end compiler remains
conditional on reaching the operational sample type below.  No failure-cover
or compiler conclusion is assumed here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16TargetAudit

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73UniformOracleBoundary
open AspisK1.V7Tag73PlainRawError

noncomputable section

/-! ## Successful refinement deterministically contains the q16 forest -/

/-- The exact q16 segment is reached from the literal adaptive prefix and is
then executed from that reached complete core. -/
def ExactQ16OperationalForestExists
    (table : FixedOracleTable) (tape : DeployedFixedTape) : Prop :=
  ∃ prefixCore q16Core,
    runActionCores table (FixedBindings.ofContext tape.messages.context)
        (adaptivePrefixPlan tape) initialCore = some prefixCore ∧
      runActionCores table (FixedBindings.ofContext tape.messages.context)
        (q16Plan tape) prefixCore = some q16Core

theorem successful_work_erased_refinement_has_exact_q16_forest
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (success : refineWorkErased table tape = some raw) :
    ExactQ16OperationalForestExists table tape := by
  obtain ⟨finalCore, fullRun⟩ :=
    refine_work_erased_constructs_full_plan_run table tape raw success
  let bindings := FixedBindings.ofContext tape.messages.context
  let suffix :=
    eventsToActions (afterAcceptedQueryScan tape.messages) ++ [.terminal]
  have normalized :
      runActionCores table bindings
        (adaptivePrefixPlan tape ++ (q16Plan tape ++ suffix)) initialCore =
          some finalCore := by
    simpa [fullPlan, suffix, List.append_assoc] using fullRun
  obtain ⟨prefixCore, prefixRun, remainingRun⟩ :=
    run_action_cores_append table bindings (adaptivePrefixPlan tape)
      (q16Plan tape ++ suffix) initialCore finalCore normalized
  obtain ⟨q16Core, q16Run, _postRun⟩ :=
    run_action_cores_append table bindings (q16Plan tape) suffix prefixCore
      finalCore remainingRun
  exact ⟨prefixCore, q16Core, prefixRun, q16Run⟩

/-- A sample contains the operational data and the proof that the deterministic
work-erased refinement actually completed. -/
structure SuccessfulWorkErasedRefinement where
  table : FixedOracleTable
  tape : DeployedFixedTape
  raw : InteractiveRawTrace
  success : refineWorkErased table tape = some raw

def successfulRefinementQ16ForestFailure :
    Set SuccessfulWorkErasedRefinement :=
  {sample | ¬ ExactQ16OperationalForestExists sample.table sample.tape}

theorem successful_refinement_q16_forest_failure_empty :
    successfulRefinementQ16ForestFailure = ∅ := by
  ext sample
  simp only [successfulRefinementQ16ForestFailure, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_not]
  exact successful_work_erased_refinement_has_exact_q16_forest sample.table
    sample.tape sample.raw sample.success

theorem successful_refinement_q16_forest_failure_probability_zero
    (law : PMF SuccessfulWorkErasedRefinement) :
    law.toOuterMeasure successfulRefinementQ16ForestFailure = 0 := by
  rw [successful_refinement_q16_forest_failure_empty]
  simp

/-- When the raw-error vocabulary is instantiated with the actual operational
q16-failure set above, its q16 probability term disappears exactly. -/
theorem successful_refinement_raw_error_has_no_q16_term
    (law : PMF SuccessfulWorkErasedRefinement)
    (events : PlainRomCompilerFailureEvents SuccessfulWorkErasedRefinement)
    (q16Event : events.adaptiveQ16QueryDagForestFailure =
      successfulRefinementQ16ForestFailure) :
    plainRomCompilerRawError law events =
      law.toOuterMeasure events.unqueriedTranscriptDrivingPrediction +
      law.toOuterMeasure events.full256InputStateOutputCollision +
      law.toOuterMeasure events.forwardReferenceOrProgrammingConflict +
      law.toOuterMeasure events.fixedInstanceAttemptBindingFailure +
      law.toOuterMeasure
        events.strictQueryRestartRuntimeTimeoutBudgetFailure := by
  rw [plain_rom_compiler_raw_error_six_term_expansion, q16Event,
    successful_refinement_q16_forest_failure_empty]
  simp

/-! ## Adaptive continuation is not a target event -/

/-- One causal exposure with an empty current target set.  The continuation is
still an arbitrary function of the newly exposed answer. -/
def emptyTargetAdaptiveStep {caps : List Nat}
    (next : Digest256 → CausalTargetTree Digest256 caps) :
    CausalTargetTree Digest256 (0 :: caps) :=
  .step ∅ (by simp) next

theorem empty_target_adaptive_step_hits_iff_continuation_hits
    {caps : List Nat}
    (next : Digest256 → CausalTargetTree Digest256 caps)
    (tape : FreshAnswerTape Digest256 (0 :: caps).length) :
    (emptyTargetAdaptiveStep next).everHits tape ↔
      (next tape.1).everHits tape.2 := by
  simp [emptyTargetAdaptiveStep, CausalTargetTree.everHits]

/-- Consequently the general causal count theorem charges zero current
targets even though the next subtree depends arbitrarily on the answer. -/
theorem empty_target_adaptive_step_count_le_tail_caps
    {caps : List Nat}
    (next : Digest256 → CausalTargetTree Digest256 caps) :
    causalHitCount (emptyTargetAdaptiveStep next) ≤
      caps.sum * (2 ^ 256) ^ caps.length := by
  have bound := causal_hit_count_le_target_caps (emptyTargetAdaptiveStep next)
  rw [AspisK1.V7FsStateRestorationCoupling.deployed_digest_256_cardinality]
    at bound
  simpa using bound

/-! ## Reduced full-256 coefficient -/

/-- Per-exposure targets after deterministic q16 forest construction removes
the q16-failure class: one unqueried prediction, all prior-output collisions,
and `P` forward/programming points. -/
def tag73ReducedPerExposureTargetCaps
    (freshExposures programmedPoints : Nat) : List Nat :=
  (List.range' 0 freshExposures).map fun prior =>
    1 + prior + programmedPoints

theorem tag73_reduced_per_exposure_target_caps_length
    (freshExposures programmedPoints : Nat) :
    (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints).length =
      freshExposures := by
  simp [tag73ReducedPerExposureTargetCaps]

private theorem sum_reduced_target_caps
    (indices : List Nat) (programmedPoints : Nat) :
    (indices.map fun prior => 1 + prior + programmedPoints).sum =
      indices.sum + indices.length * (1 + programmedPoints) := by
  induction indices with
  | nil => simp
  | cons prior indices ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

def tag73ReducedTargetCoefficient
    (freshExposures programmedPoints : Nat) : Nat :=
  freshExposures + freshExposures.choose 2 +
    programmedPoints * freshExposures

theorem tag73_reduced_per_exposure_target_caps_sum_exact
    (freshExposures programmedPoints : Nat) :
    (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints).sum =
      tag73ReducedTargetCoefficient freshExposures programmedPoints := by
  unfold tag73ReducedPerExposureTargetCaps
  rw [sum_reduced_target_caps, collision_caps_sum_exact]
  simp only [List.length_range']
  unfold tag73ReducedTargetCoefficient
  ring

/-- Exact arithmetic audit of the old coefficient: its only excess over the
reduced coefficient is the q16 rectangle `1088*Q`. -/
theorem original_coefficient_eq_reduced_add_q16_rectangle
    (freshExposures programmedPoints : Nat) :
    tag73UniformTargetCoefficient freshExposures programmedPoints =
      tag73ReducedTargetCoefficient freshExposures programmedPoints +
        1088 * freshExposures := by
  unfold tag73UniformTargetCoefficient tag73ReducedTargetCoefficient
  ring

theorem original_coefficient_strictly_exceeds_reduced_when_exposed
    (freshExposures programmedPoints : Nat)
    (nonzero : 0 < freshExposures) :
    tag73ReducedTargetCoefficient freshExposures programmedPoints <
      tag73UniformTargetCoefficient freshExposures programmedPoints := by
  rw [original_coefficient_eq_reduced_add_q16_rectangle]
  omega

theorem tag73_reduced_target_tree_hit_count_le
    (freshExposures programmedPoints : Nat)
    (tree : CausalTargetTree Digest256
      (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints)) :
    causalHitCount tree ≤
      tag73ReducedTargetCoefficient freshExposures programmedPoints *
        (2 ^ 256) ^ (freshExposures - 1) := by
  have bound := causal_hit_count_le_target_caps tree
  rw [AspisK1.V7FsStateRestorationCoupling.deployed_digest_256_cardinality,
    tag73_reduced_per_exposure_target_caps_sum_exact,
    tag73_reduced_per_exposure_target_caps_length] at bound
  exact bound

theorem tag73_reduced_target_tree_probability_le_exact_count
    (freshExposures programmedPoints : Nat)
    (tree : CausalTargetTree Digest256
      (tag73ReducedPerExposureTargetCaps freshExposures programmedPoints)) :
    (uniformDigestFreshTape
        (tag73ReducedPerExposureTargetCaps freshExposures
          programmedPoints).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((tag73ReducedTargetCoefficient freshExposures programmedPoints *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  have bound := uniform_digest_causal_hit_probability_le_exact_count tree
  calc
    (uniformDigestFreshTape
        (tag73ReducedPerExposureTargetCaps freshExposures
          programmedPoints).length).toOuterMeasure
          (causalHitEvent tree) ≤
        ((((tag73ReducedPerExposureTargetCaps freshExposures
              programmedPoints).sum *
            (2 ^ 256) ^
              ((tag73ReducedPerExposureTargetCaps freshExposures
                programmedPoints).length - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (tag73ReducedPerExposureTargetCaps freshExposures
              programmedPoints).length)) := bound
    _ = ((tag73ReducedTargetCoefficient freshExposures programmedPoints *
            (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^ freshExposures) := by
      rw [tag73_reduced_per_exposure_target_caps_sum_exact,
        tag73_reduced_per_exposure_target_caps_length]

#print axioms successful_work_erased_refinement_has_exact_q16_forest
#print axioms successful_refinement_q16_forest_failure_empty
#print axioms successful_refinement_q16_forest_failure_probability_zero
#print axioms successful_refinement_raw_error_has_no_q16_term
#print axioms empty_target_adaptive_step_hits_iff_continuation_hits
#print axioms empty_target_adaptive_step_count_le_tail_caps
#print axioms tag73_reduced_per_exposure_target_caps_sum_exact
#print axioms original_coefficient_eq_reduced_add_q16_rectangle
#print axioms original_coefficient_strictly_exceeds_reduced_when_exposed
#print axioms tag73_reduced_target_tree_hit_count_le
#print axioms tag73_reduced_target_tree_probability_le_exact_count

end

end AspisK1.V7Tag73Q16TargetAudit
