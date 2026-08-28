import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler
import AspisFormal.K1.V7Tag73SeededTargetArithmetic

/-!
# Exact K1.6 compiler resources for Tag-73

This module replaces the older one-number restoration envelope by the exact
resource parameters used by the operational compiler.  Write `Q` for the
complete first-run adversary SHA-call cap and `R` for the number of atomic
fork requests.  A fork request performs two same-randomness starts, so the
restart cap is `2 * R`, while it samples exactly one programmed output/advance
pair.

The three full-256 compiler quantities are kept distinct:

* machine-fresh coordinates
  `M = Q + 1511 + R * (Q + 1511)`;
* unified uniform coordinates, including two programmed fork coins,
  `F = M + 2 * R`; and
* full-256 compiler-oracle calls
  `G = Q + 1511 + R * (2 * Q + 1511)`.

`Q` includes every adversary SHA call, including its three separately
accounted grinding searches and any adversary Merkle calls.  The deployed
verifier's 468 typed 208-bit Merkle authentication calls remain in the K1.2
two-tree boundary and are not silently treated as full-256 transcript
exposures.  Thus a cursor used here is the full-256 compiler projection; the
typed Merkle authentication theorem must be composed separately.

The adaptive target list is exactly `[1 + G, 2 + G, ..., F + G]`.
The extra target at every coordinate is the deployed public all-zero dummy
digest, which is not itself sampled from the oracle but remains a possible
ancestor state throughout restoration.  Consequently the first-principles
coefficient is

`F + F.choose 2 + F * G`.

Equivalently, this is the old global-forward-reference family with constant
`G + 1`.  Omitting the seed is unsound: a later sampled advance answer can be
zero and can then reuse the pair programmed at the dummy root.

No compiler-failure inclusion, acceptance statement, extractor conclusion,
BCS coefficient, or independence premise occurs in this file.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerResources

set_option maxRecDepth 8192

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73GlobalForwardReferenceBound
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73SeededTargetArithmetic

noncomputable section

/-! ## Exact parameters and derived caps -/

def deployedFull256VerifierCallCap : Nat := 1511

def deployedTypedMerkleVerifierCallCap : Nat := 468

/-- Final plain-ROM compiler resource parameters.  The work fields are global
stage-specific totals, not three interchangeable nonce trials.  Runtime caps
are also stage-specific; `timeoutCutoff` is the explicit cutoff used for the
separate timeout event. -/
structure ExactCompilerResourceParameters where
  /-- `Q`: all first-run adversary SHA calls, including grinding and Merkle. -/
  q1ShaCallCap : Nat
  /-- `R`: number of requested atomic output/advance forks. -/
  forkRequestCap : Nat
  firstRunRuntimeCap : Nat
  initialVerifierRuntimeCap : Nat
  sameTapeStartRuntimeCap : Nat
  replayVerifierRuntimeCap : Nat
  timeoutCutoff : Nat
  batchWorkQueryCap : Nat
  foldWorkQueryCap : Nat
  finalWorkQueryCap : Nat

/-- Two black-box starts are charged for every atomic fork request. -/
def sameTapeStartCap (parameters : ExactCompilerResourceParameters) : Nat :=
  2 * parameters.forkRequestCap

/-- `M`: genuinely machine-fresh full-256 coordinates.  One of the two
same-tape starts per request reuses the frozen answer path and therefore does
not allocate a second complete `Q`-coordinate block. -/
def full256MachineFreshCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
    parameters.forkRequestCap *
      (parameters.q1ShaCallCap + deployedFull256VerifierCallCap)

/-- `F`: master-tape coordinates.  The additional two per request are the
uniform values later installed as programmed output/advance points. -/
def unifiedFull256ExposureCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  full256MachineFreshCap parameters + sameTapeStartCap parameters

/-- `G`: all full-256 compiler calls.  Each request charges two complete
same-tape adversary starts and one future-free verifier execution. -/
def globalFull256OracleCallCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
    parameters.forkRequestCap *
      (2 * parameters.q1ShaCallCap + deployedFull256VerifierCallCap)

/-- Total deterministic runtime allowance, with both starts and the replayed
verifier suffix charged separately for every fork request. -/
def totalCompilerRuntimeCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  parameters.firstRunRuntimeCap + parameters.initialVerifierRuntimeCap +
    parameters.forkRequestCap *
      (2 * parameters.sameTapeStartRuntimeCap +
        parameters.replayVerifierRuntimeCap)

/-- At most 64 q16 candidates are inspected in the initial verifier and in
each of the `R` replayed verifier executions. -/
def q16CandidateBranchCap
    (parameters : ExactCompilerResourceParameters) : Nat :=
  (parameters.forkRequestCap + 1) * 64

theorem exact_compiler_M_F_G_expansion
    (parameters : ExactCompilerResourceParameters) :
    full256MachineFreshCap parameters =
        parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap * (parameters.q1ShaCallCap + 1511) ∧
      unifiedFull256ExposureCap parameters =
        (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap * (parameters.q1ShaCallCap + 1511)) +
            2 * parameters.forkRequestCap ∧
      globalFull256OracleCallCap parameters =
        parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (2 * parameters.q1ShaCallCap + 1511) := by
  exact ⟨rfl, rfl, rfl⟩

theorem exact_compiler_fork_and_start_caps
    (parameters : ExactCompilerResourceParameters) :
    parameters.forkRequestCap = parameters.forkRequestCap ∧
      sameTapeStartCap parameters = 2 * parameters.forkRequestCap := by
  exact ⟨rfl, rfl⟩

/-- The positive-exposure simplification never encounters a zero denominator:
the deployed verifier alone contributes 1511 full-256 calls. -/
theorem exact_compiler_unified_exposure_cap_positive
    (parameters : ExactCompilerResourceParameters) :
    0 < unifiedFull256ExposureCap parameters := by
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

theorem exact_compiler_total_runtime_cap_expanded
    (parameters : ExactCompilerResourceParameters) :
    totalCompilerRuntimeCap parameters =
      parameters.firstRunRuntimeCap + parameters.initialVerifierRuntimeCap +
        parameters.forkRequestCap *
          (2 * parameters.sameTapeStartRuntimeCap +
            parameters.replayVerifierRuntimeCap) := by
  rfl

theorem deployed_verifier_full256_typed_merkle_split :
    1979 = deployedFull256VerifierCallCap +
      deployedTypedMerkleVerifierCallCap := by
  norm_num [deployedFull256VerifierCallCap,
    deployedTypedMerkleVerifierCallCap]

/-! ## Exact `ResourceBudget` projection -/

/-- The compiler-side full-256 budget.  The 468 typed Merkle-verifier calls
are intentionally not folded into `verifierOracleCalls`; they remain in the
K1.2 two-tree budget. -/
def exactCompilerResourceBudget
    (parameters : ExactCompilerResourceParameters) : ResourceBudget where
  adversaryOracleCalls := parameters.q1ShaCallCap
  simulatorOracleCalls := 0
  verifierOracleCalls := deployedFull256VerifierCallCap
  extractorOracleCalls := parameters.forkRequestCap *
    (2 * parameters.q1ShaCallCap + deployedFull256VerifierCallCap)
  freshOracleAnswers := full256MachineFreshCap parameters
  programmedPoints := 2 * parameters.forkRequestCap
  simulatedProofs := 0
  restartCount := sameTapeStartCap parameters
  runtimeSteps := totalCompilerRuntimeCap parameters
  batchGrindingQueries := parameters.batchWorkQueryCap
  foldGrindingQueries := parameters.foldWorkQueryCap
  finalGrindingQueries := parameters.finalWorkQueryCap
  queryCandidateBranches := q16CandidateBranchCap parameters

theorem exact_compiler_resource_budget_core_fields
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerResourceBudget parameters).adversaryOracleCalls =
        parameters.q1ShaCallCap ∧
      (exactCompilerResourceBudget parameters).verifierOracleCalls = 1511 ∧
      (exactCompilerResourceBudget parameters).extractorOracleCalls =
        parameters.forkRequestCap *
          (2 * parameters.q1ShaCallCap + 1511) ∧
      (exactCompilerResourceBudget parameters).freshOracleAnswers =
        full256MachineFreshCap parameters ∧
      (exactCompilerResourceBudget parameters).programmedPoints =
        2 * parameters.forkRequestCap ∧
      (exactCompilerResourceBudget parameters).restartCount =
        2 * parameters.forkRequestCap ∧
      (exactCompilerResourceBudget parameters).runtimeSteps =
        totalCompilerRuntimeCap parameters := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exact_compiler_resource_budget_three_work_caps
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerResourceBudget parameters).batchGrindingQueries =
        parameters.batchWorkQueryCap ∧
      (exactCompilerResourceBudget parameters).foldGrindingQueries =
        parameters.foldWorkQueryCap ∧
      (exactCompilerResourceBudget parameters).finalGrindingQueries =
        parameters.finalWorkQueryCap := by
  exact ⟨rfl, rfl, rfl⟩

/-- The actor-call projection of the final budget is definitionally `G`.
Programmed fork coins are in `F`, but programming does not increment this
oracle-call sum. -/
theorem exact_compiler_budget_actor_calls_eq_G
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerResourceBudget parameters).adversaryOracleCalls +
        (exactCompilerResourceBudget parameters).verifierOracleCalls +
        (exactCompilerResourceBudget parameters).extractorOracleCalls =
      globalFull256OracleCallCap parameters := by
  rfl

theorem within_exact_compiler_budget_retains_distinct_work_caps
    (parameters : ExactCompilerResourceParameters) (use : ResourceUse)
    (within : WithinBudget use (exactCompilerResourceBudget parameters)) :
    use.batchGrindingQueries ≤ parameters.batchWorkQueryCap ∧
      use.foldGrindingQueries ≤ parameters.foldWorkQueryCap ∧
      use.finalGrindingQueries ≤ parameters.finalWorkQueryCap := by
  unfold WithinBudget exactCompilerResourceBudget at within
  rcases within with
    ⟨_adversary, _simulator, _verifier, _extractor, _fresh, _programmed,
      _simulated, _restarts, _runtime, batch, fold, final, _q16⟩
  exact ⟨batch, fold, final⟩

/-! ## Explicit runtime and timeout accounting -/

def exactCompilerTimeoutEvent
    {Sample : Type*} (parameters : ExactCompilerResourceParameters)
    (runtime : Sample → Nat) : Set Sample :=
  {sample | parameters.timeoutCutoff ≤ runtime sample}

theorem exact_compiler_timeout_probability_le_expected_div
    {Sample : Type*} (law : PMF Sample)
    (parameters : ExactCompilerResourceParameters)
    (runtime : Sample → Nat)
    (cutoffNonzero : parameters.timeoutCutoff ≠ 0) :
    law.toOuterMeasure (exactCompilerTimeoutEvent parameters runtime) ≤
      expectedNatCost law runtime /
        (parameters.timeoutCutoff : ENNReal) := by
  exact strict_timeout_probability_le_expected_div law runtime
    parameters.timeoutCutoff cutoffNonzero

theorem exact_compiler_timeout_event_empty_of_hard_runtime_cap
    {Sample : Type*} (parameters : ExactCompilerResourceParameters)
    (runtime : Sample → Nat)
    (within : ∀ sample, runtime sample ≤ totalCompilerRuntimeCap parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    exactCompilerTimeoutEvent parameters runtime = ∅ := by
  ext sample
  simp only [exactCompilerTimeoutEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact fun timeout =>
    (Nat.not_lt_of_ge (timeout.trans (within sample))) cutoffBeyondCap

/-! ## Exact adaptive cap list and joint law -/

def exactCompilerTargetCaps
    (parameters : ExactCompilerResourceParameters) : List Nat :=
  operationalCapsFrom 1
    (unifiedFull256ExposureCap parameters)
    (globalFull256OracleCallCap parameters)

def exactCompilerTargetCoefficient
    (parameters : ExactCompilerResourceParameters) : Nat :=
  seededTargetCoefficient
    (unifiedFull256ExposureCap parameters)
    (globalFull256OracleCallCap parameters)

theorem exact_compiler_target_caps_length
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerTargetCaps parameters).length =
      unifiedFull256ExposureCap parameters := by
  exact operational_caps_from_one_length _ _

/-- Removing the 512 named q16 digest coordinates from the exact master tape
leaves precisely the first-run adversary allowance, the 999 non-q16 verifier
allowance, every replay machine block, and both programmed coordinates per
fork. -/
theorem exact_compiler_q16_residual_length_expanded
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerTargetCaps parameters).length - 512 =
      parameters.q1ShaCallCap + 999 +
        parameters.forkRequestCap *
          (parameters.q1ShaCallCap + 1511) +
        2 * parameters.forkRequestCap := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

/-- Concrete reserve inequality for any deployed accepted search.  All
initial-adversary calls, every non-q16 verifier call, and the complete
replay/fork allowance fit in the router residual without consuming a named
q16 coordinate. -/
theorem exact_compiler_q16_residual_covers_non_q16_execution
    (parameters : ExactCompilerResourceParameters)
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    parameters.q1ShaCallCap +
        tag73Full256NonQ16OracleCalls messages search +
        parameters.forkRequestCap *
          (parameters.q1ShaCallCap + 1511) +
        2 * parameters.forkRequestCap ≤
      (exactCompilerTargetCaps parameters).length - 512 := by
  rw [exact_compiler_q16_residual_length_expanded]
  have reserve := tag73_full256_non_q16_oracle_calls_le_999 messages search
  omega

theorem exact_compiler_target_caps_sum
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerTargetCaps parameters).sum =
      exactCompilerTargetCoefficient parameters := by
  exact operational_caps_from_one_sum_exact _ _

theorem exact_compiler_target_coefficient_expanded
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerTargetCoefficient parameters =
      (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap) +
      (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap).choose 2 +
      (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap) *
        (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (2 * parameters.q1ShaCallCap + 1511)) := by
  rfl

abbrev ExactCompilerSample (HiddenTape : Type)
    (parameters : ExactCompilerResourceParameters) :=
  HiddenTape × FreshAnswerTape Digest256
    (exactCompilerTargetCaps parameters).length

/-- Arbitrary finite hidden adversary tape followed by the independent,
uniform, exactly `F`-coordinate compiler tape. -/
def exactCompilerJointLaw
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters) :
    PMF (ExactCompilerSample HiddenTape parameters) :=
  hiddenTapeUniformFreshJointLaw hiddenLaw
    (exactCompilerTargetCaps parameters).length

/-- The causal tree for the exact `UnifiedExposureCursor G`.  It begins with
the deployed public dummy digest already seen; later coordinates add every
sampled answer.  Targets are chosen before their coordinate and padding fixes
the law at length `F`. -/
noncomputable def exactCompilerTargetTree
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    CausalTargetTree Digest256 (exactCompilerTargetCaps parameters) :=
  unifiedExposureTargetTreeFrom
    (globalFull256OracleCallCap parameters) transitionFuel 1
    (unifiedFull256ExposureCap parameters) {zeroBytes 32} (by simp) cursor

def exactCompilerTargetEvent
    {HiddenTape : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  hiddenDependentCausalHitEvent fun hidden =>
    exactCompilerTargetTree parameters transitionFuel (cursor hidden)

def exactCompilerExactCountError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  ((exactCompilerTargetCoefficient parameters *
      (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
      ENNReal) /
    (((2 : ENNReal) ^ 256) ^ unifiedFull256ExposureCap parameters)

def exactCompilerPositiveExposureError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  (exactCompilerTargetCoefficient parameters : ENNReal) /
    ((2 : ENNReal) ^ 256)

theorem exact_compiler_exact_count_error_expanded
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerExactCountError parameters =
      (((unifiedFull256ExposureCap parameters +
          (unifiedFull256ExposureCap parameters).choose 2 +
          unifiedFull256ExposureCap parameters *
            globalFull256OracleCallCap parameters) *
          (2 ^ 256) ^
            (unifiedFull256ExposureCap parameters - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          unifiedFull256ExposureCap parameters) := by
  rfl

/-! ## First-principles probability theorems -/

theorem exact_compiler_target_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactCompilerTargetEvent parameters transitionFuel cursor) ≤
      exactCompilerExactCountError parameters := by
  have bound := hidden_dependent_causal_tree_probability_le_exact_count
    hiddenLaw (fun hidden =>
      exactCompilerTargetTree parameters transitionFuel (cursor hidden))
  simpa only [exactCompilerJointLaw, exactCompilerTargetEvent,
    exactCompilerExactCountError, exact_compiler_target_caps_sum,
    exact_compiler_target_caps_length] using bound

private theorem exact_compiler_finite_exact_count_ratio_succ
    (coefficient exponent : Nat) :
    (((coefficient * (2 ^ 256) ^ exponent : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ (exponent + 1))) =
      (coefficient : ENNReal) / ((2 : ENNReal) ^ 256) := by
  push_cast
  apply (ENNReal.div_eq_div_iff
    (a := (2 : ENNReal) ^ 256)
    (b := ((2 : ENNReal) ^ 256) ^ (exponent + 1))
    (by norm_num) (by simp) (by positivity) (by simp)).2
  rw [pow_succ]
  ring

/-- Positive-`F` form with the literal final coefficient. -/
theorem exact_compiler_target_probability_le_div_two_pow_256
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactCompilerTargetEvent parameters transitionFuel cursor) ≤
      ((unifiedFull256ExposureCap parameters +
          (unifiedFull256ExposureCap parameters).choose 2 +
          unifiedFull256ExposureCap parameters *
            globalFull256OracleCallCap parameters : Nat) : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  have positive := exact_compiler_unified_exposure_cap_positive parameters
  obtain ⟨exponent, exposureExact⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  have exactBound := exact_compiler_target_probability_le_exact_count
    hiddenLaw parameters transitionFuel cursor
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactCompilerTargetEvent parameters transitionFuel cursor) ≤
      exactCompilerExactCountError parameters := exactBound
    _ = (exactCompilerTargetCoefficient parameters : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
      unfold exactCompilerExactCountError
      rw [exposureExact]
      exact exact_compiler_finite_exact_count_ratio_succ
        (exactCompilerTargetCoefficient parameters) exponent
    _ = ((unifiedFull256ExposureCap parameters +
          (unifiedFull256ExposureCap parameters).choose 2 +
          unifiedFull256ExposureCap parameters *
            globalFull256OracleCallCap parameters : Nat) : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
      rfl

theorem exact_compiler_target_probability_zero_when_F_zero
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (zero : unifiedFull256ExposureCap parameters = 0)
    (transitionFuel : Nat)
    (cursor : HiddenTape → UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactCompilerTargetEvent parameters transitionFuel cursor) = 0 := by
  have positive := exact_compiler_unified_exposure_cap_positive parameters
  omega

theorem exact_compiler_positive_error_expanded
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerPositiveExposureError parameters =
      ((((parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap) +
        (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap).choose 2 +
        (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (parameters.q1ShaCallCap + 1511) +
          2 * parameters.forkRequestCap) *
        (parameters.q1ShaCallCap + 1511 +
          parameters.forkRequestCap *
            (2 * parameters.q1ShaCallCap + 1511)) : Nat) : ENNReal) /
        ((2 : ENNReal) ^ 256)) := by
  rfl

#print axioms exact_compiler_M_F_G_expansion
#print axioms exact_compiler_fork_and_start_caps
#print axioms exact_compiler_unified_exposure_cap_positive
#print axioms exact_compiler_total_runtime_cap_expanded
#print axioms deployed_verifier_full256_typed_merkle_split
#print axioms exact_compiler_resource_budget_core_fields
#print axioms exact_compiler_resource_budget_three_work_caps
#print axioms exact_compiler_budget_actor_calls_eq_G
#print axioms within_exact_compiler_budget_retains_distinct_work_caps
#print axioms exact_compiler_timeout_probability_le_expected_div
#print axioms exact_compiler_timeout_event_empty_of_hard_runtime_cap
#print axioms exact_compiler_target_caps_length
#print axioms exact_compiler_q16_residual_length_expanded
#print axioms exact_compiler_q16_residual_covers_non_q16_execution
#print axioms exact_compiler_target_caps_sum
#print axioms exact_compiler_target_coefficient_expanded
#print axioms exact_compiler_exact_count_error_expanded
#print axioms exact_compiler_target_probability_le_exact_count
#print axioms exact_compiler_target_probability_le_div_two_pow_256
#print axioms exact_compiler_target_probability_zero_when_F_zero
#print axioms exact_compiler_positive_error_expanded

end

end AspisK1.V7Tag73ExactCompilerResources
