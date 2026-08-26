import Mathlib.Probability.Distributions.Uniform
import AspisFormal.K1.V7FsStateRestorationCoupling

/-!
# Strict Tag-73 resource and lazy-oracle accounting

This module is deliberately below the compiler/coupling theorem.  It does two
things only:

* count the SHA calls made by the exact deployed Tag-73 verifier schedule,
  keeping the three prover-controlled nonce-search regions separate; and
* provide finite-uniform target and union lemmas from which a concrete lazy
  random-oracle game can obtain its collision/guess coefficient.

There is no trace-cover, restoration, extraction, or Fiat--Shamir conclusion
in this file.  In particular, the target-count theorem does not assert that a
coupling failure is one of the counted target events.  The operational
query-DAG proof must establish that reduction before using the probability
bound.

The 208-bit Merkle computations are counted as calls to the shared SHA
primitive.  Their *truncated commitment-binding* collision analysis remains a
separately typed K1.2 premise; the denominator below concerns collisions or
predictions of full 32-byte lazy-oracle answers.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ResourceLazyOracle

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Exact deployed challenge inventory -/

/-- Challenge occurrences in deployed execution order.  The final three
`alpha` challenges occur after query batching; `alpha 0` occurs before
`final256`. -/
def deployedChallengeIds : List ChallengeId :=
  [.lambda, .chi, .theta] ++
  (List.ofFn fun coordinate : Fin 10 => .zerocheckPoint coordinate) ++
  [.mu, .eta] ++
  (List.ofFn fun round : Fin 10 => .semantic round) ++
  [.gamma, .kappa,
   .circlePoint 0, .oodMix 0,
   .circlePoint 1, .oodMix 1,
   .alpha 0, .queryBatch,
   .alpha 1, .alpha 2, .alpha 3]

theorem deployed_challenge_occurrence_count :
    deployedChallengeIds.length = 36 := by
  decide

def deployedChallengeBlockCap : Nat :=
  (deployedChallengeIds.map fun id =>
    samplerBlockCap (samplerMode id)).sum

/-- Thirty ordinary samples, four nonzero samples, and two secure-circle
samples give `30*4 + 4*12 + 2*12 = 192` raw 32-byte blocks. -/
theorem deployed_challenge_block_cap_exact :
    deployedChallengeBlockCap = 192 := by
  decide

def challengeBlocksUsed (messages : Messages) : Nat :=
  (deployedChallengeIds.map fun id =>
    (messages.challengeUse id).blocksUsed).sum

private theorem challenge_blocks_list_le_caps (messages : Messages) :
    ∀ ids : List ChallengeId,
      (ids.map fun id => (messages.challengeUse id).blocksUsed).sum ≤
      (ids.map fun id => samplerBlockCap (samplerMode id)).sum
  | [] => by simp
  | id :: ids => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (messages.challengeUse id).withinDeployedCap
        (challenge_blocks_list_le_caps messages ids)

/-- Every accepted bounded decoder consumes at most the exact deployed cap;
there are two distinct SHA inputs per raw block. -/
theorem challenge_blocks_used_le_192 (messages : Messages) :
    challengeBlocksUsed messages ≤ 192 := by
  calc
    challengeBlocksUsed messages ≤ deployedChallengeBlockCap := by
      exact challenge_blocks_list_le_caps messages deployedChallengeIds
    _ = 192 := deployed_challenge_block_cap_exact

/-! ## q16 cloned-forest calls -/

def selectedPrefixCounter
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (index : Fin (search.selectedCounter.val + 1)) : Fin 64 :=
  ⟨index.val, by omega⟩

theorem candidate_outcome_blocks_le_eight (outcome : CandidateOutcome) :
    outcome.blocksUsed ≤ 8 := by
  cases outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule => exact schedule.withinSixtyFourDraws

/-- Exact SHA-call count for the candidate branches actually evaluated up to
and including the selected first-cap-203 counter.  Each branch has one
counter absorb and two calls per bounded sampler block. -/
def q16BranchOracleCalls
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : Nat :=
  Finset.univ.sum fun index : Fin (search.selectedCounter.val + 1) =>
    1 + 2 * (search.outcome (selectedPrefixCounter search index)).blocksUsed

theorem selected_q16_candidate_count_le_64
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    search.selectedCounter.val + 1 ≤ 64 := by
  omega

/-- The full 64-branch forest costs at most `64 * (1 + 2*8) = 1088`
full-output SHA calls.  No independence and no first-success assumption beyond
the typed deployed search object is used. -/
theorem q16_branch_oracle_calls_le_1088
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    q16BranchOracleCalls search ≤ 1088 := by
  have each : ∀ index : Fin (search.selectedCounter.val + 1),
      1 + 2 *
          (search.outcome (selectedPrefixCounter search index)).blocksUsed ≤ 17 := by
    intro index
    have cap := candidate_outcome_blocks_le_eight
      (search.outcome (selectedPrefixCounter search index))
    omega
  calc
    q16BranchOracleCalls search ≤
        ∑ _index : Fin (search.selectedCounter.val + 1), 17 := by
      unfold q16BranchOracleCalls
      exact Finset.sum_le_sum fun index _ => each index
    _ = (search.selectedCounter.val + 1) * 17 := by simp
    _ ≤ 64 * 17 := Nat.mul_le_mul_right 17
      (selected_q16_candidate_count_le_64 search)
    _ = 1088 := by norm_num

/-! ## Typed two-tree authentication calls -/

/-- Sixteen opened leaves are hashed in each typed tree.  For one tree with
`frontierNodes` supplied siblings, the pruned binary tree has
`16 + frontierNodes - 1 = frontierNodes + 15` internal hashes. -/
def twoTreeAuthenticationOracleCalls (frontierNodes : Nat) : Nat :=
  2 * 16 + 2 * (frontierNodes + 15)

theorem two_tree_authentication_calls_formula (frontierNodes : Nat) :
    twoTreeAuthenticationOracleCalls frontierNodes =
      2 * frontierNodes + 62 := by
  simp [twoTreeAuthenticationOracleCalls]
  omega

theorem two_tree_authentication_calls_le_468
    (frontierNodes : Nat) (compact : frontierNodes ≤ 203) :
    twoTreeAuthenticationOracleCalls frontierNodes ≤ 468 := by
  rw [two_tree_authentication_calls_formula]
  omega

/-! ## Three separately positioned adversary work-query regions -/

def grindingChoiceQueries {stage : WorkStage}
    (choice : GrindingChoice stage) : Nat :=
  choice.probesBeforeSelected.length + 1

structure StageGrindingQueryUse where
  batch : Nat
  fold : Nat
  final : Nat

def stageGrindingQueryUse (messages : Messages) : StageGrindingQueryUse where
  batch := grindingChoiceQueries messages.batchGrinding
  fold := grindingChoiceQueries messages.foldGrinding
  final := grindingChoiceQueries messages.finalGrinding

@[simp] theorem stage_grinding_batch_exact (messages : Messages) :
    (stageGrindingQueryUse messages).batch =
      messages.batchGrinding.probesBeforeSelected.length + 1 := by
  rfl

@[simp] theorem stage_grinding_fold_exact (messages : Messages) :
    (stageGrindingQueryUse messages).fold =
      messages.foldGrinding.probesBeforeSelected.length + 1 := by
  rfl

@[simp] theorem stage_grinding_final_exact (messages : Messages) :
    (stageGrindingQueryUse messages).final =
      messages.finalGrinding.probesBeforeSelected.length + 1 := by
  rfl

/-- `probesBeforeSelected` is analytic adversary history, not verifier work.
The deployed verifier itself performs exactly one check of the serialized
nonce at each of the three positions. -/
def selectedWorkVerifierOracleCalls : Nat := 3

/-! ## End-to-end verifier SHA-call expression -/

def publicRootSaltOracleCalls : Nat := 2

def eventAbsorbOracleCalls : MachineEvent → Nat
  | .absorb _ => 1
  | .challenge _ _ => 0
  | .grind _ _ => 0
  | .check _ => 0

def eventListAbsorbOracleCalls (events : List MachineEvent) : Nat :=
  (events.map eventAbsorbOracleCalls).sum

/- Literal count from `beforeQueryScan`: 29 transcript absorbs before the
cloned q16 forest. -/
set_option maxHeartbeats 800000 in
theorem before_query_scan_absorb_calls_exact
    (oracle : HashOracle) (messages : Messages) :
    eventListAbsorbOracleCalls (beforeQueryScan oracle messages) = 29 := by
  simp [eventListAbsorbOracleCalls, eventAbsorbOracleCalls,
    beforeQueryScan, semanticEvents, oodEvents, challengeEvent]

/- Literal count from `afterAcceptedQueryScan`: query-batch domain and claim
plus the three remaining relation-round messages give five absorbs. -/
set_option maxHeartbeats 800000 in
theorem after_query_scan_absorb_calls_exact (messages : Messages) :
    eventListAbsorbOracleCalls (afterAcceptedQueryScan messages) = 5 := by
  simp [eventListAbsorbOracleCalls, eventAbsorbOracleCalls,
    afterAcceptedQueryScan, relationTailEvents, challengeEvent]

def acceptedLinearAbsorbOracleCalls : Nat := 29 + 5

theorem accepted_linear_absorb_calls_exact :
    acceptedLinearAbsorbOracleCalls = 34 := by
  rfl

/-- Exact expression for the deployed verifier's SHA calls, conditional on
the recorded bounded sampler uses and selected q16 search.  It includes the
two public-root salts, exactly one check of each serialized work nonce, and
both 208-bit tree authentication computations.  Earlier work probes belong to
`Q1` and are deliberately absent here. -/
def tag73VerifierOracleCalls
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : Nat :=
  publicRootSaltOracleCalls +
  acceptedLinearAbsorbOracleCalls +
  2 * challengeBlocksUsed messages +
  selectedWorkVerifierOracleCalls +
  q16BranchOracleCalls search +
  twoTreeAuthenticationOracleCalls (frontierNodes search.selectedSchedule)

/-- The full-256 transcript/random-oracle portion of the verifier calculation.
The separately typed truncated-Merkle authentication calls are excluded. -/
def tag73Full256VerifierOracleCalls
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : Nat :=
  publicRootSaltOracleCalls +
  acceptedLinearAbsorbOracleCalls +
  2 * challengeBlocksUsed messages +
  selectedWorkVerifierOracleCalls +
  q16BranchOracleCalls search

/-- Exact additive split.  This is accounting only; proving that the two
input grammars inhabit disjoint lazy-oracle domains is a separate compiler
obligation. -/
theorem verifier_calls_split_full256_and_typed_merkle
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73VerifierOracleCalls messages search =
      tag73Full256VerifierOracleCalls messages search +
      twoTreeAuthenticationOracleCalls
        (frontierNodes search.selectedSchedule) := by
  rfl

theorem tag73_full256_verifier_oracle_calls_le_1511
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73Full256VerifierOracleCalls messages search ≤ 1511 := by
  have challengeCap := challenge_blocks_used_le_192 messages
  have q16Cap := q16_branch_oracle_calls_le_1088 search
  unfold tag73Full256VerifierOracleCalls publicRootSaltOracleCalls
    acceptedLinearAbsorbOracleCalls selectedWorkVerifierOracleCalls
  omega

/-- The complete verifier ceiling is
`2 + 34 + 2*192 + 3 + 1088 + 468 = 1979`.  The potentially much larger three
stage-local adversary search counts remain separate fields of the strict
resource ledger and are already included in `Q1`. -/
theorem tag73_verifier_oracle_calls_le
    (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    tag73VerifierOracleCalls messages search ≤
      1979 := by
  have challengeCap := challenge_blocks_used_le_192 messages
  have q16Cap := q16_branch_oracle_calls_le_1088 search
  have treeCap := two_tree_authentication_calls_le_468
    (frontierNodes search.selectedSchedule) search.selectedCompact
  unfold tag73VerifierOracleCalls publicRootSaltOracleCalls
    acceptedLinearAbsorbOracleCalls selectedWorkVerifierOracleCalls
  omega

theorem fixed_verifier_call_cap_breakdown :
    1979 = 2 + 34 + 2 * 192 + 3 + 1088 + 468 := by
  norm_num

/-! ## Exact Q1/restart/runtime ledger -/

def firstRunQ1Calls
    {RandomTape Statement Proof : Type*}
    (run : FirstRun RandomTape Statement Proof) : Nat :=
  run.q1.length

@[simp] theorem first_run_q1_calls_exact
    {RandomTape Statement Proof : Type*}
    (run : FirstRun RandomTape Statement Proof) :
    firstRunQ1Calls run =
      (freezeAdversaryQ1 run.stateAtAdversaryHalt).length := by
  rfl

theorem first_run_q1_length_le_complete_history
    {RandomTape Statement Proof : Type*}
    (run : FirstRun RandomTape Statement Proof) :
    firstRunQ1Calls run ≤ run.stateAtAdversaryHalt.history.length := by
  unfold firstRunQ1Calls FirstRun.q1 freezeAdversaryQ1 actorHistory
  exact List.length_filter_le _ _

structure RestorationCost where
  oracleCalls : Nat
  runtimeSteps : Nat

/-- Concrete accounting data emitted by a first execution, one verifier run,
and a list containing one entry per actual same-tape restoration. -/
structure StrictTag73ResourceLedger where
  q1 : List QueryRecord
  verifierOracleCalls : Nat
  restorations : List RestorationCost
  firstRunRuntimeSteps : Nat
  verifierRuntimeSteps : Nat
  freshOracleAnswers : Nat
  programmedPoints : Nat
  batchGrindingQueries : Nat
  foldGrindingQueries : Nat
  finalGrindingQueries : Nat
  queryCandidateBranches : Nat

def restorationOracleCalls (ledger : StrictTag73ResourceLedger) : Nat :=
  (ledger.restorations.map RestorationCost.oracleCalls).sum

def restorationRuntimeSteps (ledger : StrictTag73ResourceLedger) : Nat :=
  (ledger.restorations.map RestorationCost.runtimeSteps).sum

def strictTag73ResourceUse (ledger : StrictTag73ResourceLedger) : ResourceUse where
  adversaryOracleCalls := ledger.q1.length
  simulatorOracleCalls := 0
  verifierOracleCalls := ledger.verifierOracleCalls
  extractorOracleCalls := restorationOracleCalls ledger
  freshOracleAnswers := ledger.freshOracleAnswers
  programmedPoints := ledger.programmedPoints
  simulatedProofs := 0
  restartCount := ledger.restorations.length
  runtimeSteps := ledger.firstRunRuntimeSteps + ledger.verifierRuntimeSteps +
    restorationRuntimeSteps ledger
  batchGrindingQueries := ledger.batchGrindingQueries
  foldGrindingQueries := ledger.foldGrindingQueries
  finalGrindingQueries := ledger.finalGrindingQueries
  queryCandidateBranches := ledger.queryCandidateBranches

/-- Hard caps.  Calls and runtime are capped separately for every restoration;
the global cap is derived rather than placed in a theorem hypothesis. -/
structure StrictTag73ResourceEnvelope where
  q1Calls : Nat
  verifierOracleCalls : Nat
  restorationCount : Nat
  oracleCallsPerRestoration : Nat
  firstRunRuntimeSteps : Nat
  verifierRuntimeSteps : Nat
  runtimeStepsPerRestoration : Nat
  freshOracleAnswers : Nat
  programmedPoints : Nat
  batchGrindingQueries : Nat
  foldGrindingQueries : Nat
  finalGrindingQueries : Nat
  queryCandidateBranches : Nat
  /-- Fresh full-256 transcript/lazy-oracle exposures only.  Calls to the
  separately typed 208-bit Merkle grammar are excluded until a disjoint-domain
  bridge is proved. -/
  full256FreshExposures : Nat

def strictTag73ResourceBudget
    (envelope : StrictTag73ResourceEnvelope) : ResourceBudget where
  adversaryOracleCalls := envelope.q1Calls
  simulatorOracleCalls := 0
  verifierOracleCalls := envelope.verifierOracleCalls
  extractorOracleCalls :=
    envelope.restorationCount * envelope.oracleCallsPerRestoration
  freshOracleAnswers := envelope.freshOracleAnswers
  programmedPoints := envelope.programmedPoints
  simulatedProofs := 0
  restartCount := envelope.restorationCount
  runtimeSteps := envelope.firstRunRuntimeSteps +
    envelope.verifierRuntimeSteps +
    envelope.restorationCount * envelope.runtimeStepsPerRestoration
  batchGrindingQueries := envelope.batchGrindingQueries
  foldGrindingQueries := envelope.foldGrindingQueries
  finalGrindingQueries := envelope.finalGrindingQueries
  queryCandidateBranches := envelope.queryCandidateBranches

/-- All SHA calls across the initial adversary run, deployed verifier, and
same-tape restorations.  This is the strict global query parameter to use in
full-output collision accounting. -/
def strictGlobalOracleCallCap
    (envelope : StrictTag73ResourceEnvelope) : Nat :=
  envelope.q1Calls + envelope.verifierOracleCalls +
    envelope.restorationCount * envelope.oracleCallsPerRestoration

private theorem list_sum_le_length_mul (values : List Nat) (cap : Nat)
    (bounded : ∀ value ∈ values, value ≤ cap) :
    values.sum ≤ values.length * cap := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have head := bounded value (by simp)
      have tail : ∀ item ∈ values, item ≤ cap := by
        intro item member
        exact bounded item (by simp [member])
      have rest := ih tail
      simpa [List.sum_cons, List.length_cons, Nat.add_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using Nat.add_le_add head rest

theorem strict_resource_ledger_within_envelope
    (ledger : StrictTag73ResourceLedger)
    (envelope : StrictTag73ResourceEnvelope)
    (q1Bound : ledger.q1.length ≤ envelope.q1Calls)
    (verifierBound :
      ledger.verifierOracleCalls ≤ envelope.verifierOracleCalls)
    (restorationCountBound :
      ledger.restorations.length ≤ envelope.restorationCount)
    (restorationCallBound : ∀ cost ∈ ledger.restorations,
      cost.oracleCalls ≤ envelope.oracleCallsPerRestoration)
    (firstRunRuntimeBound :
      ledger.firstRunRuntimeSteps ≤ envelope.firstRunRuntimeSteps)
    (verifierRuntimeBound :
      ledger.verifierRuntimeSteps ≤ envelope.verifierRuntimeSteps)
    (restorationRuntimeBound : ∀ cost ∈ ledger.restorations,
      cost.runtimeSteps ≤ envelope.runtimeStepsPerRestoration)
    (freshBound :
      ledger.freshOracleAnswers ≤ envelope.freshOracleAnswers)
    (programmedBound : ledger.programmedPoints ≤ envelope.programmedPoints)
    (batchBound :
      ledger.batchGrindingQueries ≤ envelope.batchGrindingQueries)
    (foldBound : ledger.foldGrindingQueries ≤ envelope.foldGrindingQueries)
    (finalBound : ledger.finalGrindingQueries ≤ envelope.finalGrindingQueries)
    (candidateBound :
      ledger.queryCandidateBranches ≤ envelope.queryCandidateBranches) :
    WithinBudget (strictTag73ResourceUse ledger)
      (strictTag73ResourceBudget envelope) := by
  have restorationCallsByLength :
      restorationOracleCalls ledger ≤
        ledger.restorations.length * envelope.oracleCallsPerRestoration := by
    have mappedBound : ∀ calls ∈
        ledger.restorations.map RestorationCost.oracleCalls,
        calls ≤ envelope.oracleCallsPerRestoration := by
      intro calls callsMember
      obtain ⟨cost, costMember, rfl⟩ := List.mem_map.mp callsMember
      exact restorationCallBound cost costMember
    simpa [restorationOracleCalls] using
      (list_sum_le_length_mul
        (ledger.restorations.map RestorationCost.oracleCalls)
        envelope.oracleCallsPerRestoration mappedBound)
  have restorationCallsBound :
      restorationOracleCalls ledger ≤
        envelope.restorationCount * envelope.oracleCallsPerRestoration := by
    exact restorationCallsByLength.trans
      (Nat.mul_le_mul_right envelope.oracleCallsPerRestoration
        restorationCountBound)
  have restorationRuntimeByLength :
      restorationRuntimeSteps ledger ≤
        ledger.restorations.length * envelope.runtimeStepsPerRestoration := by
    have mappedBound : ∀ steps ∈
        ledger.restorations.map RestorationCost.runtimeSteps,
        steps ≤ envelope.runtimeStepsPerRestoration := by
      intro steps stepsMember
      obtain ⟨cost, costMember, rfl⟩ := List.mem_map.mp stepsMember
      exact restorationRuntimeBound cost costMember
    simpa [restorationRuntimeSteps] using
      (list_sum_le_length_mul
        (ledger.restorations.map RestorationCost.runtimeSteps)
        envelope.runtimeStepsPerRestoration mappedBound)
  have restorationRuntimeBound' :
      restorationRuntimeSteps ledger ≤
        envelope.restorationCount * envelope.runtimeStepsPerRestoration := by
    exact restorationRuntimeByLength.trans
      (Nat.mul_le_mul_right envelope.runtimeStepsPerRestoration
        restorationCountBound)
  have totalRuntimeBound :
      ledger.firstRunRuntimeSteps + ledger.verifierRuntimeSteps +
          restorationRuntimeSteps ledger ≤
        envelope.firstRunRuntimeSteps + envelope.verifierRuntimeSteps +
          envelope.restorationCount * envelope.runtimeStepsPerRestoration :=
    Nat.add_le_add
      (Nat.add_le_add firstRunRuntimeBound verifierRuntimeBound)
      restorationRuntimeBound'
  unfold WithinBudget strictTag73ResourceUse strictTag73ResourceBudget
  exact ⟨q1Bound, le_rfl, verifierBound, restorationCallsBound,
    freshBound, programmedBound, le_rfl, restorationCountBound,
    totalRuntimeBound, batchBound, foldBound, finalBound, candidateBound⟩

theorem strict_resource_budget_total_actor_calls
    (envelope : StrictTag73ResourceEnvelope) :
    (strictTag73ResourceBudget envelope).adversaryOracleCalls +
      (strictTag73ResourceBudget envelope).verifierOracleCalls +
      (strictTag73ResourceBudget envelope).extractorOracleCalls =
      strictGlobalOracleCallCap envelope := by
  rfl

/-! ## Deterministic conflict and fixed-binding elimination -/

theorem programming_undefined_point_succeeds
    (limits : OracleLimits) (actor : QueryActor) (state : OracleState)
    (programming : Programming)
    (withinBudget :
      state.programmingHistory.length < limits.programmedPoints)
    (undefined : lookupEntry state programming.input = none) :
    ∃ nextState,
      programOracle limits actor state programming = .ok nextState := by
  simp [programOracle, Nat.not_le.mpr withinBudget, undefined]

theorem programming_conflict_has_previously_defined_input
    (limits : OracleLimits) (actor : QueryActor) (state : OracleState)
    (programming : Programming)
    (withinBudget :
      state.programmingHistory.length < limits.programmedPoints)
    (conflict : programOracle limits actor state programming =
      .error .programmingConflict) :
    (lookupEntry state programming.input).isSome = true := by
  unfold programOracle at conflict
  simp only [Nat.not_le.mpr withinBudget, ↓reduceIte] at conflict
  cases found : lookupEntry state programming.input with
  | none => simp [found] at conflict
  | some entry => simp [found]

def fixedBindingFailureEvent
    {Sample : Type*} (fixed : Context) (replayed : Sample → Context) :
    Set Sample :=
  {sample | replayed sample ≠ fixed}

theorem fixed_binding_failure_event_empty
    {Sample : Type*} (fixed : Context) (replayed : Sample → Context)
    (preserved : ∀ sample, replayed sample = fixed) :
    fixedBindingFailureEvent fixed replayed = ∅ := by
  ext sample
  simp [fixedBindingFailureEvent, preserved sample]

theorem fixed_binding_failure_probability_zero
    {Sample : Type*} (law : PMF Sample)
    (fixed : Context) (replayed : Sample → Context)
    (preserved : ∀ sample, replayed sample = fixed) :
    law.toOuterMeasure (fixedBindingFailureEvent fixed replayed) = 0 := by
  rw [fixed_binding_failure_event_empty fixed replayed preserved]
  exact measure_empty

def resourceFailureEvent
    {Sample : Type*} (use : Sample → ResourceUse) (budget : ResourceBudget) :
    Set Sample :=
  {sample | ¬ WithinBudget (use sample) budget}

theorem resource_failure_event_empty
    {Sample : Type*} (use : Sample → ResourceUse) (budget : ResourceBudget)
    (within : ∀ sample, WithinBudget (use sample) budget) :
    resourceFailureEvent use budget = ∅ := by
  ext sample
  simp [resourceFailureEvent, within sample]

theorem resource_failure_probability_zero
    {Sample : Type*} (law : PMF Sample)
    (use : Sample → ResourceUse) (budget : ResourceBudget)
    (within : ∀ sample, WithinBudget (use sample) budget) :
    law.toOuterMeasure (resourceFailureEvent use budget) = 0 := by
  rw [resource_failure_event_empty use budget within]
  exact measure_empty

/-! ## Full-256 finite targets -/

def digestFiniteTargets {count : Nat} (targets : Fin count → Digest256) :
    Finset Digest256 :=
  Finset.univ.image targets

theorem digest_finite_targets_card_le {count : Nat}
    (targets : Fin count → Digest256) :
    (digestFiniteTargets targets).card ≤ count := by
  calc
    (digestFiniteTargets targets).card ≤
        (Finset.univ : Finset (Fin count)).card := Finset.card_image_le
    _ = count := by simp

theorem uniform_digest_hits_finite_targets_le {count : Nat}
    (targets : Fin count → Digest256) :
    uniformDigest256.toOuterMeasure
        (digestFiniteTargets targets : Set Digest256) ≤
      (count : ENNReal) / ((2 : ENNReal) ^ 256) := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [uniformDigest256, PMF.uniformOfFintype_apply,
    Finset.sum_const, nsmul_eq_mul]
  rw [show (Fintype.card Digest256 : ENNReal) =
    (2 : ENNReal) ^ 256 by
      rw [deployed_digest_256_cardinality]
      norm_num]
  rw [div_eq_mul_inv]
  exact mul_le_mul_right'
    (by exact_mod_cast digest_finite_targets_card_le targets) _

theorem uniform_digest_guess_probability (guess : Digest256) :
    uniformDigest256.toOuterMeasure ({guess} : Set Digest256) =
      1 / ((2 : ENNReal) ^ 256) := by
  rw [← transported_uniform_digest_eq_uniform]
  exact transported_uniform_digest_singleton_probability guess

/-- At the `i`th fresh exposure there are at most `i` previous full outputs;
summing their target counts gives the exact unordered-pair coefficient. -/
def full256CollisionTargetCount (freshExposures : Nat) : Nat :=
  freshExposures.choose 2

theorem full256_collision_target_count_formula (freshExposures : Nat) :
    full256CollisionTargetCount freshExposures =
      freshExposures * (freshExposures - 1) / 2 := by
  exact Nat.choose_two_right freshExposures

/-! ## Event-family union accounting without independence -/

inductive Full256TargetKind where
  | unqueriedPrediction
  | inputStateOutputCollision
  | forwardReferenceOrProgrammingConflict
  | q16ClonedForest
  deriving DecidableEq, Fintype, Repr

/-- Target capacities after the operational coupling has reduced each named
bad event to fresh full-output membership. -/
structure Full256TargetCounts where
  unqueriedPrediction : Nat
  freshExposures : Nat
  forwardReferenceOrProgrammingConflict : Nat
  q16ClonedForest : Nat

def Full256TargetCounts.targets
    (counts : Full256TargetCounts) : Full256TargetKind → Nat
  | .unqueriedPrediction => counts.unqueriedPrediction
  | .inputStateOutputCollision =>
      full256CollisionTargetCount counts.freshExposures
  | .forwardReferenceOrProgrammingConflict =>
      counts.forwardReferenceOrProgrammingConflict
  | .q16ClonedForest => counts.q16ClonedForest

def full256TargetCoefficient (counts : Full256TargetCounts) : Nat :=
  ∑ kind : Full256TargetKind, counts.targets kind

theorem full256_target_coefficient_expansion
    (counts : Full256TargetCounts) :
    full256TargetCoefficient counts =
      counts.unqueriedPrediction +
      counts.freshExposures.choose 2 +
      counts.forwardReferenceOrProgrammingConflict +
      counts.q16ClonedForest := by
  unfold full256TargetCoefficient
  rw [show (Finset.univ : Finset Full256TargetKind) =
    {.unqueriedPrediction, .inputStateOutputCollision,
      .forwardReferenceOrProgrammingConflict, .q16ClonedForest} by decide]
  simp [Full256TargetCounts.targets, full256CollisionTargetCount]
  omega

/-- A conservative target inventory derived from the separately established
full-256 fresh-exposure cap.
It is intentionally not named a probability bound:

* at most `Q` unqueried outputs can drive a `Q`-exposure execution;
* output collisions have `choose(Q,2)` targets;
* each of `P` programmed points can meet at most `Q` full-output points; and
* each of at most 1088 q16 forest calls can meet at most `Q` full-output
  points.

The compiler must prove that its actual adaptive failures inject into these
families; this file does not assume that statement. -/
def strictEnvelopeTargetCounts
    (envelope : StrictTag73ResourceEnvelope) : Full256TargetCounts where
  unqueriedPrediction := envelope.full256FreshExposures
  freshExposures := envelope.full256FreshExposures
  forwardReferenceOrProgrammingConflict :=
    envelope.programmedPoints * envelope.full256FreshExposures
  q16ClonedForest := 1088 * envelope.full256FreshExposures

theorem strict_envelope_target_coefficient_exact
    (envelope : StrictTag73ResourceEnvelope) :
    full256TargetCoefficient (strictEnvelopeTargetCounts envelope) =
      envelope.full256FreshExposures +
      envelope.full256FreshExposures.choose 2 +
      envelope.programmedPoints * envelope.full256FreshExposures +
      1088 * envelope.full256FreshExposures := by
  rw [full256_target_coefficient_expansion]
  rfl

/-- Finite union bound for the four full-output event families.  The premises
are local one-family target bounds supplied by the concrete lazy-oracle game;
no disjointness or independence is assumed. -/
theorem four_full256_target_events_union_le
    {Sample : Type*} (law : PMF Sample)
    (events : Full256TargetKind → Set Sample)
    (counts : Full256TargetCounts)
    (eventBounds : ∀ kind,
      law.toOuterMeasure (events kind) ≤
        (counts.targets kind : ENNReal) / ((2 : ENNReal) ^ 256)) :
    law.toOuterMeasure (⋃ kind, events kind) ≤
      ∑ kind : Full256TargetKind,
        (counts.targets kind : ENNReal) / ((2 : ENNReal) ^ 256) := by
  exact (measure_iUnion_fintype_le law.toOuterMeasure events).trans
    (Finset.sum_le_sum fun kind _ => eventBounds kind)

theorem four_full256_target_events_union_le_exact_coefficient
    {Sample : Type*} (law : PMF Sample)
    (events : Full256TargetKind → Set Sample)
    (counts : Full256TargetCounts)
    (eventBounds : ∀ kind,
      law.toOuterMeasure (events kind) ≤
        (counts.targets kind : ENNReal) / ((2 : ENNReal) ^ 256)) :
    law.toOuterMeasure (⋃ kind, events kind) ≤
      ((counts.unqueriedPrediction : ENNReal) +
       (counts.freshExposures.choose 2 : ENNReal) +
       (counts.forwardReferenceOrProgrammingConflict : ENNReal) +
       (counts.q16ClonedForest : ENNReal)) /
        ((2 : ENNReal) ^ 256) := by
  calc
    law.toOuterMeasure (⋃ kind, events kind) ≤
        ∑ kind : Full256TargetKind,
          (counts.targets kind : ENNReal) / ((2 : ENNReal) ^ 256) :=
      four_full256_target_events_union_le law events counts eventBounds
    _ =
        ((counts.unqueriedPrediction : ENNReal) +
         (counts.freshExposures.choose 2 : ENNReal) +
         (counts.forwardReferenceOrProgrammingConflict : ENNReal) +
         (counts.q16ClonedForest : ENNReal)) /
          ((2 : ENNReal) ^ 256) := by
      rw [show (Finset.univ : Finset Full256TargetKind) =
        {.unqueriedPrediction, .inputStateOutputCollision,
          .forwardReferenceOrProgrammingConflict, .q16ClonedForest} by decide]
      simp [Full256TargetCounts.targets, full256CollisionTargetCount]
      simp only [div_eq_mul_inv]
      ring

/-- Runtime timeout is separate from the full-output target coefficient. -/
theorem strict_timeout_probability_le_expected_div
    {Sample : Type*} (law : PMF Sample) (runtime : Sample → Nat)
    (cutoff : Nat) (cutoffNonzero : cutoff ≠ 0) :
    law.toOuterMeasure {sample | cutoff ≤ runtime sample} ≤
      expectedNatCost law runtime / (cutoff : ENNReal) := by
  simpa [outerEventProbability] using
    timeout_probability_le_expected_div law runtime cutoff cutoffNonzero

#print axioms deployed_challenge_occurrence_count
#print axioms deployed_challenge_block_cap_exact
#print axioms challenge_blocks_used_le_192
#print axioms q16_branch_oracle_calls_le_1088
#print axioms two_tree_authentication_calls_le_468
#print axioms tag73_verifier_oracle_calls_le
#print axioms strict_resource_ledger_within_envelope
#print axioms programming_conflict_has_previously_defined_input
#print axioms fixed_binding_failure_probability_zero
#print axioms resource_failure_probability_zero
#print axioms uniform_digest_hits_finite_targets_le
#print axioms full256_collision_target_count_formula
#print axioms strict_envelope_target_coefficient_exact
#print axioms four_full256_target_events_union_le_exact_coefficient
#print axioms strict_timeout_probability_le_expected_div

end

end AspisK1.V7Tag73ResourceLazyOracle
