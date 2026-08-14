import AspisFormal.V5AcceptedSpendRelation
import AspisFormal.V5ImplementedWorkNormalizedEndpoint

/-!
# Conditional false-acceptance bound for the deployed V5 verifier

This file joins two existing parts of the formal development:

* `V5AcceptedSpendRelation` proves that false acceptance is contained in the
  failure event named by an accepted-run extraction theorem.
* `V5ImplementedWorkNormalizedEndpoint` proves the corrected V5 arithmetic
  bound with three selectable schedules and the S-two round count `R = 30`.

The result below does not claim that the remaining security work has already
been done.  The three failure predicates are caller-supplied.  A separate
post-release Aeneas/Lean result proves that a successful generated parser and
selector check can gate a caller-supplied `Fin 3` predicate family by selector
zero, one, or two.  It does not prove that those predicates are the real
cryptographic failure events or that its caller-supplied run-to-proof-body
function matches the complete deployed callback.  Accepted-run extraction and
each per-branch BCS bound also remain explicit premises.  Instantiating those
premises still requires the complete parser/callback bridge, proof-to-trace
extraction, and the cited PCS, FRI, Fiat--Shamir, random-oracle, and Merkle
assumptions.
-/

namespace AspisV5DeployedFalseAcceptance

open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ImplementedWorkNormalizedEndpoint
open AspisV5WorkNormalizedApplicabilityRepair
open AspisWorkNormalizedEndpoint

abbrev SpendDigest := AspisFormal.ArithmetizationCore.Digest
abbrev SpendField := AspisFormal.ArithmetizationCore.F

/-! ## Three parameterized failure events -/

/-- A generic union of three caller-supplied failure predicates.  The separate
Tag-67 selector result can gate an indexed predicate family by parsed selector
zero, one, or two.  Giving that family the meaning of the real cryptographic
failure events remains work for the security proof that instantiates and
bounds these parameters. -/
def deployedFailureUnion
    {Run : Type*}
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement) (run : Run) : Prop :=
  branchZeroFailure statement run ∨
    branchOneFailure statement run ∨
    branchTwoFailure statement run

/-- A named set for one branch failure. -/
def branchFailureEvent
    {Run : Type*}
    (branchFailure : V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement) : Set Run :=
  {run | branchFailure statement run}

/-- The set form of the three-predicate failure union. -/
def deployedFailureUnionEvent
    {Run : Type*}
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement) : Set Run :=
  {run | deployedFailureUnion branchZeroFailure branchOneFailure
    branchTwoFailure statement run}

/-- The false-acceptance event for one fixed public statement. -/
def falseAcceptanceEvent
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement)
    (deployedOwner : SpendDigest → SpendDigest)
    (deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest)
    (deployedNullifier : SpendDigest → SpendDigest → SpendDigest)
    (deployedNode : SpendDigest → SpendDigest → SpendDigest) : Set Run :=
  {run | accepts statement run ∧
    ¬ StatementHasSpendWitness statement deployedOwner deployedNote
      deployedNullifier deployedNode}

theorem deployed_failure_union_event_eq
    {Run : Type*}
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement) :
    deployedFailureUnionEvent branchZeroFailure branchOneFailure
        branchTwoFailure statement =
      branchFailureEvent branchZeroFailure statement ∪
        (branchFailureEvent branchOneFailure statement ∪
          branchFailureEvent branchTwoFailure statement) := by
  ext run
  simp only [deployedFailureUnionEvent, deployedFailureUnion,
    branchFailureEvent, Set.mem_setOf_eq, Set.mem_union]

/-! ## False acceptance is contained in the explicit union -/

/-- If accepted runs extract a valid trace outside the union of the three
parameterized failure predicates, then every false acceptance lies in that
union.  The extraction argument and the predicates' deployed meaning are
premises because they have not yet been proved for the complete verifier. -/
theorem false_accept_event_subset_deployed_failure_union
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : SpendDigest → SpendDigest}
    {deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest}
    {deployedNullifier : SpendDigest → SpendDigest → SpendDigest}
    {deployedNode : SpendDigest → SpendDigest → SpendDigest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (acceptedRunExtraction : AcceptedRunExtractsTrace accepts
      (deployedFailureUnion branchZeroFailure branchOneFailure
        branchTwoFailure) rc)
    (statement : V5PublicStatement) :
    falseAcceptanceEvent accepts statement deployedOwner deployedNote
        deployedNullifier deployedNode ⊆
      deployedFailureUnionEvent branchZeroFailure branchOneFailure
        branchTwoFailure statement := by
  simpa only [falseAcceptanceEvent, deployedFailureUnionEvent] using
    false_accept_event_subset_bad_event accepts
      (deployedFailureUnion branchZeroFailure branchOneFailure
        branchTwoFailure) rc poseidon acceptedRunExtraction statement

/-- Measure form of the accepted-run extraction result.  This theorem has no
numerical content: it only says that false acceptance is no more likely than
the parameterized three-predicate failure union. -/
theorem false_accept_measure_le_deployed_failure_union
    {Run : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run)
    (accepts : V5PublicStatement → Run → Prop)
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : SpendDigest → SpendDigest}
    {deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest}
    {deployedNullifier : SpendDigest → SpendDigest → SpendDigest}
    {deployedNode : SpendDigest → SpendDigest → SpendDigest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (acceptedRunExtraction : AcceptedRunExtractsTrace accepts
      (deployedFailureUnion branchZeroFailure branchOneFailure
        branchTwoFailure) rc)
    (statement : V5PublicStatement) :
    measure (falseAcceptanceEvent accepts statement deployedOwner deployedNote
        deployedNullifier deployedNode) ≤
      measure (deployedFailureUnionEvent branchZeroFailure branchOneFailure
        branchTwoFailure statement) :=
  MeasureTheory.measure_mono
    (false_accept_event_subset_deployed_failure_union accepts
      branchZeroFailure branchOneFailure branchTwoFailure rc poseidon
      acceptedRunExtraction statement)

/-- The probability of the explicit union is at most the sum of the three
branch probabilities.  No independence assumption is needed. -/
theorem deployed_failure_union_probability_le_branch_sum
    {Run : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run)
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement) :
    measure.real (deployedFailureUnionEvent branchZeroFailure branchOneFailure
        branchTwoFailure statement) ≤
      measure.real (branchFailureEvent branchZeroFailure statement) +
        measure.real (branchFailureEvent branchOneFailure statement) +
        measure.real (branchFailureEvent branchTwoFailure statement) := by
  rw [deployed_failure_union_event_eq]
  calc
    measure.real
        (branchFailureEvent branchZeroFailure statement ∪
          (branchFailureEvent branchOneFailure statement ∪
            branchFailureEvent branchTwoFailure statement)) ≤
        measure.real (branchFailureEvent branchZeroFailure statement) +
          measure.real
            (branchFailureEvent branchOneFailure statement ∪
              branchFailureEvent branchTwoFailure statement) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ measure.real (branchFailureEvent branchZeroFailure statement) +
          (measure.real (branchFailureEvent branchOneFailure statement) +
            measure.real (branchFailureEvent branchTwoFailure statement)) :=
      add_le_add le_rfl (MeasureTheory.measureReal_union_le _ _)
    _ = measure.real (branchFailureEvent branchZeroFailure statement) +
          measure.real (branchFailureEvent branchOneFailure statement) +
          measure.real (branchFailureEvent branchTwoFailure statement) := by
      ring

/-- Real-valued probability form of the two preceding facts. -/
theorem false_accept_probability_le_branch_sum
    {Run : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run) [MeasureTheory.IsFiniteMeasure measure]
    (accepts : V5PublicStatement → Run → Prop)
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : SpendDigest → SpendDigest}
    {deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest}
    {deployedNullifier : SpendDigest → SpendDigest → SpendDigest}
    {deployedNode : SpendDigest → SpendDigest → SpendDigest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (acceptedRunExtraction : AcceptedRunExtractsTrace accepts
      (deployedFailureUnion branchZeroFailure branchOneFailure
        branchTwoFailure) rc)
    (statement : V5PublicStatement) :
    measure.real (falseAcceptanceEvent accepts statement deployedOwner
        deployedNote deployedNullifier deployedNode) ≤
      measure.real (branchFailureEvent branchZeroFailure statement) +
        measure.real (branchFailureEvent branchOneFailure statement) +
        measure.real (branchFailureEvent branchTwoFailure statement) := by
  calc
    measure.real (falseAcceptanceEvent accepts statement deployedOwner
        deployedNote deployedNullifier deployedNode) ≤
        measure.real (deployedFailureUnionEvent branchZeroFailure
          branchOneFailure branchTwoFailure statement) :=
      MeasureTheory.measureReal_mono
        (false_accept_event_subset_deployed_failure_union accepts
          branchZeroFailure branchOneFailure branchTwoFailure rc poseidon
          acceptedRunExtraction statement)
    _ ≤ _ := deployed_failure_union_probability_le_branch_sum measure
      branchZeroFailure branchOneFailure branchTwoFailure statement

/-! ## Conditional deployed work-normalized bound -/

/-- Conditional V5 false-acceptance theorem.

The conclusion uses the corrected width-19 event ledger, exactly thirty S-two
public-coin rounds, one factor of three, and the query-budget range
`1 ≤ T ≤ 2^128`.  It becomes a deployed security theorem only after callers
identify the three failure predicates with the actual proof-system failure
events for the parsed selector and prove the full callback/run connection,
`acceptedRunExtraction`,
`branchZeroBCSBound`, `branchOneBCSBound`, and `branchTwoBCSBound`, together
with the other named implementation and cited cryptographic premises below. -/
theorem conditional_deployed_false_accept_work_normalized_le
    {Run Schedule RustBoundary : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run)
    [MeasureTheory.IsProbabilityMeasure measure]
    (accepts : V5PublicStatement → Run → Prop)
    (branchZeroFailure branchOneFailure branchTwoFailure :
      V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : SpendDigest → SpendDigest}
    {deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest}
    {deployedNullifier : SpendDigest → SpendDigest → SpendDigest}
    {deployedNode : SpendDigest → SpendDigest → SpendDigest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (acceptedRunExtraction : AcceptedRunExtractsTrace accepts
      (deployedFailureUnion branchZeroFailure branchOneFailure
        branchTwoFailure) rc)
    (statement : V5PublicStatement)
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualBatchEventProbability : Schedule → ℝ)
    (widthDeployment : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability)
    (schedule : Schedule) (scheduleAccepted : acceptedSchedule schedule)
    (epsRound : ℝ) (epsRoundNonnegative : 0 ≤ epsRound)
    (interactiveFailureDecomposition : epsRound ≤
      actualBatchEventProbability schedule + correctedNonBatchRoundError)
    (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary →
      AspisV5NonceWorkAuthentication.V5PublicMessageBoundary)
    (semantics :
      AspisV5NonceWorkAuthentication.STwoBCSIOPRoundSemantics rustRoundTrace)
    (rustInitialEnsembleM0Correspondence : Prop)
    (randomOracleAndFiatShamirApplicability : Prop)
    (pcsAndMerkleAuthenticationApplicability : Prop)
    (citedBCSAndCMSApplicability : Prop)
    (bcsDeployment : M0ExcludedBCSDeploymentPremises
      (30 : ℝ) rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability)
    (capErr T : ℝ)
    (branchZeroBCSBound :
      measure.real (branchFailureEvent branchZeroFailure statement) / T ≤
        bcsError epsRound T 30 capErr)
    (branchOneBCSBound :
      measure.real (branchFailureEvent branchOneFailure statement) / T ≤
        bcsError epsRound T 30 capErr)
    (branchTwoBCSBound :
      measure.real (branchFailureEvent branchTwoFailure statement) / T ≤
        bcsError epsRound T 30 capErr)
    (capErrNonnegative : 0 ≤ capErr) (capErrBound : capErr ≤ roCapErr)
    (queryBudgetAtLeastOne : 1 ≤ T) (queryBudgetAtMost128Bits : T ≤ 2 ^ 128) :
    measure.real (falseAcceptanceEvent accepts statement deployedOwner
        deployedNote deployedNullifier deployedNode) / T ≤
      1 / 2 ^ 100 := by
  have queryBudgetPositive : 0 < T :=
    lt_of_lt_of_le one_pos queryBudgetAtLeastOne
  have branchUnionProbabilityBound :=
    deployed_failure_union_probability_le_branch_sum measure
      branchZeroFailure branchOneFailure branchTwoFailure statement
  have normalizedBranchUnionBound :
      measure.real (deployedFailureUnionEvent branchZeroFailure
          branchOneFailure branchTwoFailure statement) / T ≤
        measure.real (branchFailureEvent branchZeroFailure statement) / T +
          measure.real (branchFailureEvent branchOneFailure statement) / T +
          measure.real (branchFailureEvent branchTwoFailure statement) / T := by
    calc
      measure.real (deployedFailureUnionEvent branchZeroFailure
          branchOneFailure branchTwoFailure statement) / T ≤
          (measure.real (branchFailureEvent branchZeroFailure statement) +
            measure.real (branchFailureEvent branchOneFailure statement) +
            measure.real (branchFailureEvent branchTwoFailure statement)) / T :=
        div_le_div_of_nonneg_right branchUnionProbabilityBound
          queryBudgetPositive.le
      _ = measure.real (branchFailureEvent branchZeroFailure statement) / T +
            measure.real (branchFailureEvent branchOneFailure statement) / T +
            measure.real (branchFailureEvent branchTwoFailure statement) / T := by
        ring
  have branchUnionEndpoint :
      measure.real (deployedFailureUnionEvent branchZeroFailure
          branchOneFailure branchTwoFailure statement) / T ≤
        1 / 2 ^ 100 :=
    corrected_selected_good_release_endpoint
      acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability widthDeployment schedule scheduleAccepted
      epsRound epsRoundNonnegative interactiveFailureDecomposition
      (30 : ℝ) rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability citedBCSAndCMSApplicability
      bcsDeployment
      (measure.real (deployedFailureUnionEvent branchZeroFailure
        branchOneFailure branchTwoFailure statement) / T)
      (measure.real (branchFailureEvent branchZeroFailure statement) / T)
      (measure.real (branchFailureEvent branchOneFailure statement) / T)
      (measure.real (branchFailureEvent branchTwoFailure statement) / T)
      capErr T normalizedBranchUnionBound branchZeroBCSBound
      branchOneBCSBound branchTwoBCSBound capErrNonnegative capErrBound
      queryBudgetAtLeastOne queryBudgetAtMost128Bits
  have falseAcceptProbabilityBound :
      measure.real (falseAcceptanceEvent accepts statement deployedOwner
          deployedNote deployedNullifier deployedNode) ≤
        measure.real (deployedFailureUnionEvent branchZeroFailure
          branchOneFailure branchTwoFailure statement) :=
    MeasureTheory.measureReal_mono
      (false_accept_event_subset_deployed_failure_union accepts
        branchZeroFailure branchOneFailure branchTwoFailure rc poseidon
        acceptedRunExtraction statement)
  exact (div_le_div_of_nonneg_right falseAcceptProbabilityBound
    queryBudgetPositive.le).trans branchUnionEndpoint

/-! ## Ordinary probability reading -/

/-- Converting a work-normalized false-acceptance bound to an ordinary
probability bound costs the query budget `T`.  The extra `min 1` records the
fact that a probability cannot exceed one.  Apply this theorem to the result
of `conditional_deployed_false_accept_work_normalized_le`. -/
theorem conditional_deployed_false_accept_raw_le_min
    {Run : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run)
    [MeasureTheory.IsProbabilityMeasure measure]
    (accepts : V5PublicStatement → Run → Prop)
    (statement : V5PublicStatement)
    (deployedOwner : SpendDigest → SpendDigest)
    (deployedNote : SpendDigest → SpendField → SpendField →
      SpendDigest → SpendDigest)
    (deployedNullifier : SpendDigest → SpendDigest → SpendDigest)
    (deployedNode : SpendDigest → SpendDigest → SpendDigest)
    (T : ℝ) (queryBudgetAtLeastOne : 1 ≤ T)
    (workNormalizedBound :
      measure.real (falseAcceptanceEvent accepts statement deployedOwner
          deployedNote deployedNullifier deployedNode) / T ≤
        1 / 2 ^ 100) :
    measure.real (falseAcceptanceEvent accepts statement deployedOwner
        deployedNote deployedNullifier deployedNode) ≤
      min 1 (T / 2 ^ 100) := by
  have queryBudgetPositive : 0 < T :=
    lt_of_lt_of_le one_pos queryBudgetAtLeastOne
  have queryScaledBound :
      measure.real (falseAcceptanceEvent accepts statement deployedOwner
          deployedNote deployedNullifier deployedNode) ≤
        T / 2 ^ 100 := by
    calc
      measure.real (falseAcceptanceEvent accepts statement deployedOwner
          deployedNote deployedNullifier deployedNode) ≤
          (1 / 2 ^ 100) * T :=
        (div_le_iff₀ queryBudgetPositive).mp workNormalizedBound
      _ = T / 2 ^ 100 := by ring
  exact le_min MeasureTheory.measureReal_le_one queryScaledBound

/-! ## Axiom audit -/

#print axioms deployed_failure_union_event_eq
#print axioms false_accept_event_subset_deployed_failure_union
#print axioms false_accept_measure_le_deployed_failure_union
#print axioms deployed_failure_union_probability_le_branch_sum
#print axioms false_accept_probability_le_branch_sum
#print axioms conditional_deployed_false_accept_work_normalized_le
#print axioms conditional_deployed_false_accept_raw_le_min

end AspisV5DeployedFalseAcceptance
