import AspisFormal.V5ComponentCQM31TowerExact
import AspisFormal.V5CompatibilityCandidateTimingBridge
import AspisFormal.V5PrefixDependentCandidateSecurity
import AspisFormal.V5RefinedAcceptedFalseAccounting
import AspisFormal.V5TerminalFixedInitialListSecurity

/-!
# Exact terminal-candidate event

The refined accepted-false theorem previously accepted four set-containment
premises saying that the sumcheck-repair, helper, equality-point, and theta
events all land in one terminal-candidate event.  This file constructs that
event and proves those containments.

For each selected decoder candidate, the event uses the exact bad sets already
defined by the Lean terminal model.  A supplied causal message plan connects
the accepted ten-round wire and its fixed-polynomial reference trace to the
adaptive degree-27 bad set.  No probability or source equality is assumed by
the containment theorem.
-/

namespace AspisV5TerminalCandidateEventBridge

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CryptographicAssumptions
open AspisV5CompatibilityCandidateTimingBridge
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriInitialListBound
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5PrefixDependentCandidateSecurity
open AspisV5RefinedAcceptedFalseAccounting
open AspisV5RefinedRawCoreAccounting
open AspisV5SequentialTerminalChallengeBound
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5Tag67FixedCandidateTiming
open AspisV5TerminalFixedInitialListSecurity
open Module

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The literal Rust-compatible four-limb tower has the cardinality used by
the numerical soundness ledger. -/
theorem qm31Exact_card_cast_eq_soundness_field :
    (Fintype.card AspisV5ComponentCQM31TowerExact.QM31Exact : Real) =
      AspisSoundnessLedger.FIELD := by
  rw [AspisV5ComponentCQM31TowerExact.qm31Exact_card]
  norm_num [AspisV5ComponentCQM31TowerExact.P, AspisSoundnessLedger.FIELD]

/-- Short name for the decoder list fixed by one committed prefix. -/
abbrev PrefixFixedInitialCandidate
    {K Prefix : Type*} [Field K] [Fintype K] [DecidableEq K]
    (encoders : CodeEncoders K) (layer0Of : Prefix → Word0 K)
    (committedPrefix : Prefix) :=
  FixedInitialCandidate encoders (layer0Of committedPrefix)

/-- The exact terminal algebra plan carried by one projected candidate run. -/
noncomputable def fixedTerminalPlanAt
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data)
    (schedule : CandidateSchedule data.base) : FixedTerminalAlgebraPlan K :=
  let view := projection.viewOf (projection.runAt schedule)
  {
    basis := projection.basis
    constraintRows := view.constraintRows
    helper := view.helper
  }

/-- Per-candidate adaptive message plans together with the exact causality
fact needed to send a concrete repair into the prefix-selected bad set. -/
structure TerminalCandidatePlanProjection
    (Run Coins K Public Root : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) where
  sumcheckPlanOf : CandidateSchedule data.base →
    AdaptiveDegree27MessagePlan K
  causal : ∀ schedule,
    WireUsesAdaptiveDegree27Plan
      (boundary.wireOf (projection.runAt schedule))
      (boundary.referenceOf (projection.runAt schedule))
      (sumcheckPlanOf schedule)

/-- One concrete event containing all four terminal bad-set witnesses for all
candidates selected by an experiment outcome. -/
noncomputable def exactTerminalCandidateFailureSet
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    {boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection}
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary) : Set Coins :=
  {coins | ∃ candidate,
    let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
    let run := projection.runAt schedule
    let view := projection.viewOf run
    let terminal := fixedTerminalPlanAt projection schedule
    view.theta ∈ terminal.thetaBad ∨
      view.zerocheckPoint ∈ terminal.pointBad view.theta ∨
      view.mu ∈ terminal.muBad view.theta view.zerocheckPoint ∨
      ∃ round,
        (boundary.wireOf run).transcript.point round ∈
          (plans.sumcheckPlanOf schedule).badAt
            (challengeHistory (boundary.wireOf run).transcript.point round)}

set_option maxRecDepth 1000000 in
/-- The exact event above discharges all four containment fields in the
non-duplicated accepted-false accounting. -/
theorem exactTerminalCandidateFailureCoverage
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    {boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection}
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary) :
    TerminalCandidateFailureCoverage boundary
      (exactTerminalCandidateFailureSet plans) := by
  refine {
    tenRoundRepair := ?_
    helperCancellation := ?_
    zerocheckCollision := ?_
    thetaCollision := ?_
  }
  · intro coins failure
    rcases failure with ⟨candidate, repair⟩
    let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
    let run := projection.runAt schedule
    have hit := tenRoundRepair_hits_adaptive_badSet
      (boundary.wireOf run) (boundary.referenceOf run)
      (plans.sumcheckPlanOf schedule) (plans.causal schedule) repair
    refine ⟨candidate, ?_⟩
    exact Or.inr (Or.inr (Or.inr hit))
  · intro coins failure
    rcases failure with ⟨candidate, helper⟩
    let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
    let run := projection.runAt schedule
    let view := projection.viewOf run
    let terminal := fixedTerminalPlanAt projection schedule
    have member : view.mu ∈ terminal.muBad view.theta
        view.zerocheckPoint := by
      apply (terminal.helperCancellation_iff view.theta
        view.zerocheckPoint view.mu).mp
      simpa [terminal, fixedTerminalPlanAt, view, run] using helper
    exact ⟨candidate, Or.inr (Or.inr (Or.inl member))⟩
  · intro coins failure
    rcases failure with ⟨candidate, zerocheck⟩
    let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
    let run := projection.runAt schedule
    let view := projection.viewOf run
    let terminal := fixedTerminalPlanAt projection schedule
    have member : view.zerocheckPoint ∈ terminal.pointBad view.theta := by
      apply (terminal.zerocheckCollision_iff view.theta
        view.zerocheckPoint).mp
      simpa [terminal, fixedTerminalPlanAt, view, run] using zerocheck
    exact ⟨candidate, Or.inr (Or.inl member)⟩
  · intro coins failure
    rcases failure with ⟨candidate, theta⟩
    let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
    let run := projection.runAt schedule
    let view := projection.viewOf run
    let terminal := fixedTerminalPlanAt projection schedule
    have member : view.theta ∈ terminal.thetaBad := by
      apply (terminal.thetaCollision_iff view.theta).mp
      simpa [terminal, fixedTerminalPlanAt, view, run] using theta
    exact ⟨candidate, Or.inl member⟩

/-- Reduce the terminal-event probability obligation to the precise ideal
comparison that remains at the Fiat--Shamir boundary.  Candidate lists may
depend on the committed prefix; their number is averaged over prefixes and
only the at-most-240 candidates within a prefix are union-bounded. -/
theorem exactTerminalCandidateFailure_probability_le_raw_bound
    {Run Coins K Public Root Prefix : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    [Fintype Prefix] [Nonempty Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    {boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection}
    (measure : Measure Coins)
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary)
    (CandidateAt : Prefix → Type*)
    [candidateFintype : ∀ p : Prefix, Fintype (CandidateAt p)]
    (terminal : ∀ p, CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p,
      CandidateAt p → AdaptiveDegree27MessagePlan K)
    (candidateCap : ∀ p, Fintype.card (CandidateAt p) ≤ 240)
    (fieldCard : (Fintype.card K : Real) = AspisSoundnessLedger.FIELD)
    (sourceHashAndConditionalSampling :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        (prefixAveragedCandidateTerminalSubtotal Prefix CandidateAt terminal
          sumcheck : Real)) :
    measure.real (exactTerminalCandidateFailureSet plans) ≤
      rawCandidateTerminalBound := by
  calc
    measure.real (exactTerminalCandidateFailureSet plans) ≤
        (prefixAveragedCandidateTerminalSubtotal Prefix CandidateAt terminal
          sumcheck : Real) := sourceHashAndConditionalSampling
    _ ≤ (73200 : Real) / Fintype.card K :=
      prefixAveragedCandidateTerminalSubtotal_real_le_240 Prefix CandidateAt
        terminal sumcheck candidateCap
    _ = rawCandidateTerminalBound := by
      rw [fieldCard]
      rfl

set_option maxRecDepth 100000 in
/-- Specialization of the production sampling boundary to the decoder list
that is fixed by the committed layer-zero word before any terminal challenge.
The candidate cap is no longer caller supplied: the published encoder-distance
theorem gives at most 222 candidates, which is stronger than the conservative
release cap of 240.  The remaining premise is exactly the production
SHA-256/Fiat--Shamir conditional-sampling comparison. -/
theorem exactTerminalCandidateFailure_probability_le_raw_bound_fixed_list
    {Run Coins K Public Root Prefix : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    [Fintype Prefix] [Nonempty Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    {boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection}
    (measure : Measure Coins)
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary)
    (encoders : CodeEncoders K)
    (layer0Of : Prefix → Word0 K)
    (hdistance : InitialEncoderDistance encoders)
    (terminal : ∀ p, PrefixFixedInitialCandidate encoders layer0Of p →
      FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p, PrefixFixedInitialCandidate encoders layer0Of p →
      AdaptiveDegree27MessagePlan K)
    (fieldCard : (Fintype.card K : Real) = AspisSoundnessLedger.FIELD)
    (sourceHashAndConditionalSampling :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        (prefixAveragedCandidateTerminalSubtotal Prefix
          (PrefixFixedInitialCandidate encoders layer0Of) terminal
          sumcheck : Real)) :
    measure.real (exactTerminalCandidateFailureSet plans) ≤
      rawCandidateTerminalBound := by
  apply exactTerminalCandidateFailure_probability_le_raw_bound measure plans
    (PrefixFixedInitialCandidate encoders layer0Of) terminal sumcheck
    (fun p ↦ ?_) fieldCard sourceHashAndConditionalSampling
  exact (fixedInitialCandidate_fintype_card_le_222 encoders (layer0Of p)
    hdistance).trans (by omega)

set_option maxRecDepth 100000 in
/-- Release specialization using the candidate type in the accepted-false
experiment.  Its candidate cap is derived from the proved distance of the
exact released circle encoder and the theorem that the apparent
outcome-indexed list is fixed before the terminal challenges.  The caller
supplies neither a candidate cap nor a coding-theory premise. -/
theorem exactTerminalCandidateFailure_probability_le_raw_bound_released_candidates
    {Run Coins K Public Root Prefix : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    [Fintype Prefix] [Nonempty Prefix]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    {boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection}
    (measure : Measure Coins)
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary)
    (experiment : CompatibilityFriExperiment Prefix K)
    (terminal : ∀ p, experiment.CandidateAt p → FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p, experiment.CandidateAt p →
      AdaptiveDegree27MessagePlan K)
    (fieldCard : (Fintype.card K : Real) = AspisSoundnessLedger.FIELD)
    (sourceHashAndConditionalSampling :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        (prefixAveragedCandidateTerminalSubtotal Prefix
          experiment.CandidateAt terminal sumcheck : Real)) :
    measure.real (exactTerminalCandidateFailureSet plans) ≤
      rawCandidateTerminalBound := by
  apply exactTerminalCandidateFailure_probability_le_raw_bound measure plans
    experiment.CandidateAt terminal sumcheck (fun p ↦ ?_) fieldCard
    sourceHashAndConditionalSampling
  exact
    (AspisV5CompatibilityCandidateTimingBridge.CompatibilityFriExperiment.candidateAt_card_le_222
      experiment p).trans (by omega)

/-- Accepted-false accounting specialized to the concrete terminal-candidate
event.  Unlike the generic theorem, this statement has no separate
set-containment premise for the four terminal failure cases. -/
theorem acceptedFalse_probability_le_with_exact_terminal_event
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection)
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary)
    (terminalBound :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        rawCandidateTerminalBound) :
    measure.real data.base.acceptedFalse ≤
      (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.arithmeticResidualFailure +
        measure.real data.hashMerkleResidualFailure := by
  exact acceptedFalse_probability_le_two_pow_neg_75_plus_remaining_failures
    measure data connections projection boundary
    (exactTerminalCandidateFailureSet plans)
    (exactTerminalCandidateFailureCoverage plans) terminalBound

/-- Production transfer using the same constructed terminal event.  The
remaining transcript/hash union stays visible rather than being silently
included in the finite-field number. -/
theorem productionFalseSpend_probability_le_with_exact_terminal_event
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection)
    (plans : TerminalCandidatePlanProjection Run Coins K Public Root
      boundary)
    (terminalBound :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        rawCandidateTerminalBound) :
    measure.real production.productionFalseSpend ≤
      (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.arithmeticResidualFailure +
        measure.real data.hashMerkleResidualFailure +
        measure.real (totalFailure production.transcriptAndHashFailures) := by
  exact productionFalseSpend_probability_le_two_pow_neg_75_plus_remaining
    measure data connections production projection boundary
    (exactTerminalCandidateFailureSet plans)
    (exactTerminalCandidateFailureCoverage plans) terminalBound

#print axioms exactTerminalCandidateFailureCoverage
#print axioms qm31Exact_card_cast_eq_soundness_field
#print axioms exactTerminalCandidateFailure_probability_le_raw_bound
#print axioms
  exactTerminalCandidateFailure_probability_le_raw_bound_fixed_list
#print axioms
  exactTerminalCandidateFailure_probability_le_raw_bound_released_candidates
#print axioms acceptedFalse_probability_le_with_exact_terminal_event
#print axioms productionFalseSpend_probability_le_with_exact_terminal_event

end AspisV5TerminalCandidateEventBridge
