import AspisFormal.V5RefinedAdaptiveObservedTheftAccounting
import AspisFormal.V5RefinedWidth19DeploymentBridge

/-!
# Adaptive theft accounting with the raw width-19 bound

This file substitutes the checked raw width-19 arithmetic into the adaptive
theft theorem.  It deliberately does not divide by the 37-bit proof-of-work
condition: an attacker who submits an accepted proof has already performed
that work.

The resulting `2^-70` term combines the existing `2^-75` ideal subtotal with
the raw width-19 term `31 / 2^75`.  It is still a conditional theorem.  The
source/authentication, hash, credential, runtime, and victim-setup terms stay
visible rather than being assigned unsupported numerical values.
-/

namespace AspisV5AdaptiveTheftWidth19Bound

open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5AdaptiveObservedTheftGame
open AspisV5CryptographicAssumptions
open AspisV5FinalSecurityAccounting
open AspisV5FixedVictimTheftGame
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5PrefixDependentCandidateSecurity
open AspisV5RefinedAcceptedFalseAccounting
open AspisV5RefinedAdaptiveObservedTheftAccounting
open AspisV5RefinedWidth19DeploymentBridge
open AspisV5SequentialTerminalChallengeBound
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5TerminalCandidateEventBridge
open AspisV5TheftStateTransitionReduction

set_option maxRecDepth 100000 in
/-- Fully composed adaptive-theft statement for the deployed QM31 field and
released candidate family, with the raw width-19 event replaced by its checked
arithmetic bound.  Every remaining unproved probability is explicit. -/
theorem deployed_qm31_adaptive_theft_probability_le_two_pow_neg_70_plus_remaining
    {Run Sample AdversaryCoins PublicArtifact Execution Public Root Prefix
      WidthPrefix WidthCandidate : Type*}
    [MeasurableSpace Sample] [Fintype Prefix] [Nonempty Prefix]
    [Nonempty WidthCandidate]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Sample
      AspisV5ComponentCQM31TowerExact.QM31Exact rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (projection : StatementBindingProjectionData Run Sample
      AspisV5ComponentCQM31TowerExact.QM31Exact data)
    (boundary : MaskedBoundaryProjectionData Run Sample
      AspisV5ComponentCQM31TowerExact.QM31Exact Public Root
      (scheme := scheme) projection)
    (plans : TerminalCandidatePlanProjection Run Sample
      AspisV5ComponentCQM31TowerExact.QM31Exact Public Root boundary)
    (candidateExperiment : CompatibilityFriExperiment Prefix
      AspisV5ComponentCQM31TowerExact.QM31Exact)
    (terminal : ∀ p, candidateExperiment.CandidateAt p →
      FixedTerminalAlgebraPlan
        AspisV5ComponentCQM31TowerExact.QM31Exact)
    (sumcheck : ∀ p, candidateExperiment.CandidateAt p →
      AdaptiveDegree27MessagePlan
        AspisV5ComponentCQM31TowerExact.QM31Exact)
    (sourceHashAndConditionalSampling :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        (prefixAveragedCandidateTerminalSubtotal Prefix
          candidateExperiment.CandidateAt terminal sumcheck : Real))
    (deployedFirstFraudulentSpend : Sample → Prop)
    (runtime : RuntimeFailurePredicates Sample)
    (chain : AdaptiveChainFailures Sample)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      runtime chain deployedOwner deployedNote deployedNullifier deployedNode
      Accepts Commits victim experiment extractAfter)
    (coverage : RefinedAdaptiveHistoryCoverage production
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample})
    (width19Connection : Width19MeasuredEventConnection
      (Prefix := WidthPrefix)
      (K := AspisV5ComponentCQM31TowerExact.QM31Exact)
      (Candidate := WidthCandidate) measure data.width19Failure)
    (cryptoBudget : ConcreteSecurityBudget)
    (cryptoAssumed : AssumedConcreteSecurityBounds measure
      production.transcriptAndHashFailures cryptoBudget)
    (credentialBudget : Real)
    (credentialAssumed :
      measure.real {sample | CredentialRecoveryAfterObservationEvent Accepts
        victim experiment extractAfter sample} ≤ credentialBudget)
    (runtimeBudget : RuntimeSecurityBudget)
    (runtimeAssumed : AssumedRuntimeSecurityBounds measure runtime
      runtimeBudget) :
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
      (1 : Real) / 2 ^ 70 +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.hashMerkleResidualFailure +
        cryptoBudget.total + credentialBudget + runtimeBudget.total +
        measure.real {sample | chain.victimSetup sample} := by
  have base :=
    deployed_adaptive_first_fraudulent_spend_probability_le_deployed_qm31_budget
      measure data connections production projection boundary plans
      candidateExperiment terminal sumcheck sourceHashAndConditionalSampling
      deployedFirstFraudulentSpend runtime chain Accepts Commits victim
      experiment extractAfter connection coverage cryptoBudget cryptoAssumed
      credentialBudget credentialAssumed runtimeBudget runtimeAssumed
  have widthBound :=
    width19_completed_attempt_failure_probability_le_31_div_two_pow_75
      measure data.width19Failure width19Connection
  have combine :
      (1 : Real) / 2 ^ 75 + (31 : Real) / 2 ^ 75 =
        (1 : Real) / 2 ^ 70 := by
    norm_num
  linarith

#print axioms
  deployed_qm31_adaptive_theft_probability_le_two_pow_neg_70_plus_remaining

end AspisV5AdaptiveTheftWidth19Bound
