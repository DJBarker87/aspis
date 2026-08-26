import AspisFormal.Pool.V7K15FixedFamilyCausalCover

/-!
# Exact finite-root certificates for independent V7 K1.5 failures

After the decoder-selected semantic and copy branches have been moved into
their fixed pre-challenge families, five K1.5 branches remain independent of
that selection: `mu = 0`, inactive-slot `chi = 0`, two sequential OOD mixes,
four relation alphas, and the final three-row `kappa` batch.  This file ties
each literal V7 predicate to its exact finite set and proves their combined
ideal subtotal is `30 / |QM31|`.
-/

set_option autoImplicit false

namespace AspisPool.V7K15IndependentRootCertificates

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5RelationSumcheckSoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

/-- The unique zero challenge used by both explicit zero branches. -/
def zeroChallengeSet : Finset QM31Exact := {0}

@[simp] theorem zeroChallengeSet_card : zeroChallengeSet.card = 1 := by
  simp [zeroChallengeSet]

theorem muZero_mem_zeroChallengeSet {mu : QM31Exact} (zero : mu = 0) :
    mu ∈ zeroChallengeSet := by
  simp [zeroChallengeSet, zero]

theorem inactiveChi_mem_zeroChallengeSet {chi : QM31Exact}
    (collision : DeployedCopyInactiveSlotCollision chi) :
    chi ∈ zeroChallengeSet := by
  simpa [zeroChallengeSet, DeployedCopyInactiveSlotCollision] using collision

/-- Every actual V7 OOD cancellation is membership in its exact ordered
two-mix set. -/
theorem oodMixCancellation_has_exact_pair_set
    (trace : FourRoundDiscrepancyTrace QM31Exact)
    (round : Fin 4) :
    trace.MixCancellation round ↔
    (trace.firstMix round, trace.secondMix round) ∈
        falseSequentialTwoMixCancellationSet
          (trace.before round.castSucc)
          (trace.firstValueError round)
          (trace.secondValueError round) :=
  FourRoundDiscrepancyTrace.mixCancellation_iff_mem trace round

/-- The exact ordered two-mix event has at most twice the field cardinality. -/
theorem oodMixCancellation_exact_pair_set_card_le
    (trace : FourRoundDiscrepancyTrace QM31Exact) (round : Fin 4) :
    (falseSequentialTwoMixCancellationSet
      (trace.before round.castSucc)
      (trace.firstValueError round)
      (trace.secondValueError round)).card ≤
        2 * Fintype.card QM31Exact :=
  falseSequentialTwoMixCancellationSet_card_le
    (trace.before round.castSucc)
    (trace.firstValueError round)
    (trace.secondValueError round)

/-- Every actual relation-alpha repair has its literal fixed degree-six root
set.  The set is selected before that round's alpha is sampled. -/
theorem relationAlphaRepair_has_exact_six_root_set
    (execution : CandidateExecution QM31Exact)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (round : Fin 4)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.alpha round ∈ execution.relationCollisionSet round ∧
      (execution.relationCollisionSet round).card ≤ 6 :=
  execution.alphaRepair_has_degreeSix_bad_set finalMatches queryExact round
    repair

/-- Under the deployed nonzero sampler, an actual three-row collision is in
the exact degree-two nonzero root set. -/
theorem kappaPointRowCollision_has_exact_two_root_set
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (kappaNonzero : kappa ≠ 0)
    (collision : KappaPointRowCollision fields extraction point kappa) :
    kappa ∈ threeRowNonzeroCollisionSet
        (fun row => rowGammaDiscrepancy fields extraction point row) ∧
      (threeRowNonzeroCollisionSet
        (fun row => rowGammaDiscrepancy fields extraction point row)).card ≤
          2 := by
  constructor
  · simp only [threeRowNonzeroCollisionSet, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨kappaNonzero, collision.2⟩
  · exact fixed_kappa_collision_set_card_le_two fields extraction point
      collision.1

/-- Ideal subtotal of the five independent categories: two singleton field
events, one two-mix event, four degree-six alpha events, and one degree-two
kappa event. -/
noncomputable def independentK15IdealSubtotal : Rat :=
  (1 : Rat) / Fintype.card QM31Exact +
  (1 : Rat) / Fintype.card QM31Exact +
  (2 : Rat) / Fintype.card QM31Exact +
  4 * ((6 : Rat) / Fintype.card QM31Exact) +
  (2 : Rat) / Fintype.card QM31Exact

theorem independentK15IdealSubtotal_eq :
    independentK15IdealSubtotal =
      (30 : Rat) / Fintype.card QM31Exact := by
  unfold independentK15IdealSubtotal
  ring

/-- The independent K1.5 subtotal alone is below `2^-119`. -/
theorem independent_k15_subtotal_le_two_pow_neg_119 :
    (30 : Real) / Fintype.card QM31Exact ≤
      (1 : Real) / 2 ^ 119 := by
  rw [qm31Exact_card]
  norm_num [P]

#print axioms zeroChallengeSet_card
#print axioms muZero_mem_zeroChallengeSet
#print axioms inactiveChi_mem_zeroChallengeSet
#print axioms oodMixCancellation_has_exact_pair_set
#print axioms oodMixCancellation_exact_pair_set_card_le
#print axioms relationAlphaRepair_has_exact_six_root_set
#print axioms kappaPointRowCollision_has_exact_two_root_set
#print axioms independentK15IdealSubtotal_eq
#print axioms independent_k15_subtotal_le_two_pow_neg_119

end AspisPool.V7K15IndependentRootCertificates
