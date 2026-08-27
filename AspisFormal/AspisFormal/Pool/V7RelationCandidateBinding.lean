import AspisFormal.V6AcceptedPathObligations
import AspisFormal.V5FriRelationCandidateBridge

/-!
# V7 query-injected four-round relation binding

Tag 73 has one relation shape that is not present in Tag 67: after the first
`1024 -> 256` fold, the verifier adds a random linear combination of the
sixteen authenticated query values to both the running scalar and the folded
weight vector.  The remaining three relation rounds then fold the disclosed
256-vector to four values.

This file models that shape directly.  All candidate values, dual weight
folds, claimed degree-six polynomials, and scalar discrepancies are
definitions.  It proves that, when the disclosed 256-vector is the fold of a
fixed initial candidate and the installed query scalar is the dot product of
that same disclosed vector with the installed query weights, terminal
acceptance can hide a wrong initial/OOD claim only through:

* the named sequential two-OOD mixing cancellation; or
* one of four named degree-six relation-evaluation collisions.

No Fiat--Shamir, source-correspondence, Merkle, or decoding statement is made
here.  Those layers must supply the fixed execution below and prove the two
exact equalities just described.  In particular, query-batch exactness is not
silently folded into a generic relation premise.
-/

set_option autoImplicit false

namespace AspisPool.V7RelationCandidateBinding

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness
open AspisV6TranscriptRelationGrammar

variable {K : Type*} [Field K]

/-- The fixed candidate and all public linear functionals used by one actual
Tag-73 relation execution.  The second OOD functional and claim may depend on
the first mix, matching the deployed transcript order. -/
structure CandidateExecution (K : Type*) [Field K] where
  initialValues : Fin 1024 → K
  disclosedFinal256 : Fin 256 → K

  initialWeights : Fin 1024 → K
  initialClaim : K
  firstOodWeights : Fin 1024 → K
  firstOodClaim : K
  secondOodWeights : K → Fin 1024 → K
  secondOodClaim : K → K
  firstMix : K
  secondMix : K

  /-- The six transmitted coefficients in each compact relation round. -/
  relationParts : Fin 4 → RelationRoundParts K
  alpha : Fin 4 → K
  quarter : K
  quarterExact : quarter * 4 = (1 : K)

  /-- The post-round-zero query functional and the scalar installed by the
  authenticated query callback. -/
  queryWeights : Fin 256 → K
  queryClaim : K

namespace CandidateExecution

/-- The exact seven-coefficient polynomial reconstructed by the verifier from
the six transmitted coefficients and its incoming scalar. -/
def claimedCoefficients (execution : CandidateExecution K)
    (incoming : K) (round : Fin 4) : RelationCoefficients K :=
  fun coefficient => relationCoefficient execution.quarter incoming
    (execution.relationParts round) coefficient

/-- The reconstructed polynomial evaluates exactly as the compact verifier's
seven-term relation evaluator. -/
theorem eval_claimedCoefficients (execution : CandidateExecution K)
    (incoming : K) (round : Fin 4) :
    (relationPolynomial (claimedCoefficients execution incoming round)).eval
        (execution.alpha round) =
      relationEvaluate execution.quarter incoming
        (execution.relationParts round) (execution.alpha round) := by
  rw [eval_relationPolynomial]
  rfl

/-- Reconstructing coefficient four makes the arity-four boundary equal the
incoming scalar; there is no separate boundary premise. -/
theorem relationBoundary_claimedCoefficients
    (execution : CandidateExecution K) (incoming : K) (round : Fin 4) :
    relationBoundary (claimedCoefficients execution incoming round) = incoming := by
  have boundary := reconstructed_relation_quartic_has_exact_boundary
    execution.quarter incoming (execution.relationParts round)
      execution.quarterExact
  simpa [relationBoundary, relationBoundaryFromParts, claimedCoefficients,
    relationCoefficient, mul_comm] using boundary

/-- The characteristic does not divide four, as witnessed by the deployed
quarter inverse. -/
theorem four_ne_zero (execution : CandidateExecution K) : (4 : K) ≠ 0 := by
  intro hfour
  have quarterExact := execution.quarterExact
  rw [hfour, mul_zero] at quarterExact
  exact zero_ne_one quarterExact

/-- Initial weights after the two sequential circle-OOD tensors. -/
def weightsAfterOod (execution : CandidateExecution K) : Fin 1024 → K :=
  mixedWeights (n := 256) execution.initialWeights execution.firstOodWeights
    execution.secondOodWeights execution.firstMix execution.secondMix

/-- Claimed scalar after the same two OOD mixes. -/
def claimAfterOod (execution : CandidateExecution K) : K :=
  execution.initialClaim + execution.firstMix * execution.firstOodClaim +
    execution.secondMix * execution.secondOodClaim execution.firstMix

/-- The first relation polynomial, reconstructed before `alpha[0]`. -/
def round0Claimed (execution : CandidateExecution K) : RelationCoefficients K :=
  claimedCoefficients execution execution.claimAfterOod 0

/-- Honest degree-six polynomial for the fixed initial candidate and the
post-OOD weights. -/
def round0Honest (execution : CandidateExecution K) : RelationCoefficients K :=
  polynomialForExtension 256 execution.weightsAfterOod execution.initialValues

/-- Candidate values after the committed `1024 -> 256` fold. -/
def foldedInitial256 (execution : CandidateExecution K) : Fin 256 → K :=
  coefficientFoldLayer 256 (execution.alpha 0) execution.initialValues

/-- Dual weights immediately after the committed fold, before query
injection. -/
def foldedOodWeights256 (execution : CandidateExecution K) : Fin 256 → K :=
  dualWeightFoldLayer 256 (execution.alpha 0) execution.weightsAfterOod

/-- Running scalar immediately after round zero, before query injection. -/
def claimAfterRound0 (execution : CandidateExecution K) : K :=
  relationEvaluate execution.quarter execution.claimAfterOod
    (execution.relationParts 0) (execution.alpha 0)

/-- The exact post-round-zero query-weight injection. -/
def weights1 (execution : CandidateExecution K) : Fin 256 → K :=
  fun index => execution.foldedOodWeights256 index + execution.queryWeights index

/-- The exact post-round-zero query-claim injection. -/
def claim1 (execution : CandidateExecution K) : K :=
  execution.claimAfterRound0 + execution.queryClaim

/-- Values after relation-only round one. -/
def values2 (execution : CandidateExecution K) : Fin 64 → K :=
  coefficientFoldLayer 64 (execution.alpha 1) execution.disclosedFinal256

/-- Weights after relation-only round one. -/
def weights2 (execution : CandidateExecution K) : Fin 64 → K :=
  dualWeightFoldLayer 64 (execution.alpha 1) execution.weights1

/-- Scalar after relation-only round one. -/
def claim2 (execution : CandidateExecution K) : K :=
  relationEvaluate execution.quarter execution.claim1
    (execution.relationParts 1) (execution.alpha 1)

/-- Values after relation-only round two. -/
def values3 (execution : CandidateExecution K) : Fin 16 → K :=
  coefficientFoldLayer 16 (execution.alpha 2) execution.values2

/-- Weights after relation-only round two. -/
def weights3 (execution : CandidateExecution K) : Fin 16 → K :=
  dualWeightFoldLayer 16 (execution.alpha 2) execution.weights2

/-- Scalar after relation-only round two. -/
def claim3 (execution : CandidateExecution K) : K :=
  relationEvaluate execution.quarter execution.claim2
    (execution.relationParts 2) (execution.alpha 2)

/-- Final four candidate values after relation-only round three. -/
def values4 (execution : CandidateExecution K) : Fin 4 → K :=
  coefficientFoldLayer 4 (execution.alpha 3) execution.values3

/-- Final four dual weights after relation-only round three. -/
def weights4 (execution : CandidateExecution K) : Fin 4 → K :=
  dualWeightFoldLayer 4 (execution.alpha 3) execution.weights3

/-- Scalar after the final relation round. -/
def claim4 (execution : CandidateExecution K) : K :=
  relationEvaluate execution.quarter execution.claim3
    (execution.relationParts 3) (execution.alpha 3)

/-- The disclosed vector really is the single natural fold of this fixed
initial candidate. -/
def Final256Matches (execution : CandidateExecution K) : Prop :=
  execution.disclosedFinal256 = execution.foldedInitial256

/-- The installed query scalar is the evaluation of the installed query
functional on the exact disclosed vector. -/
def QueryInjectionExact (execution : CandidateExecution K) : Prop :=
  execution.queryClaim =
    candidateClaim execution.queryWeights execution.disclosedFinal256

/-- The final four-value dot check performed by the verifier. -/
def RelationTerminalAccepts (execution : CandidateExecution K) : Prop :=
  candidateClaim execution.weights4 execution.values4 = execution.claim4

/-- Candidate dot products distribute over adding two weight vectors. -/
theorem candidateClaim_add_weights {n : Nat}
    (left right values : Fin n → K) :
    candidateClaim (fun index => left index + right index) values =
      candidateClaim left values + candidateClaim right values := by
  simp only [candidateClaim, mul_add, Finset.sum_add_distrib]

/-- The four claimed compact polynomials in their exact incoming-claim order. -/
def claimedAt (execution : CandidateExecution K) :
    Fin 4 → RelationCoefficients K
  | 0 => execution.round0Claimed
  | 1 => claimedCoefficients execution execution.claim1 1
  | 2 => claimedCoefficients execution execution.claim2 2
  | 3 => claimedCoefficients execution execution.claim3 3

/-- The honest candidate/weight convolution polynomial in each round. -/
def honestAt (execution : CandidateExecution K) :
    Fin 4 → RelationCoefficients K
  | 0 => execution.round0Honest
  | 1 => polynomialForExtension 64 execution.weights1 execution.disclosedFinal256
  | 2 => polynomialForExtension 16 execution.weights2 execution.values2
  | 3 => polynomialForExtension 4 execution.weights3 execution.values3

/-- Incoming scalar for each compact relation polynomial. -/
def incomingAt (execution : CandidateExecution K) : Fin 4 → K
  | 0 => execution.claimAfterOod
  | 1 => execution.claim1
  | 2 => execution.claim2
  | 3 => execution.claim3

/-- The exact scalar discrepancy trace.  Only round zero has OOD values; the
later three rounds have zero introduced errors. -/
noncomputable def discrepancyTrace
    (execution : CandidateExecution K) : FourRoundDiscrepancyTrace K where
  before := ![
    execution.initialClaim -
      candidateClaim execution.initialWeights execution.initialValues,
    execution.claim1 -
      candidateClaim execution.weights1 execution.disclosedFinal256,
    execution.claim2 - candidateClaim execution.weights2 execution.values2,
    execution.claim3 - candidateClaim execution.weights3 execution.values3,
    execution.claim4 - candidateClaim execution.weights4 execution.values4]
  firstValueError := ![
    execution.firstOodClaim -
      candidateClaim execution.firstOodWeights execution.initialValues,
    0, 0, 0]
  secondValueError := ![
    fun firstMix => execution.secondOodClaim firstMix -
      candidateClaim (execution.secondOodWeights firstMix)
        execution.initialValues,
    fun _ => 0, fun _ => 0, fun _ => 0]
  firstMix := ![execution.firstMix, 0, 0, 0]
  secondMix := ![execution.secondMix, 0, 0, 0]

/-- Round zero's mixed discrepancy is exactly the claimed incoming relation
boundary minus the fixed candidate's honest boundary. -/
theorem afterMix_zero (execution : CandidateExecution K) :
    execution.discrepancyTrace.afterMix 0 =
      execution.claimAfterOod -
        relationBoundary execution.round0Honest := by
  simpa [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace, claimAfterOod,
    round0Honest, weightsAfterOod]
    using mixed_discrepancy_eq_boundary_difference (n := 256)
      execution.initialValues execution.initialWeights execution.firstOodWeights
      execution.secondOodWeights execution.initialClaim execution.firstOodClaim
      execution.secondOodClaim execution.firstMix execution.secondMix
      execution.four_ne_zero

/-- In every relation round the post-mix discrepancy is exactly the incoming
scalar minus the honest candidate boundary.  For round zero this includes the
two adaptive OOD values; later rounds have no new OOD errors. -/
theorem afterMix_eq_incoming_sub_honest_boundary
    (execution : CandidateExecution K) (round : Fin 4) :
    execution.discrepancyTrace.afterMix round =
      execution.incomingAt round -
        relationBoundary (execution.honestAt round) := by
  fin_cases round
  · simpa [incomingAt, honestAt] using execution.afterMix_zero
  · simp [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace, incomingAt,
      honestAt]
    rw [relationBoundary_polynomialForExtension _ _ _ execution.four_ne_zero]
    rfl
  · simp [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace, incomingAt,
      honestAt]
    rw [relationBoundary_polynomialForExtension _ _ _ execution.four_ne_zero]
    rfl
  · simp [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace, incomingAt,
      honestAt]
    rw [relationBoundary_polynomialForExtension _ _ _ execution.four_ne_zero]
    rfl

/-- An actual alpha repair necessarily starts from a wrong incoming scalar;
this is the nonzeroness premise needed by the degree-six root bound. -/
theorem wrongIncoming_of_alphaRepair
    (execution : CandidateExecution K) (round : Fin 4)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.incomingAt round ≠ relationBoundary (execution.honestAt round) := by
  intro equal
  apply repair.1
  rw [execution.afterMix_eq_incoming_sub_honest_boundary round, equal, sub_self]

/-- With an exact disclosed fold and query injection, round zero's carried
discrepancy is exactly the claimed-minus-honest polynomial evaluation. -/
theorem nextError_zero (execution : CandidateExecution K)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact) :
    execution.discrepancyTrace.before 1 =
      (relationPolynomial execution.round0Claimed).eval (execution.alpha 0) -
        (relationPolynomial execution.round0Honest).eval (execution.alpha 0) := by
  change execution.claim1 -
      candidateClaim execution.weights1 execution.disclosedFinal256 =
    (relationPolynomial
        (claimedCoefficients execution execution.claimAfterOod 0)).eval
          (execution.alpha 0) -
      (relationPolynomial
        (polynomialForExtension 256 execution.weightsAfterOod
          execution.initialValues)).eval (execution.alpha 0)
  rw [eval_claimedCoefficients]
  rw [relationPolynomial_polynomialForExtension_eval]
  change execution.claimAfterRound0 + execution.queryClaim -
      candidateClaim
        (fun index => execution.foldedOodWeights256 index +
          execution.queryWeights index)
        execution.disclosedFinal256 =
    execution.claimAfterRound0 -
      candidateClaim execution.foldedOodWeights256 execution.foldedInitial256
  change execution.queryClaim =
    candidateClaim execution.queryWeights execution.disclosedFinal256 at queryExact
  change execution.disclosedFinal256 = execution.foldedInitial256 at finalMatches
  rw [candidateClaim_add_weights, queryExact, finalMatches]
  ring

/-- Round one's carried discrepancy is the exact polynomial-evaluation
difference. -/
theorem nextError_one (execution : CandidateExecution K) :
    execution.discrepancyTrace.before 2 =
      (relationPolynomial (execution.claimedAt 1)).eval (execution.alpha 1) -
        (relationPolynomial (execution.honestAt 1)).eval (execution.alpha 1) := by
  change execution.claim2 - candidateClaim execution.weights2 execution.values2 =
    (relationPolynomial
        (claimedCoefficients execution execution.claim1 1)).eval
          (execution.alpha 1) -
      (relationPolynomial
        (polynomialForExtension 64 execution.weights1
          execution.disclosedFinal256)).eval (execution.alpha 1)
  rw [eval_claimedCoefficients]
  rw [relationPolynomial_polynomialForExtension_eval]
  rfl

/-- Round two's carried discrepancy is the exact polynomial-evaluation
difference. -/
theorem nextError_two (execution : CandidateExecution K) :
    execution.discrepancyTrace.before 3 =
      (relationPolynomial (execution.claimedAt 2)).eval (execution.alpha 2) -
        (relationPolynomial (execution.honestAt 2)).eval (execution.alpha 2) := by
  change execution.claim3 - candidateClaim execution.weights3 execution.values3 =
    (relationPolynomial
        (claimedCoefficients execution execution.claim2 2)).eval
          (execution.alpha 2) -
      (relationPolynomial
        (polynomialForExtension 16 execution.weights2 execution.values2)).eval
          (execution.alpha 2)
  rw [eval_claimedCoefficients]
  rw [relationPolynomial_polynomialForExtension_eval]
  rfl

/-- Round three's carried discrepancy is the exact polynomial-evaluation
difference. -/
theorem nextError_three (execution : CandidateExecution K) :
    execution.discrepancyTrace.before 4 =
      (relationPolynomial (execution.claimedAt 3)).eval (execution.alpha 3) -
        (relationPolynomial (execution.honestAt 3)).eval (execution.alpha 3) := by
  change execution.claim4 - candidateClaim execution.weights4 execution.values4 =
    (relationPolynomial
        (claimedCoefficients execution execution.claim3 3)).eval
          (execution.alpha 3) -
      (relationPolynomial
        (polynomialForExtension 4 execution.weights3 execution.values3)).eval
          (execution.alpha 3)
  rw [eval_claimedCoefficients]
  rw [relationPolynomial_polynomialForExtension_eval]
  rfl

/-- Later rounds introduce no OOD errors, so a scalar mix cancellation there
is impossible. -/
theorem no_later_mixCancellation (execution : CandidateExecution K)
    (round : Fin 4) (positive : 0 < round.val) :
    ¬ execution.discrepancyTrace.MixCancellation round := by
  intro cancellation
  rcases cancellation with ⟨nontrivial, cancelled⟩
  have firstZero : execution.discrepancyTrace.firstValueError round = 0 := by
    fin_cases round <;> simp_all [discrepancyTrace]
  have secondZero :
      execution.discrepancyTrace.secondValueError round
        (execution.discrepancyTrace.firstMix round) = 0 := by
    fin_cases round <;> simp_all [discrepancyTrace]
  have beforeNonzero : execution.discrepancyTrace.before round.castSucc ≠ 0 := by
    rcases nontrivial with hbefore | hintroduced
    · exact hbefore
    · exact False.elim (hintroduced.elim (fun h => h firstZero)
        (fun h => h secondZero))
  apply beforeNonzero
  simpa [FourRoundDiscrepancyTrace.afterMix, firstZero, secondZero] using cancelled

/-- Fixed challenge set at which one claimed relation polynomial agrees with
the honest candidate polynomial. -/
noncomputable def relationCollisionSet (execution : CandidateExecution K)
    (round : Fin 4) [Fintype K] [DecidableEq K] : Finset K :=
  roundCollisionSet (execution.claimedAt round) (execution.honestAt round)

/-- Every scalar alpha repair is membership in the corresponding exact
degree-six collision set. -/
theorem alphaRepair_mem_relationCollisionSet
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (round : Fin 4)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.alpha round ∈ execution.relationCollisionSet round := by
  rcases repair with ⟨_, nextZero⟩
  simp only [relationCollisionSet, roundCollisionSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  fin_cases round
  · have difference := execution.nextError_zero finalMatches queryExact
    have nextZero' : execution.discrepancyTrace.before 1 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm
  · have difference := execution.nextError_one
    have nextZero' : execution.discrepancyTrace.before 2 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm
  · have difference := execution.nextError_two
    have nextZero' : execution.discrepancyTrace.before 3 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm
  · have difference := execution.nextError_three
    have nextZero' : execution.discrepancyTrace.before 4 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm

/-- The three post-query relation rounds expose their degree-six collision
sets without assuming either final-vector matching or exact query injection.
Those two premises are needed only for the round-zero handoff. -/
theorem later_alphaRepair_mem_relationCollisionSet
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K)
    (round : Fin 4) (later : 0 < round.val)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.alpha round ∈ execution.relationCollisionSet round := by
  rcases repair with ⟨_, nextZero⟩
  simp only [relationCollisionSet, roundCollisionSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  fin_cases round
  · simp at later
  · have difference := execution.nextError_one
    have nextZero' : execution.discrepancyTrace.before 2 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm
  · have difference := execution.nextError_two
    have nextZero' : execution.discrepancyTrace.before 3 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm
  · have difference := execution.nextError_three
    have nextZero' : execution.discrepancyTrace.before 4 = 0 := by
      simpa using nextZero
    rw [nextZero'] at difference
    simpa [claimedAt, honestAt] using sub_eq_zero.mp difference.symm

/-- A wrong incoming scalar has at most six repairing challenges in every
round. -/
theorem relationCollisionSet_card_le_six
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K) (round : Fin 4)
    (wrongIncoming : execution.incomingAt round ≠
      relationBoundary (execution.honestAt round)) :
    (execution.relationCollisionSet round).card ≤ 6 := by
  apply roundCollisionSet_card_le_six
    (execution.claimedAt round) (execution.honestAt round)
    (execution.incomingAt round)
  · fin_cases round
    · simpa [claimedAt, incomingAt, round0Claimed] using
        execution.relationBoundary_claimedCoefficients execution.claimAfterOod 0
    · simpa [claimedAt, incomingAt] using
        execution.relationBoundary_claimedCoefficients execution.claim1 1
    · simpa [claimedAt, incomingAt] using
        execution.relationBoundary_claimedCoefficients execution.claim2 2
    · simpa [claimedAt, incomingAt] using
        execution.relationBoundary_claimedCoefficients execution.claim3 3
  · exact wrongIncoming

/-- The exact canonical relation-alpha failure surface: an actual scalar
repair is membership in a bad set of at most six challenges.  Equality of
already-equal claimed/honest polynomials is deliberately not a failure. -/
theorem alphaRepair_has_degreeSix_bad_set
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (round : Fin 4)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.alpha round ∈ execution.relationCollisionSet round ∧
      (execution.relationCollisionSet round).card ≤ 6 := by
  exact ⟨
    execution.alphaRepair_mem_relationCollisionSet finalMatches queryExact
      round repair,
    execution.relationCollisionSet_card_le_six round
      (execution.wrongIncoming_of_alphaRepair round repair)⟩

/-- Final terminal acceptance makes the last scalar discrepancy zero. -/
theorem terminal_discrepancy_zero (execution : CandidateExecution K)
    (terminal : execution.RelationTerminalAccepts) :
    execution.discrepancyTrace.before 4 = 0 := by
  change execution.claim4 -
      candidateClaim execution.weights4 execution.values4 = 0
  rw [← terminal]
  exact sub_self _

/-- If the discrepancy immediately after query injection is nonzero but the
literal terminal comparison accepts, one of rounds one, two, or three must
repair it.  No round-zero final-vector or query-exactness premise is used. -/
theorem later_alphaRepair_of_before_one_ne_terminal
    (execution : CandidateExecution K)
    (beforeOne : execution.discrepancyTrace.before 1 ≠ 0)
    (terminal : execution.RelationTerminalAccepts) :
    ∃ round : Fin 4, 0 < round.val ∧
      execution.discrepancyTrace.AlphaRepair round := by
  have afterOne : execution.discrepancyTrace.afterMix 1 ≠ 0 := by
    simpa [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace] using
      beforeOne
  by_cases beforeTwo : execution.discrepancyTrace.before 2 = 0
  · exact ⟨1, by decide, afterOne, by simpa using beforeTwo⟩
  have afterTwo : execution.discrepancyTrace.afterMix 2 ≠ 0 := by
    simpa [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace] using
      beforeTwo
  by_cases beforeThree : execution.discrepancyTrace.before 3 = 0
  · exact ⟨2, by decide, afterTwo, by simpa using beforeThree⟩
  have afterThree : execution.discrepancyTrace.afterMix 3 ≠ 0 := by
    simpa [FourRoundDiscrepancyTrace.afterMix, discrepancyTrace] using
      beforeThree
  exact ⟨3, by decide, afterThree, by
    simpa using execution.terminal_discrepancy_zero terminal⟩

/-- A later repair is membership in one exact degree-six set. -/
theorem later_alphaRepair_has_degreeSix_bad_set
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K)
    (round : Fin 4) (later : 0 < round.val)
    (repair : execution.discrepancyTrace.AlphaRepair round) :
    execution.alpha round ∈ execution.relationCollisionSet round ∧
      (execution.relationCollisionSet round).card ≤ 6 := by
  exact ⟨execution.later_alphaRepair_mem_relationCollisionSet round later repair,
    execution.relationCollisionSet_card_le_six round
      (execution.wrongIncoming_of_alphaRepair round repair)⟩

/-- Outside the exact two-OOD cancellation and all four actual alpha-repair
events, terminal acceptance forces the initial and both OOD claims to be the
fixed candidate's true linear-functional values. -/
theorem initial_and_ood_claims_exact_outside_collisions
    [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K)
    (_finalMatches : execution.Final256Matches)
    (_queryExact : execution.QueryInjectionExact)
    (terminal : execution.RelationTerminalAccepts)
    (noOodCancellation :
      ¬ execution.discrepancyTrace.MixCancellation 0)
    (noAlphaRepair : ∀ round : Fin 4,
      ¬ execution.discrepancyTrace.AlphaRepair round) :
    execution.initialClaim =
        candidateClaim execution.initialWeights execution.initialValues ∧
      execution.firstOodClaim =
        candidateClaim execution.firstOodWeights execution.initialValues ∧
      execution.secondOodClaim execution.firstMix =
        candidateClaim (execution.secondOodWeights execution.firstMix)
          execution.initialValues := by
  have noFalse : ¬ execution.discrepancyTrace.HasInitialOrIntroducedError := by
    intro falseData
    obtain ⟨round, repair⟩ :=
      execution.discrepancyTrace.terminal_zero_has_repair
        (execution.terminal_discrepancy_zero terminal) falseData
    rcases repair with mixRepair | alphaRepair
    · by_cases roundZero : round.val = 0
      · have : round = 0 := Fin.ext roundZero
        subst round
        exact noOodCancellation mixRepair
      · exact execution.no_later_mixCancellation round (Nat.pos_of_ne_zero roundZero)
          mixRepair
    · exact noAlphaRepair round alphaRepair
  have initialZero : execution.discrepancyTrace.before 0 = 0 := by
    by_contra initialNonzero
    exact noFalse (Or.inl initialNonzero)
  have firstZero : execution.discrepancyTrace.firstValueError 0 = 0 := by
    by_contra firstNonzero
    exact noFalse (Or.inr ⟨0, Or.inl firstNonzero⟩)
  have secondZero : execution.discrepancyTrace.secondValueError 0
      execution.firstMix = 0 := by
    by_contra secondNonzero
    exact noFalse (Or.inr ⟨0, Or.inr (by simpa [discrepancyTrace] using secondNonzero)⟩)
  exact ⟨
    sub_eq_zero.mp (by simpa [discrepancyTrace] using initialZero),
    sub_eq_zero.mp (by simpa [discrepancyTrace] using firstZero),
    sub_eq_zero.mp (by simpa [discrepancyTrace] using secondZero)⟩

/-! ## Audit -/

#print axioms relationBoundary_claimedCoefficients
#print axioms afterMix_zero
#print axioms afterMix_eq_incoming_sub_honest_boundary
#print axioms wrongIncoming_of_alphaRepair
#print axioms nextError_zero
#print axioms alphaRepair_mem_relationCollisionSet
#print axioms later_alphaRepair_mem_relationCollisionSet
#print axioms relationCollisionSet_card_le_six
#print axioms alphaRepair_has_degreeSix_bad_set
#print axioms later_alphaRepair_of_before_one_ne_terminal
#print axioms later_alphaRepair_has_degreeSix_bad_set
#print axioms initial_and_ood_claims_exact_outside_collisions

end CandidateExecution
end AspisPool.V7RelationCandidateBinding
