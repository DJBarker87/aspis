import AspisFormal.V5FriRelationCandidateBridge

/-!
# From an accepted Tag-67 relation execution to the counted repair event

This file proves the deterministic implication that was deliberately absent
from `V5RelationSumcheckSoundness`.

An execution below contains the values read by the relation verifier: the
initial linear claim, two OOD claims and one seven-coefficient polynomial in
each of four rounds, and the published four final coefficients.  It also
contains one coefficient candidate supplied by a FRI list decoder.  Candidate
coefficients are folded in the natural order used by the prover, while the
verifier weights are folded in the dual order used by `WeightAccumulator`.

For that concrete execution Lean derives, rather than assumes, both scalar
equations needed by the earlier finite count:

* after the two OOD mixes, the discrepancy is the accepted boundary minus the
  candidate polynomial's boundary;
* after alpha, the next discrepancy is the accepted polynomial evaluation
  minus the candidate polynomial evaluation.

If the boundary and terminal checks accept, the candidate reaches the
published final coefficients, and some initial or OOD claim is false for that
candidate, the twelve relation challenges therefore belong to
`adaptiveFixedCandidateRepairEvent`.

The last section lifts this proved fixed-candidate implication to a supplied
finite FRI list and records the concrete list cap `240`.  A decisive deployed
step is still unproved: accepted raw Tag-67 Merkle/FRI data must produce one
coherent matching candidate for which a false spend gives the explicit
candidate-relative mismatch below.  Replacing the ideal challenges by
Fiat--Shamir outputs is also external.  Neither step is asserted here.
-/

namespace AspisV5Tag67RelationListInclusion

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness

variable {K : Type*} [Field K]

/-! ## The messages and public weights of one round -/

/-- Data fixed before the current alpha in one relation round.

The first OOD functional and claim are fixed before `firstMix`.  The second
may depend on `firstMix`, matching the Tag-67 transcript order.  The claimed
polynomial may depend on both mixes, but not on alpha. -/
structure RelationRoundMessages (K Prefix : Type*) (n : Nat) where
  firstWeights : Prefix → Fin (4 * n) → K
  secondWeights : Prefix → K → Fin (4 * n) → K
  claimedFirst : Prefix → K
  claimedSecond : Prefix → K → K
  claimedPolynomial : Prefix → K × K → RelationCoefficients K

/-- The verifier's running claim after the two deployed OOD updates. -/
def RelationRoundMessages.claimAfterMixes
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (incomingClaim : K) (history : Prefix) (mixes : K × K) : K :=
  incomingClaim + mixes.1 * round.claimedFirst history +
    mixes.2 * round.claimedSecond history mixes.1

/-- The candidate polynomial built with the same post-OOD weights as the
verifier. -/
def RelationRoundMessages.candidatePolynomial
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (values incomingWeights : Fin (4 * n) → K)
    (history : Prefix) (mixes : K × K) : RelationCoefficients K :=
  polynomialForExtension n
    (mixedWeights incomingWeights (round.firstWeights history)
      (round.secondWeights history) mixes.1 mixes.2)
    values

/-- Candidate coefficients after this round's natural arity-four fold. -/
def RelationRoundMessages.nextValues
    {Prefix : Type*} {n : Nat}
    (_round : RelationRoundMessages K Prefix n)
    (values : Fin (4 * n) → K) (block : RelationRoundChallenges K) : Fin n → K :=
  coefficientFoldLayer n block.2 values

/-- Verifier weights after this round's dual arity-four fold. -/
def RelationRoundMessages.nextWeights
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (incomingWeights : Fin (4 * n) → K)
    (history : Prefix) (block : RelationRoundChallenges K) : Fin n → K :=
  dualWeightFoldLayer n block.2
    (mixedWeights incomingWeights (round.firstWeights history)
      (round.secondWeights history) block.1.1 block.1.2)

/-- Verifier claim carried after evaluating the accepted polynomial at alpha. -/
noncomputable def RelationRoundMessages.nextClaim
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (history : Prefix) (block : RelationRoundChallenges K) : K :=
  (relationPolynomial (round.claimedPolynomial history block.1)).eval block.2

/-- Exact boundary check performed in this round. -/
def RelationRoundMessages.Accepts
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (incomingClaim : K) (history : Prefix)
    (block : RelationRoundChallenges K) : Prop :=
  relationBoundary (round.claimedPolynomial history block.1) =
    round.claimAfterMixes incomingClaim history block.1

/-- Package the actual claimed/candidate quantities into the adaptive data
used by the finite counting theorem.  All discrepancy fields are definitions,
not hypotheses. -/
noncomputable def RelationRoundMessages.toAdaptive
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (values incomingWeights : Prefix → Fin (4 * n) → K)
    (incomingClaim : Prefix → K) : AdaptiveFixedCandidateRound K Prefix where
  incomingError history :=
    incomingClaim history - candidateClaim (incomingWeights history) (values history)
  firstValueError history :=
    round.claimedFirst history -
      candidateClaim (round.firstWeights history) (values history)
  secondValueError history firstMix :=
    round.claimedSecond history firstMix -
      candidateClaim (round.secondWeights history firstMix) (values history)
  relation :=
    { incomingClaim := fun input =>
        round.claimAfterMixes (incomingClaim input.1) input.1 input.2
      claimed := fun input => round.claimedPolynomial input.1 input.2
      honest := fun input =>
        round.candidatePolynomial (values input.1) (incomingWeights input.1)
          input.1 input.2 }

/-! ## Exact algebra for one round -/

/-- The modeled post-mix discrepancy is exactly claimed boundary minus the
candidate polynomial boundary.  This is derived from the concrete dot
products and mixed weights. -/
theorem RelationRoundMessages.afterMix_eq_boundary_difference
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (values incomingWeights : Prefix → Fin (4 * n) → K)
    (incomingClaim : Prefix → K)
    (history : Prefix) (mixes : K × K)
    (hfour : (4 : K) ≠ 0) :
    let data := round.toAdaptive values incomingWeights incomingClaim
    data.incomingError history + mixes.1 * data.firstValueError history +
        mixes.2 * data.secondValueError history mixes.1 =
      data.relation.incomingClaim (history, mixes) -
        relationBoundary (data.relation.honest (history, mixes)) := by
  dsimp [RelationRoundMessages.toAdaptive]
  exact mixed_discrepancy_eq_boundary_difference
    (values history) (incomingWeights history) (round.firstWeights history)
    (round.secondWeights history) (incomingClaim history)
    (round.claimedFirst history) (round.claimedSecond history)
    mixes.1 mixes.2 hfour

/-- The carried discrepancy after alpha is exactly claimed evaluation minus
candidate evaluation.  This is the second equation needed by the root bound. -/
theorem RelationRoundMessages.nextError_eq_evaluation_difference
    {Prefix : Type*} {n : Nat}
    (round : RelationRoundMessages K Prefix n)
    (values incomingWeights : Prefix → Fin (4 * n) → K)
    (history : Prefix) (block : RelationRoundChallenges K) :
    round.nextClaim history block -
        candidateClaim
          (round.nextWeights (incomingWeights history) history block)
          (round.nextValues (values history) block) =
      (relationPolynomial (round.claimedPolynomial history block.1)).eval block.2 -
        (relationPolynomial
          (round.candidatePolynomial (values history) (incomingWeights history)
            history block.1)).eval block.2 := by
  unfold RelationRoundMessages.nextClaim RelationRoundMessages.nextWeights
    RelationRoundMessages.nextValues RelationRoundMessages.candidatePolynomial
    candidateClaim
  exact evaluation_discrepancy_eq_folded_difference block.2 (values history)
    (mixedWeights (incomingWeights history) (round.firstWeights history)
      (round.secondWeights history) block.1.1 block.1.2)
    (round.claimedPolynomial history block.1)

/-! ## Four exact Tag-67 rounds -/

/-- Claimed Tag-67 relation execution together with one possible coefficient
vector for the first committed layer.  Later candidate layers, weights, and
claims are defined by the exact folds rather than supplied independently. -/
structure AcceptedCandidateExecution (K : Type*) where
  initialValues : Fin 1024 → K
  initialWeights : Fin 1024 → K
  initialClaim : K
  round0 : RelationRoundMessages K Unit 256
  round1 : RelationRoundMessages K (RelationRoundChallenges K) 64
  round2 : RelationRoundMessages K
    (RelationRoundChallenges K × RelationRoundChallenges K) 16
  round3 : RelationRoundMessages K
    ((RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) 4
  publishedFinal : TwelveRelationChallenges K → Fin 4 → K

def round0Block (challenges : TwelveRelationChallenges K) :
    RelationRoundChallenges K := challenges.1.1.1

def round1Block (challenges : TwelveRelationChallenges K) :
    RelationRoundChallenges K := challenges.1.1.2

def round2Block (challenges : TwelveRelationChallenges K) :
    RelationRoundChallenges K := challenges.1.2

def round3Block (challenges : TwelveRelationChallenges K) :
    RelationRoundChallenges K := challenges.2

/-- Candidate coefficients at the start of round one. -/
def AcceptedCandidateExecution.values1
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K) : Fin 256 → K :=
  execution.round0.nextValues execution.initialValues history

/-- Weights at the start of round one. -/
def AcceptedCandidateExecution.weights1
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K) : Fin 256 → K :=
  execution.round0.nextWeights execution.initialWeights () history

/-- Carried claim at the start of round one. -/
noncomputable def AcceptedCandidateExecution.claim1
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K) : K :=
  execution.round0.nextClaim () history

/-- Candidate coefficients at the start of round two. -/
def AcceptedCandidateExecution.values2
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K × RelationRoundChallenges K) :
    Fin 64 → K :=
  execution.round1.nextValues (execution.values1 history.1) history.2

/-- Weights at the start of round two. -/
def AcceptedCandidateExecution.weights2
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K × RelationRoundChallenges K) :
    Fin 64 → K :=
  execution.round1.nextWeights (execution.weights1 history.1) history.1 history.2

/-- Carried claim at the start of round two. -/
noncomputable def AcceptedCandidateExecution.claim2
    (execution : AcceptedCandidateExecution K)
    (history : RelationRoundChallenges K × RelationRoundChallenges K) : K :=
  execution.round1.nextClaim history.1 history.2

/-- Candidate coefficients at the start of round three. -/
def AcceptedCandidateExecution.values3
    (execution : AcceptedCandidateExecution K)
    (history : (RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) : Fin 16 → K :=
  execution.round2.nextValues (execution.values2 history.1) history.2

/-- Weights at the start of round three. -/
def AcceptedCandidateExecution.weights3
    (execution : AcceptedCandidateExecution K)
    (history : (RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) : Fin 16 → K :=
  execution.round2.nextWeights (execution.weights2 history.1) history.1 history.2

/-- Carried claim at the start of round three. -/
noncomputable def AcceptedCandidateExecution.claim3
    (execution : AcceptedCandidateExecution K)
    (history : (RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) : K :=
  execution.round2.nextClaim history.1 history.2

/-- Candidate's four coefficients after the last natural fold. -/
def AcceptedCandidateExecution.candidateFinal
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Fin 4 → K :=
  execution.round3.nextValues (execution.values3 challenges.1) challenges.2

/-- Final dual-folded verifier weights. -/
def AcceptedCandidateExecution.finalWeights
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Fin 4 → K :=
  execution.round3.nextWeights (execution.weights3 challenges.1)
    challenges.1 challenges.2

/-- Claim carried after the fourth alpha. -/
noncomputable def AcceptedCandidateExecution.finalClaim
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : K :=
  execution.round3.nextClaim challenges.1 challenges.2

/-- Every relation boundary and the final dot-product check accepts. -/
def AcceptedCandidateExecution.RelationAccepts
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  execution.round0.Accepts execution.initialClaim () (round0Block challenges) ∧
  execution.round1.Accepts (execution.claim1 (round0Block challenges))
    (round0Block challenges) (round1Block challenges) ∧
  execution.round2.Accepts (execution.claim2 challenges.1.1)
    challenges.1.1 (round2Block challenges) ∧
  execution.round3.Accepts (execution.claim3 challenges.1)
    challenges.1 (round3Block challenges) ∧
  candidateClaim (execution.finalWeights challenges)
    (execution.publishedFinal challenges) = execution.finalClaim challenges

/-- Standard FRI extraction supplies a candidate whose four final
coefficients equal the final polynomial bound into the transcript. -/
def AcceptedCandidateExecution.FinalMatches
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  execution.publishedFinal challenges = execution.candidateFinal challenges

/-- The four adaptive round records passed to the finite counting theorem. -/
noncomputable def AcceptedCandidateExecution.adaptiveData
    (execution : AcceptedCandidateExecution K) :
    AdaptiveFixedCandidateFourRounds K where
  round0 := execution.round0.toAdaptive
    (fun _ => execution.initialValues)
    (fun _ => execution.initialWeights)
    (fun _ => execution.initialClaim)
  round1 := execution.round1.toAdaptive execution.values1 execution.weights1
    execution.claim1
  round2 := execution.round2.toAdaptive execution.values2 execution.weights2
    execution.claim2
  round3 := execution.round3.toAdaptive execution.values3 execution.weights3
    execution.claim3

/-- The scalar discrepancies along this exact accepted execution. -/
noncomputable def AcceptedCandidateExecution.discrepancyTrace
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : FourRoundDiscrepancyTrace K where
  before := ![
    execution.initialClaim -
      candidateClaim execution.initialWeights execution.initialValues,
    execution.claim1 (round0Block challenges) -
      candidateClaim (execution.weights1 (round0Block challenges))
        (execution.values1 (round0Block challenges)),
    execution.claim2 challenges.1.1 -
      candidateClaim (execution.weights2 challenges.1.1)
        (execution.values2 challenges.1.1),
    execution.claim3 challenges.1 -
      candidateClaim (execution.weights3 challenges.1)
        (execution.values3 challenges.1),
    execution.finalClaim challenges -
      candidateClaim (execution.finalWeights challenges)
        (execution.candidateFinal challenges)]
  firstValueError := ![
    execution.round0.claimedFirst () -
      candidateClaim (execution.round0.firstWeights ()) execution.initialValues,
    execution.round1.claimedFirst (round0Block challenges) -
      candidateClaim (execution.round1.firstWeights (round0Block challenges))
        (execution.values1 (round0Block challenges)),
    execution.round2.claimedFirst challenges.1.1 -
      candidateClaim (execution.round2.firstWeights challenges.1.1)
        (execution.values2 challenges.1.1),
    execution.round3.claimedFirst challenges.1 -
      candidateClaim (execution.round3.firstWeights challenges.1)
        (execution.values3 challenges.1)]
  secondValueError := ![
    fun firstMix => execution.round0.claimedSecond () firstMix -
      candidateClaim (execution.round0.secondWeights () firstMix)
        execution.initialValues,
    fun firstMix =>
      execution.round1.claimedSecond (round0Block challenges) firstMix -
        candidateClaim
          (execution.round1.secondWeights (round0Block challenges) firstMix)
          (execution.values1 (round0Block challenges)),
    fun firstMix => execution.round2.claimedSecond challenges.1.1 firstMix -
      candidateClaim (execution.round2.secondWeights challenges.1.1 firstMix)
        (execution.values2 challenges.1.1),
    fun firstMix => execution.round3.claimedSecond challenges.1 firstMix -
      candidateClaim (execution.round3.secondWeights challenges.1 firstMix)
        (execution.values3 challenges.1)]
  firstMix := ![(round0Block challenges).1.1, (round1Block challenges).1.1,
    (round2Block challenges).1.1, (round3Block challenges).1.1]
  secondMix := ![(round0Block challenges).1.2, (round1Block challenges).1.2,
    (round2Block challenges).1.2, (round3Block challenges).1.2]

/-- A candidate is false for the relation execution when its initial claim or
one of its eight OOD claims differs from the claimed scalar. -/
def AcceptedCandidateExecution.FalseForCandidate
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  (execution.discrepancyTrace challenges).HasInitialOrIntroducedError

/-! ## Derived four-round discrepancy equations -/

/-- Round zero's post-mix scalar is the candidate boundary discrepancy. -/
theorem AcceptedCandidateExecution.afterMix_zero
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0) :
    (execution.discrepancyTrace challenges).afterMix 0 =
      (execution.adaptiveData).round0.relation.incomingClaim
          ((), (round0Block challenges).1) -
        relationBoundary
          ((execution.adaptiveData).round0.relation.honest
            ((), (round0Block challenges).1)) := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, FourRoundDiscrepancyTrace.afterMix,
    RelationRoundMessages.toAdaptive, round0Block] using
      execution.round0.afterMix_eq_boundary_difference
        (fun _ => execution.initialValues)
        (fun _ => execution.initialWeights)
        (fun _ => execution.initialClaim)
        () (round0Block challenges).1 hfour

/-- Round one's post-mix scalar is the candidate boundary discrepancy. -/
theorem AcceptedCandidateExecution.afterMix_one
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0) :
    (execution.discrepancyTrace challenges).afterMix 1 =
      (execution.adaptiveData).round1.relation.incomingClaim
          (round0Block challenges, (round1Block challenges).1) -
        relationBoundary
          ((execution.adaptiveData).round1.relation.honest
            (round0Block challenges, (round1Block challenges).1)) := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, FourRoundDiscrepancyTrace.afterMix,
    RelationRoundMessages.toAdaptive, round0Block, round1Block] using
      execution.round1.afterMix_eq_boundary_difference
        execution.values1 execution.weights1 execution.claim1
        (round0Block challenges) (round1Block challenges).1 hfour

/-- Round two's post-mix scalar is the candidate boundary discrepancy. -/
theorem AcceptedCandidateExecution.afterMix_two
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0) :
    (execution.discrepancyTrace challenges).afterMix 2 =
      (execution.adaptiveData).round2.relation.incomingClaim
          (challenges.1.1, (round2Block challenges).1) -
        relationBoundary
          ((execution.adaptiveData).round2.relation.honest
            (challenges.1.1, (round2Block challenges).1)) := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, FourRoundDiscrepancyTrace.afterMix,
    RelationRoundMessages.toAdaptive, round0Block, round1Block, round2Block] using
      execution.round2.afterMix_eq_boundary_difference
        execution.values2 execution.weights2 execution.claim2
        challenges.1.1 (round2Block challenges).1 hfour

/-- Round three's post-mix scalar is the candidate boundary discrepancy. -/
theorem AcceptedCandidateExecution.afterMix_three
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0) :
    (execution.discrepancyTrace challenges).afterMix 3 =
      (execution.adaptiveData).round3.relation.incomingClaim
          (challenges.1, (round3Block challenges).1) -
        relationBoundary
          ((execution.adaptiveData).round3.relation.honest
            (challenges.1, (round3Block challenges).1)) := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, FourRoundDiscrepancyTrace.afterMix,
    RelationRoundMessages.toAdaptive, round0Block, round1Block, round2Block,
    round3Block] using
      execution.round3.afterMix_eq_boundary_difference
        execution.values3 execution.weights3 execution.claim3
        challenges.1 (round3Block challenges).1 hfour

/-- Round zero's next scalar is the claimed-minus-candidate evaluation
difference at `alpha₀`. -/
theorem AcceptedCandidateExecution.nextError_zero
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) :
    (execution.discrepancyTrace challenges).before 1 =
      (relationPolynomial
        ((execution.adaptiveData).round0.relation.claimed
          ((), (round0Block challenges).1))).eval (round0Block challenges).2 -
      (relationPolynomial
        ((execution.adaptiveData).round0.relation.honest
          ((), (round0Block challenges).1))).eval (round0Block challenges).2 := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, RelationRoundMessages.toAdaptive,
    AcceptedCandidateExecution.claim1, AcceptedCandidateExecution.values1,
    AcceptedCandidateExecution.weights1, round0Block] using
      execution.round0.nextError_eq_evaluation_difference
        (fun _ => execution.initialValues)
        (fun _ => execution.initialWeights) () (round0Block challenges)

/-- Round one's next scalar is the claimed-minus-candidate evaluation
difference at `alpha₁`. -/
theorem AcceptedCandidateExecution.nextError_one
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) :
    (execution.discrepancyTrace challenges).before 2 =
      (relationPolynomial
        ((execution.adaptiveData).round1.relation.claimed
          (round0Block challenges, (round1Block challenges).1))).eval
            (round1Block challenges).2 -
      (relationPolynomial
        ((execution.adaptiveData).round1.relation.honest
          (round0Block challenges, (round1Block challenges).1))).eval
            (round1Block challenges).2 := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, RelationRoundMessages.toAdaptive,
    AcceptedCandidateExecution.claim2, AcceptedCandidateExecution.values2,
    AcceptedCandidateExecution.weights2, round0Block, round1Block] using
      execution.round1.nextError_eq_evaluation_difference
        execution.values1 execution.weights1
        (round0Block challenges) (round1Block challenges)

/-- Round two's next scalar is the claimed-minus-candidate evaluation
difference at `alpha₂`. -/
theorem AcceptedCandidateExecution.nextError_two
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) :
    (execution.discrepancyTrace challenges).before 3 =
      (relationPolynomial
        ((execution.adaptiveData).round2.relation.claimed
          (challenges.1.1, (round2Block challenges).1))).eval
            (round2Block challenges).2 -
      (relationPolynomial
        ((execution.adaptiveData).round2.relation.honest
          (challenges.1.1, (round2Block challenges).1))).eval
            (round2Block challenges).2 := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, RelationRoundMessages.toAdaptive,
    AcceptedCandidateExecution.claim3, AcceptedCandidateExecution.values3,
    AcceptedCandidateExecution.weights3, round0Block, round1Block,
    round2Block] using
      execution.round2.nextError_eq_evaluation_difference
        execution.values2 execution.weights2 challenges.1.1
        (round2Block challenges)

/-- Round three's next scalar is the claimed-minus-candidate evaluation
difference at `alpha₃`. -/
theorem AcceptedCandidateExecution.nextError_three
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) :
    (execution.discrepancyTrace challenges).before 4 =
      (relationPolynomial
        ((execution.adaptiveData).round3.relation.claimed
          (challenges.1, (round3Block challenges).1))).eval
            (round3Block challenges).2 -
      (relationPolynomial
        ((execution.adaptiveData).round3.relation.honest
          (challenges.1, (round3Block challenges).1))).eval
            (round3Block challenges).2 := by
  simpa [AcceptedCandidateExecution.discrepancyTrace,
    AcceptedCandidateExecution.adaptiveData, RelationRoundMessages.toAdaptive,
    AcceptedCandidateExecution.finalClaim,
    AcceptedCandidateExecution.candidateFinal,
    AcceptedCandidateExecution.finalWeights, round0Block, round1Block,
    round2Block, round3Block] using
      execution.round3.nextError_eq_evaluation_difference
        execution.values3 execution.weights3 challenges.1
        (round3Block challenges)

/-! ## Membership helpers for the counted event -/

section FiniteField

variable [Fintype K] [DecidableEq K]

theorem mem_repairTriples_of_mix
    {History : Type*} (data : AdaptiveFixedCandidateRound K History)
    (history : History) (block : RelationRoundChallenges K)
    (h : block.1 ∈ data.mixRepairPairs history) :
    block ∈ data.repairTriples history := by
  simp [AdaptiveFixedCandidateRound.repairTriples, h]

theorem mem_repairTriples_of_alpha
    {History : Type*}
    (data : AdaptiveFixedCandidateRound K History)
    (history : History) (block : RelationRoundChallenges K)
    (h : block.2 ∈
      data.relation.wrongIncomingCollisionSet (history, block.1)) :
    block ∈ data.repairTriples history := by
  apply Finset.mem_union_right
  rw [AdaptiveFixedCandidateRound.alphaRepairTriples,
    mem_extendByBadChallenge]
  exact h

theorem mem_adaptiveFixedCandidateRepairEvent_of_round0
    (data : AdaptiveFixedCandidateFourRounds K)
    (challenges : TwelveRelationChallenges K)
    (h : round0Block challenges ∈ data.round0.repairTriples ()) :
    challenges ∈ adaptiveFixedCandidateRepairEvent data := by
  unfold adaptiveFixedCandidateRepairEvent round0RepairBlocks
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  simpa [round0Block] using h

theorem mem_adaptiveFixedCandidateRepairEvent_of_round1
    (data : AdaptiveFixedCandidateFourRounds K)
    (challenges : TwelveRelationChallenges K)
    (h : round1Block challenges ∈
      data.round1.repairTriples (round0Block challenges)) :
    challenges ∈ adaptiveFixedCandidateRepairEvent data := by
  unfold adaptiveFixedCandidateRepairEvent round1RepairPrefixes
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
  apply Or.inl
  apply Or.inl
  apply Or.inr
  rw [mem_extendByBadChallenge]
  simpa [round0Block, round1Block] using h

theorem mem_adaptiveFixedCandidateRepairEvent_of_round2
    (data : AdaptiveFixedCandidateFourRounds K)
    (challenges : TwelveRelationChallenges K)
    (h : round2Block challenges ∈ data.round2.repairTriples challenges.1.1) :
    challenges ∈ adaptiveFixedCandidateRepairEvent data := by
  unfold adaptiveFixedCandidateRepairEvent round2RepairPrefixes
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
  apply Or.inl
  apply Or.inr
  rw [mem_extendByBadChallenge]
  simpa [round2Block] using h

theorem mem_adaptiveFixedCandidateRepairEvent_of_round3
    (data : AdaptiveFixedCandidateFourRounds K)
    (challenges : TwelveRelationChallenges K)
    (h : round3Block challenges ∈ data.round3.repairTriples challenges.1) :
    challenges ∈ adaptiveFixedCandidateRepairEvent data := by
  unfold adaptiveFixedCandidateRepairEvent round3RepairChallenges
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
  apply Or.inr
  rw [mem_extendByBadChallenge]
  simpa [round3Block] using h

omit [Fintype K] [DecidableEq K] in
/-- Relation terminal acceptance and the standard FRI final-coefficient match
make the candidate discrepancy zero after round three. -/
theorem AcceptedCandidateExecution.terminal_discrepancy_zero
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (haccepts : execution.RelationAccepts challenges)
    (hfinal : execution.FinalMatches challenges) :
    (execution.discrepancyTrace challenges).before 4 = 0 := by
  rcases haccepts with ⟨_, _, _, _, hterminal⟩
  unfold AcceptedCandidateExecution.FinalMatches at hfinal
  rw [hfinal] at hterminal
  change execution.finalClaim challenges -
      candidateClaim (execution.finalWeights challenges)
        (execution.candidateFinal challenges) = 0
  rw [hterminal]
  exact sub_self _

/-- A scalar repair in round zero is membership in the exact counted block. -/
theorem AcceptedCandidateExecution.round0Block_mem_repairTriples
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccept : execution.round0.Accepts execution.initialClaim ()
      (round0Block challenges))
    (hrepair :
      (execution.discrepancyTrace challenges).MixCancellation 0 ∨
        (execution.discrepancyTrace challenges).AlphaRepair 0) :
    round0Block challenges ∈
      (execution.adaptiveData).round0.repairTriples () := by
  rcases hrepair with hmix | halpha
  · apply mem_repairTriples_of_mix
    have hpairs :=
      ((execution.discrepancyTrace challenges).mixCancellation_iff_mem 0).mp hmix
    simpa [AdaptiveFixedCandidateRound.mixRepairPairs,
      AcceptedCandidateExecution.adaptiveData,
      AcceptedCandidateExecution.discrepancyTrace,
      RelationRoundMessages.toAdaptive, round0Block] using hpairs
  · apply mem_repairTriples_of_alpha
    apply (execution.adaptiveData).round0.relation
      |>.mem_wrongIncomingCollisionSet_of_discrepancy_equations
        ((), (round0Block challenges).1) (round0Block challenges).2
        ((execution.discrepancyTrace challenges).afterMix 0)
        ((execution.discrepancyTrace challenges).before 1)
    · simpa [AcceptedCandidateExecution.adaptiveData,
        RelationRoundMessages.toAdaptive,
        RelationRoundMessages.Accepts] using haccept
    · exact execution.afterMix_zero challenges hfour
    · exact execution.nextError_zero challenges
    · simpa [FourRoundDiscrepancyTrace.AlphaRepair] using halpha

/-- A scalar repair in round one is membership in the exact counted block. -/
theorem AcceptedCandidateExecution.round1Block_mem_repairTriples
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccept : execution.round1.Accepts
      (execution.claim1 (round0Block challenges)) (round0Block challenges)
      (round1Block challenges))
    (hrepair :
      (execution.discrepancyTrace challenges).MixCancellation 1 ∨
        (execution.discrepancyTrace challenges).AlphaRepair 1) :
    round1Block challenges ∈
      (execution.adaptiveData).round1.repairTriples
        (round0Block challenges) := by
  rcases hrepair with hmix | halpha
  · apply mem_repairTriples_of_mix
    have hpairs :=
      ((execution.discrepancyTrace challenges).mixCancellation_iff_mem 1).mp hmix
    simpa [AdaptiveFixedCandidateRound.mixRepairPairs,
      AcceptedCandidateExecution.adaptiveData,
      AcceptedCandidateExecution.discrepancyTrace,
      RelationRoundMessages.toAdaptive, round0Block, round1Block] using hpairs
  · apply mem_repairTriples_of_alpha
    apply (execution.adaptiveData).round1.relation
      |>.mem_wrongIncomingCollisionSet_of_discrepancy_equations
        (round0Block challenges, (round1Block challenges).1)
        (round1Block challenges).2
        ((execution.discrepancyTrace challenges).afterMix 1)
        ((execution.discrepancyTrace challenges).before 2)
    · simpa [AcceptedCandidateExecution.adaptiveData,
        RelationRoundMessages.toAdaptive,
        RelationRoundMessages.Accepts] using haccept
    · exact execution.afterMix_one challenges hfour
    · exact execution.nextError_one challenges
    · simpa [FourRoundDiscrepancyTrace.AlphaRepair] using halpha

/-- A scalar repair in round two is membership in the exact counted block. -/
theorem AcceptedCandidateExecution.round2Block_mem_repairTriples
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccept : execution.round2.Accepts
      (execution.claim2 challenges.1.1) challenges.1.1
      (round2Block challenges))
    (hrepair :
      (execution.discrepancyTrace challenges).MixCancellation 2 ∨
        (execution.discrepancyTrace challenges).AlphaRepair 2) :
    round2Block challenges ∈
      (execution.adaptiveData).round2.repairTriples challenges.1.1 := by
  rcases hrepair with hmix | halpha
  · apply mem_repairTriples_of_mix
    have hpairs :=
      ((execution.discrepancyTrace challenges).mixCancellation_iff_mem 2).mp hmix
    simpa [AdaptiveFixedCandidateRound.mixRepairPairs,
      AcceptedCandidateExecution.adaptiveData,
      AcceptedCandidateExecution.discrepancyTrace,
      RelationRoundMessages.toAdaptive, round0Block, round1Block,
      round2Block] using hpairs
  · apply mem_repairTriples_of_alpha
    apply (execution.adaptiveData).round2.relation
      |>.mem_wrongIncomingCollisionSet_of_discrepancy_equations
        (challenges.1.1, (round2Block challenges).1)
        (round2Block challenges).2
        ((execution.discrepancyTrace challenges).afterMix 2)
        ((execution.discrepancyTrace challenges).before 3)
    · simpa [AcceptedCandidateExecution.adaptiveData,
        RelationRoundMessages.toAdaptive,
        RelationRoundMessages.Accepts] using haccept
    · exact execution.afterMix_two challenges hfour
    · exact execution.nextError_two challenges
    · simpa [FourRoundDiscrepancyTrace.AlphaRepair] using halpha

/-- A scalar repair in round three is membership in the exact counted block. -/
theorem AcceptedCandidateExecution.round3Block_mem_repairTriples
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccept : execution.round3.Accepts
      (execution.claim3 challenges.1) challenges.1 (round3Block challenges))
    (hrepair :
      (execution.discrepancyTrace challenges).MixCancellation 3 ∨
        (execution.discrepancyTrace challenges).AlphaRepair 3) :
    round3Block challenges ∈
      (execution.adaptiveData).round3.repairTriples challenges.1 := by
  rcases hrepair with hmix | halpha
  · apply mem_repairTriples_of_mix
    have hpairs :=
      ((execution.discrepancyTrace challenges).mixCancellation_iff_mem 3).mp hmix
    simpa [AdaptiveFixedCandidateRound.mixRepairPairs,
      AcceptedCandidateExecution.adaptiveData,
      AcceptedCandidateExecution.discrepancyTrace,
      RelationRoundMessages.toAdaptive, round0Block, round1Block,
      round2Block, round3Block] using hpairs
  · apply mem_repairTriples_of_alpha
    apply (execution.adaptiveData).round3.relation
      |>.mem_wrongIncomingCollisionSet_of_discrepancy_equations
        (challenges.1, (round3Block challenges).1)
        (round3Block challenges).2
        ((execution.discrepancyTrace challenges).afterMix 3)
        ((execution.discrepancyTrace challenges).before 4)
    · simpa [AcceptedCandidateExecution.adaptiveData,
        RelationRoundMessages.toAdaptive,
        RelationRoundMessages.Accepts] using haccept
    · exact execution.afterMix_three challenges hfour
    · exact execution.nextError_three challenges
    · simpa [FourRoundDiscrepancyTrace.AlphaRepair] using halpha

/-! ## The decisive fixed-candidate inclusion -/

/-- An accepted relation execution that ends at the FRI candidate's published
final coefficients cannot hide a false candidate outside the counted event.

Unlike the earlier conditional scalar lemma, the two discrepancy equations
are not premises here: `afterMix_zero`--`afterMix_three` and
`nextError_zero`--`nextError_three` derive them from the candidate folds and
the verifier's dual weight folds. -/
theorem AcceptedCandidateExecution.accepted_false_mem_repairEvent
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccepts : execution.RelationAccepts challenges)
    (hfinal : execution.FinalMatches challenges)
    (hfalse : execution.FalseForCandidate challenges) :
    challenges ∈
      adaptiveFixedCandidateRepairEvent execution.adaptiveData := by
  have hterminal := execution.terminal_discrepancy_zero challenges haccepts hfinal
  have hrepair :=
    (execution.discrepancyTrace challenges).terminal_zero_has_repair
      hterminal hfalse
  rcases haccepts with ⟨haccept0, haccept1, haccept2, haccept3, _⟩
  rcases hrepair with ⟨round, hround⟩
  fin_cases round
  · apply mem_adaptiveFixedCandidateRepairEvent_of_round0
    exact execution.round0Block_mem_repairTriples challenges hfour
      haccept0 hround
  · apply mem_adaptiveFixedCandidateRepairEvent_of_round1
    exact execution.round1Block_mem_repairTriples challenges hfour
      haccept1 hround
  · apply mem_adaptiveFixedCandidateRepairEvent_of_round2
    exact execution.round2Block_mem_repairTriples challenges hfour
      haccept2 hround
  · apply mem_adaptiveFixedCandidateRepairEvent_of_round3
    exact execution.round3Block_mem_repairTriples challenges hfour
      haccept3 hround

/-! ## A coherent finite FRI candidate family -/

/-- No fixed initial candidate in the supplied family reaches the final
polynomial published by this transcript. -/
def NoCandidateFinalMatch
    {Candidate : Type*}
    (executions : Candidate → AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  ∀ candidate, ¬(executions candidate).FinalMatches challenges

/-- If a coherent fixed family contains a matching false candidate and the
relation checks accept, the transcript is in the union of the already-counted
fixed-candidate events.

"Coherent" matters here: each family member has one fixed initial
`Fin 1024` coefficient vector, and all four later vectors are its deterministic
folds.  This is one family of size `L`, not four independently chosen lists. -/
theorem matching_false_candidate_mem_boundedCandidateRepairEvent
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (executions : Candidate → AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccepts : ∀ candidate,
      (executions candidate).RelationAccepts challenges)
    (hfalse : ∀ candidate,
      (executions candidate).FalseForCandidate challenges)
    (hmatch : ∃ candidate,
      (executions candidate).FinalMatches challenges) :
    challenges ∈ boundedCandidateRepairEvent
      (fun candidate => (executions candidate).adaptiveData) := by
  classical
  rcases hmatch with ⟨candidate, hcandidate⟩
  have hmem := (executions candidate).accepted_false_mem_repairEvent
    challenges hfour (haccepts candidate) hcandidate (hfalse candidate)
  unfold boundedCandidateRepairEvent
  rw [Finset.mem_biUnion]
  exact ⟨candidate, Finset.mem_univ candidate, hmem⟩

/-- Exact deterministic decomposition before using any FRI theorem: either no
candidate in the supplied coherent family reaches the published final
polynomial, or the twelve relation challenges are in the repair-event union.

The first disjunct is the standard Merkle/FRI extraction-and-matching failure
boundary.  The custom relation implication in the second disjunct is proved
above and is not assumed here. -/
theorem accepted_false_candidate_family_decomposition
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (executions : Candidate → AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hfour : (4 : K) ≠ 0)
    (haccepts : ∀ candidate,
      (executions candidate).RelationAccepts challenges)
    (hfalse : ∀ candidate,
      (executions candidate).FalseForCandidate challenges) :
    NoCandidateFinalMatch executions challenges ∨
      challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (executions candidate).adaptiveData) := by
  classical
  by_cases hmatch : ∃ candidate,
      (executions candidate).FinalMatches challenges
  · exact Or.inr <| matching_false_candidate_mem_boundedCandidateRepairEvent
      executions challenges hfour haccepts hfalse hmatch
  · apply Or.inl
    intro candidate hcandidate
    exact hmatch ⟨candidate, hcandidate⟩

/-! ## List cap and an explicit raw-FRI boundary -/

/-- A coherent candidate family of cardinality at most 240 has repair-event
cardinality at most `240 * 32 * |K|^11`. -/
theorem boundedCandidateRepairEvent_card_le_240
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K)
    (hcard : Fintype.card Candidate ≤ 240) :
    (boundedCandidateRepairEvent data).card ≤
      240 * (32 * Fintype.card K ^ 11) := by
  exact (boundedCandidateRepairEvent_card_le data).trans
    (Nat.mul_le_mul_right (32 * Fintype.card K ^ 11) hcard)

/-- Uniform twelve-challenge mass for a coherent family of at most 240 fixed
initial candidates is at most `32 * 240 / |K|`. -/
theorem uniformBoundedCandidateRepairProbability_le_240
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate → AdaptiveFixedCandidateFourRounds K)
    (hcard : Fintype.card Candidate ≤ 240) :
    uniformBoundedCandidateRepairProbability data ≤
      (32 * 240 : ℚ) / Fintype.card K := by
  have hbase := uniformBoundedCandidateRepairProbability_le data
  have hnumerator :
      (32 * Fintype.card Candidate : ℚ) ≤ 32 * 240 := by
    exact_mod_cast Nat.mul_le_mul_left 32 hcard
  have hdenominator : (0 : ℚ) ≤ Fintype.card K := by positivity
  exact hbase.trans (div_le_div_of_nonneg_right hnumerator hdenominator)

/-- Full twelve-challenge executions selected by an external false-acceptance
predicate. -/
noncomputable def falseAcceptEvent
    (FalseAccept : TwelveRelationChallenges K → Prop) :
    Finset (TwelveRelationChallenges K) := by
  classical
  exact Finset.univ.filter FalseAccept

/-- The decisive still-unproved premise between a raw accepted FRI execution
and the custom relation proof.

`hextract` is intentionally stated in protocol terms: raw false acceptance
must yield one member of the fixed coherent candidate family for which the
relation checks accept, the final four coefficients match, and the candidate
is false for an initial/OOD claim.  It does **not** assume membership in a bad
challenge set.  The latter is the conclusion, proved through the exact
relation algebra above.  Establishing `hextract` for the deployed callback is
substantial: it must cover Merkle binding, coherent FRI list extraction, and
the semantic step from a false spend statement to `FalseForCandidate`. -/
theorem falseAcceptEvent_subset_boundedCandidateRepairEvent
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (executions : Candidate → AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate,
        (executions candidate).RelationAccepts challenges ∧
        (executions candidate).FinalMatches challenges ∧
        (executions candidate).FalseForCandidate challenges) :
    falseAcceptEvent FalseAccept ⊆
      boundedCandidateRepairEvent
        (fun candidate => (executions candidate).adaptiveData) := by
  classical
  intro challenges hfalseAccept
  have hfalse : FalseAccept challenges := by
    simpa [falseAcceptEvent] using hfalseAccept
  rcases hextract hfalse with ⟨candidate, haccepts, hfinal, hcandidateFalse⟩
  have hrepair := (executions candidate).accepted_false_mem_repairEvent
    challenges hfour haccepts hfinal hcandidateFalse
  unfold boundedCandidateRepairEvent
  rw [Finset.mem_biUnion]
  exact ⟨candidate, Finset.mem_univ candidate, hrepair⟩

/-- Under the explicit extraction/matching premise and the list cap 240, the
raw false-acceptance event occupies at most `240 * 32 * |K|^11` challenge
tuples. -/
theorem falseAcceptEvent_card_le_240
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (executions : Candidate → AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hcard : Fintype.card Candidate ≤ 240)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate,
        (executions candidate).RelationAccepts challenges ∧
        (executions candidate).FinalMatches challenges ∧
        (executions candidate).FalseForCandidate challenges) :
    (falseAcceptEvent FalseAccept).card ≤
      240 * (32 * Fintype.card K ^ 11) := by
  exact (Finset.card_le_card
    (falseAcceptEvent_subset_boundedCandidateRepairEvent
      executions FalseAccept hfour hextract)).trans
    (boundedCandidateRepairEvent_card_le_240
      (fun candidate => (executions candidate).adaptiveData) hcard)

/-- Exact uniform probability of the supplied raw false-acceptance predicate
in the twelve ideal relation challenges. -/
noncomputable def uniformFalseAcceptProbability
    (FalseAccept : TwelveRelationChallenges K → Prop) : ℚ :=
  (falseAcceptEvent FalseAccept).card /
    Fintype.card (TwelveRelationChallenges K)

/-- Conditional endpoint for the custom relation part: once standard FRI
extraction supplies a coherent list of at most 240 candidates and the
candidate-relative false condition, raw false acceptance has ideal uniform
mass at most `32 * 240 / |K|`. -/
theorem uniformFalseAcceptProbability_le_240
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (executions : Candidate → AcceptedCandidateExecution K)
    (FalseAccept : TwelveRelationChallenges K → Prop)
    (hfour : (4 : K) ≠ 0)
    (hcard : Fintype.card Candidate ≤ 240)
    (hextract : ∀ {challenges}, FalseAccept challenges →
      ∃ candidate,
        (executions candidate).RelationAccepts challenges ∧
        (executions candidate).FinalMatches challenges ∧
        (executions candidate).FalseForCandidate challenges) :
    uniformFalseAcceptProbability FalseAccept ≤
      (32 * 240 : ℚ) / Fintype.card K := by
  have hsubset := falseAcceptEvent_subset_boundedCandidateRepairEvent
    executions FalseAccept hfour hextract
  have hcardEvent : (falseAcceptEvent FalseAccept).card ≤
      (boundedCandidateRepairEvent
        (fun candidate => (executions candidate).adaptiveData)).card :=
    Finset.card_le_card hsubset
  have hdenominator : (0 : ℚ) ≤
      Fintype.card (TwelveRelationChallenges K) := by positivity
  calc
    uniformFalseAcceptProbability FalseAccept ≤
        uniformBoundedCandidateRepairProbability
          (fun candidate => (executions candidate).adaptiveData) := by
      unfold uniformFalseAcceptProbability
        uniformBoundedCandidateRepairProbability
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcardEvent)
        hdenominator
    _ ≤ (32 * 240 : ℚ) / Fintype.card K :=
      uniformBoundedCandidateRepairProbability_le_240
        (fun candidate => (executions candidate).adaptiveData) hcard

/-! ## Numeric check behind the list cap -/

/-- Guruswami--Sudan list-size expression used for `m = 10` and
`rho = 1/512`: `(m + 1/2) / sqrt(rho)`.  The external list-decoding theorem
and its applicability to this circle/arity-four FRI remain separate; only the
numeric specialization is checked here. -/
noncomputable def deployedGsListExpression : ℝ :=
  ((21 : ℝ) / 2) / Real.sqrt ((1 : ℝ) / 512)

/-- The deployed numeric expression is strictly below 240. -/
theorem deployed_gs_list_expression_lt_240 :
    deployedGsListExpression < 240 := by
  unfold deployedGsListExpression
  have hrho : (0 : ℝ) < 1 / 512 := by norm_num
  have hsqrt : (Real.sqrt ((1 : ℝ) / 512)) ^ 2 = 1 / 512 :=
    Real.sq_sqrt hrho.le
  have hsqrtpos : 0 < Real.sqrt ((1 : ℝ) / 512) :=
    Real.sqrt_pos.2 hrho
  rw [div_lt_iff₀ hsqrtpos]
  nlinarith

/-- Taking the natural ceiling of the checked expression still gives a list
cap at most 240. -/
theorem deployed_gs_list_ceiling_le_240 :
    ⌈deployedGsListExpression⌉₊ ≤ 240 := by
  rw [Nat.ceil_le]
  exact (deployed_gs_list_expression_lt_240).le

end FiniteField

#print axioms RelationRoundMessages.afterMix_eq_boundary_difference
#print axioms RelationRoundMessages.nextError_eq_evaluation_difference
#print axioms AcceptedCandidateExecution.accepted_false_mem_repairEvent
#print axioms matching_false_candidate_mem_boundedCandidateRepairEvent
#print axioms accepted_false_candidate_family_decomposition
#print axioms falseAcceptEvent_subset_boundedCandidateRepairEvent
#print axioms falseAcceptEvent_card_le_240
#print axioms uniformFalseAcceptProbability_le_240
#print axioms deployed_gs_list_ceiling_le_240

end AspisV5Tag67RelationListInclusion
