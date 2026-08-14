import AspisFormal.V5FinalSecurityAccounting

/-!
# Raw one-proof V5 security accounting

This file separates two different experiments.

* The raw experiment samples one proof transcript and does not divide any
  event by a proof-of-work success probability.
* `releasedCoreSubtotal` in `V5FinalSecurityAccounting` is the separate
  work-normalized subtotal.  Its `2^-108` theorem is not a theorem about the
  raw one-proof probability.

The six raw arithmetic terms are the ideal without-replacement q18 miss, four
released FRI bad-fibre caps divided only by `|QM31|`, and the relation repair
bound `32 * 240 / |QM31|`.  Production-to-ideal, transcript, primitive, and
runtime connections remain explicit assumptions.
-/

namespace AspisV5RawFinalSecurityAccounting

open MeasureTheory
open AspisV5CryptographicAssumptions
open AspisV5FinalSecurityAccounting
open AspisV5FriAdaptiveUnmatched
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriPublishedThresholds
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67RelationListInclusion
open AspisV5WithoutReplacementQuerySoundness
open AspisSoundnessLedger

/-! ## Raw arithmetic terms -/

/-- Worst-case ideal q18 miss mass for a bad set of at most 6082 fibres.
There is no proof-of-work divisor in this definition. -/
noncomputable def rawQ18IdealMissBound : Real :=
  (((6082 : Nat).descFactorial 18 : Nat) : Real) /
    (((131072 : Nat).descFactorial 18 : Nat) : Real)

/-- One released adaptive FRI fibre cap divided only by the QM31 field size.
There is no proof-of-work divisor in this definition. -/
noncomputable def rawFriFibreBound (round : Fin 4) : Real :=
  ((releasedChallengeCap round : Nat) : Real) / FIELD

/-- Raw relation-repair mass for 32 roots and at most 240 fixed candidates. -/
noncomputable def rawRelationRepairBound : Real :=
  (32 * 240 : Real) / FIELD

/-- The six raw one-proof arithmetic terms, with no grinding normalization. -/
noncomputable def rawCoreSubtotal : Real :=
  rawQ18IdealMissBound +
    rawFriFibreBound 0 + rawFriFibreBound 1 +
    rawFriFibreBound 2 + rawFriFibreBound 3 +
    rawRelationRepairBound

/-! ## Exact ideal-experiment connections -/

/-- The exact without-replacement counting theorem gives the raw q18 bound
directly, before any work experiment is introduced. -/
theorem ideal_q18_miss_le_raw_bound
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082) :
    idealMissProbability (q := 18) bad ≤ rawQ18IdealMissBound := by
  simpa only [rawQ18IdealMissBound] using
    (ideal_miss_probability_mono_card (q := 18) (cap := 6082)
      bad hcard (by norm_num))

/-- The raw q18 bound is the exact eighteen-factor hypergeometric ratio. -/
theorem raw_q18_bound_eq_product :
    rawQ18IdealMissBound =
      ((6082 : Real) / 131072) * (6081 / 131071) * (6080 / 131070) *
        (6079 / 131069) * (6078 / 131068) * (6077 / 131067) *
        (6076 / 131066) * (6075 / 131065) * (6074 / 131064) *
        (6073 / 131063) * (6072 / 131062) * (6071 / 131061) *
        (6070 / 131060) * (6069 / 131059) * (6068 / 131058) *
        (6067 / 131057) * (6066 / 131056) * (6065 / 131055) := by
  exact deployed_descFactorial_ratio_eq_product

/-- Select one of the four suffix-conditioned tuple events. -/
noncomputable def roundTupleEventAt
    {K : Type*} [Fintype K] [DecidableEq K]
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Fin 4 -> Finset (AspisV5FriAdaptiveUnmatched.FourChallenges K) := ![
  round0TupleEvent bad,
  round1TupleEvent bad,
  round2TupleEvent bad,
  round3TupleEvent bad]

theorem roundTupleEventAt_card_le
    {K : Type*} [Fintype K] [DecidableEq K]
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (round : Fin 4) :
    (roundTupleEventAt bad round).card ≤
      Fintype.card K ^ 3 * cap round := by
  fin_cases round
  · exact round0TupleEvent_card_le bad
  · exact round1TupleEvent_card_le bad
  · exact round2TupleEvent_card_le bad
  · exact round3TupleEvent_card_le bad

/-- Exact uniform mass of one suffix-conditioned FRI round event. -/
noncomputable def uniformRoundBadChallengeProbability
    {K : Type*} [Fintype K] [DecidableEq K]
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (round : Fin 4) : Rat :=
  (roundTupleEventAt bad round).card / Fintype.card K ^ 4

/-- Each existing fibre-cardinality theorem becomes exactly `cap/|K|` under
four independent uniform field challenges.  No work event occurs here. -/
theorem uniform_round_bad_challenge_probability_le
    {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (round : Fin 4) :
    uniformRoundBadChallengeProbability bad round ≤
      (cap round : Rat) / Fintype.card K := by
  let fieldCard := Fintype.card K
  have hfieldNat : 0 < fieldCard := Fintype.card_pos_iff.mpr inferInstance
  have hfield : (0 : Rat) < fieldCard := by exact_mod_cast hfieldNat
  have hcount := roundTupleEventAt_card_le bad round
  unfold uniformRoundBadChallengeProbability
  change ((roundTupleEventAt bad round).card : Rat) /
      (fieldCard : Rat) ^ 4 ≤ (cap round : Rat) / (fieldCard : Rat)
  rw [div_le_iff₀ (pow_pos hfield 4)]
  calc
    ((roundTupleEventAt bad round).card : Rat) ≤
        (fieldCard : Rat) ^ 3 * (cap round : Rat) := by
      exact_mod_cast hcount
    _ = (cap round : Rat) / (fieldCard : Rat) *
        (fieldCard : Rat) ^ 4 := by
      field_simp

/-- Existing relation-repair cardinality gives the raw `32*240/|K|` ideal
mass directly. -/
theorem ideal_relation_repair_probability_le_raw_ratio
    {K Candidate : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype Candidate] [DecidableEq Candidate]
    (data : Candidate -> AdaptiveFixedCandidateFourRounds K)
    (hcard : Fintype.card Candidate ≤ 240) :
    uniformBoundedCandidateRepairProbability data ≤
      (32 * 240 : Rat) / Fintype.card K :=
  uniformBoundedCandidateRepairProbability_le_240 data hcard

/-- Raw q18 probability is below `2^-79`.  The imported arithmetic theorem
has a `2^-32` factor; here it is algebraically removed rather than treated as
part of the raw experiment. -/
theorem raw_q18_bound_le_two_pow_neg_79 :
    rawQ18IdealMissBound ≤ (1 : Real) / 2 ^ 79 := by
  rw [raw_q18_bound_eq_product]
  have h := AspisSoundnessLedger.raw_query_miss
  norm_num at h ⊢

/-- Coarse raw exponents for the four released FRI fibres. -/
def rawFriExponent : Fin 4 -> Nat := ![75, 78, 82, 88]

/-- Removing the explicit work divisor from the existing arithmetic gives a
raw cap/field bound for each FRI round.  The conclusion itself contains no
work factor. -/
theorem raw_fri_fibre_bound_le (round : Fin 4) :
    rawFriFibreBound round ≤ (1 : Real) / 2 ^ rawFriExponent round := by
  fin_cases round
  · have h := released_fri_cap_work_probability_le (0 : Fin 4)
    change rawFriFibreBound 0 / 2 ^ 34 ≤ (1 : Real) / 2 ^ 109 at h
    change rawFriFibreBound 0 ≤ (1 : Real) / 2 ^ 75
    norm_num at h ⊢
    linarith
  · have h := released_fri_cap_work_probability_le (1 : Fin 4)
    change rawFriFibreBound 1 / 2 ^ 33 ≤ (1 : Real) / 2 ^ 111 at h
    change rawFriFibreBound 1 ≤ (1 : Real) / 2 ^ 78
    norm_num at h ⊢
    linarith
  · have h := released_fri_cap_work_probability_le (2 : Fin 4)
    change rawFriFibreBound 2 / 2 ^ 30 ≤ (1 : Real) / 2 ^ 112 at h
    change rawFriFibreBound 2 ≤ (1 : Real) / 2 ^ 82
    norm_num at h ⊢
    linarith
  · have h := released_fri_cap_work_probability_le (3 : Fin 4)
    change rawFriFibreBound 3 / 2 ^ 25 ≤ (1 : Real) / 2 ^ 113 at h
    change rawFriFibreBound 3 ≤ (1 : Real) / 2 ^ 88
    norm_num at h ⊢
    linarith

/-- A tighter round-zero estimate.  The coarse `2^-75` bound above is too
loose to add to the other five raw terms and retain 75 bits.  Reusing the same
rational lower bound on `sqrt (255 / 131072)` proves that round zero is at
most `3 * 2^-77`. -/
theorem raw_fri_round_zero_le_three_mul_two_pow_neg_77 :
    rawFriFibreBound 0 ≤ (3 : Real) / 2 ^ 77 := by
  have hcap := released_challenge_cap_le_threshold (0 : Fin 4)
  have hone :
      (1 : Real) * ((21 / 2) / Real.sqrt (255 / 131072)) *
          ((2 * ((21 / 2) / Real.sqrt (255 / 131072)) ^ 4 / 3) *
            (255 / 131072) + 1) * 131072 / FIELD / 2 ^ 0 ≤
        (1 : Real) / 2 ^ 77 :=
    sqrt_event_bound 1 (21 / 2) (255 / 131072) 131072
      (4410777 / 100000000) 0 77
      (by norm_num) (by norm_num) (by norm_num)
      (by unfold FIELD; norm_num)
  calc
    rawFriFibreBound 0 ≤
        challengeThreshold 10 round0Rate 131072 / FIELD := by
      exact div_le_div_of_nonneg_right hcap FIELD_pos.le
    _ = 3 *
        ((1 : Real) * ((21 / 2) / Real.sqrt (255 / 131072)) *
          ((2 * ((21 / 2) / Real.sqrt (255 / 131072)) ^ 4 / 3) *
            (255 / 131072) + 1) * 131072 / FIELD / 2 ^ 0) := by
      norm_num [challengeThreshold, concurrencyThreshold, ell, round0Rate]
      ring
    _ ≤ 3 * ((1 : Real) / 2 ^ 77) := by
      exact mul_le_mul_of_nonneg_left hone (by norm_num)
    _ = (3 : Real) / 2 ^ 77 := by ring

/-- The raw relation-repair term is below `2^-111`. -/
theorem raw_relation_repair_bound_le_two_pow_neg_111 :
    rawRelationRepairBound ≤ (1 : Real) / 2 ^ 111 := by
  exact relation_repair_event_le_released_bound rawRelationRepairBound (by
    rfl)

/-- Conservative raw one-proof subtotal.  This is intentionally much larger
than the work-normalized `2^-108` subtotal. -/
theorem raw_core_subtotal_le_two_pow_neg_74 :
    rawCoreSubtotal ≤ (1 : Real) / 2 ^ 74 := by
  have hquery := raw_q18_bound_le_two_pow_neg_79
  have hfri0 := raw_fri_fibre_bound_le (0 : Fin 4)
  have hfri1 := raw_fri_fibre_bound_le (1 : Fin 4)
  have hfri2 : rawFriFibreBound 2 ≤ (1 : Real) / 2 ^ 82 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (2 : Fin 4))
  have hfri3 : rawFriFibreBound 3 ≤ (1 : Real) / 2 ^ 88 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (3 : Fin 4))
  have hrelation := raw_relation_repair_bound_le_two_pow_neg_111
  norm_num [rawCoreSubtotal, rawFriExponent] at hquery hrelation hfri0 hfri1 hfri2 hfri3 ⊢
  linarith

/-- The tighter round-zero estimate retains a full 75-bit conservative raw
subtotal.  This is still only the six ideal arithmetic terms; all production,
hash, extraction, and runtime budgets remain separate. -/
theorem raw_core_subtotal_le_two_pow_neg_75 :
    rawCoreSubtotal ≤ (1 : Real) / 2 ^ 75 := by
  have hquery := raw_q18_bound_le_two_pow_neg_79
  have hfri0 := raw_fri_round_zero_le_three_mul_two_pow_neg_77
  have hfri1 : rawFriFibreBound 1 ≤ (1 : Real) / 2 ^ 78 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (1 : Fin 4))
  have hfri2 : rawFriFibreBound 2 ≤ (1 : Real) / 2 ^ 82 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (2 : Fin 4))
  have hfri3 : rawFriFibreBound 3 ≤ (1 : Real) / 2 ^ 88 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (3 : Fin 4))
  have hrelation := raw_relation_repair_bound_le_two_pow_neg_111
  norm_num [rawCoreSubtotal] at hquery hfri0 hfri1 hfri2 hfri3 hrelation ⊢
  linarith

/-! ## Raw core events and assumptions -/

/-- The six core events in the raw one-proof experiment.  The first set uses
the inherited field name `queryAndFinalWorkMiss`, but under the assumptions in
this file it is bounded as the raw ideal q18 miss, with no work condition. -/
def rawOneProofCoreEvents
    {Coins : Type*} (events : FinalSecurityEvents Coins) : List (Set Coins) :=
  [events.queryAndFinalWorkMiss,
    events.friRound0,
    events.friRound1,
    events.friRound2,
    events.friRound3,
    events.relationRepair]

def rawOneProofCoreFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins) : Set Coins :=
  (rawOneProofCoreEvents events).foldr (· ∪ ·) ∅

/-- Exact raw bounds assumed for the six core events.  These fields are the
production/experiment connections; the numerical right sides are defined and
checked above. -/
structure AssumedRawOneProofCoreBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins) : Prop where
  queryMiss :
    measure.real events.queryAndFinalWorkMiss ≤ rawQ18IdealMissBound
  friRound0 : measure.real events.friRound0 ≤ rawFriFibreBound 0
  friRound1 : measure.real events.friRound1 ≤ rawFriFibreBound 1
  friRound2 : measure.real events.friRound2 ≤ rawFriFibreBound 2
  friRound3 : measure.real events.friRound3 ≤ rawFriFibreBound 3
  relationRepair :
    measure.real events.relationRepair ≤ rawRelationRepairBound

theorem raw_one_proof_core_probability_le_subtotal
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (assumed : AssumedRawOneProofCoreBounds measure events) :
    measure.real (rawOneProofCoreFailure events) ≤ rawCoreSubtotal := by
  have hunion := measureReal_foldr_union_le_sum measure
    (rawOneProofCoreEvents events)
  have hsum :
      ((rawOneProofCoreEvents events).map
          (fun event => measure.real event)).sum ≤ rawCoreSubtotal := by
    simp only [rawOneProofCoreEvents, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    unfold rawCoreSubtotal
    linarith [assumed.queryMiss, assumed.friRound0, assumed.friRound1,
      assumed.friRound2, assumed.friRound3, assumed.relationRepair]
  exact hunion.trans hsum

/-! ## Raw final accounting -/

/-- Per-branch final bounds in the raw one-proof experiment. -/
noncomputable def rawFinalBudgetBound
    (budget : ExternalSecurityBudget) : FinalFailureKind -> Real
  | .queryAndFinalWorkMiss => rawQ18IdealMissBound
  | .friRound0 => rawFriFibreBound 0
  | .friRound1 => rawFriFibreBound 1
  | .friRound2 => rawFriFibreBound 2
  | .friRound3 => rawFriFibreBound 3
  | .relationRepair => rawRelationRepairBound
  | .transcriptRustToLean => budget.transcriptAndPrimitives.rustToLean
  | .sha256ImplementationDivergence =>
      budget.transcriptAndPrimitives.sha256ImplementationDivergence
  | .sha256Collision => budget.transcriptAndPrimitives.sha256Collision
  | .sha256Preimage => budget.transcriptAndPrimitives.sha256Preimage
  | .sha256RandomOracle => budget.transcriptAndPrimitives.sha256RandomOracle
  | .poseidon2ImplementationDivergence =>
      budget.transcriptAndPrimitives.poseidon2ImplementationDivergence
  | .poseidon2Collision => budget.transcriptAndPrimitives.poseidon2Collision
  | .poseidon2Preimage => budget.transcriptAndPrimitives.poseidon2Preimage
  | .acceptedRunRelationBridge => budget.acceptedRunRelationBridge
  | .proofMerkleOpeningBridge => budget.proofMerkleOpeningBridge
  | .victimCredentialRecovery => budget.victimCredentialRecovery
  | .rustStateModelMismatch => budget.runtime.rustStateModelMismatch
  | .systemProgramOrPdaMismatch => budget.runtime.systemProgramOrPdaMismatch
  | .writableAccountLockFailure => budget.runtime.writableAccountLockFailure
  | .rejectedTransactionRollbackFailure =>
      budget.runtime.rejectedTransactionRollbackFailure
  | .committedMarkerPersistenceFailure =>
      budget.runtime.committedMarkerPersistenceFailure
  | .finalizedStateObservationFailure =>
      budget.runtime.finalizedStateObservationFailure
  | .closeOrRefundModelMismatch => budget.runtime.closeOrRefundModelMismatch

noncomputable def rawFinalBudgetTotal
    (budget : ExternalSecurityBudget) : Real :=
  (orderedFinalFailureKinds.map (rawFinalBudgetBound budget)).sum

theorem raw_final_budget_total_eq
    (budget : ExternalSecurityBudget) :
    rawFinalBudgetTotal budget = rawCoreSubtotal + budget.total := by
  simp [rawFinalBudgetTotal, orderedFinalFailureKinds, rawFinalBudgetBound,
    rawCoreSubtotal, ExternalSecurityBudget.total,
    RuntimeSecurityBudget.total, ConcreteSecurityBudget.total,
    orderedFailureKinds, ConcreteSecurityBudget.bound]
  ring

/-- Every raw one-proof premise.  Only the first six fields differ from the
work-normalized assumptions; every external bridge, primitive, credential,
and runtime budget remains unchanged and explicit. -/
structure AssumedRawFinalSecurityBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget) : Prop where
  core : AssumedRawOneProofCoreBounds measure events
  transcriptAndPrimitives : AssumedConcreteSecurityBounds measure
    events.transcriptAndPrimitives budget.transcriptAndPrimitives
  acceptedRunRelationBridge :
    measure.real events.acceptedRunRelationBridge ≤
      budget.acceptedRunRelationBridge
  proofMerkleOpeningBridge :
    measure.real events.proofMerkleOpeningBridge ≤
      budget.proofMerkleOpeningBridge
  victimCredentialRecovery :
    measure.real events.victimCredentialRecovery ≤
      budget.victimCredentialRecovery
  rustStateModelMismatch :
    measure.real {coins | events.runtime.rustStateModelMismatch coins} ≤
      budget.runtime.rustStateModelMismatch
  systemProgramOrPdaMismatch :
    measure.real {coins | events.runtime.systemProgramOrPdaMismatch coins} ≤
      budget.runtime.systemProgramOrPdaMismatch
  writableAccountLockFailure :
    measure.real {coins | events.runtime.writableAccountLockFailure coins} ≤
      budget.runtime.writableAccountLockFailure
  rejectedTransactionRollbackFailure :
    measure.real
      {coins | events.runtime.rejectedTransactionRollbackFailure coins} ≤
      budget.runtime.rejectedTransactionRollbackFailure
  committedMarkerPersistenceFailure :
    measure.real
      {coins | events.runtime.committedMarkerPersistenceFailure coins} ≤
      budget.runtime.committedMarkerPersistenceFailure
  finalizedStateObservationFailure :
    measure.real
      {coins | events.runtime.finalizedStateObservationFailure coins} ≤
      budget.runtime.finalizedStateObservationFailure
  closeOrRefundModelMismatch :
    measure.real {coins | events.runtime.closeOrRefundModelMismatch coins} ≤
      budget.runtime.closeOrRefundModelMismatch

theorem assumed_raw_final_bound_for_kind
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget)
    (kind : FinalFailureKind) :
    measure.real (events.event kind) ≤ rawFinalBudgetBound budget kind := by
  cases kind with
  | queryAndFinalWorkMiss => exact assumed.core.queryMiss
  | friRound0 => exact assumed.core.friRound0
  | friRound1 => exact assumed.core.friRound1
  | friRound2 => exact assumed.core.friRound2
  | friRound3 => exact assumed.core.friRound3
  | relationRepair => exact assumed.core.relationRepair
  | transcriptRustToLean =>
      exact assumed.transcriptAndPrimitives.eventBound .rustToLean
  | sha256ImplementationDivergence =>
      exact assumed.transcriptAndPrimitives.eventBound
        .sha256ImplementationDivergence
  | sha256Collision =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256Collision
  | sha256Preimage =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256Preimage
  | sha256RandomOracle =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256RandomOracle
  | poseidon2ImplementationDivergence =>
      exact assumed.transcriptAndPrimitives.eventBound
        .poseidon2ImplementationDivergence
  | poseidon2Collision =>
      exact assumed.transcriptAndPrimitives.eventBound .poseidon2Collision
  | poseidon2Preimage =>
      exact assumed.transcriptAndPrimitives.eventBound .poseidon2Preimage
  | acceptedRunRelationBridge => exact assumed.acceptedRunRelationBridge
  | proofMerkleOpeningBridge => exact assumed.proofMerkleOpeningBridge
  | victimCredentialRecovery => exact assumed.victimCredentialRecovery
  | rustStateModelMismatch => exact assumed.rustStateModelMismatch
  | systemProgramOrPdaMismatch => exact assumed.systemProgramOrPdaMismatch
  | writableAccountLockFailure => exact assumed.writableAccountLockFailure
  | rejectedTransactionRollbackFailure =>
      exact assumed.rejectedTransactionRollbackFailure
  | committedMarkerPersistenceFailure =>
      exact assumed.committedMarkerPersistenceFailure
  | finalizedStateObservationFailure =>
      exact assumed.finalizedStateObservationFailure
  | closeOrRefundModelMismatch => exact assumed.closeOrRefundModelMismatch

theorem total_final_failure_probability_le_raw_budget
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤ rawFinalBudgetTotal budget := by
  calc
    measure.real (totalFinalFailure events) ≤
        (orderedFinalFailureKinds.map
          (fun kind => measure.real (events.event kind))).sum :=
      total_final_failure_probability_le_branch_sum measure events
    _ ≤ (orderedFinalFailureKinds.map
        (rawFinalBudgetBound budget)).sum := by
      apply List.sum_le_sum
      intro kind _
      exact assumed_raw_final_bound_for_kind measure events budget assumed kind
    _ = rawFinalBudgetTotal budget := rfl

/-- Raw total-failure endpoint with all external terms still visible. -/
theorem total_final_failure_probability_le_raw_core_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤
      rawCoreSubtotal + budget.total := by
  exact (total_final_failure_probability_le_raw_budget
    measure events budget assumed).trans_eq (raw_final_budget_total_eq budget)

/-- Any attack already reduced to the common final event ledger inherits the
raw one-proof bound. -/
theorem raw_attack_probability_le_core_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (attack : Set Coins) (covered : attack ⊆ totalFinalFailure events)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real attack ≤ rawCoreSubtotal + budget.total := by
  exact (MeasureTheory.measureReal_mono covered).trans
    (total_final_failure_probability_le_raw_core_plus_external
      measure events budget assumed)

theorem total_final_failure_probability_le_two_pow_neg_74_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤
      (1 : Real) / 2 ^ 74 + budget.total := by
  exact (total_final_failure_probability_le_raw_core_plus_external
    measure events budget assumed).trans (by
      linarith [raw_core_subtotal_le_two_pow_neg_74])

theorem total_final_failure_probability_le_two_pow_neg_75_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤
      (1 : Real) / 2 ^ 75 + budget.total := by
  exact (total_final_failure_probability_le_raw_core_plus_external
    measure events budget assumed).trans (by
      linarith [raw_core_subtotal_le_two_pow_neg_75])

/-- Raw attack endpoint once the caller has reduced that attack to the common
failure ledger.  The `budget.total` summand is intentionally not hidden: the
theorem is not a deployed numerical theft bound until those external terms
are instantiated. -/
theorem raw_attack_probability_le_two_pow_neg_75_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (attack : Set Coins) (covered : attack ⊆ totalFinalFailure events)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget) :
    measure.real attack ≤ (1 : Real) / 2 ^ 75 + budget.total := by
  exact (raw_attack_probability_le_core_plus_external measure events attack
    covered budget assumed).trans (by
      linarith [raw_core_subtotal_le_two_pow_neg_75])

/-! ## Explicit classification of the older subtotal -/

/-- Alias whose name records the experiment represented by the older
`releasedCoreSubtotal`. -/
noncomputable abbrev workNormalizedCoreSubtotal : Real :=
  releasedCoreSubtotal

/-- The existing `2^-108` theorem is retained under a name that states its
experiment.  It is work-normalized and is not substituted for `rawCoreSubtotal`
anywhere in this file. -/
theorem work_normalized_released_core_subtotal_le_two_pow_neg_108 :
    workNormalizedCoreSubtotal ≤ (1 : Real) / 2 ^ 108 :=
  released_core_subtotal_le

/-! ## Axiom audit -/

#print axioms ideal_q18_miss_le_raw_bound
#print axioms uniform_round_bad_challenge_probability_le
#print axioms ideal_relation_repair_probability_le_raw_ratio
#print axioms raw_q18_bound_le_two_pow_neg_79
#print axioms raw_fri_fibre_bound_le
#print axioms raw_fri_round_zero_le_three_mul_two_pow_neg_77
#print axioms raw_core_subtotal_le_two_pow_neg_74
#print axioms raw_core_subtotal_le_two_pow_neg_75
#print axioms raw_one_proof_core_probability_le_subtotal
#print axioms total_final_failure_probability_le_raw_core_plus_external
#print axioms raw_attack_probability_le_core_plus_external
#print axioms raw_attack_probability_le_two_pow_neg_75_plus_external
#print axioms work_normalized_released_core_subtotal_le_two_pow_neg_108

end AspisV5RawFinalSecurityAccounting
