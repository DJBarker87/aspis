import AspisFormal.V5CryptographicAssumptions
import AspisFormal.V5FriReleasedAdaptiveExtraction
import AspisFormal.V5MerkleAuthenticationBinding
import AspisFormal.V5Tag67RelationListInclusion
import AspisFormal.V5TheftStateTransitionReduction

/-!
# Final V5 security-event accounting

This file performs one deliberately plain task: it puts every event needed by
the current fixed-victim reduction into one union and adds its probability
budget once.  It does not turn an unproved implementation or cryptographic
claim into a number.

The six proof-system terms with kernel-checked finite arithmetic are:

* the eighteen-query miss together with its separate 32-bit work reduction;
* four adaptive FRI challenge-fibre events, each with its own work reduction;
* the relation-repair event for one coherent list of at most 240 candidates.

Every connection from a production execution to those ideal experiments is
still an explicit premise.  The eight transcript/primitive events from
`V5CryptographicAssumptions`, the accepted-run/relation bridge, the proof
Merkle-opening bridge, credential recovery, and all seven runtime failures
also retain caller-supplied budgets. A marker-address collision is not counted
as theft: an occupied colliding marker makes the spend fail and can only deny
service in the sequential state model.

Two apparent extra terms are intentionally not counted again:

* a collision in the SHA-256 proof Merkle tree is the existing SHA-256
  collision event; and
* the nullifier, note-commitment, and victim-tree collision witnesses in the
  fixed-victim theorem are covered by the existing Poseidon2 collision event.

The containment premises below make those identifications visible.  Without
them, or without the production-to-ideal experiment premises, the final
probability theorem cannot be applied.
-/

namespace AspisV5FinalSecurityAccounting

open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open Aspis.TheftResistance
open AspisV5AcceptedSpendRelation
open AspisV5CryptographicAssumptions
open AspisV5FixedVictimTheftGame
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriCurveDecodabilityTransport
open AspisV5FriPublishedThresholds
open AspisV5MerkleAuthenticationBinding
open AspisV5Tag67RelationListInclusion
open AspisV5TheftResistance
open AspisV5TheftStateTransitionReduction
open AspisV5WithoutReplacementQuerySoundness
open AspisSoundnessLedger

/-! ## One non-duplicated event ledger -/

/-- The 24 probability branches used by the final accounting theorem. -/
inductive FinalFailureKind where
  | queryAndFinalWorkMiss
  | friRound0
  | friRound1
  | friRound2
  | friRound3
  | relationRepair
  | transcriptRustToLean
  | sha256ImplementationDivergence
  | sha256Collision
  | sha256Preimage
  | sha256RandomOracle
  | poseidon2ImplementationDivergence
  | poseidon2Collision
  | poseidon2Preimage
  | acceptedRunRelationBridge
  | proofMerkleOpeningBridge
  | victimCredentialRecovery
  | rustStateModelMismatch
  | systemProgramOrPdaMismatch
  | writableAccountLockFailure
  | rejectedTransactionRollbackFailure
  | committedMarkerPersistenceFailure
  | finalizedStateObservationFailure
  | closeOrRefundModelMismatch
  deriving DecidableEq, Fintype

def orderedFinalFailureKinds : List FinalFailureKind :=
  [.queryAndFinalWorkMiss,
    .friRound0,
    .friRound1,
    .friRound2,
    .friRound3,
    .relationRepair,
    .transcriptRustToLean,
    .sha256ImplementationDivergence,
    .sha256Collision,
    .sha256Preimage,
    .sha256RandomOracle,
    .poseidon2ImplementationDivergence,
    .poseidon2Collision,
    .poseidon2Preimage,
    .acceptedRunRelationBridge,
    .proofMerkleOpeningBridge,
    .victimCredentialRecovery,
    .rustStateModelMismatch,
    .systemProgramOrPdaMismatch,
    .writableAccountLockFailure,
    .rejectedTransactionRollbackFailure,
    .committedMarkerPersistenceFailure,
    .finalizedStateObservationFailure,
    .closeOrRefundModelMismatch]

theorem final_failure_kind_count_is_twenty_four :
    Fintype.card FinalFailureKind = 24 := by
  decide

theorem ordered_final_failure_kinds_are_exactly_once :
    orderedFinalFailureKinds.Nodup /\
      forall kind : FinalFailureKind, kind ∈ orderedFinalFailureKinds := by
  decide

/-- Concrete events for one experiment.  The relation bridge includes the
remaining accepted-run-to-model and candidate/trace failures; it is not a
claim that those failures are impossible. -/
structure FinalSecurityEvents (Coins : Type*) where
  queryAndFinalWorkMiss : Set Coins
  friRound0 : Set Coins
  friRound1 : Set Coins
  friRound2 : Set Coins
  friRound3 : Set Coins
  relationRepair : Set Coins
  transcriptAndPrimitives : SecurityFailureEvents Coins
  acceptedRunRelationBridge : Set Coins
  proofMerkleOpeningBridge : Set Coins
  victimCredentialRecovery : Set Coins
  runtime : RuntimeFailurePredicates Coins

def FinalSecurityEvents.event
    {Coins : Type*} (events : FinalSecurityEvents Coins) :
    FinalFailureKind -> Set Coins
  | .queryAndFinalWorkMiss => events.queryAndFinalWorkMiss
  | .friRound0 => events.friRound0
  | .friRound1 => events.friRound1
  | .friRound2 => events.friRound2
  | .friRound3 => events.friRound3
  | .relationRepair => events.relationRepair
  | .transcriptRustToLean =>
      events.transcriptAndPrimitives.event .rustToLean
  | .sha256ImplementationDivergence =>
      events.transcriptAndPrimitives.event .sha256ImplementationDivergence
  | .sha256Collision =>
      events.transcriptAndPrimitives.event .sha256Collision
  | .sha256Preimage =>
      events.transcriptAndPrimitives.event .sha256Preimage
  | .sha256RandomOracle =>
      events.transcriptAndPrimitives.event .sha256RandomOracle
  | .poseidon2ImplementationDivergence =>
      events.transcriptAndPrimitives.event .poseidon2ImplementationDivergence
  | .poseidon2Collision =>
      events.transcriptAndPrimitives.event .poseidon2Collision
  | .poseidon2Preimage =>
      events.transcriptAndPrimitives.event .poseidon2Preimage
  | .acceptedRunRelationBridge => events.acceptedRunRelationBridge
  | .proofMerkleOpeningBridge => events.proofMerkleOpeningBridge
  | .victimCredentialRecovery => events.victimCredentialRecovery
  | .rustStateModelMismatch =>
      {coins | events.runtime.rustStateModelMismatch coins}
  | .systemProgramOrPdaMismatch =>
      {coins | events.runtime.systemProgramOrPdaMismatch coins}
  | .writableAccountLockFailure =>
      {coins | events.runtime.writableAccountLockFailure coins}
  | .rejectedTransactionRollbackFailure =>
      {coins | events.runtime.rejectedTransactionRollbackFailure coins}
  | .committedMarkerPersistenceFailure =>
      {coins | events.runtime.committedMarkerPersistenceFailure coins}
  | .finalizedStateObservationFailure =>
      {coins | events.runtime.finalizedStateObservationFailure coins}
  | .closeOrRefundModelMismatch =>
      {coins | events.runtime.closeOrRefundModelMismatch coins}

def totalFinalFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins) : Set Coins :=
  (orderedFinalFailureKinds.map events.event).foldr (· ∪ ·) ∅

theorem one_final_failure_is_in_total
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (kind : FinalFailureKind) :
    events.event kind ⊆ totalFinalFailure events := by
  apply member_subset_foldr_union
  apply List.mem_map.mpr
  exact ⟨kind, ordered_final_failure_kinds_are_exactly_once.2 kind, rfl⟩

/-! ## The released arithmetic terms -/

/-- Per-round work-normalized endpoints for the four proved adaptive
challenge-fibre counts. -/
noncomputable def releasedFriBound : Fin 4 -> Real := ![
  (1 : Real) / 2 ^ 109,
  (1 : Real) / 2 ^ 111,
  (1 : Real) / 2 ^ 112,
  (1 : Real) / 2 ^ 113]

@[simp] theorem releasedFriBound_zero :
    releasedFriBound 0 = (1 : Real) / 2 ^ 109 := rfl

@[simp] theorem releasedFriBound_one :
    releasedFriBound 1 = (1 : Real) / 2 ^ 111 := rfl

@[simp] theorem releasedFriBound_two :
    releasedFriBound 2 = (1 : Real) / 2 ^ 112 := rfl

@[simp] theorem releasedFriBound_three :
    releasedFriBound 3 = (1 : Real) / 2 ^ 113 := rfl

/-- The six finite-arithmetic terms: q18+work, four FRI fibres+work, and the
cap-240 relation repair event. -/
noncomputable def releasedCoreSubtotal : Real :=
  (1 : Real) / 2 ^ 111 +
    releasedFriBound 0 + releasedFriBound 1 +
    releasedFriBound 2 + releasedFriBound 3 +
    (1 : Real) / 2 ^ 111

/-- The six finite-arithmetic terms together fit below `2^-108`.  This is a
subtotal, not a deployed theft-resistance claim. -/
theorem released_core_subtotal_le :
    releasedCoreSubtotal ≤ (1 : Real) / 2 ^ 108 := by
  change
    (1 : Real) / 2 ^ 111 + 1 / 2 ^ 109 + 1 / 2 ^ 111 +
      1 / 2 ^ 112 + 1 / 2 ^ 113 + 1 / 2 ^ 111 ≤ 1 / 2 ^ 108
  norm_num

/-- Reuse the exact without-replacement q18 theorem once a caller supplies
the separate work/experiment reduction. -/
theorem query_and_final_work_event_le_released_bound
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082)
    (probability : Real)
    (experimentConnection : probability ≤
      idealMissProbability (q := 18) bad / 2 ^ 32) :
    probability ≤ (1 : Real) / 2 ^ 111 :=
  experimentConnection.trans
    (deployed_q18_ideal_miss_ratio_div_2pow32_le bad hcard)

/-- The integer challenge cap for each adaptive FRI round is no larger than
the real threshold used by the released arithmetic. -/
theorem released_challenge_cap_le_threshold (round : Fin 4) :
    ((releasedChallengeCap round : Nat) : Real) ≤
      match round with
      | 0 => challengeThreshold 10 round0Rate 131072
      | 1 => challengeThreshold 9 round1Rate 32768
      | 2 => challengeThreshold 6 round2Rate 8192
      | 3 => challengeThreshold 3 round3Rate 2048 := by
  fin_cases round
  · exact floor_challengeThreshold_le _
      (challengeThreshold_nonneg 10 round0Rate 131072 (by norm_num [round0Rate]))
  · exact floor_challengeThreshold_le _
      (challengeThreshold_nonneg 9 round1Rate 32768 (by norm_num [round1Rate]))
  · exact floor_challengeThreshold_le _
      (challengeThreshold_nonneg 6 round2Rate 8192 (by norm_num [round2Rate]))
  · exact floor_challengeThreshold_le _
      (challengeThreshold_nonneg 3 round3Rate 2048 (by norm_num [round3Rate]))

/-- Work exponents checked immediately before the four released FRI
challenges. -/
def releasedFriWork : Fin 4 -> Nat := ![34, 33, 30, 25]

/-- The new exact integer fibre caps feed the previously kernel-checked
released arithmetic.  This theorem is arithmetic only: applying the work
factor to a production experiment still needs the random-oracle/work
reduction recorded in `AssumedFinalSecurityBounds`. -/
theorem released_fri_cap_work_probability_le (round : Fin 4) :
    ((releasedChallengeCap round : Nat) : Real) / FIELD /
        2 ^ releasedFriWork round ≤ releasedFriBound round := by
  fin_cases round
  · have hcap : ((releasedChallengeCap 0 : Nat) : Real) ≤
        challengeThreshold 10 round0Rate 131072 := by
      simpa using released_challenge_cap_le_threshold (0 : Fin 4)
    calc
      ((releasedChallengeCap 0 : Nat) : Real) / FIELD / 2 ^ 34 ≤
          challengeThreshold 10 round0Rate 131072 / FIELD / 2 ^ 34 := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hcap FIELD_pos.le) (by positivity)
      _ = (3 : Real) * ((21 / 2) / Real.sqrt (255 / 131072)) *
          ((2 * ((21 / 2) / Real.sqrt (255 / 131072)) ^ 4 / 3) *
            (255 / 131072) + 1) * 131072 / FIELD / 2 ^ 34 := by
        norm_num [challengeThreshold, concurrencyThreshold, ell, round0Rate]
        ring
      _ ≤ (1 : Real) / 2 ^ 109 := fold0_bound
      _ = releasedFriBound 0 := releasedFriBound_zero.symm
  · have hcap : ((releasedChallengeCap 1 : Nat) : Real) ≤
        challengeThreshold 9 round1Rate 32768 := by
      simpa using released_challenge_cap_le_threshold (1 : Fin 4)
    calc
      ((releasedChallengeCap 1 : Nat) : Real) / FIELD / 2 ^ 33 ≤
          challengeThreshold 9 round1Rate 32768 / FIELD / 2 ^ 33 := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hcap FIELD_pos.le) (by positivity)
      _ = (3 : Real) * ((19 / 2) / Real.sqrt (63 / 32768)) *
          ((2 * ((19 / 2) / Real.sqrt (63 / 32768)) ^ 4 / 3) *
            (63 / 32768) + 1) * 32768 / FIELD / 2 ^ 33 := by
        norm_num [challengeThreshold, concurrencyThreshold, ell, round1Rate]
        ring
      _ ≤ (1 : Real) / 2 ^ 111 := fold1_bound
      _ = releasedFriBound 1 := releasedFriBound_one.symm
  · have hcap : ((releasedChallengeCap 2 : Nat) : Real) ≤
        challengeThreshold 6 round2Rate 8192 := by
      simpa using released_challenge_cap_le_threshold (2 : Fin 4)
    calc
      ((releasedChallengeCap 2 : Nat) : Real) / FIELD / 2 ^ 30 ≤
          challengeThreshold 6 round2Rate 8192 / FIELD / 2 ^ 30 := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hcap FIELD_pos.le) (by positivity)
      _ = (3 : Real) * ((13 / 2) / Real.sqrt (15 / 8192)) *
          ((2 * ((13 / 2) / Real.sqrt (15 / 8192)) ^ 4 / 3) *
            (15 / 8192) + 1) * 8192 / FIELD / 2 ^ 30 := by
        norm_num [challengeThreshold, concurrencyThreshold, ell, round2Rate]
        ring
      _ ≤ (1 : Real) / 2 ^ 112 := fold2_bound
      _ = releasedFriBound 2 := releasedFriBound_two.symm
  · have hcap : ((releasedChallengeCap 3 : Nat) : Real) ≤
        challengeThreshold 3 round3Rate 2048 := by
      simpa using released_challenge_cap_le_threshold (3 : Fin 4)
    calc
      ((releasedChallengeCap 3 : Nat) : Real) / FIELD / 2 ^ 25 ≤
          challengeThreshold 3 round3Rate 2048 / FIELD / 2 ^ 25 := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hcap FIELD_pos.le) (by positivity)
      _ = (3 : Real) * ((7 / 2) / Real.sqrt (3 / 2048)) *
          ((2 * ((7 / 2) / Real.sqrt (3 / 2048)) ^ 4 / 3) *
            (3 / 2048) + 1) * 2048 / FIELD / 2 ^ 25 := by
        norm_num [challengeThreshold, concurrencyThreshold, ell, round3Rate]
        ring
      _ ≤ (1 : Real) / 2 ^ 113 := fold3_bound
      _ = releasedFriBound 3 := releasedFriBound_three.symm

/-- Reuse the cap-240 relation-repair arithmetic once a caller connects its
production event to the ideal twelve-challenge experiment. -/
theorem relation_repair_event_le_released_bound
    (probability : Real)
    (experimentConnection : probability ≤ (32 * 240 : Real) / FIELD) :
    probability ≤ (1 : Real) / 2 ^ 111 := by
  exact experimentConnection.trans (by
    unfold FIELD
    norm_num)

/-! ## Caller-supplied budgets for the unproved boundaries -/

structure RuntimeSecurityBudget where
  rustStateModelMismatch : Real
  systemProgramOrPdaMismatch : Real
  writableAccountLockFailure : Real
  rejectedTransactionRollbackFailure : Real
  committedMarkerPersistenceFailure : Real
  finalizedStateObservationFailure : Real
  closeOrRefundModelMismatch : Real

def RuntimeSecurityBudget.total (budget : RuntimeSecurityBudget) : Real :=
  budget.rustStateModelMismatch +
    budget.systemProgramOrPdaMismatch +
    budget.writableAccountLockFailure +
    budget.rejectedTransactionRollbackFailure +
    budget.committedMarkerPersistenceFailure +
    budget.finalizedStateObservationFailure +
    budget.closeOrRefundModelMismatch

structure ExternalSecurityBudget where
  transcriptAndPrimitives : ConcreteSecurityBudget
  acceptedRunRelationBridge : Real
  proofMerkleOpeningBridge : Real
  victimCredentialRecovery : Real
  runtime : RuntimeSecurityBudget

def ExternalSecurityBudget.total (budget : ExternalSecurityBudget) : Real :=
  budget.transcriptAndPrimitives.total +
    budget.acceptedRunRelationBridge +
    budget.proofMerkleOpeningBridge +
    budget.victimCredentialRecovery +
    budget.runtime.total

noncomputable def finalBudgetBound
    (budget : ExternalSecurityBudget) : FinalFailureKind -> Real
  | .queryAndFinalWorkMiss => (1 : Real) / 2 ^ 111
  | .friRound0 => releasedFriBound 0
  | .friRound1 => releasedFriBound 1
  | .friRound2 => releasedFriBound 2
  | .friRound3 => releasedFriBound 3
  | .relationRepair => (1 : Real) / 2 ^ 111
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

noncomputable def finalBudgetTotal (budget : ExternalSecurityBudget) : Real :=
  (orderedFinalFailureKinds.map (finalBudgetBound budget)).sum

theorem final_budget_total_eq
    (budget : ExternalSecurityBudget) :
    finalBudgetTotal budget =
      releasedCoreSubtotal + budget.total := by
  simp [finalBudgetTotal, orderedFinalFailureKinds, finalBudgetBound,
    releasedCoreSubtotal, ExternalSecurityBudget.total,
    RuntimeSecurityBudget.total, ConcreteSecurityBudget.total,
    orderedFailureKinds, ConcreteSecurityBudget.bound]
  ring

/-- Every numerical premise needed by the final union bound.  The six first
fields are the experiment connections needed to use the proved finite
arithmetic.  The remaining fields are explicit external assumptions. -/
structure AssumedFinalSecurityBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget) : Prop where
  queryAndFinalWorkMiss :
    measure.real events.queryAndFinalWorkMiss ≤ (1 : Real) / 2 ^ 111
  friRound0 : measure.real events.friRound0 ≤
    ((releasedChallengeCap 0 : Nat) : Real) / FIELD / 2 ^ 34
  friRound1 : measure.real events.friRound1 ≤
    ((releasedChallengeCap 1 : Nat) : Real) / FIELD / 2 ^ 33
  friRound2 : measure.real events.friRound2 ≤
    ((releasedChallengeCap 2 : Nat) : Real) / FIELD / 2 ^ 30
  friRound3 : measure.real events.friRound3 ≤
    ((releasedChallengeCap 3 : Nat) : Real) / FIELD / 2 ^ 25
  relationRepair :
    measure.real events.relationRepair ≤ (32 * 240 : Real) / FIELD
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

theorem assumed_final_bound_for_kind
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget)
    (kind : FinalFailureKind) :
    measure.real (events.event kind) ≤ finalBudgetBound budget kind := by
  cases kind with
  | queryAndFinalWorkMiss => exact assumed.queryAndFinalWorkMiss
  | friRound0 =>
      change measure.real events.friRound0 ≤ releasedFriBound 0
      exact assumed.friRound0.trans (by
        simpa [releasedFriWork] using
          released_fri_cap_work_probability_le (0 : Fin 4))
  | friRound1 =>
      change measure.real events.friRound1 ≤ releasedFriBound 1
      exact assumed.friRound1.trans (by
        simpa [releasedFriWork] using
          released_fri_cap_work_probability_le (1 : Fin 4))
  | friRound2 =>
      change measure.real events.friRound2 ≤ releasedFriBound 2
      exact assumed.friRound2.trans (by
        simpa [releasedFriWork] using
          released_fri_cap_work_probability_le (2 : Fin 4))
  | friRound3 =>
      change measure.real events.friRound3 ≤ releasedFriBound 3
      exact assumed.friRound3.trans (by
        simpa [releasedFriWork] using
          released_fri_cap_work_probability_le (3 : Fin 4))
  | relationRepair =>
      change measure.real events.relationRepair ≤ (1 : Real) / 2 ^ 111
      exact relation_repair_event_le_released_bound _ assumed.relationRepair
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

/-! ## Symbolic and budgeted probability bounds -/

/-- Pure symbolic union bound.  Every one of the 24 branches occurs once in
both the event list and the sum. -/
theorem total_final_failure_probability_le_branch_sum
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins) :
    measure.real (totalFinalFailure events) ≤
      (orderedFinalFailureKinds.map
        (fun kind => measure.real (events.event kind))).sum := by
  exact measureReal_foldr_union_le_sum measure
    (orderedFinalFailureKinds.map events.event)

/-- Symbolic endpoint for any attack event covered by the ledger.  No branch
budget is assumed here. -/
theorem covered_event_probability_le_branch_sum
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) [MeasureTheory.IsFiniteMeasure measure]
    (events : FinalSecurityEvents Coins) (attack : Set Coins)
    (covered : attack ⊆ totalFinalFailure events) :
    measure.real attack ≤
      (orderedFinalFailureKinds.map
        (fun kind => measure.real (events.event kind))).sum := by
  exact (MeasureTheory.measureReal_mono covered).trans
    (total_final_failure_probability_le_branch_sum measure events)

/-- Instantiate the symbolic union bound with all supplied budgets. -/
theorem total_final_failure_probability_le_budget
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤ finalBudgetTotal budget := by
  calc
    measure.real (totalFinalFailure events) ≤
        (orderedFinalFailureKinds.map
          (fun kind => measure.real (events.event kind))).sum :=
      total_final_failure_probability_le_branch_sum measure events
    _ ≤ (orderedFinalFailureKinds.map (finalBudgetBound budget)).sum := by
      apply List.sum_le_sum
      intro kind _
      exact assumed_final_bound_for_kind measure events budget assumed kind
    _ = finalBudgetTotal budget := rfl

/-- Concrete arithmetic endpoint with every unproved term still visible.
There is deliberately no conversion of this expression into a deployed
security-bit or theft-resistance claim. -/
theorem total_final_failure_probability_le_released_subtotal_plus_external
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget) :
    measure.real (totalFinalFailure events) ≤
      (1 : Real) / 2 ^ 108 + budget.total := by
  calc
    measure.real (totalFinalFailure events) ≤ finalBudgetTotal budget :=
      total_final_failure_probability_le_budget measure events budget assumed
    _ = releasedCoreSubtotal + budget.total := final_budget_total_eq budget
    _ ≤ (1 : Real) / 2 ^ 108 + budget.total :=
      by linarith [released_core_subtotal_le]

/-! ## Connecting the fixed-victim theorem without counting events twice -/

/-- The proof-system part of the ledger.  In particular this does not contain
credential recovery or runtime failures. -/
def proofSoundnessFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins) : Set Coins :=
  events.queryAndFinalWorkMiss ∪ events.friRound0 ∪ events.friRound1 ∪
    events.friRound2 ∪ events.friRound3 ∪ events.relationRepair ∪
    totalFailure events.transcriptAndPrimitives ∪
    events.acceptedRunRelationBridge ∪ events.proofMerkleOpeningBridge

theorem proof_soundness_failure_subset_total
    {Coins : Type*} (events : FinalSecurityEvents Coins) :
    proofSoundnessFailure events ⊆ totalFinalFailure events := by
  have transcriptSubset :
      totalFailure events.transcriptAndPrimitives ⊆ totalFinalFailure events := by
    intro coins failure
    unfold totalFailure at failure
    simp only [orderedFailureKinds, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Set.mem_union, Set.mem_empty_iff_false,
      or_false] at failure
    rcases failure with rust | shaImplementation | shaCollision |
        shaPreimage | shaOracle | poseidonImplementation | poseidonCollision |
        poseidonPreimage
    · exact one_final_failure_is_in_total events .transcriptRustToLean rust
    · exact one_final_failure_is_in_total events
        .sha256ImplementationDivergence shaImplementation
    · exact one_final_failure_is_in_total events .sha256Collision shaCollision
    · exact one_final_failure_is_in_total events .sha256Preimage shaPreimage
    · exact one_final_failure_is_in_total events .sha256RandomOracle shaOracle
    · exact one_final_failure_is_in_total events
        .poseidon2ImplementationDivergence poseidonImplementation
    · exact one_final_failure_is_in_total events .poseidon2Collision
        poseidonCollision
    · exact one_final_failure_is_in_total events .poseidon2Preimage
        poseidonPreimage
  intro coins failure
  simp only [proofSoundnessFailure, Set.mem_union] at failure
  rcases failure with ((((((((query | fri0) | fri1) | fri2) | fri3) |
      relation) | transcript) | relationBridge) | merkleBridge)
  · exact one_final_failure_is_in_total events .queryAndFinalWorkMiss query
  · exact one_final_failure_is_in_total events .friRound0 fri0
  · exact one_final_failure_is_in_total events .friRound1 fri1
  · exact one_final_failure_is_in_total events .friRound2 fri2
  · exact one_final_failure_is_in_total events .friRound3 fri3
  · exact one_final_failure_is_in_total events .relationRepair relation
  · exact transcriptSubset transcript
  · exact one_final_failure_is_in_total events .acceptedRunRelationBridge
      relationBridge
  · exact one_final_failure_is_in_total events .proofMerkleOpeningBridge
      merkleBridge

/-- The proof-Merkle implementation failure and its hash-collision failure
use two already-counted branches.  In particular, the hash collision is not
assigned a second "Merkle" probability budget. -/
structure ProofMerkleFailureCoverage
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (rustOpeningFailure hashCollision : Set Coins) : Prop where
  rustOpeningFailure :
    rustOpeningFailure ⊆ events.proofMerkleOpeningBridge
  hashCollision : hashCollision ⊆
    events.transcriptAndPrimitives.event .sha256Collision

theorem proof_merkle_failures_subset_total
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (rustOpeningFailure hashCollision : Set Coins)
    (coverage : ProofMerkleFailureCoverage events rustOpeningFailure
      hashCollision) :
    rustOpeningFailure ∪ hashCollision ⊆ totalFinalFailure events := by
  exact Set.union_subset
    (Set.Subset.trans coverage.rustOpeningFailure
      (one_final_failure_is_in_total events .proofMerkleOpeningBridge))
    (Set.Subset.trans coverage.hashCollision
      (one_final_failure_is_in_total events .sha256Collision))

/-- Exact containment obligations that connect the five mathematical theft
branches to already-counted final events.  Three different Poseidon2
collision witnesses share one primitive event and therefore one budget. -/
structure TheftFailureCoverage
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (extraction credential nullifierSecondPreimage noteSecondPreimage
      victimTreeCollision : Set Coins) : Prop where
  extraction : extraction ⊆ proofSoundnessFailure events
  credential : credential ⊆ events.victimCredentialRecovery
  nullifierSecondPreimage : nullifierSecondPreimage ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision
  noteSecondPreimage : noteSecondPreimage ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision
  victimTreeCollision : victimTreeCollision ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision

/-- The existing first-or-repeat fixed-victim reduction lands in the one
non-duplicated event ledger, provided the explicit cryptographic and
implementation containments hold. -/
theorem first_or_repeat_victim_spend_subset_total_final_failure
    {Address Pool Execution Coins : Type*}
    [DecidableEq Address]
    (events : FinalSecurityEvents Coins)
    (deriveMarkerAddress : Digest -> Address)
    (deployedOwner : Digest -> Digest)
    (deployedNote : Digest -> F -> F -> Digest -> Digest)
    (deployedNullifier : Digest -> Digest -> Digest)
    (deployedNode : Digest -> Digest -> Digest)
    (Accepts : V5PublicStatement -> Execution -> Prop)
    (extract : V5PublicStatement -> Execution -> V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins -> Execution)
    (committedAgain : Coins -> Prop)
    (repeatConnection : RepeatMarkerConnection (Pool := Pool)
      deriveMarkerAddress events.runtime committedAgain
      (victimNullifier deployedNullifier victim) statement.nullifier)
    (coverage : TheftFailureCoverage events
      {coins | ExtractionFailureEvent
        (V5WitnessRelation deployedOwner deployedNote deployedNullifier
          deployedNode) Accepts extract statement adversary coins}
      {coins | VictimCredentialRecoveryEvent Accepts extract statement victim
        adversary coins}
      {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
        witnessRandomness extract statement victim.opening.secret
        victim.opening.randomness adversary coins}
      {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
        extract statement victim.opening adversary coins}
      {coins | SamePositionMerkleCollisionEvent deployedOwner deployedNote
        deployedNode extract statement victim adversary coins}) :
    {coins | FirstOrRepeatVictimSpendEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts extract statement victim adversary
      committedAgain coins} ⊆ totalFinalFailure events := by
  intro coins attack
  have listed := first_or_repeat_victim_spend_implies_listed_failure
    (Pool := Pool) deriveMarkerAddress events.runtime deployedOwner deployedNote
    deployedNullifier deployedNode Accepts extract statement victim adversary
    committedAgain repeatConnection coins attack
  rcases listed with extraction | credential | nullifier | note | tree | runtime
  · exact proof_soundness_failure_subset_total events
      (coverage.extraction extraction)
  · exact one_final_failure_is_in_total events .victimCredentialRecovery
      (coverage.credential credential)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.nullifierSecondPreimage nullifier)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.noteSecondPreimage note)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.victimTreeCollision tree)
  · rcases runtime with rust | system | lock | rollback | persistence |
        finality | close
    · exact one_final_failure_is_in_total events .rustStateModelMismatch rust
    · exact one_final_failure_is_in_total events .systemProgramOrPdaMismatch
        system
    · exact one_final_failure_is_in_total events .writableAccountLockFailure lock
    · exact one_final_failure_is_in_total events
        .rejectedTransactionRollbackFailure rollback
    · exact one_final_failure_is_in_total events
        .committedMarkerPersistenceFailure persistence
    · exact one_final_failure_is_in_total events
        .finalizedStateObservationFailure finality
    · exact one_final_failure_is_in_total events .closeOrRefundModelMismatch
        close

/-- Final fixed-victim probability statement.  The right side still contains
every external cryptographic, implementation, credential, and runtime budget
supplied by the caller. -/
theorem first_or_repeat_victim_spend_probability_le_explicit_budget
    {Address Pool Execution Coins : Type*}
    [DecidableEq Address] [MeasurableSpace Coins]
    (measure : Measure Coins)
    [MeasureTheory.IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget)
    (deriveMarkerAddress : Digest -> Address)
    (deployedOwner : Digest -> Digest)
    (deployedNote : Digest -> F -> F -> Digest -> Digest)
    (deployedNullifier : Digest -> Digest -> Digest)
    (deployedNode : Digest -> Digest -> Digest)
    (Accepts : V5PublicStatement -> Execution -> Prop)
    (extract : V5PublicStatement -> Execution -> V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins -> Execution)
    (committedAgain : Coins -> Prop)
    (repeatConnection : RepeatMarkerConnection (Pool := Pool)
      deriveMarkerAddress events.runtime committedAgain
      (victimNullifier deployedNullifier victim) statement.nullifier)
    (coverage : TheftFailureCoverage events
      {coins | ExtractionFailureEvent
        (V5WitnessRelation deployedOwner deployedNote deployedNullifier
          deployedNode) Accepts extract statement adversary coins}
      {coins | VictimCredentialRecoveryEvent Accepts extract statement victim
        adversary coins}
      {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
        witnessRandomness extract statement victim.opening.secret
        victim.opening.randomness adversary coins}
      {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
        extract statement victim.opening adversary coins}
      {coins | SamePositionMerkleCollisionEvent deployedOwner deployedNote
        deployedNode extract statement victim adversary coins}) :
    measure.real {coins | FirstOrRepeatVictimSpendEvent deployedOwner
      deployedNote deployedNullifier deployedNode Accepts extract statement
      victim adversary committedAgain coins} ≤
      (1 : Real) / 2 ^ 108 + budget.total := by
  have subset := first_or_repeat_victim_spend_subset_total_final_failure
    (Pool := Pool) events deriveMarkerAddress deployedOwner deployedNote
    deployedNullifier deployedNode Accepts extract statement victim adversary
    committedAgain repeatConnection coverage
  exact (MeasureTheory.measureReal_mono subset).trans
    (total_final_failure_probability_le_released_subtotal_plus_external
      measure events budget assumed)

/-! ## Axiom audit -/

#print axioms final_failure_kind_count_is_twenty_four
#print axioms ordered_final_failure_kinds_are_exactly_once
#print axioms one_final_failure_is_in_total
#print axioms released_core_subtotal_le
#print axioms query_and_final_work_event_le_released_bound
#print axioms released_challenge_cap_le_threshold
#print axioms released_fri_cap_work_probability_le
#print axioms relation_repair_event_le_released_bound
#print axioms total_final_failure_probability_le_branch_sum
#print axioms covered_event_probability_le_branch_sum
#print axioms total_final_failure_probability_le_budget
#print axioms proof_soundness_failure_subset_total
#print axioms proof_merkle_failures_subset_total
#print axioms first_or_repeat_victim_spend_subset_total_final_failure
#print axioms first_or_repeat_victim_spend_probability_le_explicit_budget

end AspisV5FinalSecurityAccounting
