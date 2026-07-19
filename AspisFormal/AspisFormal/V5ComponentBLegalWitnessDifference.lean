import AspisFormal.V5ComponentBCorrelatedResidualCoverage

/-!
# Component B: identity-compatible state-space obstruction candidate

The previous freeze audit correctly refuted surjectivity onto an unconstrained
76-coordinate product.  Merely replacing that product by pairs with identical
271 raw mask-state coordinates is not a deployed closure theorem: the masking
coupling translates those coordinates to cancel real-message differences.
This file therefore does not define the legal witness space as an encoder
range and does not assume that all 271 state differences vanish.

Instead it isolates the largest simple state-space over-approximation allowed
by two authenticated sumcheck identities at a fixed transcript point: the
initial-claim difference and terminal-covector difference are both zero.
This is not the actual Spend-witness image and does not assert generic
zero-boundary legality over an arbitrary field.  At the Boolean row-976 point
this over-approximation contains the exact direction with
round-nine tails `c16 = 1`, `c17 = -1`.  Its physical rows are 976 and 977;
the third Boolean MLE row 988 is a reserved zero.  The terminal is unchanged,
but the first two MLE releases change by `1` and `-1`.  All 255 pads and the
dependent pivot are zero at rows 976, 977 and 988, so their image cannot cover
this direction.  The obstruction persists after multiplication by every
nonzero `eta`, matching the runtime nonzero-eta requirement.

This is an algebraic identity-compatible obstruction candidate, not yet a
deployed witness attack.  A theorem characterising the actual Spend-witness
image is absent; even realisability of this one direction remains an explicit
interface below.  That interface is not coupled here to an A-good schedule or
to the same runtime transcript as the reachability interface.  SHA/random-
oracle reachability of the row-976 point, exact
Rust serialization/encoder equality, computational Merkle/PCS properties,
entropy, and Fiat--Shamir compiler security likewise remain assumptions.
-/

namespace AspisV5ComponentBLegalWitnessDifference

open AspisV5CompactTerminal
open AspisV5InactiveClaimJointHiding
open AspisV5ComponentBCorrelatedResidualCoverage

abbrev Message (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.Message K
abbrev StateSample (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.StateSample K
abbrev StateCoordinate :=
  AspisV5ComponentBCorrelatedResidualCoverage.StateCoordinate

/-! ## The identity-compatible row-976 direction -/

/-- Round nine and the two adjacent free tail coordinates whose physical
rows are 976 and 977. -/
def roundNine : Round := ⟨9, by norm_num [AspisV5SumcheckCommitment.roundCount]⟩
def tail15 : TailDegree := ⟨15, by norm_num [AspisV5SumcheckCommitment.tailCount]⟩
def tail16 : TailDegree := ⟨16, by norm_num [AspisV5SumcheckCommitment.tailCount]⟩

/-- The exact 271-state direction: initial difference zero; only round-nine
free tails 15 and 16 are nonzero, with values `1` and `-1`. -/
def row976StateDifference (K : Type*) [Field K] : StateSample K :=
  (0, fun round degree =>
    if round = roundNine ∧ degree = tail15 then 1
    else if round = roundNine ∧ degree = tail16 then -1
    else 0)

/-- Its exact structured 1,024-row message, including every derived constant
coefficient. -/
def row976StateMessage (K : Type*) [Field K] : Message K :=
  rowMessage (row976StateDifference K).1 (row976StateDifference K).2

/-- State ordinals 259 and 260 are exactly physical rows 976 and 977. -/
def state259 : StateCoordinate := .inr (roundNine, tail15)
def state260 : StateCoordinate := .inr (roundNine, tail16)

theorem state259_wire_ordinal : (stateWireOrdinal state259 : ℕ) = 259 := by
  decide

theorem state260_wire_ordinal : (stateWireOrdinal state260 : ℕ) = 260 := by
  decide

theorem state259_physical_row : stateRow state259 = row976MLERow 0 := by
  decide

theorem state260_physical_row : stateRow state260 = row976MLERow 1 := by
  decide

/-- The third Boolean MLE read is reserved zero row 988, not an independent
state or pad coordinate. -/
theorem row988_is_reserved_zero :
    row976MLERow 2 = zeroTailRow roundNine 0 := by
  decide

/-- Exact released values of the identity-compatible direction at the three
Boolean relation points: `(1, -1, 0)`. -/
theorem row976MLE_stateMessage_values {K : Type*} [Field K] :
    row976MLE K (row976StateMessage K) 0 = 1 ∧
      row976MLE K (row976StateMessage K) 1 = -1 ∧
      row976MLE K (row976StateMessage K) 2 = 0 := by
  constructor
  · rw [row976MLE_apply, ← state259_physical_row]
    calc
      row976StateMessage K (stateRow state259) =
          stateValue (row976StateDifference K) state259 :=
        rowMessage_recovers_state (row976StateDifference K) state259
      _ = 1 := by
        simp [stateValue, state259, row976StateDifference]
  · constructor
    · rw [row976MLE_apply, ← state260_physical_row]
      calc
        row976StateMessage K (stateRow state260) =
            stateValue (row976StateDifference K) state260 :=
          rowMessage_recovers_state (row976StateDifference K) state260
        _ = -1 := by
          simp [stateValue, state260, row976StateDifference,
            show tail16 ≠ tail15 by decide]
    · rw [row976MLE_apply, row988_is_reserved_zero]
      exact rowMessage_at_zeroTailRow _ _ roundNine 0

/-- The state direction has zero initial-claim difference. -/
theorem row976StateDifference_initial_zero {K : Type*} [Field K] :
    (row976StateDifference K).1 = 0 := rfl

/-- The two nonzero stored coefficients are exactly `c16 = 1` and
`c17 = -1` in round nine. -/
theorem row976StateDifference_c16 {K : Type*} [Field K] :
    storedCoefficient (row976StateDifference K).2
      (roundNine, tail15.succ) = 1 := by
  rw [storedCoefficient_succ]
  simp [row976StateDifference]

theorem row976StateDifference_c17 {K : Type*} [Field K] :
    storedCoefficient (row976StateDifference K).2
      (roundNine, tail16.succ) = -1 := by
  rw [storedCoefficient_succ]
  simp [row976StateDifference, tail15, tail16]

private theorem tailEvaluation_two_spikes
    {K : Type*} [Field K] (first second : TailDegree)
    (hne : first ≠ second) (left right x : K) :
    AspisV5SumcheckCommitment.tailEvaluation
        (fun degree => if degree = first then left
          else if degree = second then right else 0) x =
      left * (x ^ ((first : ℕ) + 1) - AspisV5SumcheckCommitment.half) +
        right * (x ^ ((second : ℕ) + 1) -
          AspisV5SumcheckCommitment.half) := by
  classical
  rw [AspisV5SumcheckCommitment.tailEvaluation]
  have hsplit :
      (fun degree : TailDegree =>
        (if degree = first then left else if degree = second then right else 0) *
          (x ^ ((degree : ℕ) + 1) - AspisV5SumcheckCommitment.half)) =
      fun degree =>
        (if degree = first then
            left * (x ^ ((degree : ℕ) + 1) - AspisV5SumcheckCommitment.half)
          else 0) +
        (if degree = second then
            right * (x ^ ((degree : ℕ) + 1) - AspisV5SumcheckCommitment.half)
          else 0) := by
    funext degree
    by_cases hfirst : degree = first
    · subst degree
      simp [hne]
    · by_cases hsecond : degree = second
      · subst degree
        simp [hfirst]
      · simp [hfirst, hsecond]
  rw [hsplit, Finset.sum_add_distrib]
  simp

private theorem row976Point_roundNine_zero {K : Type*} [Field K] :
    row976Point K roundNine = 0 := by
  change (if false then (1 : K) else 0) = 0
  rfl

/-- Every round-tail contribution evaluates to zero at the row-976 point.
For rounds zero through eight the tail is zero; in round nine the point is
zero and the two contributions cancel because the derived constant is zero. -/
theorem row976StateDifference_tailEvaluation_zero
    {K : Type*} [Field K] (round : Round) :
    AspisV5SumcheckCommitment.tailEvaluation
        ((row976StateDifference K).2 round) (row976Point K round) = 0 := by
  by_cases hround : round = roundNine
  · subst round
    rw [row976Point_roundNine_zero]
    change AspisV5SumcheckCommitment.tailEvaluation
      (fun degree => if degree = tail15 then 1
        else if degree = tail16 then -1 else 0) 0 = 0
    rw [tailEvaluation_two_spikes tail15 tail16 (by decide)]
    norm_num [tail15, tail16]
  · have htail : (row976StateDifference K).2 round = 0 := by
      funext degree
      simp [row976StateDifference, hround]
    rw [htail]
    simp [AspisV5SumcheckCommitment.tailEvaluation]

/-- The authenticated ten-round terminal identity is unchanged by this
state direction at the row-976 transcript point. -/
theorem row976StateDifference_terminal_zero {K : Type*} [Field K] :
    AspisV5SumcheckCommitment.tenRoundTerminal
      (row976StateDifference K).1 (row976StateDifference K).2
      (row976Point K) = 0 := by
  rw [AspisV5SumcheckCommitment.tenRoundTerminal,
    AspisV5SumcheckCommitment.chainContributions_eq_closed]
  simp only [row976StateDifference_initial_zero, mul_zero, zero_add,
    AspisV5SumcheckCommitment.tenContributions]
  rw [AspisV5SumcheckCommitment.weightedContributions_ofFn_eq_sum]
  simp [row976StateDifference_tailEvaluation_zero]

/-- The largest simple identity-compatible state over-approximation used in
this file: equality of the initial claim and exact authenticated terminal
covector.  It is not a definition of the actual Spend-witness image. -/
def IdentityCompatibleStateOverapprox
    {K : Type*} [Field K] (point : Round → K) (state : StateSample K) : Prop :=
  state.1 = 0 ∧
    AspisV5SumcheckCommitment.terminalCovector point state.1 state.2 = 0

/-- The coupling-target over-approximation produced by scaling an
identity-compatible state direction by `eta` and embedding it in the exact
structured state rows.  Actual witness realisability is not asserted. -/
def IdentityCompatibleCouplingMessage
    {K : Type*} [Field K] (point : Round → K) (eta : K)
    (difference : Message K) : Prop :=
  ∃ state : StateSample K,
    IdentityCompatibleStateOverapprox point state ∧
      difference = eta • rowMessage state.1 state.2

theorem row976StateDifference_identityCompatible
    {K : Type*} [Field K] :
    IdentityCompatibleStateOverapprox (row976Point K)
      (row976StateDifference K) :=
  ⟨row976StateDifference_initial_zero, by
    rw [← AspisV5SumcheckCommitment.tenRoundTerminal_eq_terminalCovector]
    exact row976StateDifference_terminal_zero⟩

theorem row976StateMessage_mem_identityCompatibleCouplingMessage
    {K : Type*} [Field K] (eta : K) :
    IdentityCompatibleCouplingMessage (row976Point K) eta
      (eta • row976StateMessage K) := by
  exact ⟨row976StateDifference K,
    row976StateDifference_identityCompatible, rfl⟩

/-- The pad-plus-dependent-pivot image is zero on all three row-976 Boolean
MLE coordinates, so it cannot generate this identity-compatible direction. -/
theorem row976StateMessage_not_mem_padPlusPivot_range
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K) :
    row976StateMessage K ∉ LinearMap.range (padPlusPivotEncoder inactive) := by
  rintro ⟨sample, equal⟩
  have hmle := congrArg (row976MLE K) equal
  rw [row976MLE_padPlusPivot_zero inactive sample] at hmle
  have hfirst := congrFun hmle 0
  rw [row976MLE_stateMessage_values.1] at hfirst
  simp at hfirst

/-- Runtime derives `eta` with `challenge_nonzero_qm31`.  For every nonzero
eta, the required translated state direction remains outside the pad image;
this theorem does not use the imported eta-zero synthetic rank schedule. -/
theorem nonzeroEta_row976StateMessage_not_mem_padPlusPivot_range
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (eta : K) (heta : eta ≠ 0) :
    eta • row976StateMessage K ∉
      LinearMap.range (padPlusPivotEncoder inactive) := by
  rintro ⟨sample, equal⟩
  have hmle := congrArg (row976MLE K) equal
  have hpad := row976MLE_padPlusPivot_zero inactive sample
  rw [map_smul, hpad] at hmle
  have hfirst := congrFun hmle 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hfirst
  rw [row976MLE_stateMessage_values.1, mul_one] at hfirst
  exact heta hfirst.symm

/-- Residual-space form of the same obstruction.  This is the theorem shape
consumed by hiding: the nonzero-eta three-coordinate target is not in the
image of the released MLE map restricted to pads plus pivot. -/
theorem nonzeroEta_row976MLEResidual_not_mem_padPlusPivot_image
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (eta : K) (heta : eta ≠ 0) :
    eta • row976MLE K (row976StateMessage K) ∉
      LinearMap.range ((row976MLE K).comp (padPlusPivotEncoder inactive)) := by
  rintro ⟨sample, equal⟩
  have hfirst := congrFun equal 0
  rw [LinearMap.comp_apply, row976MLE_padPlusPivot_zero inactive sample,
    Pi.zero_apply] at hfirst
  simp only [Pi.smul_apply, smul_eq_mul] at hfirst
  rw [row976MLE_stateMessage_values.1, mul_one] at hfirst
  exact heta hfirst.symm

/-- Eta-one specialization, useful as a concrete nonzero algebraic target
without reusing the imported eta-zero rank-only schedule. -/
theorem row976MLE_stateDifference_not_in_pad_image
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K) :
    row976MLE K (row976StateMessage K) ∉
      LinearMap.range ((row976MLE K).comp (padPlusPivotEncoder inactive)) := by
  simpa using
    nonzeroEta_row976MLEResidual_not_mem_padPlusPivot_image
      inactive (1 : K) one_ne_zero

/-- Full 76-coordinate form of the same over-approximation obstruction.  For
an arbitrary raw release map, the tuple `(inactive, 72 raw, 3 MLE)` of the
nonzero-eta direction is outside the complete pad-plus-pivot residual image.
Only the first MLE coordinate is used; this is not an actual-witness claim. -/
theorem nonzeroEta_completeResidualOverapprox_not_mem_range
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K]
      (AspisV5ComponentBCorrelatedResidualCoverage.RawCoordinate → K))
    (eta : K) (heta : eta ≠ 0) :
    (inactive (eta • row976StateMessage K),
        raw (eta • row976StateMessage K),
        row976MLE K (eta • row976StateMessage K)) ∉
      LinearMap.range (completeResidualMap inactive raw (row976MLE K)) := by
  rintro ⟨sample, equal⟩
  rw [completeResidualMap_apply] at equal
  have hmle := congrArg
    (fun view : AspisV5ComponentBCorrelatedResidualCoverage.ResidualView K =>
      view.2.2) equal
  change row976MLE K ((padPlusPivotEncoder inactive) sample) =
    row976MLE K (eta • row976StateMessage K) at hmle
  have hfirst := congrFun hmle 0
  rw [row976MLE_padPlusPivot_zero inactive sample, Pi.zero_apply] at hfirst
  rw [map_smul] at hfirst
  simp only [Pi.smul_apply, smul_eq_mul] at hfirst
  rw [row976MLE_stateMessage_values.1, mul_one] at hfirst
  exact heta hfirst.symm

/-- **Over-approximation obstruction.**  For every nonzero eta, the
identity-compatible target over-approximation contains a difference outside
the pad-plus-dependent-pivot image.  This does not establish noncoverage of
the uncharacterised actual Spend-witness image. -/
theorem identityCompatibleOverapprox_not_covered_by_padPlusPivot
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (eta : K) (heta : eta ≠ 0) :
    ∃ difference : Message K,
      IdentityCompatibleCouplingMessage (row976Point K) eta difference ∧
        difference ∉ LinearMap.range (padPlusPivotEncoder inactive) := by
  exact ⟨eta • row976StateMessage K,
    row976StateMessage_mem_identityCompatibleCouplingMessage eta,
    nonzeroEta_row976StateMessage_not_mem_padPlusPivot_range
      inactive eta heta⟩

/-- Released-residual form: the identity-compatible over-approximation has a
concrete nonzero-eta MLE difference outside the released pad image. -/
theorem identityCompatibleMLEResidualOverapprox_not_covered_by_padPlusPivot
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (eta : K) (heta : eta ≠ 0) :
    IdentityCompatibleCouplingMessage (row976Point K) eta
        (eta • row976StateMessage K) ∧
      eta • row976MLE K (row976StateMessage K) ∉
        LinearMap.range
          ((row976MLE K).comp (padPlusPivotEncoder inactive)) :=
  ⟨row976StateMessage_mem_identityCompatibleCouplingMessage eta,
    nonzeroEta_row976MLEResidual_not_mem_padPlusPivot_image
      inactive eta heta⟩

/-! ## Explicit deployment interfaces -/

namespace UnmetDeployment

/-- Exact Rust/Lean correspondence for the structured state encoder and the
three point-major B-lane MLE releases. -/
def RustStateAndMLECorrespondence
    {K : Type*} [Field K]
    (rustEncodeState : StateSample K → Message K)
    (rustMLE : Message K → (AspisV5ComponentBCorrelatedResidualCoverage.MLECoordinate → K)) :
    Prop :=
  rustEncodeState = (fun state : StateSample K => rowMessage state.1 state.2) ∧
    rustMLE = row976MLE K

/-- Missing design theorem: the actual Spend witness-pair relation can realise
the displayed semantic state difference before multiplication by nonzero
eta.  This is deliberately not proved from recurrence algebra and is not
coupled here to an A-good schedule or to the runtime transcript below. -/
def SpendWitnessPairRealisesRow976StateDifference
    {Witness K : Type*} [Field K]
    (semanticState : Witness → StateSample K)
    (legalPair : Set (Witness × Witness)) : Prop :=
  ∃ pair ∈ legalPair,
    semanticState pair.2 - semanticState pair.1 = row976StateDifference K

/-- Missing transcript/compiler theorem: some runtime accepted transcript has
the row-976 point and a nonzero eta.  It does not assert that this is the same
execution, A-good schedule, or witness pair as the preceding interface. -/
def RuntimeReachesRow976WithNonzeroEta
    {Transcript K : Type*} [Field K]
    (accepted : Transcript → Prop) (point : Transcript → Round → K)
    (eta : Transcript → K) : Prop :=
  ∃ transcript, accepted transcript ∧ point transcript = row976Point K ∧
    eta transcript ≠ 0

end UnmetDeployment

end AspisV5ComponentBLegalWitnessDifference

#print axioms AspisV5ComponentBLegalWitnessDifference.state259_wire_ordinal
#print axioms AspisV5ComponentBLegalWitnessDifference.state260_wire_ordinal
#print axioms AspisV5ComponentBLegalWitnessDifference.state259_physical_row
#print axioms AspisV5ComponentBLegalWitnessDifference.state260_physical_row
#print axioms AspisV5ComponentBLegalWitnessDifference.row988_is_reserved_zero
#print axioms AspisV5ComponentBLegalWitnessDifference.row976MLE_stateMessage_values
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_initial_zero
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_c16
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_c17
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_tailEvaluation_zero
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_terminal_zero
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateDifference_identityCompatible
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateMessage_mem_identityCompatibleCouplingMessage
#print axioms AspisV5ComponentBLegalWitnessDifference.row976StateMessage_not_mem_padPlusPivot_range
#print axioms AspisV5ComponentBLegalWitnessDifference.nonzeroEta_row976StateMessage_not_mem_padPlusPivot_range
#print axioms AspisV5ComponentBLegalWitnessDifference.nonzeroEta_row976MLEResidual_not_mem_padPlusPivot_image
#print axioms AspisV5ComponentBLegalWitnessDifference.row976MLE_stateDifference_not_in_pad_image
#print axioms AspisV5ComponentBLegalWitnessDifference.nonzeroEta_completeResidualOverapprox_not_mem_range
#print axioms AspisV5ComponentBLegalWitnessDifference.identityCompatibleOverapprox_not_covered_by_padPlusPivot
#print axioms AspisV5ComponentBLegalWitnessDifference.identityCompatibleMLEResidualOverapprox_not_covered_by_padPlusPivot
