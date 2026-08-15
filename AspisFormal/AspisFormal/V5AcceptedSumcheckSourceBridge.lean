import AspisFormal.V5AcceptedTerminalResidualExtraction
import AspisFormal.V5SumcheckTranscriptBinding
import AspisFormal.V5TranscriptSourceAdapter
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Accepted ten-round sumcheck: source order and mathematical consequence

This file separates four facts which were previously bundled into one
`maskedBoundary` field.

1. The verifier reads ten complete degree-27 messages.  In each round it
   checks `p(0) + p(1)` against the current claim, absorbs that message, then
   derives the challenge used to evaluate it.
2. The final value returned by the ten rounds is the evaluation of the last
   message at the tenth challenge.
3. Reference messages derived from one fixed committed polynomial supply ten
   degree-27 rounds at the same transcript point, and the authenticated
   terminal opening agrees with their final value.
4. If the accepted initial claim is wrong for that fixed oracle, but the final
   values agree, one of the ten challenges must be a root of a nonzero
   degree-at-most-27 difference polynomial.

The last statement is the ordinary sumcheck repair event.  For one fixed
round it contains at most 27 field elements.  Turning the ten adaptive events
into a probability requires a separate Fiat--Shamir/conditional-uniformity
argument; no such distribution claim is made here.

The final theorem constructs the exact `ExtractedMaskedSumcheckBoundary`
needed by `V5AcceptedTerminalResidualExtraction` from independently named
pieces.  It does not assume that acceptance alone authenticates an oracle.
-/

namespace AspisV5AcceptedSumcheckSourceBridge

open scoped BigOperators
open Polynomial
open AspisSumcheckMasking
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5SumcheckTranscriptBinding
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open AspisFormal.ArithmetizationCore
open AspisV5ProductionPublicResidualBinding
open Module

variable {K : Type*} [Field K]

abbrev Degree27Message (K : Type*) := RoundCoeff K 27

/-! ## The exact ten-round value flow -/

/-- Claim before round zero and after each of the ten rounds.  `step = 0`
is the supplied initial claim.  `step = round + 1` is the evaluation of that
round's complete degree-27 message at its transcript challenge. -/
def claimAtStep
    (initial : K)
    (messages : Fin 10 → Degree27Message K)
    (point : Fin 10 → K) : Fin 11 → K :=
  Fin.cases initial (fun round => coeffEval (messages round) (point round))

@[simp]
theorem claimAtStep_zero
    (initial : K)
    (messages : Fin 10 → Degree27Message K)
    (point : Fin 10 → K) :
    claimAtStep initial messages point 0 = initial := by
  rfl

@[simp]
theorem claimAtStep_succ
    (initial : K)
    (messages : Fin 10 → Degree27Message K)
    (point : Fin 10 → K)
    (round : Fin 10) :
    claimAtStep initial messages point round.succ =
      coeffEval (messages round) (point round) := by
  rfl

/-- The ten boundary comparisons performed by the streaming verifier.  At
round `i`, the full message has endpoint sum equal to the claim entering that
round. -/
structure TenRoundBoundaryChecks
    (initial : K)
    (messages : Fin 10 → Degree27Message K)
    (point : Fin 10 → K) : Prop where
  boundary : ∀ round,
    roundBoundary (messages round) =
      claimAtStep initial messages point round.castSucc

/-- A successful modeled production sumcheck.  The embedded `AcceptedRun`
fixes `eta` from the pre-eta transcript and fixes round `i`'s challenge from
the prefix containing messages zero through `i`.  The remaining fields are
exactly the boundary checks, nonzero-eta rejection result, and returned final
claim of `verify_state_only_sumcheck_streaming`. -/
structure AcceptedProductionTenRoundWire
    {Public Root : Type*}
    (scheme : FiatShamirSchedule Public Root K) where
  transcript : AcceptedRun scheme
  initialClaim : K
  terminalClaim : K
  etaNonzero : transcript.eta ≠ 0
  checks : TenRoundBoundaryChecks initialClaim transcript.messages
    transcript.point
  terminal : terminalClaim =
    claimAtStep initialClaim transcript.messages transcript.point (Fin.last 10)

variable {Public Root : Type*}
variable {scheme : FiatShamirSchedule Public Root K}

/-- Round zero checks its endpoint sum against the supplied initial claim. -/
theorem accepted_round_zero_boundary
    (wire : AcceptedProductionTenRoundWire scheme) :
    roundBoundary
        (wire.transcript.messages
          (⟨0, by norm_num [AspisV5SumcheckCommitment.roundCount]⟩ :
            Fin AspisV5SumcheckCommitment.roundCount)) =
      wire.initialClaim := by
  simpa [claimAtStep, AspisV5SumcheckCommitment.roundCount] using
    wire.checks.boundary (0 : Fin 10)

/-- Every later round checks its endpoint sum against the previous round's
evaluation.  This is the exact value flow of the Rust `running_claim` update. -/
theorem accepted_later_round_boundary
    (wire : AcceptedProductionTenRoundWire scheme)
    (previous : Fin 9) :
    roundBoundary (wire.transcript.messages previous.succ) =
      coeffEval (wire.transcript.messages previous.castSucc)
        (wire.transcript.point previous.castSucc) := by
  simpa [claimAtStep] using wire.checks.boundary previous.succ

/-- The returned final claim is the tenth message evaluated at the tenth
challenge. -/
theorem accepted_terminal_is_tenth_evaluation
    (wire : AcceptedProductionTenRoundWire scheme) :
    wire.terminalClaim =
      coeffEval (wire.transcript.messages (Fin.last 9))
        (wire.transcript.point (Fin.last 9)) := by
  have lastIsSuccessor : (Fin.last 10) = (Fin.last 9).succ := by
    apply Fin.ext
    rfl
  have terminal := wire.terminal
  rw [lastIsSuccessor, claimAtStep_succ] at terminal
  exact terminal

/-- Challenge `i` is derived from the committed pre-eta transcript, eta, and
exactly messages zero through `i`.  No later message or opening occurs in the
function's input. -/
theorem accepted_round_challenge_uses_exact_message_prefix
    (wire : AcceptedProductionTenRoundWire scheme)
    (round : Fin 10) :
    wire.transcript.point round =
      scheme.roundChallenge wire.transcript.preEta wire.transcript.eta
        (List.ofFn fun earlier : Fin (round.val + 1) =>
          wire.transcript.messages
            ⟨earlier.val,
              lt_of_le_of_lt (Nat.lt_succ_iff.mp earlier.isLt) round.isLt⟩) := by
  rw [wire.transcript.point_eq]
  rfl

/-! ## Exact byte framing of the ten source rounds -/

/-- The successful source-shaped driver absorbs the 448 message bytes under
label 29 with the round byte prepended, then asks for that round's challenge. -/
theorem source_round_is_framed_message_then_challenge
    (input : V5TranscriptInputs) (round : Fin 10) :
    sourceSemanticRound input round =
      [.absorb (.semanticSumcheck round) 29
          (roundByte round :: bytes (input.semanticSumcheck round)),
        .squeeze (.relationChallenge round)] := by
  rfl

/-- The sixteen little-endian bytes of coefficient `coefficient` in one
448-byte source message. -/
def semanticCoefficientBytes
    (input : V5TranscriptInputs) (round : Fin 10)
    (coefficient : Fin 28) : AspisV5ComponentCQM31Representation.QM31Bytes :=
  fun byte => input.semanticSumcheck round
    ⟨16 * coefficient.val + byte.val, by
      have hc := coefficient.isLt
      have hb := byte.isLt
      omega⟩

/-- Exact field-level relation between the bytes absorbed for a source round
and the degree-27 message used by the mathematical verifier model. -/
def SourceRoundBytesDecodeTo
    (input : V5TranscriptInputs) (round : Fin 10)
    (message : Degree27Message AspisV5ComponentCQM31TowerExact.QM31Exact) : Prop :=
  ∀ coefficient,
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
        (semanticCoefficientBytes input round coefficient) =
      some (message coefficient)

/-- The source byte projection is deliberately kept separate from the
accepted mathematical wire.  A Rust-to-Lean control-flow proof must provide
this record for the ten messages decoded by the successful run. -/
structure SourceMessageDecodeEvidence
    (input : V5TranscriptInputs)
    (messages : Fin 10 →
      Degree27Message AspisV5ComponentCQM31TowerExact.QM31Exact) : Prop where
  round : ∀ index, SourceRoundBytesDecodeTo input index (messages index)

/-- The final masked claim is the third field in the 48-byte terminal tuple
absorbed immediately after the point and evaluation tables. -/
def terminalMaskedClaimBytes
    (input : V5TranscriptInputs) :
    AspisV5ComponentCQM31Representation.QM31Bytes :=
  fun byte => input.terminalClaims
    ⟨32 + byte.val, by
      have hb := byte.isLt
      omega⟩

/-- Exact decoded-field projection from the transcript bytes to one accepted
ten-round wire over the deployed QM31 tower.  This is the small interface a
complete Rust control-flow proof must produce. -/
structure SourceAcceptedWireDecodeEvidence
    {ExactPublic ExactRoot : Type*}
    {exactScheme : FiatShamirSchedule ExactPublic ExactRoot
      AspisV5ComponentCQM31TowerExact.QM31Exact}
    (input : V5TranscriptInputs)
    (wire : AcceptedProductionTenRoundWire exactScheme) : Prop where
  initialClaim :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE input.initialClaim =
      some wire.initialClaim
  messages : SourceMessageDecodeEvidence input wire.transcript.messages
  terminalClaim :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
        (terminalMaskedClaimBytes input) =
      some wire.terminalClaim

/-! ## A fixed-polynomial reference trace and the repair event -/

/-- Ten reference degree-27 restrictions of one committed polynomial, at the
same transcript point as the accepted messages.  The initial value is the
Boolean sum of its fixed table.

This deterministic record does not itself prove when the table or messages
were fixed.  A probability theorem must separately show that the committed
polynomial is fixed before `eta`, and that round `i`'s reference message is
determined by that polynomial and the preceding challenges before challenge
`i` is sampled. -/
structure FixedOracleTenRoundTrace
    (table : Fin 1024 → K)
    (point : Fin 10 → K) where
  messages : Fin 10 → Degree27Message K
  checks : TenRoundBoundaryChecks (tableSum table) messages point

/-- Difference between the accepted running claim and the honest running
claim before/after each round. -/
def claimDifference
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (step : Fin 11) : K :=
  claimAtStep wire.initialClaim wire.transcript.messages wire.transcript.point step -
    claimAtStep (tableSum table) honest.messages wire.transcript.point step

/-- In one round the incoming claims differ but the outgoing evaluations
agree.  This is the precise degree-27 repair event. -/
def RoundRepair
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (round : Fin 10) : Prop :=
  claimDifference wire honest round.castSucc ≠ 0 ∧
    claimDifference wire honest round.succ = 0

def TenRoundRepair
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point) : Prop :=
  ∃ round, RoundRepair wire honest round

/-- Any eleven-value sequence which starts nonzero and ends zero has an
adjacent nonzero-to-zero transition. -/
theorem ten_step_sequence_has_repair
    (difference : Fin 11 → K)
    (initialNonzero : difference 0 ≠ 0)
    (terminalZero : difference (Fin.last 10) = 0) :
    ∃ round : Fin 10,
      difference round.castSucc ≠ 0 ∧ difference round.succ = 0 := by
  by_contra noRepair
  have propagate : ∀ round : Fin 10,
      difference round.castSucc ≠ 0 → difference round.succ ≠ 0 := by
    intro round beforeNonzero afterZero
    exact noRepair ⟨round, beforeNonzero, afterZero⟩
  have d1 : difference (1 : Fin 11) ≠ 0 := by
    simpa using propagate (0 : Fin 10) initialNonzero
  have d2 : difference (2 : Fin 11) ≠ 0 := by
    simpa using propagate (1 : Fin 10) d1
  have d3 : difference (3 : Fin 11) ≠ 0 := by
    simpa using propagate (2 : Fin 10) d2
  have d4 : difference (4 : Fin 11) ≠ 0 := by
    simpa using propagate (3 : Fin 10) d3
  have d5 : difference (5 : Fin 11) ≠ 0 := by
    simpa using propagate (4 : Fin 10) d4
  have d6 : difference (6 : Fin 11) ≠ 0 := by
    simpa using propagate (5 : Fin 10) d5
  have d7 : difference (7 : Fin 11) ≠ 0 := by
    simpa using propagate (6 : Fin 10) d6
  have d8 : difference (8 : Fin 11) ≠ 0 := by
    simpa using propagate (7 : Fin 10) d7
  have d9 : difference (9 : Fin 11) ≠ 0 := by
    simpa using propagate (8 : Fin 10) d8
  have d10 : difference (10 : Fin 11) ≠ 0 := by
    simpa using propagate (9 : Fin 10) d9
  exact d10 (by simpa using terminalZero)

/-- A wrong initial claim and an authenticated honest terminal force a repair
in one of the ten rounds. -/
theorem tenRoundRepair_of_wrong_initial_and_equal_terminal
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (initialWrong : wire.initialClaim ≠ tableSum table)
    (terminalEqual :
      claimAtStep wire.initialClaim wire.transcript.messages
          wire.transcript.point (Fin.last 10) =
        claimAtStep (tableSum table) honest.messages
          wire.transcript.point (Fin.last 10)) :
    TenRoundRepair wire honest := by
  apply ten_step_sequence_has_repair (claimDifference wire honest)
  · simpa [claimDifference] using sub_ne_zero.mpr initialWrong
  · simp only [claimDifference, terminalEqual, sub_self]

/-! ## The degree-27 root set for one repaired round -/

/-- Ordinary polynomial represented by the 28 wire coefficients. -/
noncomputable def messagePolynomial
    (message : Degree27Message K) : K[X] :=
  ∑ degree : Fin 28, C (message degree) * X ^ degree.val

@[simp]
theorem eval_messagePolynomial
    (message : Degree27Message K) (x : K) :
    (messagePolynomial message).eval x = coeffEval message x := by
  simp [messagePolynomial, Polynomial.eval_finsetSum, coeffEval]

@[simp]
theorem coeff_messagePolynomial
    (message : Degree27Message K) (degree : Fin 28) :
    (messagePolynomial message).coeff degree.val = message degree := by
  classical
  unfold messagePolynomial
  rw [← lcoeff_apply, map_sum]
  calc
    (∑ other : Fin 28,
        (C (message other) * X ^ other.val).coeff degree.val) =
        (C (message degree) * X ^ degree.val).coeff degree.val := by
      apply Fintype.sum_eq_single degree
      intro other hne
      simp [coeff_C_mul, Fin.ext_iff] at hne ⊢
      omega
    _ = message degree := by simp [coeff_C_mul]

theorem messagePolynomial_injective :
    Function.Injective (messagePolynomial (K := K)) := by
  intro left right equalPolynomials
  funext degree
  have equalCoefficient := congrArg
    (fun polynomial : K[X] => polynomial.coeff degree.val) equalPolynomials
  simpa using equalCoefficient

theorem natDegree_messagePolynomial_le_twenty_seven
    (message : Degree27Message K) :
    (messagePolynomial message).natDegree ≤ 27 := by
  classical
  unfold messagePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro degree _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ degree.val).trans (by omega)

/-- A repaired round's claimed and honest complete messages are different. -/
theorem roundRepair_messages_different
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (round : Fin 10)
    (repair : RoundRepair wire honest round) :
    wire.transcript.messages round ≠ honest.messages round := by
  intro equalMessages
  apply repair.1
  simp only [claimDifference]
  rw [← wire.checks.boundary round, ← honest.checks.boundary round,
    equalMessages, sub_self]

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Challenges where two fixed complete degree-27 messages evaluate equally. -/
noncomputable def degree27CollisionSet
    (claimed honest : Degree27Message K) : Finset K :=
  Finset.univ.filter fun challenge =>
    coeffEval claimed challenge = coeffEval honest challenge

/-- Distinct complete messages can agree at at most 27 field challenges. -/
theorem degree27CollisionSet_card_le
    (claimed honest : Degree27Message K)
    (different : claimed ≠ honest) :
    (degree27CollisionSet claimed honest).card ≤ 27 := by
  let difference := messagePolynomial claimed - messagePolynomial honest
  have polynomialNonzero : difference ≠ 0 := by
    intro zeroDifference
    apply different
    apply messagePolynomial_injective
    exact sub_eq_zero.mp zeroDifference
  have subsetRoots : (degree27CollisionSet claimed honest).val ⊆
      difference.roots := by
    intro challenge member
    have equalEvaluation : coeffEval claimed challenge =
        coeffEval honest challenge := by
      simpa [degree27CollisionSet] using member
    rw [Polynomial.mem_roots polynomialNonzero]
    simp only [Polynomial.IsRoot, difference, Polynomial.eval_sub,
      eval_messagePolynomial, sub_eq_zero]
    exact equalEvaluation
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (natDegree_messagePolynomial_le_twenty_seven claimed)
        (natDegree_messagePolynomial_le_twenty_seven honest)))

/-- A concrete repaired round lands in the degree-27 collision set. -/
theorem roundRepair_mem_degree27CollisionSet
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (round : Fin 10)
    (repair : RoundRepair wire honest round) :
    wire.transcript.point round ∈
      degree27CollisionSet (wire.transcript.messages round)
        (honest.messages round) := by
  rw [degree27CollisionSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have outgoingZero := repair.2
  simpa [claimDifference] using sub_eq_zero.mp outgoingZero

/-- Therefore the challenge set capable of repairing any one fixed wrong
round has size at most 27.  An adaptive ten-round probability still needs
conditional-uniformity at each message prefix. -/
theorem repaired_round_collision_set_card_le_twenty_seven
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point)
    (round : Fin 10)
    (repair : RoundRepair wire honest round) :
    (degree27CollisionSet (wire.transcript.messages round)
      (honest.messages round)).card ≤ 27 := by
  exact degree27CollisionSet_card_le _ _
    (roundRepair_messages_different wire honest round repair)

/-- Exact mass of one fixed round's collision set under a uniform field
challenge.  This is deliberately a one-round quantity. -/
noncomputable def uniformDegree27CollisionProbability
    (claimed honest : Degree27Message K) : ℚ :=
  (degree27CollisionSet claimed honest).card / Fintype.card K

theorem uniformDegree27CollisionProbability_le
    (claimed honest : Degree27Message K)
    (different : claimed ≠ honest) :
    uniformDegree27CollisionProbability claimed honest ≤
      (27 : ℚ) / Fintype.card K := by
  have fieldCardPositive : (0 : ℚ) < Fintype.card K := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : K)⟩)
  rw [uniformDegree27CollisionProbability,
    div_le_div_iff_of_pos_right fieldCardPositive]
  exact_mod_cast degree27CollisionSet_card_le claimed honest different

end FiniteField

/-! ## Construction of the fixed masked-boundary equation -/

/-- Independently auditable inputs for the sumcheck-to-boundary step.  The
mask's initial sum and the final fixed-polynomial evaluation are
authentication facts.  `outsideRepair` is the algebraic soundness event
handled above.  This record is deterministic; it does not by itself establish
the pre-challenge dependence needed for a probability bound. -/
structure AcceptedMaskedBoundaryPieces
    (wire : AcceptedProductionTenRoundWire scheme)
    (eta : K) (real mask : Fin 1024 → K) where
  etaMatches : wire.transcript.eta = eta
  honest : FixedOracleTenRoundTrace (maskedOracle eta real mask)
    wire.transcript.point
  maskInitialAuthenticated : wire.initialClaim = tableSum mask
  terminalAuthenticated : wire.terminalClaim =
    claimAtStep (tableSum (maskedOracle eta real mask)) honest.messages
      wire.transcript.point (Fin.last 10)
  outsideRepair : ¬ TenRoundRepair wire honest

/-- Outside the ten-round repair event, the accepted source-shaped value flow,
the authenticated mask sum, and the authenticated honest terminal imply the
exact fixed mixed-boundary equation. -/
theorem accepted_wire_implies_extracted_masked_boundary
    (wire : AcceptedProductionTenRoundWire scheme)
    (eta : K) (real mask : Fin 1024 → K)
    (pieces : AcceptedMaskedBoundaryPieces wire eta real mask) :
    ExtractedMaskedSumcheckBoundary eta real mask := by
  refine {
    etaNonzero := ?_
    boundary := ?_
  }
  · rw [← pieces.etaMatches]
    exact wire.etaNonzero
  · by_contra boundaryWrong
    have initialWrong : wire.initialClaim ≠
        tableSum (maskedOracle eta real mask) := by
      rw [pieces.maskInitialAuthenticated]
      exact Ne.symm boundaryWrong
    have terminalEqual :
        claimAtStep wire.initialClaim wire.transcript.messages
            wire.transcript.point (Fin.last 10) =
          claimAtStep (tableSum (maskedOracle eta real mask))
            pieces.honest.messages wire.transcript.point (Fin.last 10) := by
      rw [← wire.terminal, pieces.terminalAuthenticated]
    exact pieces.outsideRepair
      (tenRoundRepair_of_wrong_initial_and_equal_terminal wire pieces.honest
        initialWrong terminalEqual)

/-- The accepted initial claim is not the authenticated Boolean sum of the
fixed mask table. -/
def MaskInitialClaimAuthenticationFailure
    (wire : AcceptedProductionTenRoundWire scheme)
    (mask : Fin 1024 → K) : Prop :=
  wire.initialClaim ≠ tableSum mask

/-- The final value returned by the ten-round verifier is not the
authenticated evaluation of the fixed polynomial's reference trace. -/
def FixedTerminalOpeningAuthenticationFailure
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (honest : FixedOracleTenRoundTrace table wire.transcript.point) : Prop :=
  wire.terminalClaim ≠
    claimAtStep (tableSum table) honest.messages wire.transcript.point
      (Fin.last 10)

/-- Once one fixed-polynomial reference trace is supplied, failure of the desired
mixed-boundary equation has only three causes at this layer: the mask sum was
not authenticated, the fixed terminal opening was not authenticated, or a
degree-27 round repair occurred. -/
theorem accepted_wire_boundary_or_three_named_failures
    (wire : AcceptedProductionTenRoundWire scheme)
    (eta : K) (real mask : Fin 1024 → K)
    (etaMatches : wire.transcript.eta = eta)
    (honest : FixedOracleTenRoundTrace (maskedOracle eta real mask)
      wire.transcript.point) :
    ExtractedMaskedSumcheckBoundary eta real mask ∨
      MaskInitialClaimAuthenticationFailure wire mask ∨
      FixedTerminalOpeningAuthenticationFailure wire honest ∨
      TenRoundRepair wire honest := by
  by_cases maskFailure : MaskInitialClaimAuthenticationFailure wire mask
  · exact Or.inr (Or.inl maskFailure)
  by_cases terminalFailure :
      FixedTerminalOpeningAuthenticationFailure wire honest
  · exact Or.inr (Or.inr (Or.inl terminalFailure))
  by_cases repair : TenRoundRepair wire honest
  · exact Or.inr (Or.inr (Or.inr repair))
  left
  exact accepted_wire_implies_extracted_masked_boundary wire eta real mask {
    etaMatches := etaMatches
    honest := honest
    maskInitialAuthenticated := not_ne_iff.mp maskFailure
    terminalAuthenticated := not_ne_iff.mp terminalFailure
    outsideRepair := repair
  }

/-! ## Split construction of the remaining evidence record -/

variable [Algebra F K]

/-- The old three-field record can now be built from trace projection,
residual mapping, and the proved ten-round boundary construction. -/
theorem acceptedTraceAndSumcheckEvidence_of_split_pieces
    (statement : AspisV5AcceptedSpendRelation.V5PublicStatement)
    (basis : Basis (Fin 4) AspisFormal.ArithmetizationCore.F K)
    (view : AcceptedTerminalRunView K)
    (traceProjection : AcceptedTraceProjectionEvidence view)
    (residualMap : AcceptedResidualMapEvidence statement view)
    (wire : AcceptedProductionTenRoundWire scheme)
    (pieces : AcceptedMaskedBoundaryPieces wire view.eta
      (sourceUnmaskedZerocheckTable basis view.constraintRows view.theta
        view.zerocheckPoint view.mu view.helper)
      view.mask) :
    AcceptedTraceAndSumcheckEvidence statement basis view where
  traceProjection := traceProjection
  residualMap := residualMap
  maskedBoundary := accepted_wire_implies_extracted_masked_boundary wire
    view.eta
    (sourceUnmaskedZerocheckTable basis view.constraintRows view.theta
      view.zerocheckPoint view.mu view.helper)
    view.mask pieces

#print axioms claimAtStep_succ
#print axioms accepted_round_zero_boundary
#print axioms accepted_later_round_boundary
#print axioms accepted_terminal_is_tenth_evaluation
#print axioms accepted_round_challenge_uses_exact_message_prefix
#print axioms source_round_is_framed_message_then_challenge
#print axioms ten_step_sequence_has_repair
#print axioms tenRoundRepair_of_wrong_initial_and_equal_terminal
#print axioms eval_messagePolynomial
#print axioms coeff_messagePolynomial
#print axioms messagePolynomial_injective
#print axioms natDegree_messagePolynomial_le_twenty_seven
#print axioms degree27CollisionSet_card_le
#print axioms roundRepair_messages_different
#print axioms roundRepair_mem_degree27CollisionSet
#print axioms repaired_round_collision_set_card_le_twenty_seven
#print axioms uniformDegree27CollisionProbability_le
#print axioms accepted_wire_implies_extracted_masked_boundary
#print axioms accepted_wire_boundary_or_three_named_failures
#print axioms acceptedTraceAndSumcheckEvidence_of_split_pieces

end AspisV5AcceptedSumcheckSourceBridge
