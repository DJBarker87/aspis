import AspisFormal.V5AcceptedSumcheckSourceBridge
import AspisFormal.V6AcceptedPathObligations

/-!
# Exact Tag-73 compact semantic-sumcheck binding

The Tag-73 wire sends twenty-seven field elements in each semantic round.  It
omits coefficient one and reconstructs it from the incoming claim.  This file
connects that compact representation to the complete degree-27 messages used
by the accepted-sumcheck soundness development.

The important consequence is structural: once the initial claim, the 270
sent fields, and the ten transcript challenges are fixed, all 280 polynomial
coefficients, every boundary check, and the returned terminal claim are fixed.
There is no independent boundary premise at this layer.

This is a deterministic algebraic/source-shape result.  Authentication of the
fixed mask initial claim, agreement of the semantic callback with the fixed
masked oracle at the terminal point, and the adaptive Fiat--Shamir probability
bound remain separately named obligations.
-/

set_option autoImplicit false

namespace AspisPool.V7CompactSemanticBinding

open AspisSumcheckMasking
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6TranscriptRelationGrammar

variable {K : Type*} [Field K]

/-- The complete degree-27 message reconstructed from one compact Tag-73
round.  Coefficient zero and coefficients two through twenty-seven are sent;
coefficient one is the unique value making `p(0) + p(1)` equal the incoming
claim. -/
def compactSemanticMessage
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) : Degree27Message K :=
  fun coefficient =>
    semanticCoefficient
      (semanticRunningClaim fields point round.val)
      (semanticParts fields round) coefficient

/-- All ten complete messages reconstructed from the compact fixed section. -/
def compactSemanticMessages
    (fields : FixedFieldView K) (point : Fin 10 → K) :
    Fin 10 → Degree27Message K :=
  fun round => compactSemanticMessage fields point round

@[simp]
theorem compactSemanticMessage_coefficient_zero
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    compactSemanticMessage fields point round 0 =
      fields.semanticSent round 0 := by
  simp [compactSemanticMessage, semanticCoefficient, semanticParts]

@[simp]
theorem compactSemanticMessage_coefficient_one
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    compactSemanticMessage fields point round 1 =
      reconstructedSemanticLinear
        (semanticRunningClaim fields point round.val)
        (semanticParts fields round) := by
  simp [compactSemanticMessage, semanticCoefficient]

/-- Coefficients two through twenty-seven are exactly sent fields one through
twenty-six. -/
theorem compactSemanticMessage_higher
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) (higher : Fin 26) :
    compactSemanticMessage fields point round
        ⟨higher.val + 2, by omega⟩ =
      fields.semanticSent round ⟨higher.val + 1, by omega⟩ := by
  simp [compactSemanticMessage, semanticCoefficient, semanticParts]

/-- The complete reconstructed coefficient sum is the sent constant, the
reconstructed linear coefficient, and the twenty-six sent higher values. -/
theorem sum_compactSemanticMessage
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    ∑ coefficient : Fin 28,
        compactSemanticMessage fields point round coefficient =
      (semanticParts fields round).constant +
        reconstructedSemanticLinear
          (semanticRunningClaim fields point round.val)
          (semanticParts fields round) +
        ∑ higher : Fin 26, (semanticParts fields round).higher higher := by
  calc
    (∑ coefficient : Fin 28,
        compactSemanticMessage fields point round coefficient) =
        compactSemanticMessage fields point round 0 +
          ∑ tail : Fin 27,
            compactSemanticMessage fields point round tail.succ := by
      rw [Fin.sum_univ_succ]
    _ = compactSemanticMessage fields point round 0 +
        (compactSemanticMessage fields point round 1 +
          ∑ higher : Fin 26,
            compactSemanticMessage fields point round higher.succ.succ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.succ_zero_eq_one]
    _ = fields.semanticSent round 0 +
        (reconstructedSemanticLinear
            (semanticRunningClaim fields point round.val)
            (semanticParts fields round) +
          ∑ higher : Fin 26, (semanticParts fields round).higher higher) := by
      rw [compactSemanticMessage_coefficient_zero,
        compactSemanticMessage_coefficient_one]
      congr 2
    _ = (semanticParts fields round).constant +
        reconstructedSemanticLinear
          (semanticRunningClaim fields point round.val)
          (semanticParts fields round) +
        ∑ higher : Fin 26, (semanticParts fields round).higher higher := by
      simp only [semanticParts, add_assoc]

/-- The omitted linear coefficient makes each compact message satisfy the
exact incoming boundary. -/
theorem roundBoundary_compactSemanticMessage
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    roundBoundary (compactSemanticMessage fields point round) =
      semanticRunningClaim fields point round.val := by
  rw [roundBoundary, compactSemanticMessage_coefficient_zero,
    sum_compactSemanticMessage]
  simpa only [semanticBoundaryFromParts, semanticParts, add_assoc] using
    reconstructed_semantic_linear_has_exact_boundary
      (semanticRunningClaim fields point round.val)
      (semanticParts fields round)

/-- Evaluating reconstructed round `i` at challenge `i` is precisely the
recursive claim entering round `i+1`. -/
theorem coeffEval_compactSemanticMessage
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (round : Fin 10) :
    coeffEval (compactSemanticMessage fields point round) (point round) =
      semanticRunningClaim fields point (round.val + 1) := by
  rw [semanticRunningClaim]
  simp only [round.isLt, dite_true]
  rfl

/-- The generic eleven-step claim chain and the Tag-73 recursive claim are
definitionally the same after compact reconstruction. -/
theorem claimAtStep_compactSemanticMessages
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (step : Fin 11) :
    claimAtStep fields.initialClaim
        (compactSemanticMessages fields point) point step =
      semanticRunningClaim fields point step.val := by
  refine Fin.cases ?_ (fun round => ?_) step
  · rfl
  · simpa [compactSemanticMessages] using
      coeffEval_compactSemanticMessage fields point round

/-- All ten production boundary checks follow from compact coefficient-one
reconstruction. -/
theorem compactSemanticMessages_boundaryChecks
    (fields : FixedFieldView K) (point : Fin 10 → K) :
    TenRoundBoundaryChecks fields.initialClaim
      (compactSemanticMessages fields point) point := by
  refine ⟨?_⟩
  intro round
  calc
    roundBoundary (compactSemanticMessages fields point round) =
        semanticRunningClaim fields point round.val := by
      simpa only [compactSemanticMessages] using
        roundBoundary_compactSemanticMessage fields point round
    _ = claimAtStep fields.initialClaim
        (compactSemanticMessages fields point) point round.castSucc := by
      symm
      rw [claimAtStep_compactSemanticMessages]
      rfl

/-- The tenth compact-message evaluation is exactly the terminal claim used
by the Tag-73 semantic callback. -/
theorem compactSemanticMessages_terminal
    (fields : FixedFieldView K) (point : Fin 10 → K) :
    semanticTerminalClaim fields point =
      claimAtStep fields.initialClaim
        (compactSemanticMessages fields point) point (Fin.last 10) := by
  rw [claimAtStep_compactSemanticMessages]
  rfl

variable {Public Root : Type*}
variable {scheme : FiatShamirSchedule Public Root K}

/-- Minimal source/transcript evidence needed to identify an accepted run's
complete mathematical messages with the Tag-73 compact fixed fields.  The
message equality is the byte-decoder/source bridge; no algebraic boundary or
terminal equation is assumed. -/
structure CompactAcceptedRunEvidence
    (fields : FixedFieldView K) (transcript : AcceptedRun scheme) : Prop where
  messages : transcript.messages =
    compactSemanticMessages fields transcript.point
  etaNonzero : transcript.eta ≠ 0

/-- Construct the generic accepted ten-round wire from exact compact Tag-73
fields.  Boundary checks and terminal recurrence are proved above rather than
supplied by the caller. -/
def acceptedProductionWireOfCompact
    (fields : FixedFieldView K) (transcript : AcceptedRun scheme)
    (evidence : CompactAcceptedRunEvidence fields transcript) :
    AcceptedProductionTenRoundWire scheme where
  transcript := transcript
  initialClaim := fields.initialClaim
  terminalClaim := semanticTerminalClaim fields transcript.point
  etaNonzero := evidence.etaNonzero
  checks := by
    rw [evidence.messages]
    exact compactSemanticMessages_boundaryChecks fields transcript.point
  terminal := by
    rw [evidence.messages]
    exact compactSemanticMessages_terminal fields transcript.point

/-- Exact coefficient-level consequence of the source bridge: every one of
the 280 complete wire coefficients is fixed by the 270 sent fields, the
initial claim, and the preceding challenges. -/
theorem acceptedProductionWireOfCompact_message
    (fields : FixedFieldView K) (transcript : AcceptedRun scheme)
    (evidence : CompactAcceptedRunEvidence fields transcript)
    (round : Fin AspisV5SumcheckCommitment.roundCount)
    (coefficient : Fin 28) :
    (acceptedProductionWireOfCompact fields transcript evidence).transcript.messages
        round coefficient =
      compactSemanticMessage fields transcript.point
        ⟨round.val, by
          simpa [AspisV5SumcheckCommitment.roundCount] using round.isLt⟩
        coefficient := by
  change transcript.messages round coefficient = _
  rw [evidence.messages]
  rfl

/-- Instantiate the already-kernel-checked degree-27 repair theorem with the
exact compact Tag-73 wire.  This is the deterministic K1.5 sumcheck boundary:
outside mask-initial authentication failure, terminal-opening authentication
failure, or a named ten-round repair, the mixed Boolean boundary is exact. -/
theorem compact_acceptance_boundary_or_three_named_failures
    (fields : FixedFieldView K) (transcript : AcceptedRun scheme)
    (evidence : CompactAcceptedRunEvidence fields transcript)
    (eta : K) (real mask : Fin 1024 → K)
    (etaMatches : transcript.eta = eta)
    (honest : FixedOracleTenRoundTrace (maskedOracle eta real mask)
      transcript.point) :
    let wire := acceptedProductionWireOfCompact fields transcript evidence
    ExtractedMaskedSumcheckBoundary eta real mask ∨
      MaskInitialClaimAuthenticationFailure wire mask ∨
      FixedTerminalOpeningAuthenticationFailure wire honest ∨
      TenRoundRepair wire honest := by
  exact accepted_wire_boundary_or_three_named_failures
    (acceptedProductionWireOfCompact fields transcript evidence)
    eta real mask etaMatches honest

#print axioms roundBoundary_compactSemanticMessage
#print axioms compactSemanticMessages_boundaryChecks
#print axioms compactSemanticMessages_terminal
#print axioms acceptedProductionWireOfCompact_message
#print axioms compact_acceptance_boundary_or_three_named_failures

end AspisPool.V7CompactSemanticBinding
