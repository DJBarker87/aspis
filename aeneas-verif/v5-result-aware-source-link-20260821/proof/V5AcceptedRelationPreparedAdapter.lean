import V5AcceptedCompositeExactEvidence
import V5RelationAcceptanceSourceProof

/-!
# Accepted relation-call connection

The accepted-entry extraction and the dedicated relation-caller extraction
use different Lean namespaces.  The normalized accepted-entry module invokes
the translated outer relation-phase caller through an explicit
field-for-field adapter.  This file proves that a successful accepted composite
call therefore reaches that caller's final-polynomial gate with the same
parsed bytes, challenges, prepared claims, and terminal value.  It does not
remove the focused caller bundle's separately recorded helper boundaries.
-/

namespace AspisV5AcceptedRelationPreparedAdapter

open Aeneas Aeneas.Std Result
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedCompositeExactEvidence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev CallerQM31 := V5RelationCallerGenerated.aspis_core.field.QM31
abbrev EntryParsed := V5AcceptedEntryGenerated.v5_cu_probe.ParsedProbeData
abbrev CallerParsed := V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData
abbrev EntryPreparedClaims :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims
abbrev CallerPreparedClaims :=
  V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims

def mapFixedArray {A B : Type} {count : Std.Usize}
    (convert : A → B) (values : Array A count) : Array B count :=
  ⟨values.val.map convert, by simpa using values.property⟩

def mapVec {A B : Type} (convert : A → B)
    (values : alloc.vec.Vec A) : alloc.vec.Vec B :=
  ⟨values.val.map convert, by simpa using values.property⟩

def qm31ToCaller (value : EntryQM31) : CallerQM31 :=
  V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller value

def qm31ArrayToCaller {count : Std.Usize}
    (values : Array EntryQM31 count) : Array CallerQM31 count :=
  V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray
    V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller values

def preparedMultiplierToCaller
    (value : V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier) :
    V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier :=
  V5AcceptedEntryGenerated.v5_cu_probe.preparedMultiplierToRelationCaller value

def privateRootsToCaller
    (roots :
      V5AcceptedEntryGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots) :
    V5RelationCallerGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots :=
  V5AcceptedEntryGenerated.v5_cu_probe.privateRootsToRelationCaller roots

def parsedToCaller (parsed : EntryParsed) : CallerParsed :=
  V5AcceptedEntryGenerated.v5_cu_probe.parsedToRelationCaller parsed

def preparedClaimsToCaller
    (claims : EntryPreparedClaims) : CallerPreparedClaims :=
  V5AcceptedEntryGenerated.v5_cu_probe.preparedClaimsToRelationCaller claims

@[simp] theorem mapFixedArray_values
    {A B : Type} {count : Std.Usize} (convert : A → B)
    (values : Array A count) :
    (mapFixedArray convert values).val = values.val.map convert := rfl

@[simp] theorem mapVec_values
    {A B : Type} (convert : A → B) (values : alloc.vec.Vec A) :
    (mapVec convert values).val = values.val.map convert := rfl

@[simp] theorem qm31ToCaller_components (value : EntryQM31) :
    (qm31ToCaller value).c0.a = value.c0.a ∧
    (qm31ToCaller value).c0.b = value.c0.b ∧
    (qm31ToCaller value).c1.a = value.c1.a ∧
    (qm31ToCaller value).c1.b = value.c1.b := by
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem qm31ToCaller_fromRelationCaller (value : CallerQM31) :
    qm31ToCaller
        (V5AcceptedEntryGenerated.v5_cu_probe.qm31FromRelationCaller value) =
      value := by
  cases value with
  | mk c0 c1 =>
      cases c0
      cases c1
      rfl

theorem relationCaller_qm31_roundtrip (value : CallerQM31) :
    V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
        (V5AcceptedEntryGenerated.v5_cu_probe.qm31FromRelationCaller value) =
      value := by
  cases value with
  | mk c0 c1 =>
      cases c0
      cases c1
      rfl

@[simp] theorem parsedToCaller_relation_bytes (parsed : EntryParsed) :
    (parsedToCaller parsed).relation_scales = parsed.relation_scales ∧
    (parsedToCaller parsed).relation_points = parsed.relation_points ∧
    (parsedToCaller parsed).relation_claims = parsed.relation_claims ∧
    (parsedToCaller parsed).relation_alphas = parsed.relation_alphas ∧
    (parsedToCaller parsed).relation_final = parsed.relation_final ∧
    (parsedToCaller parsed).v5_relation_stress = parsed.v5_relation_stress := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem preparedClaimsToCaller_layout
    (claims : EntryPreparedClaims) :
    (preparedClaimsToCaller claims).inner.claims.val =
        claims.inner.claims.val.map qm31ToCaller ∧
    (preparedClaimsToCaller claims).inner.powers.val =
        claims.inner.powers.val.map qm31ToCaller ∧
    (preparedClaimsToCaller claims).c1_weight_limbs =
        claims.c1_weight_limbs ∧
    (preparedClaimsToCaller claims).c2_multipliers.val =
        claims.c2_multipliers.val.map preparedMultiplierToCaller := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful normalized accepted-entry relation call is exactly a
successful call of the focused, fully translated relation body. -/
theorem accepted_relation_phase_source_transport
    (parsed : EntryParsed)
    (finalPolynomial alphas : Array EntryQM31 4#usize)
    (kappa inactiveClaim : EntryQM31)
    (roundChallenges : Array EntryQM31 10#usize)
    (preparedClaims : EntryPreparedClaims)
    (terminalClaim : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_relation_phase
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims = .ok (.Ok terminalClaim)) :
    V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
        (parsedToCaller parsed)
        (qm31ArrayToCaller finalPolynomial)
        (qm31ArrayToCaller alphas)
        (qm31ToCaller kappa)
        (qm31ToCaller inactiveClaim)
        (qm31ArrayToCaller roundChallenges)
        (preparedClaimsToCaller preparedClaims) =
      .ok (.Ok (qm31ToCaller terminalClaim)) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_relation_phase at success
  simp only [parsedToCaller, qm31ArrayToCaller, qm31ToCaller,
    preparedClaimsToCaller]
  generalize hcaller :
      V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
        (V5AcceptedEntryGenerated.v5_cu_probe.parsedToRelationCaller parsed)
        (V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray
          V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
          finalPolynomial)
        (V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray
          V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller alphas)
        (V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller kappa)
        (V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller inactiveClaim)
        (V5AcceptedEntryGenerated.v5_cu_probe.relationCallerMapFixedArray
          V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
          roundChallenges)
        (V5AcceptedEntryGenerated.v5_cu_probe.preparedClaimsToRelationCaller
          preparedClaims) = callerResult at success
  cases callerResult with
  | fail error => simp at success
  | div => simp at success
  | ok callerResult =>
      cases callerResult with
      | Err error => simp at success
      | Ok callerTerminal =>
          have terminalEquality :
              V5AcceptedEntryGenerated.v5_cu_probe.qm31FromRelationCaller
                  callerTerminal = terminalClaim := by
            simpa [hcaller] using success
          congr 2
          calc
            callerTerminal =
                V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
                  (V5AcceptedEntryGenerated.v5_cu_probe.qm31FromRelationCaller
                    callerTerminal) :=
              (relationCaller_qm31_roundtrip callerTerminal).symm
            _ =
                V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
                  terminalClaim := congrArg
                    V5AcceptedEntryGenerated.v5_cu_probe.qm31ToRelationCaller
                    terminalEquality

structure AcceptedCallerRelationGate
    (parsed : EntryParsed)
    (finalPolynomial alphas : Array EntryQM31 4#usize)
    (kappa inactiveClaim : EntryQM31)
    (roundChallenges : Array EntryQM31 10#usize)
    (preparedClaims : EntryPreparedClaims)
    (terminalClaim : EntryQM31)
    (output :
      V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress) :
    Prop where
  callerSuccess :
    V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
        (parsedToCaller parsed)
        (qm31ArrayToCaller finalPolynomial)
        (qm31ArrayToCaller alphas)
        (qm31ToCaller kappa)
        (qm31ToCaller inactiveClaim)
        (qm31ArrayToCaller roundChallenges)
        (preparedClaimsToCaller preparedClaims) =
      .ok (.Ok (qm31ToCaller terminalClaim))
  finalPolynomialMatch :
    output.final_coefficients = qm31ArrayToCaller finalPolynomial
  terminalClaimMatch : output.terminal_claim = qm31ToCaller terminalClaim

theorem accepted_relation_call_reaches_checked_gate
    (parsed : EntryParsed)
    (finalPolynomial alphas : Array EntryQM31 4#usize)
    (kappa inactiveClaim : EntryQM31)
    (roundChallenges : Array EntryQM31 10#usize)
    (preparedClaims : EntryPreparedClaims)
    (terminalClaim : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_relation_phase
          parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
          preparedClaims = .ok (.Ok terminalClaim)) :
    ∃ output,
      AcceptedCallerRelationGate parsed finalPolynomial
        alphas kappa inactiveClaim roundChallenges preparedClaims terminalClaim
        output := by
  have callerSuccess := accepted_relation_phase_source_transport parsed
    finalPolynomial alphas kappa inactiveClaim roundChallenges preparedClaims
    terminalClaim success
  obtain ⟨output, finalMatch, terminalMatch⟩ :=
    AspisV5RelationAcceptanceSourceProof.extracted_mode9_success_implies_final_polynomial_match
      (parsedToCaller parsed) (qm31ArrayToCaller finalPolynomial)
      (qm31ArrayToCaller alphas) (qm31ToCaller kappa)
      (qm31ToCaller inactiveClaim) (qm31ArrayToCaller roundChallenges)
      (preparedClaimsToCaller preparedClaims)
      (qm31ToCaller terminalClaim)
      callerSuccess
  exact ⟨output, {
    callerSuccess := callerSuccess
    finalPolynomialMatch := finalMatch
    terminalClaimMatch := terminalMatch
  }⟩

/-- One accepted composite execution reaches the checked relation-caller gate
with exactly the values shared with its FRI phase. -/
theorem accepted_composite_reaches_checked_relation_gate
    (terminalBoundary : EntryTerminalBoundary)
    (accountData : Slice Std.U8)
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          terminalBoundary accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
        finalPolynomial queries alphas friSum preparedClaims relationSum
        phaseSum openings sink output,
      AcceptedCompositeExactEvidence terminalBoundary accountData parsed liveStatement
        statementDigest acceptedValue verifiedPrefix prefixTranscript
        verifiedTerminal relationTranscript finalPolynomial queries alphas
        friSum preparedClaims relationSum phaseSum openings sink ∧
      AcceptedCallerRelationGate parsed finalPolynomial alphas
        verifiedPrefix.kappa verifiedPrefix.inactive_claim
        verifiedPrefix.round_challenges preparedClaims relationSum output := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, openings, sink, evidence⟩ :=
    accepted_composite_builds_exact_evidence terminalBoundary accountData parsed liveStatement
      statementDigest acceptedValue success
  obtain ⟨output, gate⟩ :=
    accepted_relation_call_reaches_checked_gate parsed finalPolynomial alphas
      verifiedPrefix.kappa
      verifiedPrefix.inactive_claim verifiedPrefix.round_challenges
      preparedClaims relationSum evidence.compositeCalls.relationCheckSuccess
  refine ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
    relationTranscript, finalPolynomial, queries, alphas, friSum,
    preparedClaims, relationSum, phaseSum, openings, sink, output, evidence,
    gate⟩

#print axioms accepted_relation_call_reaches_checked_gate
#print axioms accepted_composite_reaches_checked_relation_gate

end AspisV5AcceptedRelationPreparedAdapter
