import V5AcceptedCompositeExactEvidence
import V5RelationAcceptanceSourceProof

/-!
# Accepted relation-call adapter

The accepted-entry extraction and the dedicated relation-caller extraction
use different Lean namespaces.  This file gives the exact, field-preserving
conversion between their inputs.  It then states the one source-transport
property needed to replace the opaque relation call in the accepted-entry
extraction with the translated caller body.

The transport property is a named premise, not an axiom and not a completed
proof.  Everything after that premise is proved: an accepted composite call
reaches the translated caller's final-polynomial gate with the same parsed
bytes, challenges, prepared claims, and terminal value.
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
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def qm31ArrayToCaller {count : Std.Usize}
    (values : Array EntryQM31 count) : Array CallerQM31 count :=
  mapFixedArray qm31ToCaller values

def privateRootsToCaller
    (roots :
      V5AcceptedEntryGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots) :
    V5RelationCallerGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots :=
  { c1 := roots.c1
    c2 := roots.c2
    later := roots.later }

def parsedToCaller (parsed : EntryParsed) : CallerParsed :=
  { gamma := qm31ToCaller parsed.gamma
    production_c1 := parsed.production_c1
    candidate_c1 := parsed.candidate_c1
    c2 := parsed.c2
    relation_scales := parsed.relation_scales
    relation_points := parsed.relation_points
    relation_claims := parsed.relation_claims
    relation_alphas := parsed.relation_alphas
    relation_final := parsed.relation_final
    v5_fold_nonces := parsed.v5_fold_nonces
    v5_batch_nonce := parsed.v5_batch_nonce
    v5_wire_prefix := parsed.v5_wire_prefix
    v5_atomic_terminal_context := parsed.v5_atomic_terminal_context
    v5_private_roots := privateRootsToCaller parsed.v5_private_roots
    v5_final_coefficients := parsed.v5_final_coefficients
    v5_relation_stress := parsed.v5_relation_stress
    v5_final_nonce := parsed.v5_final_nonce
    v5_query_selector := parsed.v5_query_selector
    v5_private_proof := parsed.v5_private_proof }

def preparedClaimsToCaller
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier)
    (claims : EntryPreparedClaims) : CallerPreparedClaims :=
  { inner :=
      { claims := mapVec qm31ToCaller claims.inner.claims
        powers := mapVec qm31ToCaller claims.inner.powers }
    c1_weight_limbs := claims.c1_weight_limbs
    c2_multipliers :=
      mapFixedArray convertMultiplier claims.c2_multipliers }

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

@[simp] theorem parsedToCaller_relation_bytes (parsed : EntryParsed) :
    (parsedToCaller parsed).relation_scales = parsed.relation_scales ∧
    (parsedToCaller parsed).relation_points = parsed.relation_points ∧
    (parsedToCaller parsed).relation_claims = parsed.relation_claims ∧
    (parsedToCaller parsed).relation_alphas = parsed.relation_alphas ∧
    (parsedToCaller parsed).relation_final = parsed.relation_final ∧
    (parsedToCaller parsed).v5_relation_stress = parsed.v5_relation_stress := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem preparedClaimsToCaller_layout
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier)
    (claims : EntryPreparedClaims) :
    (preparedClaimsToCaller convertMultiplier claims).inner.claims.val =
        claims.inner.claims.val.map qm31ToCaller ∧
    (preparedClaimsToCaller convertMultiplier claims).inner.powers.val =
        claims.inner.powers.val.map qm31ToCaller ∧
    (preparedClaimsToCaller convertMultiplier claims).c1_weight_limbs =
        claims.c1_weight_limbs ∧
    (preparedClaimsToCaller convertMultiplier claims).c2_multipliers.val =
        claims.c2_multipliers.val.map convertMultiplier := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The exact remaining cross-extraction statement for the relation caller.
Both extractions refer to the same Rust function, but the accepted-entry
snapshot deliberately leaves that function opaque.  Proving this property
requires checking the field-preserving conversion above against the fully
translated caller snapshot. -/
def AcceptedRelationPhaseSourceTransport
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier) :
    Prop :=
  ∀ (parsed : EntryParsed)
    (finalPolynomial alphas : Array EntryQM31 4#usize)
    (kappa inactiveClaim : EntryQM31)
    (roundChallenges : Array EntryQM31 10#usize)
    (preparedClaims : EntryPreparedClaims)
    (terminalClaim : EntryQM31),
    V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_relation_phase
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims = .ok (.Ok terminalClaim) →
    V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
        (parsedToCaller parsed)
        (qm31ArrayToCaller finalPolynomial)
        (qm31ArrayToCaller alphas)
        (qm31ToCaller kappa)
        (qm31ToCaller inactiveClaim)
        (qm31ArrayToCaller roundChallenges)
        (preparedClaimsToCaller convertMultiplier preparedClaims) =
      .ok (.Ok (qm31ToCaller terminalClaim))

structure AcceptedCallerRelationGate
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier)
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
        (preparedClaimsToCaller convertMultiplier preparedClaims) =
      .ok (.Ok (qm31ToCaller terminalClaim))
  finalPolynomialMatch :
    output.final_coefficients = qm31ArrayToCaller finalPolynomial
  terminalClaimMatch : output.terminal_claim = qm31ToCaller terminalClaim

theorem accepted_relation_call_reaches_checked_gate
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier)
    (transport : AcceptedRelationPhaseSourceTransport convertMultiplier)
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
      AcceptedCallerRelationGate convertMultiplier parsed finalPolynomial
        alphas kappa inactiveClaim roundChallenges preparedClaims terminalClaim
        output := by
  have callerSuccess := transport parsed finalPolynomial alphas kappa
    inactiveClaim roundChallenges preparedClaims terminalClaim success
  obtain ⟨output, finalMatch, terminalMatch⟩ :=
    AspisV5RelationAcceptanceSourceProof.extracted_mode9_success_implies_final_polynomial_match
      (parsedToCaller parsed) (qm31ArrayToCaller finalPolynomial)
      (qm31ArrayToCaller alphas) (qm31ToCaller kappa)
      (qm31ToCaller inactiveClaim) (qm31ArrayToCaller roundChallenges)
      (preparedClaimsToCaller convertMultiplier preparedClaims)
      (qm31ToCaller terminalClaim)
      callerSuccess
  exact ⟨output, {
    callerSuccess := callerSuccess
    finalPolynomialMatch := finalMatch
    terminalClaimMatch := terminalMatch
  }⟩

/-- One accepted composite execution reaches the checked relation-caller gate
with exactly the values shared with its FRI phase.  The only premise is the
named cross-extraction source transport above. -/
theorem accepted_composite_reaches_checked_relation_gate
    (convertMultiplier :
      V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier →
        V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier)
    (transport : AcceptedRelationPhaseSourceTransport convertMultiplier)
    (accountData : Slice Std.U8)
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
        finalPolynomial queries alphas friSum preparedClaims relationSum
        phaseSum openings sink output,
      AcceptedCompositeExactEvidence accountData parsed liveStatement
        statementDigest acceptedValue verifiedPrefix prefixTranscript
        verifiedTerminal relationTranscript finalPolynomial queries alphas
        friSum preparedClaims relationSum phaseSum openings sink ∧
      AcceptedCallerRelationGate convertMultiplier parsed finalPolynomial alphas
        verifiedPrefix.kappa verifiedPrefix.inactive_claim
        verifiedPrefix.round_challenges preparedClaims relationSum output := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, openings, sink, evidence⟩ :=
    accepted_composite_builds_exact_evidence accountData parsed liveStatement
      statementDigest acceptedValue success
  obtain ⟨output, gate⟩ :=
    accepted_relation_call_reaches_checked_gate convertMultiplier transport
      parsed finalPolynomial alphas verifiedPrefix.kappa
      verifiedPrefix.inactive_claim verifiedPrefix.round_challenges
      preparedClaims relationSum evidence.compositeCalls.relationCheckSuccess
  refine ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
    relationTranscript, finalPolynomial, queries, alphas, friSum,
    preparedClaims, relationSum, phaseSum, openings, sink, output, evidence,
    gate⟩

#print axioms accepted_relation_call_reaches_checked_gate
#print axioms accepted_composite_reaches_checked_relation_gate

end AspisV5AcceptedRelationPreparedAdapter
