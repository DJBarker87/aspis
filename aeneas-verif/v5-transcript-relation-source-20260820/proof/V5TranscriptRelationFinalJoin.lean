import V5TranscriptRelationSourceProof
import V5RelationAcceptanceSourceProof
import AspisFormal.V5TranscriptSourceAdapter

/-!
# Production relation transcript and final-polynomial join

The transcript extraction records the production helper's call order, round
and sample indices, and fold nonces, but deliberately erases field values and
hash state.  The maintained transcript model records the complete labels and
payload bytes.  This file defines that erasure explicitly and proves that the
two schedules are identical.

The final theorem places this schedule result next to the independently
extracted production caller theorem: a successful mode-9 relation phase can
return only a relation result whose final coefficients equal the polynomial
already accepted by FRI.  It does not claim that the still-opaque nested
relation arithmetic accepted exactly the maintained mathematical relation.
-/

namespace AspisV5TranscriptRelationFinalJoin

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open V5TranscriptRelationGenerated
open AspisV5TranscriptRelationSourceProof

/-! ## Exact observable projection of the maintained source trace -/

/-- Project a complete maintained transcript event to the observation surface
used by the Aeneas extraction.  The opaque production helpers combine the
fold-work check with the subsequent nonce absorb, so the check becomes one
`foldWork` event and the separate absorb is erased. -/
def eraseRelationEvent (input : V5TranscriptInputs) :
    TranscriptEvent → List RelationTranscriptEvent
  | .squeeze (.oodPoint round _) =>
      if round.val = 0 then [.secureCirclePoint] else [.lineOodPoint]
  | .absorb (.oodValue round sample) label _ =>
      [.absorbOod label.val round.val sample.val]
  | .squeeze (.oodMix _ _) => [.squeezeQm31]
  | .absorb (.relationSumcheck round) _ _ =>
      [.relationSumcheck round.val]
  | .verifyWork (.fold round) _ _ =>
      [.foldWork round.val (input.foldNonce round).val]
  | .absorb (.foldNonce _) _ _ => []
  | .squeeze (.foldChallenge _) => [.squeezeQm31]
  | .absorb (.circleRoot layer) _ _ =>
      if layer.val = 0 then [] else [.laterRoot (layer.val - 1)]
  | _ => []

theorem erase_source_relation_round_exact
    (input : V5TranscriptInputs) (round : Fin 4) :
    (sourceRelationRound input round).flatMap (eraseRelationEvent input) =
      roundEvents round.val (input.foldNonce round).val := by
  fin_cases round <;>
    simp [sourceRelationRound, sourceOodSample, sourceCheckAndAbsorb,
      sourceLaterRoot, laterLayer, sourceAbsorb, sourceSqueeze,
      workAbsorbSlot, AbsorbSlot.label, eraseRelationEvent, roundEvents,
      sampleEvents]

/-- The complete maintained four-round relation transcript has exactly the
same observable schedule as the Aeneas-translated production helper. -/
theorem erase_source_relation_exact (input : V5TranscriptInputs) :
    (sourceRelation input).flatMap (eraseRelationEvent input) =
      fourRoundEvents (fun round => (input.foldNonce round).val) := by
  simp [sourceRelation, fourRoundEvents, erase_source_relation_round_exact]

/-! ## Join to the exact generated execution -/

open V5TranscriptRelationGenerated

/-- For matching fold nonces, the exact Aeneas-generated production helper
appends precisely the observable projection of the maintained relation trace.
No hash or field-value equality is smuggled into this statement. -/
theorem generated_helper_matches_erased_source_relation
    (input : V5TranscriptInputs)
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (noncesMatch : ∀ round : Fin 4,
      parsed.v5_fold_nonces.val[round.val]!.val =
        (input.foldNonce round).val) :
    v5_cu_probe.replay_real_v5_relation_rounds transcript parsed =
      .ok (.Ok
        { events := transcript.events ++
            (sourceRelation input).flatMap (eraseRelationEvent input) }) := by
  rw [generated_replay_relation_rounds_exact, erase_source_relation_exact]
  have hnonces :
      (fun round : Fin 4 =>
          parsed.v5_fold_nonces.val[round.val]!.val) =
        (fun round : Fin 4 => (input.foldNonce round).val) := by
    funext round
    exact noncesMatch round
  rw [hnonces]

/-! ## Join to the production final-polynomial acceptance gate -/

open AspisV5RelationAcceptanceSourceProof

/-- The two checked production facts needed on either side of the remaining
nested relation-arithmetic seam:

1. the translated transcript helper executes the maintained relation
   schedule on the extraction's exact observation surface; and
2. if the translated production mode-9 relation caller succeeds, its returned
   coefficients equal the final polynomial already accepted by FRI, and its
   terminal claim is the value returned by the caller.

The conclusion intentionally leaves the relation verifier's returned record
existential: proving that the opaque nested loop can return success only for
the maintained mathematical relation is the remaining implementation proof. -/
theorem generated_schedule_and_final_polynomial_gate
    (input : V5TranscriptInputs)
    (transcript : V5TranscriptRelationGenerated.aspis_core.transcript.Transcript)
    (transcriptParsed : V5TranscriptRelationGenerated.v5_cu_probe.ParsedProbeData)
    (noncesMatch : ∀ round : Fin 4,
      transcriptParsed.v5_fold_nonces.val[round.val]!.val =
        (input.foldNonce round).val)
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (finalPolynomial : Array
      V5RelationCallerGenerated.aspis_core.field.QM31 4#usize)
    (alphas : Array V5RelationCallerGenerated.aspis_core.field.QM31 4#usize)
    (kappa inactiveClaim : V5RelationCallerGenerated.aspis_core.field.QM31)
    (roundChallenges : Array
      V5RelationCallerGenerated.aspis_core.field.QM31 10#usize)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (terminalClaim : V5RelationCallerGenerated.aspis_core.field.QM31)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.verify_mode9_relation_phase
          parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
          preparedClaims = .ok (.Ok terminalClaim)) :
    (V5TranscriptRelationGenerated.v5_cu_probe.replay_real_v5_relation_rounds
        transcript transcriptParsed =
      .ok (.Ok
        { events := transcript.events ++
            (sourceRelation input).flatMap (eraseRelationEvent input) })) ∧
      ∃ output :
          V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress,
        output.final_coefficients = finalPolynomial ∧
          output.terminal_claim = terminalClaim := by
  exact ⟨generated_helper_matches_erased_source_relation input transcript
      transcriptParsed noncesMatch,
    extracted_mode9_success_implies_final_polynomial_match parsed
      finalPolynomial alphas kappa inactiveClaim roundChallenges
      preparedClaims terminalClaim success⟩

#print axioms erase_source_relation_exact
#print axioms generated_helper_matches_erased_source_relation
#print axioms generated_schedule_and_final_polynomial_gate

end AspisV5TranscriptRelationFinalJoin
