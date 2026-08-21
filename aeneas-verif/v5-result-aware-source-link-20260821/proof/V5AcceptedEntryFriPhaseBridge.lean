import V5AcceptedEntrySourceBridge

/-!
# Successful production FRI phase exposes its exact calls

This file inverts the successful result of the extracted production FRI
phase.  It records the private openings, prepared claims, and the successful
call to the full production FRI checker with the exact values used by the
accepted verifier.  No implementation/model assumption is introduced here.
-/

namespace AspisV5AcceptedEntryFriPhaseBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5AcceptedEntrySourceBridge

abbrev EntryParsed :=
  V5AcceptedEntryGenerated.v5_cu_probe.ParsedProbeData
abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev EntryOpenings :=
  V5AcceptedEntryGenerated.v5_cu_probe.private_openings.VerifiedV5PrivateOpenings
abbrev EntryPreparedClaims :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims
abbrev EntryFriSink :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5FriCheckSink

/-- Exact successful calls made by one successful production FRI phase. -/
structure AcceptedFriPhaseCallFacts
    (parsed : EntryParsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array EntryQM31 4#usize)
    (alphas : Array EntryQM31 4#usize)
    (gamma friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims)
    (openings : EntryOpenings)
    (sink : EntryFriSink) : Prop where
  privateSuffixSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_private_suffix
        parsed queries = .ok (.Ok openings)
  prepareClaimsSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepare_v5_pcs_claims
        gamma parsed.relation_claims = .ok (.Ok preparedClaims)
  fullFriCheckSuccess :
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.check_v5_fri_queries
        openings preparedClaims alphas finalPolynomial
        V5AcceptedEntryGenerated.aspis_core.field.M31.inv =
      .ok (.Ok sink)
  returnedSum : sink.folded_layer0_sum = friSum

def AcceptedFriPhaseCallChain
    (parsed : EntryParsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array EntryQM31 4#usize)
    (alphas : Array EntryQM31 4#usize)
    (gamma friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims) : Prop :=
  ∃ openings sink,
    AcceptedFriPhaseCallFacts parsed queries finalPolynomial alphas gamma
      friSum preparedClaims openings sink

private theorem mapped_ok_implies_original_ok
    {valueType oldError newError closureType : Type}
    (mapError : core.ops.function.FnOnce closureType oldError newError)
    (source : core.result.Result valueType oldError)
    (closure : closureType)
    (value : valueType)
    (success :
      V5AcceptedEntryGenerated.core.result.Result.map_err mapError source
          closure = .ok (.Ok value)) :
    source = .Ok value := by
  cases source with
  | Ok actual =>
      simp only [V5AcceptedEntryGenerated.core.result.Result.map_err,
        Result.ok.injEq,
        core.result.Result.Ok.injEq] at success
      subst actual
      rfl
  | Err error =>
      generalize hcall : mapError.call_once closure error = callResult
        at success
      cases callResult <;>
        simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
          Bind.bind, Aeneas.Std.bind, hcall] at success

/-- A successful extracted FRI phase exposes the exact full FRI-check call
and all of the values passed to it by the accepted verifier. -/
theorem accepted_fri_phase_builds_exact_call
    (parsed : EntryParsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array EntryQM31 4#usize)
    (alphas : Array EntryQM31 4#usize)
    (gamma friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_fri_phase
          parsed queries finalPolynomial alphas gamma =
        .ok (.Ok (friSum, preparedClaims))) :
    AcceptedFriPhaseCallChain parsed queries finalPolynomial alphas gamma
      friSum preparedClaims := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_fri_phase at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨privateResult, privateSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨privateFlow, privateBranchSuccess, success⟩ := success
  cases privateFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue openings =>
      have hprivateResult := branch_eq_ok_of_continue
        privateResult openings privateBranchSuccess
      rw [hprivateResult] at privateSuccess
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨prepareResult, prepareSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨mappedPrepare, mapPrepareSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨prepareFlow, prepareBranchSuccess, success⟩ := success
      cases prepareFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
      | Continue prepared =>
          have hmappedPrepare := branch_eq_ok_of_continue
            mappedPrepare prepared prepareBranchSuccess
          rw [hmappedPrepare] at mapPrepareSuccess
          have hprepareResult := mapped_ok_implies_original_ok
            _ prepareResult () prepared mapPrepareSuccess
          rw [hprepareResult] at prepareSuccess
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨checkResult, checkSuccess, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨mappedCheck, mapCheckSuccess, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨checkFlow, checkBranchSuccess, success⟩ := success
          cases checkFlow with
          | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at success
          | Continue sink =>
              have hmappedCheck := branch_eq_ok_of_continue
                mappedCheck sink checkBranchSuccess
              rw [hmappedCheck] at mapCheckSuccess
              have hcheckResult := mapped_ok_implies_original_ok
                _ checkResult () sink mapCheckSuccess
              rw [hcheckResult] at checkSuccess
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at success
              rcases success with ⟨hsum, hprepared⟩
              subst prepared
              refine ⟨openings, sink, ?_⟩
              exact {
                privateSuffixSuccess := privateSuccess
                prepareClaimsSuccess := prepareSuccess
                fullFriCheckSuccess := checkSuccess
                returnedSum := hsum
              }

#print axioms accepted_fri_phase_builds_exact_call

end AspisV5AcceptedEntryFriPhaseBridge
