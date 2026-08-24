import V5AcceptedEntrySourceBridge

/-!
# Accepted prefix to the concrete batch-work check

This proof follows the generated Rust body of `verify_v5_wire_prefix` through
every successful branch until the batch nonce check.  It then unfolds the
generated batch helper and proves that the accepted call used difficulty 37.
No cryptographic assumption is introduced here.
-/

namespace AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

open Aeneas Aeneas.Std Result ControlFlow Error

attribute [local simp]
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

abbrev PrefixHash :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

theorem accepted_prefix_has_batch_gamma_and_inactive_decode
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash)
    (verified : V5AcceptedEntryGenerated.v5_cu_probe.VerifiedRealV5Wire)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    ∃ beforeSemantic afterSemantic semanticProof initialClaim semanticVerification
        beforeBatch afterBatch afterGamma inactiveOffset beforeKappa afterKappa,
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming
          beforeSemantic semanticProof initialClaim =
        .ok (.Ok semanticVerification, afterSemantic) ∧
      verified.round_challenges = semanticVerification.point ∧
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          beforeBatch parsed.v5_batch_nonce =
        .ok (.Ok (), afterBatch) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31
          afterBatch = .ok (.Ok verified.gamma, afterGamma) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_prefix_qm31
          parsed.v5_wire_prefix inactiveOffset =
        .ok (.Ok verified.inactive_claim) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31
          beforeKappa = .ok (.Ok verified.kappa, afterKappa) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨headerValid, _, success⟩ := success
  cases headerValid with
  | false => simp at success
  | true =>
    simp only [if_true] at success
    rw [bind_eq_ok_iff] at success
    obtain ⟨_, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨_, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨_, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨reservedFlow, _, success⟩ := success
    cases reservedFlow with
    | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame, core.convert.FromSame.from] at success
    | Continue _ =>
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨rootsMatch, _, success⟩ := success
      cases rootsMatch with
      | false => simp at success
      | true =>
        simp only [if_true] at success
        rw [bind_eq_ok_iff] at success
        obtain ⟨_, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨digestFlow, _, success⟩ := success
        cases digestFlow with
        | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame, core.convert.FromSame.from] at success
        | Continue _ =>
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨lambdaPair, _, success⟩ := success
          rcases lambdaPair with ⟨_, _⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨_, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨lambdaFlow, _, success⟩ := success
          cases lambdaFlow with
          | Break residual =>
            cases residual with
            | Ok impossible => nomatch impossible
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
          | Continue _ =>
            simp only at success
            rw [bind_eq_ok_iff] at success
            obtain ⟨chiPair, _, success⟩ := success
            rcases chiPair with ⟨_, _⟩
            rw [bind_eq_ok_iff] at success
            obtain ⟨_, _, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨chiFlow, _, success⟩ := success
            cases chiFlow with
            | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame, core.convert.FromSame.from] at success
            | Continue _ =>
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨_, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨_, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨zeroPair, _, success⟩ := success
              rcases zeroPair with ⟨_, _⟩
              rw [bind_eq_ok_iff] at success
              obtain ⟨_, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨zeroFlow, _, success⟩ := success
              cases zeroFlow with
              | Break residual =>
                cases residual with
                | Ok impossible => nomatch impossible
                | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at success
              | Continue _ =>
                simp only at success
                rw [bind_eq_ok_iff] at success
                obtain ⟨_, _, success⟩ := success
                rw [bind_eq_ok_iff] at success
                obtain ⟨_, _, success⟩ := success
                rw [bind_eq_ok_iff] at success
                obtain ⟨initialFlow, _, success⟩ := success
                cases initialFlow with
                | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame, core.convert.FromSame.from] at success
                | Continue initialClaim =>
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨maskPair, _, success⟩ := success
                  rcases maskPair with ⟨_, beforeSemantic⟩
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨_, _, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨maskFlow, _, success⟩ := success
                  cases maskFlow with
                  | Break residual =>
                    cases residual with
                    | Ok impossible => nomatch impossible
                    | Err error =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame, core.convert.FromSame.from] at success
                  | Continue _ =>
                    simp only at success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨_, _, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨_, _, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨semanticProof, _, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨semanticPair, semanticSuccess, success⟩ := success
                    rcases semanticPair with ⟨semanticResult, afterSemantic⟩
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨mappedSemantic, mappedSemanticSuccess, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨semanticFlow, semanticBranchSuccess, success⟩ := success
                    cases semanticFlow with
                    | Break residual =>
                      cases residual with
                      | Ok impossible => nomatch impossible
                      | Err error =>
                        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame, core.convert.FromSame.from] at success
                    | Continue semanticVerification =>
                      have hmappedSemantic := branch_eq_ok_of_continue
                        mappedSemantic semanticVerification semanticBranchSuccess
                      rw [hmappedSemantic] at mappedSemanticSuccess
                      have hsemanticResult :
                          semanticResult = .Ok semanticVerification := by
                        cases semanticResult with
                        | Err error =>
                          simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                            V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlySumcheckVerifyErrorProgramError.call_once]
                            at mappedSemanticSuccess
                        | Ok actualSemantic =>
                          simp [V5AcceptedEntryGenerated.core.result.Result.map_err]
                            at mappedSemanticSuccess
                          subst actualSemantic
                          rfl
                      rw [hsemanticResult] at semanticSuccess
                      simp only at success
                      rw [bind_eq_ok_iff] at success
                      obtain ⟨_, _, success⟩ := success
                      rw [bind_eq_ok_iff] at success
                      obtain ⟨pointsDiffer, _, success⟩ := success
                      cases pointsDiffer with
                      | true => simp at success
                      | false =>
                        simp only [Bool.false_eq_true, if_false] at success
                        rw [bind_eq_ok_iff] at success
                        obtain ⟨_, _, success⟩ := success
                        rw [bind_eq_ok_iff] at success
                        obtain ⟨_, _, success⟩ := success
                        rw [bind_eq_ok_iff] at success
                        obtain ⟨claimsDiffer, _, success⟩ := success
                        cases claimsDiffer with
                        | true => simp at success
                        | false =>
                          simp only [Bool.false_eq_true, if_false] at success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨_, _, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨_, _, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨_, _, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨_, _, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨_, _, success⟩ := success
                          rw [bind_eq_ok_iff] at success
                          obtain ⟨terminalRealFlow, _, success⟩ := success
                          cases terminalRealFlow with
                          | Break residual =>
                            cases residual with
                            | Ok impossible => nomatch impossible
                            | Err error =>
                              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                core.convert.FromSame, core.convert.FromSame.from] at success
                          | Continue _ =>
                            simp only at success
                            rw [bind_eq_ok_iff] at success
                            obtain ⟨_, _, success⟩ := success
                            rw [bind_eq_ok_iff] at success
                            obtain ⟨_, _, success⟩ := success
                            rw [bind_eq_ok_iff] at success
                            obtain ⟨terminalMaskFlow, _, success⟩ := success
                            cases terminalMaskFlow with
                            | Break residual =>
                              cases residual with
                              | Ok impossible => nomatch impossible
                              | Err error =>
                                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  core.convert.FromSame, core.convert.FromSame.from] at success
                            | Continue _ =>
                              simp only at success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨_, _, success⟩ := success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨_, _, success⟩ := success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨_, _, success⟩ := success
                              rw [bind_eq_ok_iff] at success
                              obtain ⟨terminalMaskedFlow, _, success⟩ := success
                              cases terminalMaskedFlow with
                              | Break residual =>
                                cases residual with
                                | Ok impossible => nomatch impossible
                                | Err error =>
                                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame, core.convert.FromSame.from] at success
                              | Continue _ =>
                                simp only at success
                                rw [bind_eq_ok_iff] at success
                                obtain ⟨maskedDiffers, _, success⟩ := success
                                cases maskedDiffers with
                                | true => simp at success
                                | false =>
                                  simp only [Bool.false_eq_true, if_false] at success
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨inactiveOffset, _, success⟩ := success
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨_, _, success⟩ := success
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨_, _, success⟩ := success
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨beforeBatch, _, success⟩ := success
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨batchPair, batchSuccess, success⟩ := success
                                  rcases batchPair with ⟨batchResult, afterBatch⟩
                                  rw [bind_eq_ok_iff] at success
                                  obtain ⟨batchFlow, batchBranchSuccess, success⟩ := success
                                  cases batchFlow with
                                  | Break residual =>
                                    cases residual with
                                    | Ok impossible => nomatch impossible
                                    | Err error =>
                                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                        core.convert.FromSame, core.convert.FromSame.from] at success
                                  | Continue unitValue =>
                                    have hbatchResult := branch_eq_ok_of_continue
                                      batchResult unitValue batchBranchSuccess
                                    cases unitValue
                                    rw [hbatchResult] at batchSuccess
                                    simp only at success
                                    rw [bind_eq_ok_iff] at success
                                    obtain ⟨gammaPair, gammaSuccess, success⟩ := success
                                    rcases gammaPair with ⟨gammaResult, afterGamma⟩
                                    rw [bind_eq_ok_iff] at success
                                    obtain ⟨mappedGamma, mappedGammaSuccess, success⟩ := success
                                    rw [bind_eq_ok_iff] at success
                                    obtain ⟨gammaFlow, gammaBranchSuccess, success⟩ := success
                                    cases gammaFlow with
                                    | Break residual =>
                                      cases residual with
                                      | Ok impossible => nomatch impossible
                                      | Err error => simp at success
                                    | Continue sampledGamma =>
                                      have hmappedGamma := branch_eq_ok_of_continue
                                        mappedGamma sampledGamma gammaBranchSuccess
                                      rw [hmappedGamma] at mappedGammaSuccess
                                      cases gammaResult with
                                      | Err error =>
                                        simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                                          V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedProgramError.call_once]
                                          at mappedGammaSuccess
                                      | Ok actualGamma =>
                                        simp [V5AcceptedEntryGenerated.core.result.Result.map_err]
                                          at mappedGammaSuccess
                                        subst actualGamma
                                        simp only at success
                                        rw [bind_eq_ok_iff] at success
                                        obtain ⟨inactiveResult, inactiveSuccess, success⟩ := success
                                        rw [bind_eq_ok_iff] at success
                                        obtain ⟨inactiveFlow, inactiveBranchSuccess, success⟩ := success
                                        cases inactiveFlow with
                                        | Break residual =>
                                          cases residual with
                                          | Ok impossible => nomatch impossible
                                          | Err error => simp at success
                                        | Continue inactiveClaim =>
                                          have hinactiveResult :=
                                            branch_eq_ok_of_continue inactiveResult
                                              inactiveClaim inactiveBranchSuccess
                                          rw [hinactiveResult] at inactiveSuccess
                                          simp only at success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨_, _, success⟩ := success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨_, _, success⟩ := success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨_, _, success⟩ := success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨transcript16, _, success⟩ := success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨kappaPair, kappaSuccess, success⟩ := success
                                          rcases kappaPair with ⟨kappaResult, afterKappa⟩
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨mappedKappa, mappedKappaSuccess, success⟩ := success
                                          rw [bind_eq_ok_iff] at success
                                          obtain ⟨kappaFlow, kappaBranchSuccess, success⟩ := success
                                          cases kappaFlow with
                                          | Break residual =>
                                            cases residual with
                                            | Ok impossible => nomatch impossible
                                            | Err error => simp at success
                                          | Continue kappa =>
                                            have hmappedKappa := branch_eq_ok_of_continue
                                              mappedKappa kappa kappaBranchSuccess
                                            rw [hmappedKappa] at mappedKappaSuccess
                                            have hkappaResult : kappaResult = .Ok kappa := by
                                              cases kappaResult with
                                              | Err error =>
                                                simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                                                  V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix.closure_6.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedProgramError.call_once]
                                                  at mappedKappaSuccess
                                              | Ok actualKappa =>
                                                simp [V5AcceptedEntryGenerated.core.result.Result.map_err]
                                                  at mappedKappaSuccess
                                                subst actualKappa
                                                rfl
                                            rw [hkappaResult] at kappaSuccess
                                            simp only at success
                                            rw [bind_eq_ok_iff] at success
                                            obtain ⟨gammaDiffers, _, success⟩ := success
                                            cases gammaDiffers with
                                            | true => simp at success
                                            | false =>
                                              simp only [Bool.false_eq_true, if_false] at success
                                              rw [bind_eq_ok_iff] at success
                                              obtain ⟨scale0Result, _, success⟩ := success
                                              rw [bind_eq_ok_iff] at success
                                              obtain ⟨scale0Flow, _, success⟩ := success
                                              cases scale0Flow with
                                              | Break residual =>
                                                cases residual with
                                                | Ok impossible => nomatch impossible
                                                | Err error => simp at success
                                              | Continue scale0 =>
                                                simp only at success
                                                rw [bind_eq_ok_iff] at success
                                                obtain ⟨_, _, success⟩ := success
                                                rw [bind_eq_ok_iff] at success
                                                obtain ⟨scale0Differs, _, success⟩ := success
                                                cases scale0Differs with
                                                | true => simp at success
                                                | false =>
                                                  simp only [Bool.false_eq_true, if_false] at success
                                                  rw [bind_eq_ok_iff] at success
                                                  obtain ⟨scale1Result, _, success⟩ := success
                                                  rw [bind_eq_ok_iff] at success
                                                  obtain ⟨scale1Flow, _, success⟩ := success
                                                  cases scale1Flow with
                                                  | Break residual =>
                                                    cases residual with
                                                    | Ok impossible => nomatch impossible
                                                    | Err error => simp at success
                                                  | Continue scale1 =>
                                                    simp only at success
                                                    rw [bind_eq_ok_iff] at success
                                                    obtain ⟨scale1Differs, _, success⟩ := success
                                                    cases scale1Differs with
                                                    | true => simp at success
                                                    | false =>
                                                      simp only [Bool.false_eq_true, if_false] at success
                                                      rw [bind_eq_ok_iff] at success
                                                      obtain ⟨scale2Result, _, success⟩ := success
                                                      rw [bind_eq_ok_iff] at success
                                                      obtain ⟨scale2Flow, _, success⟩ := success
                                                      cases scale2Flow with
                                                      | Break residual =>
                                                        cases residual with
                                                        | Ok impossible => nomatch impossible
                                                        | Err error => simp at success
                                                      | Continue scale2 =>
                                                        simp only at success
                                                        rw [bind_eq_ok_iff] at success
                                                        obtain ⟨_, _, success⟩ := success
                                                        rw [bind_eq_ok_iff] at success
                                                        obtain ⟨scale2Differs, _, success⟩ := success
                                                        cases scale2Differs with
                                                        | true => simp at success
                                                        | false =>
                                                          simp only [Bool.false_eq_true, if_false] at success
                                                          rw [bind_eq_ok_iff] at success
                                                          obtain ⟨terminalResult, _, success⟩ := success
                                                          rw [bind_eq_ok_iff] at success
                                                          obtain ⟨_, _, success⟩ := success
                                                          rw [bind_eq_ok_iff] at success
                                                          obtain ⟨terminalFlow, _, success⟩ := success
                                                          cases terminalFlow with
                                                          | Break residual =>
                                                            cases residual with
                                                            | Ok impossible => nomatch impossible
                                                            | Err error => simp at success
                                                          | Continue terminal =>
                                                            rcases terminal with ⟨contextStatement, context⟩
                                                            simp only at success
                                                            rw [bind_eq_ok_iff] at success
                                                            obtain ⟨statementDiffers, _, success⟩ := success
                                                            cases statementDiffers with
                                                            | true => simp at success
                                                            | false =>
                                                              simp only [Bool.false_eq_true, if_false] at success
                                                              rw [bind_eq_ok_iff] at success
                                                              obtain ⟨contextDiffers, _, success⟩ := success
                                                              cases contextDiffers with
                                                              | true => simp at success
                                                              | false =>
                                                                simp only [Bool.false_eq_true, if_false] at success
                                                                have hverified : verified.gamma = sampledGamma := by
                                                                  exact (congrArg
                                                                    (fun output => output.fst.gamma)
                                                                    (core.result.Result.Ok.inj
                                                                      (Result.ok.inj success))).symm
                                                                have hverifiedInactive :
                                                                    verified.inactive_claim = inactiveClaim := by
                                                                  exact (congrArg
                                                                    (fun output => output.fst.inactive_claim)
                                                                    (core.result.Result.Ok.inj
                                                                      (Result.ok.inj success))).symm
                                                                have hverifiedKappa :
                                                                    verified.kappa = kappa := by
                                                                  exact (congrArg
                                                                    (fun output => output.fst.kappa)
                                                                    (core.result.Result.Ok.inj
                                                                      (Result.ok.inj success))).symm
                                                                have hverifiedPoint :
                                                                    verified.round_challenges =
                                                                      semanticVerification.point := by
                                                                  exact (congrArg
                                                                    (fun output =>
                                                                      output.fst.round_challenges)
                                                                    (core.result.Result.Ok.inj
                                                                      (Result.ok.inj success))).symm
                                                                subst sampledGamma
                                                                exact ⟨beforeSemantic, afterSemantic,
                                                                  semanticProof, initialClaim,
                                                                  semanticVerification, beforeBatch,
                                                                  afterBatch, afterGamma, inactiveOffset,
                                                                  transcript16, afterKappa,
                                                                  semanticSuccess, hverifiedPoint,
                                                                  batchSuccess, gammaSuccess,
                                                                  hverifiedInactive.symm ▸ inactiveSuccess,
                                                                  hverifiedKappa.symm ▸ kappaSuccess⟩

/-- The previously used batch/gamma projection remains available with its
original statement.  The richer theorem above additionally retains the
decoder call that produced the accepted inactive claim. -/
theorem accepted_prefix_has_batch_and_gamma_successor
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash)
    (verified : V5AcceptedEntryGenerated.v5_cu_probe.VerifiedRealV5Wire)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    ∃ beforeBatch afterBatch afterGamma,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          beforeBatch parsed.v5_batch_nonce =
        .ok (.Ok (), afterBatch) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31
          afterBatch = .ok (.Ok verified.gamma, afterGamma) := by
  obtain ⟨_, _, _, _, _, beforeBatch, afterBatch, afterGamma, _, _, _, _, _,
      batchSuccess, gammaSuccess, _, _⟩ :=
    accepted_prefix_has_batch_gamma_and_inactive_decode parsed liveStatement
      statementDigest hash verified returnedTranscript success
  exact ⟨beforeBatch, afterBatch, afterGamma, batchSuccess, gammaSuccess⟩

theorem accepted_prefix_has_batch_success
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash)
    (verified : V5AcceptedEntryGenerated.v5_cu_probe.VerifiedRealV5Wire)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    ∃ beforeBatch afterBatch,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          beforeBatch parsed.v5_batch_nonce =
        .ok (.Ok (), afterBatch) := by
  obtain ⟨beforeBatch, afterBatch, _, batchSuccess, _⟩ :=
    accepted_prefix_has_batch_and_gamma_successor parsed liveStatement
      statementDigest hash verified returnedTranscript success
  exact ⟨beforeBatch, afterBatch, batchSuccess⟩

theorem batch_success_implies_difficulty_37_work
    (beforeBatch afterBatch : EntryTranscript)
    (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          beforeBatch nonce =
        .ok (.Ok (), afterBatch)) :
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeBatch nonce 37#u8 = .ok (.Ok ()) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨difficulty, difficultySuccess, success⟩ := success
  have hdifficulty : difficulty = 37#u8 := by
    have hdifficultyReverse : 37#u8 = difficulty := by
      simpa [V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_difficulty]
        using difficultySuccess
    exact hdifficultyReverse.symm
  subst difficulty
  rw [bind_eq_ok_iff] at success
  obtain ⟨workResult, workSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨workFlow, branchSuccess, success⟩ := success
  cases workFlow with
  | Break residual =>
    cases residual with
    | Ok impossible => nomatch impossible
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue unitValue =>
    have hworkResult := branch_eq_ok_of_continue
      workResult unitValue branchSuccess
    cases unitValue
    simpa [hworkResult] using workSuccess

theorem accepted_prefix_proves_batch_work
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash)
    (verified : V5AcceptedEntryGenerated.v5_cu_probe.VerifiedRealV5Wire)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    ∃ beforeBatch afterBatch,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          beforeBatch parsed.v5_batch_nonce =
        .ok (.Ok (), afterBatch) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
          beforeBatch parsed.v5_batch_nonce 37#u8 = .ok (.Ok ()) := by
  obtain ⟨beforeBatch, afterBatch, batchSuccess⟩ :=
    accepted_prefix_has_batch_success parsed liveStatement statementDigest hash
      verified returnedTranscript success
  exact ⟨beforeBatch, afterBatch, batchSuccess,
    batch_success_implies_difficulty_37_work
      beforeBatch afterBatch parsed.v5_batch_nonce batchSuccess⟩

#print axioms accepted_prefix_has_batch_success
#print axioms batch_success_implies_difficulty_37_work
#print axioms accepted_prefix_proves_batch_work

end AspisV5AcceptedEntrySourceBridge
