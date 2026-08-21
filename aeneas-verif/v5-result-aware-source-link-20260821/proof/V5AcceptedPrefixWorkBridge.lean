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

abbrev PrefixHash :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

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
                | Continue _ =>
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨maskPair, _, success⟩ := success
                  rcases maskPair with ⟨_, _⟩
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
                    obtain ⟨_, _, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨semanticPair, _, success⟩ := success
                    rcases semanticPair with ⟨_, _⟩
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨_, _, success⟩ := success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨semanticFlow, _, success⟩ := success
                    cases semanticFlow with
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
                                  obtain ⟨_, _, success⟩ := success
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
