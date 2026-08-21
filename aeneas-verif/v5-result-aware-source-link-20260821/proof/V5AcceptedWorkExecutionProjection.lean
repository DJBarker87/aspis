import V5AcceptedRemainingWorkBridge

/-!
# Accepted production work execution

This file projects the six successful work checks already obtained from the
generated production entry point onto the concrete transcript operations that
the source executed.  It does not introduce a second acceptance assumption.
-/

namespace AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5NonceWorkAuthentication

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

def entryWorkWireView (parsed : EntryParsed) :
    AspisV5NonceWorkAuthentication.WorkWireView where
  nonces
    | .batch => nonceOfGenerated parsed.v5_batch_nonce
    | .fold round =>
        nonceOfGenerated parsed.v5_fold_nonces.val[round.val]!
    | .finalQuery => nonceOfGenerated parsed.v5_final_nonce

theorem entry_transcript_input_has_exact_work_nonces
    (parsed : EntryParsed) (statementDigest : Array Std.U8 32#usize) :
    (entryTranscriptInput parsed statementDigest).nonce =
      AspisV5NonceWorkAuthentication.WorkWireView.nonces
        (entryWorkWireView parsed) := by
  funext kind
  cases kind <;> rfl

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

theorem generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

theorem generated_u64_bytes_are_exact_nonce_le (value : Std.U64) :
    (core.num.U64.to_le_bytes value).val.map byteOfGenerated =
      List.ofFn (nonceLEBytes (nonceOfGenerated value)) := by
  have modelRoundTrip :
      AspisV5PrefixNonceEncodingProof.modelNonce (nonceOfGenerated value) =
        value := by
    apply UScalar.eq_of_val_eq
    rfl
  have exactBytes :=
    AspisV5PrefixNonceEncodingProof.generated_nonce_bytes_are_exact
      (nonceOfGenerated value)
  rw [modelRoundTrip] at exactBytes
  change
    (core.num.U64.to_le_bytes value).val.map
        AspisV5PrefixNonceEncodingProof.generatedToByte =
      List.ofFn (nonceLEBytes (nonceOfGenerated value))
  exact exactBytes

theorem generated_fold_work_record_exact
    (round : Std.Usize) (nonce : Std.U64) :
    V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_record round nonce =
      .ok (Array.make 9#usize
        [UScalar.cast .U8 round,
         (core.num.U64.to_le_bytes nonce).val[0]!,
         (core.num.U64.to_le_bytes nonce).val[1]!,
         (core.num.U64.to_le_bytes nonce).val[2]!,
         (core.num.U64.to_le_bytes nonce).val[3]!,
         (core.num.U64.to_le_bytes nonce).val[4]!,
         (core.num.U64.to_le_bytes nonce).val[5]!,
         (core.num.U64.to_le_bytes nonce).val[6]!,
         (core.num.U64.to_le_bytes nonce).val[7]!]) := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_record, lift,
    generated_array_index_run]

theorem require_real_v5_work_success_implies_grinding_ok
    (before : EntryTranscript) (nonce : Std.U64) (bits : Std.U8)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
          before nonce bits = .ok (.Ok ())) :
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before nonce bits = .ok true := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work at success
  unfold V5AcceptedEntryGenerated.v5_cu_probe.v5_real_work_is_valid at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨valid, grindingSuccess, success⟩ := success
  cases valid <;> simp_all

theorem batch_helper_success_implies_absorb
    (before after : EntryTranscript) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
          before nonce = .ok (.Ok (), after)) :
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_batch_nonce
        before nonce = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨difficulty, difficultySuccess, success⟩ := success
  have hdifficulty : difficulty = 37#u8 := by
    have reverse : 37#u8 = difficulty := by
      simpa [V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_difficulty]
        using difficultySuccess
    exact reverse.symm
  subst difficulty
  rw [bind_eq_ok_iff] at success
  obtain ⟨workResult, workSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨workFlow, workBranchSuccess, success⟩ := success
  cases workFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue unitValue =>
      have hworkResult := branch_eq_ok_of_continue
        workResult unitValue workBranchSuccess
      cases unitValue
      rw [hworkResult] at workSuccess
      rw [bind_eq_ok_iff] at success
      obtain ⟨absorbed, absorbSuccess, success⟩ := success
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq, true_and] at success
      subst absorbed
      exact absorbSuccess

theorem fold_helper_success_implies_absorb
    (before after : EntryTranscript) (round : Std.Usize) (nonce : Std.U64)
    (bits : Std.U8)
    (difficulty :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_difficulty round =
        .ok (some bits))
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          before round nonce = .ok (.Ok (), after)) :
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_fold_nonce
        before round nonce = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selected, selectedSuccess, success⟩ := success
  rw [difficulty] at selectedSuccess
  simp only [Result.ok.injEq, Option.some.injEq] at selectedSuccess
  subst selected
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedResult, selectedResultSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedFlow, selectedBranchSuccess, success⟩ := success
  cases selectedFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue selectedBits =>
      have hselectedResult := branch_eq_ok_of_continue
        selectedResult selectedBits selectedBranchSuccess
      rw [hselectedResult] at selectedResultSuccess
      simp [V5AcceptedEntryGenerated.core.option.Option.ok_or] at selectedResultSuccess
      subst selectedBits
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨workResult, workSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨workFlow, workBranchSuccess, success⟩ := success
      cases workFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
      | Continue unitValue =>
          have hworkResult := branch_eq_ok_of_continue
            workResult unitValue workBranchSuccess
          cases unitValue
          rw [hworkResult] at workSuccess
          rw [bind_eq_ok_iff] at success
          obtain ⟨absorbed, absorbSuccess, success⟩ := success
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq, true_and] at success
          subst absorbed
          exact absorbSuccess

theorem final_helper_success_implies_absorb
    (before after : EntryTranscript) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          before nonce = .ok (.Ok (), after)) :
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_final_nonce
        before nonce = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨difficulty, difficultySuccess, success⟩ := success
  have hdifficulty : difficulty = 32#u8 := by
    have reverse : 32#u8 = difficulty := by
      simpa [V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_difficulty]
        using difficultySuccess
    exact reverse.symm
  subst difficulty
  rw [bind_eq_ok_iff] at success
  obtain ⟨workResult, workSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨workFlow, workBranchSuccess, success⟩ := success
  cases workFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at success
  | Continue unitValue =>
      have hworkResult := branch_eq_ok_of_continue
        workResult unitValue workBranchSuccess
      cases unitValue
      rw [hworkResult] at workSuccess
      rw [bind_eq_ok_iff] at success
      obtain ⟨absorbed, absorbSuccess, success⟩ := success
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq, true_and] at success
      subst absorbed
      exact absorbSuccess

theorem batch_absorb_success_has_actual_transcript_call
    (before after : EntryTranscript) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_batch_nonce
          before nonce = .ok after) :
    ∃ label record,
      V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_absorb_input nonce =
          .ok (label, record) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
          before label (Array.to_slice record) = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_batch_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨input, inputSuccess, success⟩ := success
  rcases input with ⟨label, record⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨slice, sliceSuccess, success⟩ := success
  simp only [lift, Result.ok.injEq] at sliceSuccess
  subst slice
  exact ⟨label, record, inputSuccess, success⟩

theorem fold_absorb_success_has_actual_transcript_call
    (before after : EntryTranscript) (round : Std.Usize) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_fold_nonce
          before round nonce = .ok after) :
    ∃ label record,
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_absorb_input
          round nonce = .ok (label, record) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
          before label (Array.to_slice record) = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_fold_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨input, inputSuccess, success⟩ := success
  rcases input with ⟨label, record⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨slice, sliceSuccess, success⟩ := success
  simp only [lift, Result.ok.injEq] at sliceSuccess
  subst slice
  exact ⟨label, record, inputSuccess, success⟩

theorem final_absorb_success_has_actual_transcript_call
    (before after : EntryTranscript) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_final_nonce
          before nonce = .ok after) :
    ∃ label record,
      V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_absorb_input nonce =
          .ok (label, record) ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
          before label (Array.to_slice record) = .ok after := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_final_nonce at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨input, inputSuccess, success⟩ := success
  rcases input with ⟨label, record⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨slice, sliceSuccess, success⟩ := success
  simp only [lift, Result.ok.injEq] at sliceSuccess
  subst slice
  exact ⟨label, record, inputSuccess, success⟩

theorem batch_absorb_input_success_components
    (nonce : Std.U64) (label : Std.U8) (record : Array Std.U8 8#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_absorb_input nonce =
        .ok (label, record)) :
    record = core.num.U64.to_le_bytes nonce ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE =
        .ok label := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_absorb_input at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedRecord, recordSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedLabel, labelSuccess, success⟩ := success
  simp only [Result.ok.injEq, Prod.mk.injEq] at success
  have recordExact :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_record nonce =
        .ok (core.num.U64.to_le_bytes nonce) := by rfl
  rw [recordExact] at recordSuccess
  simp only [Result.ok.injEq] at recordSuccess
  rw [success.2] at recordSuccess
  rw [success.1] at labelSuccess
  exact ⟨recordSuccess.symm, labelSuccess⟩

theorem final_absorb_input_success_components
    (nonce : Std.U64) (label : Std.U8) (record : Array Std.U8 8#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_absorb_input nonce =
        .ok (label, record)) :
    record = core.num.U64.to_le_bytes nonce ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.label.GRIND_NONCE =
        .ok label := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_absorb_input at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedRecord, recordSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedLabel, labelSuccess, success⟩ := success
  simp only [Result.ok.injEq, Prod.mk.injEq] at success
  have recordExact :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_record nonce =
        .ok (core.num.U64.to_le_bytes nonce) := by rfl
  rw [recordExact] at recordSuccess
  simp only [Result.ok.injEq] at recordSuccess
  rw [success.2] at recordSuccess
  rw [success.1] at labelSuccess
  exact ⟨recordSuccess.symm, labelSuccess⟩

theorem fold_absorb_input_success_components
    (round : Std.Usize) (nonce : Std.U64) (label : Std.U8)
    (record : Array Std.U8 9#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_absorb_input
        round nonce = .ok (label, record)) :
    V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_record round nonce =
        .ok record ∧
      V5AcceptedEntryGenerated.aspis_core.transcript.label.M31_CIRCLE_FOLD_POW_NONCE =
        .ok label := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_absorb_input at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedRecord, recordSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectedLabel, labelSuccess, success⟩ := success
  simp only [Result.ok.injEq, Prod.mk.injEq] at success
  rw [success.2] at recordSuccess
  rw [success.1] at labelSuccess
  exact ⟨recordSuccess, labelSuccess⟩

theorem batch_absorb_record_matches_maintained_payload
    (nonce : Std.U64) (label : Std.U8) (record : Array Std.U8 8#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_batch_work_absorb_input nonce =
        .ok (label, record)) :
    record.val.map byteOfGenerated =
      workAbsorbPayload .batch (nonceOfGenerated nonce) := by
  have components := batch_absorb_input_success_components
    nonce label record success
  rw [components.1]
  simpa [workAbsorbPayload] using generated_u64_bytes_are_exact_nonce_le nonce

theorem final_absorb_record_matches_maintained_payload
    (nonce : Std.U64) (label : Std.U8) (record : Array Std.U8 8#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_final_work_absorb_input nonce =
        .ok (label, record)) :
    record.val.map byteOfGenerated =
      workAbsorbPayload .finalQuery (nonceOfGenerated nonce) := by
  have components := final_absorb_input_success_components
    nonce label record success
  rw [components.1]
  simpa [workAbsorbPayload] using generated_u64_bytes_are_exact_nonce_le nonce

theorem fold_work_record_has_exact_nine_bytes
    (round : Std.Usize) (nonce : Std.U64)
    (record : Array Std.U8 9#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_record round nonce =
        .ok record) :
    record.val[0]! = UScalar.cast .U8 round ∧
      ∀ index : Fin 8,
        record.val[index.val + 1]! =
          (core.num.U64.to_le_bytes nonce).val[index.val]! := by
  rw [generated_fold_work_record_exact round nonce] at success
  simp only [Result.ok.injEq] at success
  subst record
  constructor
  · simp [Array.make]
  · intro index
    fin_cases index <;> simp [Array.make]

/-- The generated fold record is not merely nine bytes long: after the exact
Rust-to-model byte conversion it is the maintained `[round || nonce_le64]`
payload.  Restricting `round` to `Fin 4` is the production loop bound. -/
private theorem list_of_length_eight_is_exact_gets
    {T : Type} [Inhabited T] (values : List T)
    (hlength : values.length = 8) :
    values = [values[0]!, values[1]!, values[2]!, values[3]!,
      values[4]!, values[5]!, values[6]!, values[7]!] := by
  apply List.ext_getElem
  · simp [hlength]
  · intro index hleft hright
    have hindex : index < 8 := by simpa [hlength] using hleft
    interval_cases index
    · change values[0] = values[0]!
      exact list_get_eq_getElemBang values 0 hleft
    · change values[1] = values[1]!
      exact list_get_eq_getElemBang values 1 hleft
    · change values[2] = values[2]!
      exact list_get_eq_getElemBang values 2 hleft
    · change values[3] = values[3]!
      exact list_get_eq_getElemBang values 3 hleft
    · change values[4] = values[4]!
      exact list_get_eq_getElemBang values 4 hleft
    · change values[5] = values[5]!
      exact list_get_eq_getElemBang values 5 hleft
    · change values[6] = values[6]!
      exact list_get_eq_getElemBang values 6 hleft
    · change values[7] = values[7]!
      exact list_get_eq_getElemBang values 7 hleft

theorem fold_absorb_record_matches_maintained_payload
    (generatedRound : Std.Usize) (round : Fin 4)
    (hround : generatedRound.val = round.val) (nonce : Std.U64)
    (record : Array Std.U8 9#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_record
          generatedRound nonce = .ok record) :
    record.val.map byteOfGenerated =
      workAbsorbPayload (.fold round) (nonceOfGenerated nonce) := by
  rw [generated_fold_work_record_exact
    generatedRound nonce] at success
  simp only [Result.ok.injEq] at success
  subst record
  rw [show
    (Array.make 9#usize
      [UScalar.cast .U8 generatedRound,
       (core.num.U64.to_le_bytes nonce).val[0]!,
       (core.num.U64.to_le_bytes nonce).val[1]!,
       (core.num.U64.to_le_bytes nonce).val[2]!,
       (core.num.U64.to_le_bytes nonce).val[3]!,
       (core.num.U64.to_le_bytes nonce).val[4]!,
       (core.num.U64.to_le_bytes nonce).val[5]!,
       (core.num.U64.to_le_bytes nonce).val[6]!,
       (core.num.U64.to_le_bytes nonce).val[7]!]).val =
      [UScalar.cast .U8 generatedRound,
       (core.num.U64.to_le_bytes nonce).val[0]!,
       (core.num.U64.to_le_bytes nonce).val[1]!,
       (core.num.U64.to_le_bytes nonce).val[2]!,
       (core.num.U64.to_le_bytes nonce).val[3]!,
       (core.num.U64.to_le_bytes nonce).val[4]!,
       (core.num.U64.to_le_bytes nonce).val[5]!,
       (core.num.U64.to_le_bytes nonce).val[6]!,
       (core.num.U64.to_le_bytes nonce).val[7]!] by rfl]
  simp only [List.map_cons, List.map_nil]
  have hbytesLength :
      (core.num.U64.to_le_bytes nonce).val.length = 8 := by
    simpa using (core.num.U64.to_le_bytes nonce).property
  have hbytes := list_of_length_eight_is_exact_gets
    (core.num.U64.to_le_bytes nonce).val hbytesLength
  have hmap := congrArg (List.map byteOfGenerated) hbytes
  simp only [List.map_cons, List.map_nil] at hmap
  rw [← hmap, generated_u64_bytes_are_exact_nonce_le nonce]
  unfold workAbsorbPayload
  congr 1
  apply Fin.ext
  simp [byteOfGenerated, AspisV5PrefixNonceEncodingProof.generatedToByte,
    hround]
  exact Nat.lt_trans round.isLt (by decide)

theorem batch_work_label_is_exact :
    V5AcceptedEntryGenerated.aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE =
      .ok 28#u8 := by rfl

theorem fold_work_label_is_exact :
    V5AcceptedEntryGenerated.aspis_core.transcript.label.M31_CIRCLE_FOLD_POW_NONCE =
      .ok 20#u8 := by rfl

theorem final_work_label_is_exact :
    V5AcceptedEntryGenerated.aspis_core.transcript.label.GRIND_NONCE =
      .ok 5#u8 := by rfl

def AcceptedGeneratedBatchExecution (parsed : EntryParsed) : Prop :=
  ∃ before after,
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before parsed.v5_batch_nonce 37#u8 = .ok true ∧
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_batch_nonce
        before parsed.v5_batch_nonce = .ok after

def AcceptedGeneratedFoldExecution
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8) : Prop :=
  ∃ nonce before after,
    Array.index_usize nonces round = .ok nonce ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before nonce bits = .ok true ∧
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_fold_nonce
        before round nonce = .ok after

def AcceptedGeneratedFoldSlotExecution
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8) : Prop :=
  ∃ before after,
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before nonces.val[round.val]! bits = .ok true ∧
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_fold_nonce
        before round nonces.val[round.val]! = .ok after

theorem generated_fold_execution_uses_array_slot
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8) (hround : round.val < 4)
    (execution : AcceptedGeneratedFoldExecution nonces round bits) :
    AcceptedGeneratedFoldSlotExecution nonces round bits := by
  unfold AcceptedGeneratedFoldExecution at execution
  unfold AcceptedGeneratedFoldSlotExecution
  obtain ⟨nonce, before, after, nonceIndex, grindingSuccess, absorbSuccess⟩ :=
    execution
  have exactRead := generated_array_index_run nonces round (by
    simpa using hround)
  rw [exactRead] at nonceIndex
  simp only [Result.ok.injEq] at nonceIndex
  subst nonce
  exact ⟨before, after, grindingSuccess, absorbSuccess⟩

def AcceptedGeneratedFinalExecution (parsed : EntryParsed) : Prop :=
  ∃ before after,
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before parsed.v5_final_nonce 32#u8 = .ok true ∧
    V5AcceptedEntryGenerated.v5_cu_probe.absorb_real_v5_final_nonce
        before parsed.v5_final_nonce = .ok after

structure AcceptedGeneratedSixWorkExecution (parsed : EntryParsed) : Prop where
  batch : AcceptedGeneratedBatchExecution parsed
  fold0 : AcceptedGeneratedFoldExecution parsed.v5_fold_nonces 0#usize 34#u8
  fold1 : AcceptedGeneratedFoldExecution parsed.v5_fold_nonces 1#usize 33#u8
  fold2 : AcceptedGeneratedFoldExecution parsed.v5_fold_nonces 2#usize 30#u8
  fold3 : AcceptedGeneratedFoldExecution parsed.v5_fold_nonces 3#usize 25#u8
  finalQuery : AcceptedGeneratedFinalExecution parsed

structure AcceptedGeneratedPositionedSixWorkExecution
    (parsed : EntryParsed) : Prop where
  batch : AcceptedGeneratedBatchExecution parsed
  fold0 : AcceptedGeneratedFoldSlotExecution
    parsed.v5_fold_nonces 0#usize 34#u8
  fold1 : AcceptedGeneratedFoldSlotExecution
    parsed.v5_fold_nonces 1#usize 33#u8
  fold2 : AcceptedGeneratedFoldSlotExecution
    parsed.v5_fold_nonces 2#usize 30#u8
  fold3 : AcceptedGeneratedFoldSlotExecution
    parsed.v5_fold_nonces 3#usize 25#u8
  finalQuery : AcceptedGeneratedFinalExecution parsed

theorem generated_six_work_execution_uses_exact_nonce_slots
    (parsed : EntryParsed) (execution : AcceptedGeneratedSixWorkExecution parsed) :
    AcceptedGeneratedPositionedSixWorkExecution parsed := {
  batch := execution.batch
  fold0 := generated_fold_execution_uses_array_slot
    parsed.v5_fold_nonces 0#usize 34#u8 (by decide) execution.fold0
  fold1 := generated_fold_execution_uses_array_slot
    parsed.v5_fold_nonces 1#usize 33#u8 (by decide) execution.fold1
  fold2 := generated_fold_execution_uses_array_slot
    parsed.v5_fold_nonces 2#usize 30#u8 (by decide) execution.fold2
  fold3 := generated_fold_execution_uses_array_slot
    parsed.v5_fold_nonces 3#usize 25#u8 (by decide) execution.fold3
  finalQuery := execution.finalQuery
}

theorem required_batch_work_implies_generated_execution
    (parsed : EntryParsed) (required : AcceptedBatchRequiredWork parsed) :
    AcceptedGeneratedBatchExecution parsed := by
  unfold AcceptedBatchRequiredWork at required
  unfold AcceptedGeneratedBatchExecution
  obtain ⟨before, after, helperSuccess, requiredSuccess⟩ := required
  exact ⟨before, after,
    require_real_v5_work_success_implies_grinding_ok
      before parsed.v5_batch_nonce 37#u8 requiredSuccess,
    batch_helper_success_implies_absorb before after
      parsed.v5_batch_nonce helperSuccess⟩

theorem required_fold_work_implies_generated_execution
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8)
    (difficulty :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_difficulty round =
        .ok (some bits))
    (required : AcceptedFoldRequiredWork nonces round bits) :
    AcceptedGeneratedFoldExecution nonces round bits := by
  unfold AcceptedFoldRequiredWork at required
  unfold AcceptedGeneratedFoldExecution
  obtain ⟨nonce, before, after, nonceIndex, helperSuccess, requiredSuccess⟩ :=
    required
  exact ⟨nonce, before, after, nonceIndex,
    require_real_v5_work_success_implies_grinding_ok
      before nonce bits requiredSuccess,
    fold_helper_success_implies_absorb before after round nonce bits
      difficulty helperSuccess⟩

theorem required_final_work_implies_generated_execution
    (parsed : EntryParsed) (required : AcceptedFinalRequiredWork parsed) :
    AcceptedGeneratedFinalExecution parsed := by
  unfold AcceptedFinalRequiredWork at required
  unfold AcceptedGeneratedFinalExecution
  obtain ⟨before, after, helperSuccess, requiredSuccess⟩ := required
  exact ⟨before, after,
    require_real_v5_work_success_implies_grinding_ok
      before parsed.v5_final_nonce 32#u8 requiredSuccess,
    final_helper_success_implies_absorb before after
      parsed.v5_final_nonce helperSuccess⟩

theorem accepted_six_required_work_implies_generated_execution
    (parsed : EntryParsed) (required : AcceptedSixRequiredWork parsed) :
    AcceptedGeneratedSixWorkExecution parsed := by
  unfold AcceptedSixRequiredWork at required
  rcases required with ⟨batch, ⟨fold0, fold1, fold2, fold3⟩, finalQuery⟩
  exact {
    batch := required_batch_work_implies_generated_execution parsed batch
    fold0 := required_fold_work_implies_generated_execution
      parsed.v5_fold_nonces 0#usize 34#u8 (by rfl) fold0
    fold1 := required_fold_work_implies_generated_execution
      parsed.v5_fold_nonces 1#usize 33#u8 (by rfl) fold1
    fold2 := required_fold_work_implies_generated_execution
      parsed.v5_fold_nonces 2#usize 30#u8 (by rfl) fold2
    fold3 := required_fold_work_implies_generated_execution
      parsed.v5_fold_nonces 3#usize 25#u8 (by rfl) fold3
    finalQuery := required_final_work_implies_generated_execution
      parsed finalQuery
  }

theorem accepted_composite_proves_generated_six_work_execution
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedGeneratedSixWorkExecution parsed :=
  accepted_six_required_work_implies_generated_execution parsed
    (accepted_composite_proves_six_work accountData parsed liveStatement
      statementDigest acceptedValue success)

theorem accepted_composite_proves_positioned_six_work_execution
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedGeneratedPositionedSixWorkExecution parsed :=
  generated_six_work_execution_uses_exact_nonce_slots parsed
    (accepted_composite_proves_generated_six_work_execution accountData parsed
      liveStatement statementDigest acceptedValue success)

/-! ## Exact labels and byte payloads at the six production calls -/

def AcceptedGeneratedBatchExactCall (parsed : EntryParsed) : Prop :=
  ∃ (before after : EntryTranscript) (record : Array Std.U8 8#usize),
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before parsed.v5_batch_nonce 37#u8 = .ok true ∧
    record.val.map byteOfGenerated =
      workAbsorbPayload .batch (nonceOfGenerated parsed.v5_batch_nonce) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
        before 28#u8 (Array.to_slice record) = .ok after

def AcceptedGeneratedFoldExactCall
    (nonces : Array Std.U64 4#usize) (generatedRound : Std.Usize)
    (round : Fin 4) (bits : Std.U8) : Prop :=
  ∃ (before after : EntryTranscript) (record : Array Std.U8 9#usize),
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before nonces.val[generatedRound.val]! bits = .ok true ∧
    record.val.map byteOfGenerated =
      workAbsorbPayload (.fold round)
        (nonceOfGenerated nonces.val[generatedRound.val]!) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
        before 20#u8 (Array.to_slice record) = .ok after

def AcceptedGeneratedFinalExactCall (parsed : EntryParsed) : Prop :=
  ∃ (before after : EntryTranscript) (record : Array Std.U8 8#usize),
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.grinding_ok
        before parsed.v5_final_nonce 32#u8 = .ok true ∧
    record.val.map byteOfGenerated =
      workAbsorbPayload .finalQuery (nonceOfGenerated parsed.v5_final_nonce) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
        before 5#u8 (Array.to_slice record) = .ok after

theorem generated_batch_execution_has_exact_call
    (parsed : EntryParsed) (execution : AcceptedGeneratedBatchExecution parsed) :
    AcceptedGeneratedBatchExactCall parsed := by
  rcases execution with ⟨before, after, grindingSuccess, absorbSuccess⟩
  rcases batch_absorb_success_has_actual_transcript_call
      before after parsed.v5_batch_nonce absorbSuccess with
    ⟨label, record, inputSuccess, transcriptSuccess⟩
  have components := batch_absorb_input_success_components
    parsed.v5_batch_nonce label record inputSuccess
  have labelExact : label = 28#u8 := by
    have reverse : 28#u8 = label := by
      simpa [batch_work_label_is_exact] using components.2
    exact reverse.symm
  subst label
  exact ⟨before, after, record, grindingSuccess,
    batch_absorb_record_matches_maintained_payload
      parsed.v5_batch_nonce 28#u8 record inputSuccess,
    transcriptSuccess⟩

theorem generated_fold_execution_has_exact_call
    (nonces : Array Std.U64 4#usize) (generatedRound : Std.Usize)
    (round : Fin 4) (bits : Std.U8)
    (hround : generatedRound.val = round.val)
    (execution :
      AcceptedGeneratedFoldSlotExecution nonces generatedRound bits) :
    AcceptedGeneratedFoldExactCall nonces generatedRound round bits := by
  rcases execution with ⟨before, after, grindingSuccess, absorbSuccess⟩
  rcases fold_absorb_success_has_actual_transcript_call
      before after generatedRound nonces.val[generatedRound.val]!
      absorbSuccess with
    ⟨label, record, inputSuccess, transcriptSuccess⟩
  have components := fold_absorb_input_success_components
    generatedRound nonces.val[generatedRound.val]! label record inputSuccess
  have labelExact : label = 20#u8 := by
    have reverse : 20#u8 = label := by
      simpa [fold_work_label_is_exact] using components.2
    exact reverse.symm
  subst label
  exact ⟨before, after, record, grindingSuccess,
    fold_absorb_record_matches_maintained_payload generatedRound round hround
      nonces.val[generatedRound.val]! record components.1,
    transcriptSuccess⟩

theorem generated_final_execution_has_exact_call
    (parsed : EntryParsed) (execution : AcceptedGeneratedFinalExecution parsed) :
    AcceptedGeneratedFinalExactCall parsed := by
  rcases execution with ⟨before, after, grindingSuccess, absorbSuccess⟩
  rcases final_absorb_success_has_actual_transcript_call
      before after parsed.v5_final_nonce absorbSuccess with
    ⟨label, record, inputSuccess, transcriptSuccess⟩
  have components := final_absorb_input_success_components
    parsed.v5_final_nonce label record inputSuccess
  have labelExact : label = 5#u8 := by
    have reverse : 5#u8 = label := by
      simpa [final_work_label_is_exact] using components.2
    exact reverse.symm
  subst label
  exact ⟨before, after, record, grindingSuccess,
    final_absorb_record_matches_maintained_payload
      parsed.v5_final_nonce 5#u8 record inputSuccess,
    transcriptSuccess⟩

structure AcceptedGeneratedExactSixWorkCalls (parsed : EntryParsed) : Prop where
  batch : AcceptedGeneratedBatchExactCall parsed
  fold0 : AcceptedGeneratedFoldExactCall
    parsed.v5_fold_nonces 0#usize (0 : Fin 4) 34#u8
  fold1 : AcceptedGeneratedFoldExactCall
    parsed.v5_fold_nonces 1#usize (1 : Fin 4) 33#u8
  fold2 : AcceptedGeneratedFoldExactCall
    parsed.v5_fold_nonces 2#usize (2 : Fin 4) 30#u8
  fold3 : AcceptedGeneratedFoldExactCall
    parsed.v5_fold_nonces 3#usize (3 : Fin 4) 25#u8
  finalQuery : AcceptedGeneratedFinalExactCall parsed

theorem positioned_execution_has_exact_six_work_calls
    (parsed : EntryParsed)
    (execution : AcceptedGeneratedPositionedSixWorkExecution parsed) :
    AcceptedGeneratedExactSixWorkCalls parsed := {
  batch := generated_batch_execution_has_exact_call parsed execution.batch
  fold0 := generated_fold_execution_has_exact_call parsed.v5_fold_nonces
    0#usize (0 : Fin 4) 34#u8 (by rfl) execution.fold0
  fold1 := generated_fold_execution_has_exact_call parsed.v5_fold_nonces
    1#usize (1 : Fin 4) 33#u8 (by rfl) execution.fold1
  fold2 := generated_fold_execution_has_exact_call parsed.v5_fold_nonces
    2#usize (2 : Fin 4) 30#u8 (by rfl) execution.fold2
  fold3 := generated_fold_execution_has_exact_call parsed.v5_fold_nonces
    3#usize (3 : Fin 4) 25#u8 (by rfl) execution.fold3
  finalQuery := generated_final_execution_has_exact_call parsed
    execution.finalQuery
}

theorem accepted_composite_proves_exact_six_work_calls
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedGeneratedExactSixWorkCalls parsed :=
  positioned_execution_has_exact_six_work_calls parsed
    (accepted_composite_proves_positioned_six_work_execution accountData parsed
      liveStatement statementDigest acceptedValue success)

#print axioms accepted_composite_proves_generated_six_work_execution
#print axioms accepted_composite_proves_positioned_six_work_execution
#print axioms accepted_composite_proves_exact_six_work_calls

end AspisV5AcceptedEntrySourceBridge
