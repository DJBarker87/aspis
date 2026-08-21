import V5AcceptedPrefixWorkBridge

/-!
# Accepted relation and query work checks

This file follows the generated production relation replay and query-tail
bodies.  A successful accepted run therefore supplies the four fold work
checks and the final-query work check, in addition to the batch check proved
in `V5AcceptedPrefixWorkBridge`.
-/

namespace AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Aeneas Aeneas.Std Result ControlFlow Error

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

deriving instance DecidableEq for
  V5AcceptedEntryGenerated.aspis_core.field.CM31
deriving instance DecidableEq for
  V5AcceptedEntryGenerated.aspis_core.field.QM31

/-- The exact extracted field comparison used by the combined production
snapshot.  This discharges the accepted `!= false` check without adding an
equality assumption. -/
theorem accepted_entry_qm31_ne_false_implies_eq
    (left right : EntryQM31)
    (success :
      core.cmp.PartialEq.ne.trait_default
          V5AcceptedEntryGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          left right = .ok false) :
    left = right := by
  rcases left with ⟨⟨la0, la1⟩, ⟨lb0, lb1⟩⟩
  rcases right with ⟨⟨ra0, ra1⟩, ⟨rb0, rb1⟩⟩
  by_cases h0 : la0 = ra0 <;> by_cases h1 : la1 = ra1 <;>
    by_cases h2 : lb0 = rb0 <;> by_cases h3 : lb1 = rb1 <;>
    simp_all [core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      V5AcceptedEntryGenerated.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      V5AcceptedEntryGenerated.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

def AcceptedBatchChallengeSuccessor
    (parsed : EntryParsed) (verified : EntryVerifiedPrefix) : Prop :=
  ∃ beforeBatch afterBatch afterGamma,
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
        beforeBatch parsed.v5_batch_nonce = .ok (.Ok (), afterBatch) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31
        afterBatch = .ok (.Ok verified.gamma, afterGamma)

def AcceptedFoldChallengeSuccessor
    (parsed : EntryParsed) (round : Std.Usize) : Prop :=
  ∃ nonce beforeFold afterFold sampledAlpha decodedAlpha afterChallenge,
    Array.index_usize parsed.v5_fold_nonces round = .ok nonce ∧
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
        beforeFold round nonce = .ok (.Ok (), afterFold) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
        afterFold = .ok (.Ok sampledAlpha, afterChallenge) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas round = .ok (.Ok decodedAlpha) ∧
    core.cmp.PartialEq.ne.trait_default
        V5AcceptedEntryGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        decodedAlpha sampledAlpha = .ok false ∧
    sampledAlpha = decodedAlpha

def AcceptedFourFoldChallengeSuccessors (parsed : EntryParsed) : Prop :=
  AcceptedFoldChallengeSuccessor parsed 0#usize ∧
  AcceptedFoldChallengeSuccessor parsed 1#usize ∧
  AcceptedFoldChallengeSuccessor parsed 2#usize ∧
  AcceptedFoldChallengeSuccessor parsed 3#usize

def AcceptedFinalQuerySuccessor
    (parsed : EntryParsed) (queries : Array Std.U32 18#usize) : Prop :=
  ∃ beforeFinal afterFinal selectorBytes selectorLabel afterSelector
      queryBound drawLimit sampledQueries afterQueries,
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
        beforeFinal parsed.v5_final_nonce = .ok (.Ok (), afterFinal) ∧
    (lift (Array.to_slice (Array.make 1#usize [parsed.v5_query_selector])) :
        Result (Slice Std.U8)) = .ok selectorBytes ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.label.M31_STATE_ONLY_QUERY_CANDIDATE =
        .ok selectorLabel ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.absorb
        afterFinal selectorLabel selectorBytes = .ok afterSelector ∧
    (1#u32 <<< 17#i32 : Result Std.U32) = .ok queryBound ∧
    V5AcceptedEntryGenerated.aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT =
        .ok drawLimit ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_queries_without_replacement
        afterSelector V5AcceptedEntryGenerated.v5_cu_probe.V5_CU_PROBE_QUERY_COUNT
        queryBound drawLimit = .ok (.Ok sampledQueries, afterQueries) ∧
    V5AcceptedEntryGenerated.Array.Insts.CoreConvertTryFromVecVec.try_from
        Global 18#usize sampledQueries = .ok (.Ok queries)

theorem accepted_prefix_has_batch_challenge_successor
    (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash)
    (verified : EntryVerifiedPrefix)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    AcceptedBatchChallengeSuccessor parsed verified := by
  unfold AcceptedBatchChallengeSuccessor
  exact accepted_prefix_has_batch_and_gamma_successor parsed liveStatement
    statementDigest hash verified returnedTranscript success

theorem fold_success_implies_required_work
    (beforeFold afterFold : EntryTranscript)
    (round : Std.Usize) (nonce : Std.U64) (bits : Std.U8)
    (difficulty :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_difficulty round =
        .ok (some bits))
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          beforeFold round nonce = .ok (.Ok (), afterFold)) :
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeFold nonce bits = .ok (.Ok ()) := by
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
          simpa [hworkResult] using workSuccess

theorem final_success_implies_difficulty_32_work
    (beforeFinal afterFinal : EntryTranscript) (nonce : Std.U64)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          beforeFinal nonce = .ok (.Ok (), afterFinal)) :
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeFinal nonce 32#u8 = .ok (.Ok ()) := by
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
      simpa [hworkResult] using workSuccess

private abbrev TailIter :=
  core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut
      V5AcceptedEntryGenerated.aspis_core.field.QM31)

private def tailSeedArray
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) :
    Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize :=
  Array.repeat 4#usize seed

private def tailIter0
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter :=
  { iter := { slice := Array.to_slice (tailSeedArray seed), i := 0 }, count := 0#usize }

private def tailBack0 : TailIter → TailIter := fun current => current

private def tailIter1
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter :=
  { tailIter0 seed with
    iter := { (tailIter0 seed).iter with i := 1 }, count := 1#usize }

private def tailBack1
    (q0 : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter → TailIter :=
  fun current =>
    { current with
      iter := { current.iter with slice := current.iter.slice.setAtNat 0 q0 } }

private def tailIter2
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter :=
  { tailIter0 seed with
    iter := { (tailIter0 seed).iter with i := 2 }, count := 2#usize }

private def tailBack2
    (q0 q1 : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter → TailIter :=
  fun current =>
    tailBack1 q0
      { current with
        iter := { current.iter with slice := current.iter.slice.setAtNat 1 q1 } }

private def tailIter3
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter :=
  { tailIter0 seed with
    iter := { (tailIter0 seed).iter with i := 3 }, count := 3#usize }

private def tailBack3
    (q0 q1 q2 : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter → TailIter :=
  fun current =>
    tailBack2 q0 q1
      { current with
        iter := { current.iter with slice := current.iter.slice.setAtNat 2 q2 } }

private def tailIter4
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31) : TailIter :=
  { tailIter0 seed with
    iter := { (tailIter0 seed).iter with i := 4 }, count := 4#usize }

private def tailBack4
    (q0 q1 q2 q3 : V5AcceptedEntryGenerated.aspis_core.field.QM31) :
    TailIter → TailIter :=
  fun current =>
    tailBack3 q0 q1 q2
      { current with
        iter := { current.iter with slice := current.iter.slice.setAtNat 3 q3 } }

private theorem usize_add_0_1 :
    (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := by
  change UScalar.add 0#usize 1#usize = .ok 1#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_1_1 :
    (1#usize + 1#usize : Result Std.Usize) = .ok 2#usize := by
  change UScalar.add 1#usize 1#usize = .ok 2#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_2_1 :
    (2#usize + 1#usize : Result Std.Usize) = .ok 3#usize := by
  change UScalar.add 2#usize 1#usize = .ok 3#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_3_1 :
    (3#usize + 1#usize : Result Std.Usize) = .ok 4#usize := by
  change UScalar.add 3#usize 1#usize = .ok 4#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem tail_body_state0
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (decodeSuccess :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 0#usize = .ok (.Ok q0)) :
    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      (tailIter0 seed) tailBack0 =
        .ok (.cont (tailIter1 seed, tailBack1 q0)) := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter1, tailBack0, tailBack1, tailSeedArray,
    Array.to_slice, Array.repeat, usize_add_0_1, decodeSuccess]
  funext current
  rfl

private theorem tail_body_state1
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (decodeSuccess :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 1#usize = .ok (.Ok q1)) :
    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      (tailIter1 seed) (tailBack1 q0) =
        .ok (.cont (tailIter2 seed, tailBack2 q0 q1)) := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter1, tailIter2, tailBack1, tailBack2,
    tailSeedArray, Array.to_slice, Array.repeat, usize_add_1_1, decodeSuccess]
  funext current
  rfl

private theorem tail_body_state2
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 q2 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (decodeSuccess :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 2#usize = .ok (.Ok q2)) :
    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      (tailIter2 seed) (tailBack2 q0 q1) =
        .ok (.cont (tailIter3 seed, tailBack3 q0 q1 q2)) := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter2, tailIter3, tailBack1, tailBack2, tailBack3,
    tailSeedArray, Array.to_slice, Array.repeat, usize_add_2_1, decodeSuccess]
  funext current
  rfl

private theorem tail_body_state3
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 q2 q3 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (decodeSuccess :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 3#usize = .ok (.Ok q3)) :
    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      (tailIter3 seed) (tailBack3 q0 q1 q2) =
        .ok (.cont (tailIter4 seed, tailBack4 q0 q1 q2 q3)) := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter3, tailIter4, tailBack1, tailBack2, tailBack3,
    tailBack4, tailSeedArray, Array.to_slice, Array.repeat, usize_add_3_1,
    decodeSuccess]
  funext current
  rfl

private theorem tail_body_state4_success_has_final_work
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 q2 q3 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
        parsed toSliceBack iterBack enumBack transcript nonce selector
        (tailIter4 seed) (tailBack4 q0 q1 q2 q3) =
          .ok (.done (some (.Ok (polynomial, queries))))) :
    ∃ beforeFinal afterFinal,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          beforeFinal nonce = .ok (.Ok (), afterFinal) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body at success
  simp [V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
    tailSeedArray, Array.to_slice, Array.repeat] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨beforeFinal, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperPair, helperSuccess, success⟩ := success
  rcases helperPair with ⟨helperResult, afterFinal⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperFlow, helperBranchSuccess, success⟩ := success
  cases helperFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
  | Continue unitValue =>
      have hhelperResult := branch_eq_ok_of_continue
        helperResult unitValue helperBranchSuccess
      cases unitValue
      rw [hhelperResult] at helperSuccess
      exact ⟨beforeFinal, afterFinal, helperSuccess⟩

private theorem tail_body_state4_success_has_final_successor
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 q2 q3 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
        parsed toSliceBack iterBack enumBack transcript nonce selector
        (tailIter4 seed) (tailBack4 q0 q1 q2 q3) =
          .ok (.done (some (.Ok (polynomial, queries))))) :
    AcceptedFinalQuerySuccessor
        { parsed with v5_final_nonce := nonce, v5_query_selector := selector }
        queries ∧
      polynomial =
        toSliceBack
          (iterBack
            (enumBack
              (tailBack4 q0 q1 q2 q3 (tailIter4 seed)))) := by
  unfold AcceptedFinalQuerySuccessor
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body at success
  simp [V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
    tailSeedArray, Array.to_slice, Array.repeat] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨beforeFinal, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperPair, helperSuccess, success⟩ := success
  rcases helperPair with ⟨helperResult, afterFinal⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperFlow, helperBranchSuccess, success⟩ := success
  cases helperFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
  | Continue unitValue =>
      have hhelperResult := branch_eq_ok_of_continue
        helperResult unitValue helperBranchSuccess
      cases unitValue
      rw [hhelperResult] at helperSuccess
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨selectorBytes, selectorBytesSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨selectorLabel, selectorLabelSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨afterSelector, selectorAbsorbSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨queryBound, queryBoundSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨drawLimit, drawLimitSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨queryPair, querySuccess, success⟩ := success
      rcases queryPair with ⟨queryResult, afterQueries⟩
      rw [bind_eq_ok_iff] at success
      obtain ⟨mappedQueryResult, mappedQuerySuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨queryFlow, queryBranchSuccess, success⟩ := success
      cases queryFlow with
      | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error => simp at success
      | Continue sampledQueries =>
          have hmappedQueryResult := branch_eq_ok_of_continue
            mappedQueryResult sampledQueries queryBranchSuccess
          rw [hmappedQueryResult] at mappedQuerySuccess
          cases queryResult with
          | Err error =>
              simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorProgramError.call_once]
                at mappedQuerySuccess
          | Ok actualQueries =>
              simp [V5AcceptedEntryGenerated.core.result.Result.map_err] at mappedQuerySuccess
              subst actualQueries
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨arrayResult, arraySuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨mappedArrayResult, mappedArraySuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨arrayFlow, arrayBranchSuccess, success⟩ := success
              cases arrayFlow with
              | Break residual =>
                  cases residual with
                  | Ok impossible => nomatch impossible
                  | Err error => simp at success
              | Continue acceptedQueries =>
                  have hmappedArrayResult := branch_eq_ok_of_continue
                    mappedArrayResult acceptedQueries arrayBranchSuccess
                  rw [hmappedArrayResult] at mappedArraySuccess
                  cases arrayResult with
                  | Err error =>
                      simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                        V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32ProgramError.call_once]
                        at mappedArraySuccess
                  | Ok actualAcceptedQueries =>
                      simp [V5AcceptedEntryGenerated.core.result.Result.map_err] at mappedArraySuccess
                      subst actualAcceptedQueries
                      simp only at success
                      have hqueries : acceptedQueries = queries := by
                        exact congrArg Prod.snd
                          (core.result.Result.Ok.inj
                            (Option.some.inj
                              (ControlFlow.done.inj (Result.ok.inj success))))
                      have hpair :=
                        core.result.Result.Ok.inj
                          (Option.some.inj
                            (ControlFlow.done.inj (Result.ok.inj success)))
                      have hpolynomial :
                          toSliceBack
                              (iterBack
                                (enumBack
                                  (tailBack4 q0 q1 q2 q3
                                    (tailIter4 seed)))) = polynomial :=
                        congrArg Prod.fst hpair
                      subst acceptedQueries
                      constructor
                      · exact ⟨beforeFinal, afterFinal, selectorBytes,
                          selectorLabel, afterSelector, queryBound, drawLimit,
                          sampledQueries, afterQueries, helperSuccess,
                          by simpa [Array.to_slice] using selectorBytesSuccess,
                          selectorLabelSuccess, selectorAbsorbSuccess,
                          queryBoundSuccess, drawLimitSuccess, querySuccess,
                          arraySuccess⟩
                      · exact hpolynomial.symm

private theorem tail_body_state4_ne_cont
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (q0 q1 q2 q3 : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (state : TailIter × (TailIter → TailIter))
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
        parsed toSliceBack iterBack enumBack transcript nonce selector
        (tailIter4 seed) (tailBack4 q0 q1 q2 q3) = .ok (.cont state)) :
    False := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body at impossible
  simp [V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next,
    tailIter0, tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
    tailSeedArray, Array.to_slice, Array.repeat] at impossible
  rw [bind_eq_ok_iff] at impossible
  obtain ⟨_, _, impossible⟩ := impossible
  rw [bind_eq_ok_iff] at impossible
  obtain ⟨_, _, impossible⟩ := impossible
  rw [bind_eq_ok_iff] at impossible
  obtain ⟨helperPair, _, impossible⟩ := impossible
  rcases helperPair with ⟨_, _⟩
  rw [bind_eq_ok_iff] at impossible
  obtain ⟨helperFlow, _, impossible⟩ := impossible
  cases helperFlow with
  | Break residual =>
      cases residual with
      | Ok never => nomatch never
      | Err error => simp at impossible
  | Continue unitValue =>
      simp only at impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨queryPair, _, impossible⟩ := impossible
      rcases queryPair with ⟨_, _⟩
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨_, _, impossible⟩ := impossible
      rw [bind_eq_ok_iff] at impossible
      obtain ⟨queryFlow, _, impossible⟩ := impossible
      cases queryFlow with
      | Break residual =>
          cases residual with
          | Ok never => nomatch never
          | Err error => simp at impossible
      | Continue values =>
          simp only at impossible
          rw [bind_eq_ok_iff] at impossible
          obtain ⟨_, _, impossible⟩ := impossible
          rw [bind_eq_ok_iff] at impossible
          obtain ⟨_, _, impossible⟩ := impossible
          rw [bind_eq_ok_iff] at impossible
          obtain ⟨arrayFlow, _, impossible⟩ := impossible
          cases arrayFlow with
          | Break residual =>
              cases residual with
              | Ok never => nomatch never
              | Err error => simp at impossible
          | Continue values => simp at impossible

private theorem tail_loop_success_has_final_work
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
          parsed toSliceBack iterBack enumBack (tailIter0 seed) tailBack0
          transcript nonce selector = .ok (some (.Ok (polynomial, queries)))) :
    ∃ beforeFinal afterFinal,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          beforeFinal nonce = .ok (.Ok (), afterFinal) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hdecode0 :
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
      parsed.v5_final_coefficients 0#usize = decoded0 at success
  cases decoded0 with
  | fail error =>
      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
        tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
        usize_add_0_1, hdecode0] at success
  | div =>
      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
        tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
        usize_add_0_1, hdecode0] at success
  | ok decodedResult0 =>
      cases decodedResult0 with
      | Err error =>
          simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
            V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
            core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
            tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
            usize_add_0_1, hdecode0] at success
      | Ok q0 =>
          rw [tail_body_state0 parsed transcript nonce selector seed q0
            toSliceBack iterBack enumBack hdecode0] at success
          simp only at success
          rw [Aeneas.Std.loop.eq_def] at success
          simp only at success
          generalize hdecode1 :
            V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
              parsed.v5_final_coefficients 1#usize = decoded1 at success
          cases decoded1 with
          | fail error =>
              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                tailIter2, tailBack1, tailBack2, tailSeedArray,
                Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
          | div =>
              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                tailIter2, tailBack1, tailBack2, tailSeedArray,
                Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
          | ok decodedResult1 =>
              cases decodedResult1 with
              | Err error =>
                  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                    tailIter2, tailBack1, tailBack2, tailSeedArray,
                    Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
              | Ok q1 =>
                  rw [tail_body_state1 parsed transcript nonce selector seed q0 q1
                    toSliceBack iterBack enumBack hdecode1] at success
                  simp only at success
                  rw [Aeneas.Std.loop.eq_def] at success
                  simp only at success
                  generalize hdecode2 :
                    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                      parsed.v5_final_coefficients 2#usize = decoded2 at success
                  cases decoded2 with
                  | fail error =>
                      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                        tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                        Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                  | div =>
                      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                        tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                        Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                  | ok decodedResult2 =>
                      cases decodedResult2 with
                      | Err error =>
                          simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                            V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                            core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                            tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                            Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                      | Ok q2 =>
                          rw [tail_body_state2 parsed transcript nonce selector seed q0 q1 q2
                            toSliceBack iterBack enumBack hdecode2] at success
                          simp only at success
                          rw [Aeneas.Std.loop.eq_def] at success
                          simp only at success
                          generalize hdecode3 :
                            V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                              parsed.v5_final_coefficients 3#usize = decoded3 at success
                          cases decoded3 with
                          | fail error =>
                              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                tailSeedArray, Array.to_slice, Array.repeat,
                                usize_add_3_1, hdecode3] at success
                          | div =>
                              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                tailSeedArray, Array.to_slice, Array.repeat,
                                usize_add_3_1, hdecode3] at success
                          | ok decodedResult3 =>
                              cases decodedResult3 with
                              | Err error =>
                                  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                    tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                    tailSeedArray, Array.to_slice, Array.repeat,
                                    usize_add_3_1, hdecode3] at success
                              | Ok q3 =>
                                  rw [tail_body_state3 parsed transcript nonce selector seed q0 q1 q2 q3
                                    toSliceBack iterBack enumBack hdecode3] at success
                                  simp only at success
                                  rw [Aeneas.Std.loop.eq_def] at success
                                  simp only at success
                                  generalize hbody :
                                    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
                                      parsed toSliceBack iterBack enumBack transcript nonce selector
                                      (tailIter4 seed) (tailBack4 q0 q1 q2 q3) = bodyResult at success
                                  cases bodyResult with
                                  | fail error => simp at success
                                  | div => simp at success
                                  | ok flow =>
                                      cases flow with
                                      | cont state =>
                                          exact False.elim
                                            (tail_body_state4_ne_cont parsed transcript nonce selector
                                              seed q0 q1 q2 q3 toSliceBack iterBack enumBack state hbody)
                                      | done out =>
                                          have hout : out = some (.Ok (polynomial, queries)) := by
                                            simpa using success
                                          subst out
                                          exact tail_body_state4_success_has_final_work
                                            parsed transcript nonce selector seed q0 q1 q2 q3
                                            toSliceBack iterBack enumBack polynomial queries hbody

private theorem tail_loop_success_has_final_successor
    (parsed : EntryParsed) (transcript : EntryTranscript)
    (nonce : Std.U64) (selector : Std.U8)
    (seed : V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (toSliceBack : Slice V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31 →
      Slice V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (enumBack : TailIter →
      core.slice.iter.IterMut
        V5AcceptedEntryGenerated.aspis_core.field.QM31)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
          parsed toSliceBack iterBack enumBack (tailIter0 seed) tailBack0
          transcript nonce selector = .ok (some (.Ok (polynomial, queries)))) :
    ∃ q0 q1 q2 q3,
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 0#usize = .ok (.Ok q0) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 1#usize = .ok (.Ok q1) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 2#usize = .ok (.Ok q2) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.v5_final_coefficients 3#usize = .ok (.Ok q3) ∧
      AcceptedFinalQuerySuccessor
        { parsed with v5_final_nonce := nonce, v5_query_selector := selector }
        queries ∧
      polynomial =
        toSliceBack
          (iterBack
            (enumBack
              (tailBack4 q0 q1 q2 q3 (tailIter4 seed)))) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hdecode0 :
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
      parsed.v5_final_coefficients 0#usize = decoded0 at success
  cases decoded0 with
  | fail error =>
      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
        tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
        usize_add_0_1, hdecode0] at success
  | div =>
      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
        tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
        usize_add_0_1, hdecode0] at success
  | ok decodedResult0 =>
      cases decodedResult0 with
      | Err error =>
          simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
            V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
            core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
            tailBack0, tailBack1, tailSeedArray, Array.to_slice, Array.repeat,
            usize_add_0_1, hdecode0] at success
      | Ok q0 =>
          rw [tail_body_state0 parsed transcript nonce selector seed q0
            toSliceBack iterBack enumBack hdecode0] at success
          simp only at success
          rw [Aeneas.Std.loop.eq_def] at success
          simp only at success
          generalize hdecode1 :
            V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
              parsed.v5_final_coefficients 1#usize = decoded1 at success
          cases decoded1 with
          | fail error =>
              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                tailIter2, tailBack1, tailBack2, tailSeedArray,
                Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
          | div =>
              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                tailIter2, tailBack1, tailBack2, tailSeedArray,
                Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
          | ok decodedResult1 =>
              cases decodedResult1 with
              | Err error =>
                  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
                    tailIter2, tailBack1, tailBack2, tailSeedArray,
                    Array.to_slice, Array.repeat, usize_add_1_1, hdecode1] at success
              | Ok q1 =>
                  rw [tail_body_state1 parsed transcript nonce selector seed q0 q1
                    toSliceBack iterBack enumBack hdecode1] at success
                  simp only at success
                  rw [Aeneas.Std.loop.eq_def] at success
                  simp only at success
                  generalize hdecode2 :
                    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                      parsed.v5_final_coefficients 2#usize = decoded2 at success
                  cases decoded2 with
                  | fail error =>
                      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                        tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                        Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                  | div =>
                      simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                        V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                        core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                        tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                        Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                  | ok decodedResult2 =>
                      cases decodedResult2 with
                      | Err error =>
                          simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                            V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                            core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2,
                            tailIter3, tailBack1, tailBack2, tailBack3, tailSeedArray,
                            Array.to_slice, Array.repeat, usize_add_2_1, hdecode2] at success
                      | Ok q2 =>
                          rw [tail_body_state2 parsed transcript nonce selector seed q0 q1 q2
                            toSliceBack iterBack enumBack hdecode2] at success
                          simp only at success
                          rw [Aeneas.Std.loop.eq_def] at success
                          simp only at success
                          generalize hdecode3 :
                            V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                              parsed.v5_final_coefficients 3#usize = decoded3 at success
                          cases decoded3 with
                          | fail error =>
                              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                tailSeedArray, Array.to_slice, Array.repeat,
                                usize_add_3_1, hdecode3] at success
                          | div =>
                              simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                tailSeedArray, Array.to_slice, Array.repeat,
                                usize_add_3_1, hdecode3] at success
                          | ok decodedResult3 =>
                              cases decodedResult3 with
                              | Err error =>
                                  simp [V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
                                    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next,
                                    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3,
                                    tailIter4, tailBack1, tailBack2, tailBack3, tailBack4,
                                    tailSeedArray, Array.to_slice, Array.repeat,
                                    usize_add_3_1, hdecode3] at success
                              | Ok q3 =>
                                  rw [tail_body_state3 parsed transcript nonce selector seed q0 q1 q2 q3
                                    toSliceBack iterBack enumBack hdecode3] at success
                                  simp only at success
                                  rw [Aeneas.Std.loop.eq_def] at success
                                  simp only at success
                                  generalize hbody :
                                    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
                                      parsed toSliceBack iterBack enumBack transcript nonce selector
                                      (tailIter4 seed) (tailBack4 q0 q1 q2 q3) = bodyResult at success
                                  cases bodyResult with
                                  | fail error => simp at success
                                  | div => simp at success
                                  | ok flow =>
                                      cases flow with
                                      | cont state =>
                                          exact False.elim
                                            (tail_body_state4_ne_cont parsed transcript nonce selector
                                              seed q0 q1 q2 q3 toSliceBack iterBack enumBack state hbody)
                                      | done out =>
                                          have hout : out = some (.Ok (polynomial, queries)) := by
                                            simpa using success
                                          subst out
                                          obtain ⟨hfinal, hpolynomial⟩ :=
                                            tail_body_state4_success_has_final_successor
                                              parsed transcript nonce selector seed q0 q1 q2 q3
                                              toSliceBack iterBack enumBack polynomial queries hbody
                                          exact ⟨q0, q1, q2, q3,
                                            rfl, rfl, rfl, rfl, hfinal,
                                            hpolynomial⟩

theorem complete_tail_success_has_final_work
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (selector : Std.U8)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    ∃ beforeFinal afterFinal,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          beforeFinal parsed.v5_final_nonce = .ok (.Ok (), afterFinal) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨differs, _, success⟩ := success
  cases differs with
  | true => simp at success
  | false =>
      simp only [Bool.false_eq_true, if_false] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨selectorValid, _, success⟩ := success
      cases selectorValid with
      | false => simp at success
      | true =>
          simp only [if_true] at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨seed, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨slicePair, sliceSuccess, success⟩ := success
          rcases slicePair with ⟨finalSlice, toSliceBack⟩
          simp [lift, Array.to_slice_mut] at sliceSuccess
          rcases sliceSuccess with ⟨sliceSuccess, toSliceBackSuccess⟩
          subst finalSlice
          subst toSliceBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨iterPair, iterSuccess, success⟩ := success
          rcases iterPair with ⟨initialIter, iterBack⟩
          simp [core.slice.Slice.iter_mut] at iterSuccess
          rcases iterSuccess with ⟨iterSuccess, iterBackSuccess⟩
          subst initialIter
          subst iterBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨enumPair, enumSuccess, success⟩ := success
          rcases enumPair with ⟨initialEnum, enumBack⟩
          simp [V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate]
            at enumSuccess
          rcases enumSuccess with ⟨enumSuccess, enumBackSuccess⟩
          subst initialEnum
          subst enumBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨pending, loopSuccess, success⟩ := success
          cases pending with
          | none => simp at success
          | some result =>
              have hresult : result = .Ok (polynomial, queries) := by
                simpa using success
              subst result
              exact tail_loop_success_has_final_work
                parsed transcript parsed.v5_final_nonce selector seed
                (Array.from_slice (Array.repeat 4#usize seed))
                (fun current => current.slice) (fun current => current.iter)
                polynomial queries (by
                  change
                    V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
                      parsed (Array.from_slice (Array.repeat 4#usize seed))
                      (fun current => current.slice) (fun current => current.iter)
                      (tailIter0 seed) tailBack0 transcript
                      parsed.v5_final_nonce selector =
                        .ok (some (.Ok (polynomial, queries))) at loopSuccess
                  exact loopSuccess)

/-- Exact decoder calls and wire order of the four returned final
coefficients. -/
def AcceptedFinalPolynomialDecode
    (parsed : EntryParsed)
    (polynomial : Array EntryQM31 4#usize) : Prop :=
  ∃ q0 q1 q2 q3,
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.v5_final_coefficients 0#usize = .ok (.Ok q0) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.v5_final_coefficients 1#usize = .ok (.Ok q1) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.v5_final_coefficients 2#usize = .ok (.Ok q2) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.v5_final_coefficients 3#usize = .ok (.Ok q3) ∧
    polynomial.val = [q0, q1, q2, q3]

private theorem complete_tail_success_has_decoded_polynomial_aux
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (selector : Std.U8)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalQuerySuccessor
        { parsed with v5_query_selector := selector } queries ∧
      AcceptedFinalPolynomialDecode parsed polynomial := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨differs, _, success⟩ := success
  cases differs with
  | true => simp at success
  | false =>
      simp only [Bool.false_eq_true, if_false] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨selectorValid, _, success⟩ := success
      cases selectorValid with
      | false => simp at success
      | true =>
          simp only [if_true] at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨seed, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨slicePair, sliceSuccess, success⟩ := success
          rcases slicePair with ⟨finalSlice, toSliceBack⟩
          simp [lift, Array.to_slice_mut] at sliceSuccess
          rcases sliceSuccess with ⟨sliceSuccess, toSliceBackSuccess⟩
          subst finalSlice
          subst toSliceBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨iterPair, iterSuccess, success⟩ := success
          rcases iterPair with ⟨initialIter, iterBack⟩
          simp [core.slice.Slice.iter_mut] at iterSuccess
          rcases iterSuccess with ⟨iterSuccess, iterBackSuccess⟩
          subst initialIter
          subst iterBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨enumPair, enumSuccess, success⟩ := success
          rcases enumPair with ⟨initialEnum, enumBack⟩
          simp [V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate]
            at enumSuccess
          rcases enumSuccess with ⟨enumSuccess, enumBackSuccess⟩
          subst initialEnum
          subst enumBack
          rw [bind_eq_ok_iff] at success
          obtain ⟨pending, loopSuccess, success⟩ := success
          cases pending with
          | none => simp at success
          | some result =>
              have hresult : result = .Ok (polynomial, queries) := by
                simpa using success
              subst result
              obtain ⟨q0, q1, q2, q3, hdecode0, hdecode1, hdecode2,
                  hdecode3, hfinal, hpolynomial⟩ :=
                tail_loop_success_has_final_successor
                  parsed transcript parsed.v5_final_nonce selector seed
                  (Array.from_slice (Array.repeat 4#usize seed))
                  (fun current => current.slice) (fun current => current.iter)
                  polynomial queries (by
                    change
                      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
                        parsed (Array.from_slice (Array.repeat 4#usize seed))
                        (fun current => current.slice) (fun current => current.iter)
                        (tailIter0 seed) tailBack0 transcript
                        parsed.v5_final_nonce selector =
                          .ok (some (.Ok (polynomial, queries))) at loopSuccess
                    exact loopSuccess)
              constructor
              · simpa using hfinal
              · refine ⟨q0, q1, q2, q3, hdecode0, hdecode1,
                    hdecode2, hdecode3, ?_⟩
                simpa [tailIter0, tailIter4, tailBack1, tailBack2,
                  tailBack3, tailBack4, tailSeedArray, Array.repeat,
                  Array.from_slice, Array.to_slice, Slice.setAtNat] using
                    congrArg Subtype.val hpolynomial

theorem complete_tail_success_has_final_successor
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (selector : Std.U8)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalQuerySuccessor
      { parsed with v5_query_selector := selector } queries :=
  (complete_tail_success_has_decoded_polynomial_aux transcript parsed selector
    polynomial queries success).1

theorem complete_tail_success_has_decoded_polynomial
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (selector : Std.U8)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalPolynomialDecode parsed polynomial :=
  (complete_tail_success_has_decoded_polynomial_aux transcript parsed selector
    polynomial queries success).2

theorem selected_query_success_has_final_work
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (point : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 10#usize)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    ∃ beforeFinal afterFinal,
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
          beforeFinal parsed.v5_final_nonce = .ok (.Ok (), afterFinal) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript at success
  unfold V5AcceptedEntryGenerated.v5_cu_probe.checked_v5_selected_good_candidate at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectorValid, _, success⟩ := success
  cases selectorValid with
  | false => simp at success
  | true =>
      simp only [if_true] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨derivePair, deriveCallSuccess, success⟩ := success
      rcases derivePair with ⟨deriveResult, deriveState⟩
      rw [bind_eq_ok_iff] at success
      obtain ⟨deriveFlow, deriveBranchSuccess, success⟩ := success
      cases deriveFlow with
      | Break residual =>
          cases residual with
          | Ok never => nomatch never
          | Err error => simp at success
      | Continue derivedValue =>
          have hderiveResult := branch_eq_ok_of_continue
            deriveResult derivedValue deriveBranchSuccess
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluatePair, _, success⟩ := success
          rcases evaluatePair with ⟨evaluateResult, _⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluateFlow, _, success⟩ := success
          cases evaluateFlow with
          | Break residual =>
              cases residual with
              | Ok never => nomatch never
              | Err error => simp at success
          | Continue good =>
              cases good with
              | false => simp at success
              | true =>
                  have hderivedValue : derivedValue = (polynomial, queries) := by
                    simpa using success
                  subst derivedValue
                  rw [hderiveResult] at deriveCallSuccess
                  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript.closure.Insts.CoreOpsFunctionFnMutTupleU8ResultPairArrayQM314ArrayU3218ProgramError.call_mut at deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨clonedTranscript, _, deriveCallSuccess⟩ := deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨completeResult, completeSuccess, deriveCallSuccess⟩ := deriveCallSuccess
                  have hcompleteResult : completeResult = .Ok (polynomial, queries) := by
                    exact congrArg Prod.fst (Result.ok.inj deriveCallSuccess)
                  subst completeResult
                  exact complete_tail_success_has_final_work
                    clonedTranscript parsed parsed.v5_query_selector
                    polynomial queries completeSuccess

theorem selected_query_success_has_final_successor
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (point : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 10#usize)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalQuerySuccessor parsed queries := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript at success
  unfold V5AcceptedEntryGenerated.v5_cu_probe.checked_v5_selected_good_candidate at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectorValid, _, success⟩ := success
  cases selectorValid with
  | false => simp at success
  | true =>
      simp only [if_true] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨derivePair, deriveCallSuccess, success⟩ := success
      rcases derivePair with ⟨deriveResult, deriveState⟩
      rw [bind_eq_ok_iff] at success
      obtain ⟨deriveFlow, deriveBranchSuccess, success⟩ := success
      cases deriveFlow with
      | Break residual =>
          cases residual with
          | Ok never => nomatch never
          | Err error => simp at success
      | Continue derivedValue =>
          have hderiveResult := branch_eq_ok_of_continue
            deriveResult derivedValue deriveBranchSuccess
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluatePair, _, success⟩ := success
          rcases evaluatePair with ⟨evaluateResult, _⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluateFlow, _, success⟩ := success
          cases evaluateFlow with
          | Break residual =>
              cases residual with
              | Ok never => nomatch never
              | Err error => simp at success
          | Continue good =>
              cases good with
              | false => simp at success
              | true =>
                  have hderivedValue : derivedValue = (polynomial, queries) := by
                    simpa using success
                  subst derivedValue
                  rw [hderiveResult] at deriveCallSuccess
                  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript.closure.Insts.CoreOpsFunctionFnMutTupleU8ResultPairArrayQM314ArrayU3218ProgramError.call_mut at deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨clonedTranscript, _, deriveCallSuccess⟩ := deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨completeResult, completeSuccess, deriveCallSuccess⟩ := deriveCallSuccess
                  have hcompleteResult : completeResult = .Ok (polynomial, queries) := by
                    exact congrArg Prod.fst (Result.ok.inj deriveCallSuccess)
                  subst completeResult
                  simpa using complete_tail_success_has_final_successor
                    clonedTranscript parsed parsed.v5_query_selector
                    polynomial queries completeSuccess

/-- The polynomial returned by the selected-good-query driver is exactly the
four values decoded from the final-coefficient wire section. -/
theorem selected_query_success_has_decoded_polynomial
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (point : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 10#usize)
    (polynomial : Array V5AcceptedEntryGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalPolynomialDecode parsed polynomial := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript at success
  unfold V5AcceptedEntryGenerated.v5_cu_probe.checked_v5_selected_good_candidate at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨selectorValid, _, success⟩ := success
  cases selectorValid with
  | false => simp at success
  | true =>
      simp only [if_true] at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨derivePair, deriveCallSuccess, success⟩ := success
      rcases derivePair with ⟨deriveResult, deriveState⟩
      rw [bind_eq_ok_iff] at success
      obtain ⟨deriveFlow, deriveBranchSuccess, success⟩ := success
      cases deriveFlow with
      | Break residual =>
          cases residual with
          | Ok never => nomatch never
          | Err error => simp at success
      | Continue derivedValue =>
          have hderiveResult := branch_eq_ok_of_continue
            deriveResult derivedValue deriveBranchSuccess
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluatePair, _, success⟩ := success
          rcases evaluatePair with ⟨evaluateResult, _⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨evaluateFlow, _, success⟩ := success
          cases evaluateFlow with
          | Break residual =>
              cases residual with
              | Ok never => nomatch never
              | Err error => simp at success
          | Continue good =>
              cases good with
              | false => simp at success
              | true =>
                  have hderivedValue : derivedValue = (polynomial, queries) := by
                    simpa using success
                  subst derivedValue
                  rw [hderiveResult] at deriveCallSuccess
                  unfold V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript.closure.Insts.CoreOpsFunctionFnMutTupleU8ResultPairArrayQM314ArrayU3218ProgramError.call_mut at deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨clonedTranscript, _, deriveCallSuccess⟩ :=
                    deriveCallSuccess
                  rw [bind_eq_ok_iff] at deriveCallSuccess
                  obtain ⟨completeResult, completeSuccess,
                      deriveCallSuccess⟩ := deriveCallSuccess
                  have hcompleteResult :
                      completeResult = .Ok (polynomial, queries) := by
                    exact congrArg Prod.fst (Result.ok.inj deriveCallSuccess)
                  subst completeResult
                  exact complete_tail_success_has_decoded_polynomial
                    clonedTranscript parsed parsed.v5_query_selector
                    polynomial queries completeSuccess

private abbrev EntryRoots :=
  V5AcceptedEntryGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots

private theorem inner_active_body_start0_cont_next
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRange : core.ops.range.Range Std.Usize)
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 0#usize, «end» := 2#usize } transcript =
        .ok (.cont (returnedRange, returnedTranscript))) :
    returnedRange = { start := 1#usize, «end» := 2#usize } := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at impossible
  have hmax0 : (0#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmax0Nat : 0 < UScalar.max UScalarTy.Usize := by simpa using hmax0
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax0, hmax0Nat] at impossible
  split at impossible
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)

private theorem inner_active_body_start1_cont_next
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRange : core.ops.range.Range Std.Usize)
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 1#usize, «end» := 2#usize } transcript =
        .ok (.cont (returnedRange, returnedTranscript))) :
    returnedRange = { start := 2#usize, «end» := 2#usize } := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at impossible
  have hmax1 : (1#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmax1Nat : 1 < UScalar.max UScalarTy.Usize := by simpa using hmax1
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax1, hmax1Nat] at impossible
  split at impossible
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)

private theorem inner_active_body_start0_ne_done_one
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript : EntryTranscript)
    (returnedTranscript : EntryTranscript) (returnedRoots : EntryRoots)
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 0#usize, «end» := 2#usize } transcript =
        .ok (.done (returnedTranscript, returnedRoots, 1#u32))) :
    False := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at impossible
  have hmax0 : (0#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmax0Nat : 0 < UScalar.max UScalarTy.Usize := by simpa using hmax0
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax0, hmax0Nat] at impossible
  split at impossible
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)

private theorem inner_active_body_start1_ne_done_one
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript : EntryTranscript)
    (returnedTranscript : EntryTranscript) (returnedRoots : EntryRoots)
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 1#usize, «end» := 2#usize } transcript =
        .ok (.done (returnedTranscript, returnedRoots, 1#u32))) :
    False := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at impossible
  have hmax1 : (1#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmax1Nat : 1 < UScalar.max UScalarTy.Usize := by simpa using hmax1
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax1, hmax1Nat] at impossible
  split at impossible
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)

private theorem inner_tail_body_ne_cont
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript : EntryTranscript)
    (returnedRange : core.ops.range.Range Std.Usize)
    (returnedTranscript : EntryTranscript)
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 2#usize, «end» := 2#usize } transcript =
        .ok (.cont (returnedRange, returnedTranscript))) :
    False := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at impossible
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt] at impossible
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)
  all_goals
    repeat
      rw [bind_eq_ok_iff] at impossible
      rcases impossible with ⟨_, _, impossible⟩
    try (split at impossible)
    try (simp_all)

private theorem inner_tail_body_success_has_fold_work
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 2#usize, «end» := 2#usize } transcript =
        .ok (.done (returnedTranscript, returnedRoots, 1#u32))) :
    ∃ nonce beforeFold afterFold,
      Array.index_usize nonces round = .ok nonce ∧
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          beforeFold round nonce = .ok (.Ok (), afterFold) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at success
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt] at success
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
  obtain ⟨beforeFold, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨nonce, nonceSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperPair, helperSuccess, success⟩ := success
  rcases helperPair with ⟨helperResult, afterFold⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperFlow, helperBranchSuccess, success⟩ := success
  cases helperFlow with
  | Break residual =>
      cases residual with
      | Ok never => nomatch never
      | Err error => simp at success
  | Continue unitValue =>
      have hhelperResult := branch_eq_ok_of_continue
        helperResult unitValue helperBranchSuccess
      cases unitValue
      rw [hhelperResult] at helperSuccess
      exact ⟨nonce, beforeFold, afterFold, nonceSuccess, helperSuccess⟩

private theorem inner_tail_body_success_has_fold_successor
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 2#usize, «end» := 2#usize } transcript =
        .ok (.done (returnedTranscript, returnedRoots, 1#u32))) :
    AcceptedFoldChallengeSuccessor
      { parsed with v5_fold_nonces := nonces } round := by
  unfold AcceptedFoldChallengeSuccessor
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at success
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt] at success
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
  obtain ⟨beforeFold, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨nonce, nonceSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperPair, helperSuccess, success⟩ := success
  rcases helperPair with ⟨helperResult, afterFold⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨helperFlow, helperBranchSuccess, success⟩ := success
  cases helperFlow with
  | Break residual =>
      cases residual with
      | Ok never => nomatch never
      | Err error => simp at success
  | Continue unitValue =>
      have hhelperResult := branch_eq_ok_of_continue
        helperResult unitValue helperBranchSuccess
      cases unitValue
      rw [hhelperResult] at helperSuccess
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨challengePair, challengeSuccess, success⟩ := success
      rcases challengePair with ⟨challengeResult, afterChallenge⟩
      rw [bind_eq_ok_iff] at success
      obtain ⟨mappedResult, mappedSuccess, success⟩ := success
      rw [bind_eq_ok_iff] at success
      obtain ⟨challengeFlow, challengeBranchSuccess, success⟩ := success
      cases challengeFlow with
      | Break residual =>
          cases residual with
          | Ok never => nomatch never
          | Err error => simp at success
      | Continue sampledAlpha =>
          have hmappedResult := branch_eq_ok_of_continue
            mappedResult sampledAlpha challengeBranchSuccess
          rw [hmappedResult] at mappedSuccess
          cases challengeResult with
          | Err error =>
              simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                bind_eq_ok_iff] at mappedSuccess
          | Ok actualAlpha =>
              simp [V5AcceptedEntryGenerated.core.result.Result.map_err] at mappedSuccess
              subst actualAlpha
              rw [bind_eq_ok_iff] at success
              obtain ⟨decodeResult, decodeSuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨decodeFlow, decodeBranchSuccess, success⟩ := success
              cases decodeFlow with
              | Break residual =>
                  cases residual with
                  | Ok never => nomatch never
                  | Err error => simp at success
              | Continue decodedAlpha =>
                  have hdecodeResult := branch_eq_ok_of_continue
                    decodeResult decodedAlpha decodeBranchSuccess
                  rw [hdecodeResult] at decodeSuccess
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨differs, comparisonSuccess, success⟩ := success
                  cases differs with
                  | true => simp at success
                  | false =>
                      have alphaEq : sampledAlpha = decodedAlpha :=
                        (accepted_entry_qm31_ne_false_implies_eq
                          decodedAlpha sampledAlpha comparisonSuccess).symm
                      exact ⟨nonce, beforeFold, afterFold, sampledAlpha,
                        decodedAlpha, afterChallenge, by simpa using nonceSuccess,
                        helperSuccess, challengeSuccess, decodeSuccess,
                        comparisonSuccess, alphaEq⟩

private theorem inner_loop_start0_success_steps
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    ∃ nextTranscript,
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 0#usize, «end» := 2#usize } transcript =
        .ok (.cont ({ start := 1#usize, «end» := 2#usize }, nextTranscript)) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 1#usize, «end» := 2#usize } nextTranscript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 0#usize, «end» := 2#usize } transcript = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | done output =>
          rcases output with ⟨doneTranscript, doneRoots, doneFlag⟩
          simp only at success
          have hFlag : doneFlag = 1#u32 :=
            congrArg (fun output => output.2.2) (Result.ok.inj success)
          exact False.elim (inner_active_body_start0_ne_done_one
            parsed q nonces batch roots final selector round transcript
            doneTranscript doneRoots (by simpa [hFlag] using hbody))
      | cont state =>
          rcases state with ⟨returnedRange, nextTranscript⟩
          simp only at success
          have hRange := inner_active_body_start0_cont_next
            parsed q nonces batch roots final selector round transcript
            nextTranscript returnedRange hbody
          subst returnedRange
          refine ⟨nextTranscript, rfl, ?_⟩
          simpa [V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0]
            using success

private theorem inner_loop_start1_success_steps
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 1#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    ∃ nextTranscript,
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 1#usize, «end» := 2#usize } transcript =
        .ok (.cont ({ start := 2#usize, «end» := 2#usize }, nextTranscript)) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 2#usize, «end» := 2#usize } nextTranscript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 1#usize, «end» := 2#usize } transcript = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | done output =>
          rcases output with ⟨doneTranscript, doneRoots, doneFlag⟩
          simp only at success
          have hFlag : doneFlag = 1#u32 :=
            congrArg (fun output => output.2.2) (Result.ok.inj success)
          exact False.elim (inner_active_body_start1_ne_done_one
            parsed q nonces batch roots final selector round transcript
            doneTranscript doneRoots (by simpa [hFlag] using hbody))
      | cont state =>
          rcases state with ⟨returnedRange, nextTranscript⟩
          simp only at success
          have hRange := inner_active_body_start1_cont_next
            parsed q nonces batch roots final selector round transcript
            nextTranscript returnedRange hbody
          subst returnedRange
          refine ⟨nextTranscript, rfl, ?_⟩
          simpa [V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0]
            using success

private theorem inner_loop_tail_success_has_fold_work
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 2#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    ∃ nonce beforeFold afterFold,
      Array.index_usize nonces round = .ok nonce ∧
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          beforeFold round nonce = .ok (.Ok (), afterFold) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 2#usize, «end» := 2#usize } transcript = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | cont state =>
          rcases state with ⟨returnedRange, nextTranscript⟩
          exact False.elim (inner_tail_body_ne_cont
            parsed q nonces batch roots final selector round transcript
            returnedRange nextTranscript hbody)
      | done output =>
          rcases output with ⟨doneTranscript, doneRoots, doneFlag⟩
          simp only at success
          have hOutput :
              (doneTranscript, doneRoots, doneFlag) =
                (returnedTranscript, returnedRoots, 1#u32) :=
            Result.ok.inj success
          have hbody' :
              V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
                  parsed q nonces batch roots final selector round
                  { start := 2#usize, «end» := 2#usize } transcript =
                .ok (.done (returnedTranscript, returnedRoots, 1#u32)) := by
            rw [hbody, hOutput]
          exact inner_tail_body_success_has_fold_work
            parsed q nonces batch roots final selector round transcript
            returnedTranscript returnedRoots hbody'

private theorem inner_loop_tail_success_has_fold_successor
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 2#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    AcceptedFoldChallengeSuccessor
      { parsed with v5_fold_nonces := nonces } round := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := 2#usize, «end» := 2#usize } transcript = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | cont state =>
          rcases state with ⟨returnedRange, nextTranscript⟩
          exact False.elim (inner_tail_body_ne_cont
            parsed q nonces batch roots final selector round transcript
            returnedRange nextTranscript hbody)
      | done output =>
          rcases output with ⟨doneTranscript, doneRoots, doneFlag⟩
          simp only at success
          have hOutput :
              (doneTranscript, doneRoots, doneFlag) =
                (returnedTranscript, returnedRoots, 1#u32) :=
            Result.ok.inj success
          have hbody' :
              V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
                  parsed q nonces batch roots final selector round
                  { start := 2#usize, «end» := 2#usize } transcript =
                .ok (.done (returnedTranscript, returnedRoots, 1#u32)) := by
            rw [hbody, hOutput]
          exact inner_tail_body_success_has_fold_successor
            parsed q nonces batch roots final selector round transcript
            returnedTranscript returnedRoots hbody'

theorem inner_loop_success_has_fold_work
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    ∃ nonce beforeFold afterFold,
      Array.index_usize nonces round = .ok nonce ∧
      V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
          beforeFold round nonce = .ok (.Ok (), afterFold) := by
  obtain ⟨transcript1, _, success1⟩ := inner_loop_start0_success_steps
    parsed q nonces batch roots final selector round transcript
    returnedTranscript returnedRoots success
  obtain ⟨transcript2, _, success2⟩ := inner_loop_start1_success_steps
    parsed q nonces batch roots final selector round transcript1
    returnedTranscript returnedRoots success1
  exact inner_loop_tail_success_has_fold_work
    parsed q nonces batch roots final selector round transcript2
    returnedTranscript returnedRoots success2

theorem inner_loop_success_has_fold_successor
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    AcceptedFoldChallengeSuccessor
      { parsed with v5_fold_nonces := nonces } round := by
  obtain ⟨transcript1, _, success1⟩ := inner_loop_start0_success_steps
    parsed q nonces batch roots final selector round transcript
    returnedTranscript returnedRoots success
  obtain ⟨transcript2, _, success2⟩ := inner_loop_start1_success_steps
    parsed q nonces batch roots final selector round transcript1
    returnedTranscript returnedRoots success1
  exact inner_loop_tail_success_has_fold_successor
    parsed q nonces batch roots final selector round transcript2
    returnedTranscript returnedRoots success2

def AcceptedFoldHelperRun
    (nonces : Array Std.U64 4#usize) (round : Std.Usize) : Prop :=
  ∃ nonce beforeFold afterFold,
    Array.index_usize nonces round = .ok nonce ∧
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
        beforeFold round nonce = .ok (.Ok (), afterFold)

def AcceptedFourFoldHelperRuns
    (nonces : Array Std.U64 4#usize) : Prop :=
  AcceptedFoldHelperRun nonces 0#usize ∧
  AcceptedFoldHelperRun nonces 1#usize ∧
  AcceptedFoldHelperRun nonces 2#usize ∧
  AcceptedFoldHelperRun nonces 3#usize

private theorem fold_run_of_inner_success
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    AcceptedFoldHelperRun nonces round := by
  unfold AcceptedFoldHelperRun
  obtain ⟨nonce, beforeFold, afterFold, nonceIndex, helperSuccess⟩ :=
    inner_loop_success_has_fold_work parsed q nonces batch roots final selector
      round transcript returnedTranscript returnedRoots success
  exact ⟨nonce, beforeFold, afterFold, nonceIndex, helperSuccess⟩

private theorem fold_successor_of_inner_success
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    AcceptedFoldChallengeSuccessor
      { parsed with v5_fold_nonces := nonces } round :=
  inner_loop_success_has_fold_successor parsed q nonces batch roots final selector
    round transcript returnedTranscript returnedRoots success

private theorem outer_active_body_cont_yields_inner
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (iter nextIter returnedIter : core.ops.range.Range Std.Usize)
    (round : Std.Usize)
    (transcript roundTranscript : EntryTranscript)
    (roundRoots : EntryRoots)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some round, nextIter))
    (hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed q nonces batch final selector iter transcript roots =
        .ok (.cont (returnedIter, roundTranscript, roundRoots))) :
    returnedIter = nextIter ∧
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (roundTranscript, roundRoots, 1#u32) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body at hbody
  simp only [hnext, Aeneas.Std.bind_tc_ok] at hbody
  rw [bind_eq_ok_iff] at hbody
  obtain ⟨innerOutput, innerSuccess, hbody⟩ := hbody
  rcases innerOutput with ⟨innerTranscript, innerRoots, flag⟩
  split at hbody
  · rename_i _ hFlag
    have hOne : (1#32#uscalar : Std.U32) = 1#u32 := by
      apply UScalar.eq_of_val_eq
      rfl
    have hFlag' : flag = 1#u32 := hFlag.trans hOne
    subst flag
    cases hbody
    exact ⟨rfl, by
      simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using innerSuccess⟩
  · exact False.elim (by cases Result.ok.inj hbody)

private theorem outer_active_body_ne_successful_done
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (round : Std.Usize)
    (transcript returnedTranscript : EntryTranscript)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some round, nextIter))
    (impossible :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed q nonces batch final selector iter transcript roots =
        .ok (.done (some (.Ok returnedTranscript)))) :
    False := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body at impossible
  simp only [hnext, Aeneas.Std.bind_tc_ok] at impossible
  rw [bind_eq_ok_iff] at impossible
  obtain ⟨innerOutput, _, impossible⟩ := impossible
  rcases innerOutput with ⟨innerTranscript, innerRoots, flag⟩
  split at impossible <;> exact (by cases Result.ok.inj impossible)

private theorem outer_loop_active_success_steps
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (round : Std.Usize)
    (transcript returnedTranscript : EntryTranscript)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some round, nextIter))
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed iter transcript q nonces batch roots final selector =
        .ok (some (.Ok returnedTranscript))) :
    ∃ roundTranscript roundRoots,
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (roundTranscript, roundRoots, 1#u32) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed nextIter roundTranscript q nonces batch roundRoots final selector =
        .ok (some (.Ok returnedTranscript)) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed q nonces batch final selector iter transcript roots = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | done output =>
          simp only at success
          have hOutput : output = some (.Ok returnedTranscript) :=
            Result.ok.inj success
          subst output
          exact False.elim (outer_active_body_ne_successful_done
            parsed q nonces batch roots final selector iter nextIter round
            transcript returnedTranscript hnext hbody)
      | cont state =>
          rcases state with ⟨returnedIter, roundTranscript, roundRoots⟩
          simp only at success
          obtain ⟨hIter, hInner⟩ := outer_active_body_cont_yields_inner
            parsed q nonces batch roots final selector iter nextIter returnedIter
            round transcript roundTranscript roundRoots hnext hbody
          subst returnedIter
          refine ⟨roundTranscript, roundRoots, hInner, ?_⟩
          simpa [V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0]
            using success

private theorem outer_range_next_0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 4#usize } =
      .ok (some 0#usize, { start := 1#usize, «end» := 4#usize }) := by
  have hmax : (0#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 0 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

private theorem outer_range_next_1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 4#usize } =
      .ok (some 1#usize, { start := 2#usize, «end» := 4#usize }) := by
  have hmax : (1#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 1 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

private theorem outer_range_next_2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 4#usize } =
      .ok (some 2#usize, { start := 3#usize, «end» := 4#usize }) := by
  have hmax : (2#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 2 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

private theorem outer_range_next_3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 4#usize } =
      .ok (some 3#usize, { start := 4#usize, «end» := 4#usize }) := by
  have hmax : (3#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 3 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

private theorem outer_loop_start0_success_steps
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed { start := 0#usize, «end» := 4#usize } transcript q nonces
          batch roots final selector =
        .ok (some (.Ok returnedTranscript))) :
    ∃ roundTranscript roundRoots,
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector 0#usize =
        .ok (roundTranscript, roundRoots, 1#u32) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed { start := 1#usize, «end» := 4#usize } roundTranscript q nonces
          batch roundRoots final selector =
        .ok (some (.Ok returnedTranscript)) := by
  have hmax0 : (0#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmax0Nat : 0 < UScalar.max UScalarTy.Usize := by simpa using hmax0
  have hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := 0#usize, «end» := 4#usize } =
        .ok (some 0#usize, { start := 1#usize, «end» := 4#usize }) := by
    simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
      core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
      hmax0, hmax0Nat]
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0 at success
  rw [Aeneas.Std.loop.eq_def] at success
  simp only at success
  generalize hbody :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed q nonces batch final selector
          { start := 0#usize, «end» := 4#usize } transcript roots = bodyResult at success
  cases bodyResult with
  | fail error => simp only at success; cases success
  | div => simp only at success; cases success
  | ok flow =>
      cases flow with
      | done output =>
          simp only at success
          have hOutput : output = some (.Ok returnedTranscript) :=
            Result.ok.inj success
          subst output
          exact False.elim (outer_active_body_ne_successful_done
            parsed q nonces batch roots final selector
            { start := 0#usize, «end» := 4#usize }
            { start := 1#usize, «end» := 4#usize }
            0#usize transcript returnedTranscript hnext hbody)
      | cont state =>
          rcases state with ⟨returnedIter, roundTranscript, roundRoots⟩
          simp only at success
          obtain ⟨hIter, hInner⟩ := outer_active_body_cont_yields_inner
            parsed q nonces batch roots final selector
            { start := 0#usize, «end» := 4#usize }
            { start := 1#usize, «end» := 4#usize }
            returnedIter 0#usize transcript roundTranscript roundRoots hnext hbody
          subst returnedIter
          refine ⟨roundTranscript, roundRoots, hInner, ?_⟩
          simpa [V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0]
            using success

theorem outer_loop_success_has_four_fold_runs
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed { start := 0#usize, «end» := 4#usize } transcript q nonces
          batch roots final selector =
        .ok (some (.Ok returnedTranscript))) :
    AcceptedFourFoldHelperRuns nonces := by
  obtain ⟨transcript1, roots1, inner0, loop1⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots final selector
      { start := 0#usize, «end» := 4#usize }
      { start := 1#usize, «end» := 4#usize } 0#usize transcript
      returnedTranscript outer_range_next_0 success
  obtain ⟨transcript2, roots2, inner1, loop2⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots1 final selector
      { start := 1#usize, «end» := 4#usize }
      { start := 2#usize, «end» := 4#usize } 1#usize transcript1
      returnedTranscript outer_range_next_1 loop1
  obtain ⟨transcript3, roots3, inner2, loop3⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots2 final selector
      { start := 2#usize, «end» := 4#usize }
      { start := 3#usize, «end» := 4#usize } 2#usize transcript2
      returnedTranscript outer_range_next_2 loop2
  obtain ⟨transcript4, roots4, inner3, _⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots3 final selector
      { start := 3#usize, «end» := 4#usize }
      { start := 4#usize, «end» := 4#usize } 3#usize transcript3
      returnedTranscript outer_range_next_3 loop3
  unfold AcceptedFourFoldHelperRuns
  exact ⟨
    fold_run_of_inner_success parsed q nonces batch roots final selector
      0#usize transcript transcript1 roots1 inner0,
    fold_run_of_inner_success parsed q nonces batch roots1 final selector
      1#usize transcript1 transcript2 roots2 inner1,
    fold_run_of_inner_success parsed q nonces batch roots2 final selector
      2#usize transcript2 transcript3 roots3 inner2,
    fold_run_of_inner_success parsed q nonces batch roots3 final selector
      3#usize transcript3 transcript4 roots4 inner3⟩

theorem outer_loop_success_has_four_fold_successors
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
          parsed { start := 0#usize, «end» := 4#usize } transcript q nonces
          batch roots final selector =
        .ok (some (.Ok returnedTranscript))) :
    AcceptedFourFoldChallengeSuccessors
      { parsed with v5_fold_nonces := nonces } := by
  obtain ⟨transcript1, roots1, inner0, loop1⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots final selector
      { start := 0#usize, «end» := 4#usize }
      { start := 1#usize, «end» := 4#usize } 0#usize transcript
      returnedTranscript outer_range_next_0 success
  obtain ⟨transcript2, roots2, inner1, loop2⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots1 final selector
      { start := 1#usize, «end» := 4#usize }
      { start := 2#usize, «end» := 4#usize } 1#usize transcript1
      returnedTranscript outer_range_next_1 loop1
  obtain ⟨transcript3, roots3, inner2, loop3⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots2 final selector
      { start := 2#usize, «end» := 4#usize }
      { start := 3#usize, «end» := 4#usize } 2#usize transcript2
      returnedTranscript outer_range_next_2 loop2
  obtain ⟨transcript4, roots4, inner3, _⟩ :=
    outer_loop_active_success_steps parsed q nonces batch roots3 final selector
      { start := 3#usize, «end» := 4#usize }
      { start := 4#usize, «end» := 4#usize } 3#usize transcript3
      returnedTranscript outer_range_next_3 loop3
  unfold AcceptedFourFoldChallengeSuccessors
  exact ⟨
    fold_successor_of_inner_success parsed q nonces batch roots final selector
      0#usize transcript transcript1 roots1 inner0,
    fold_successor_of_inner_success parsed q nonces batch roots1 final selector
      1#usize transcript1 transcript2 roots2 inner1,
    fold_successor_of_inner_success parsed q nonces batch roots2 final selector
      2#usize transcript2 transcript3 roots3 inner2,
    fold_successor_of_inner_success parsed q nonces batch roots3 final selector
      3#usize transcript3 transcript4 roots4 inner3⟩

theorem relation_success_has_four_fold_runs
    (parsed : EntryParsed)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
          transcript parsed = .ok (.Ok returnedTranscript)) :
    AcceptedFourFoldHelperRuns parsed.v5_fold_nonces := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroResult, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroFlow, _, success⟩ := success
  cases zeroFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
  | Continue unitValue =>
      cases unitValue
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨pending, outerSuccess, success⟩ := success
      cases pending with
      | none => simp at success
      | some result =>
          have hResult : result = .Ok returnedTranscript :=
            Result.ok.inj success
          subst result
          apply outer_loop_success_has_four_fold_runs
            parsed parsed.gamma parsed.v5_fold_nonces parsed.v5_batch_nonce
            parsed.v5_private_roots parsed.v5_final_nonce parsed.v5_query_selector
            transcript returnedTranscript
          simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_ROUNDS]
            using outerSuccess

theorem relation_success_has_four_fold_successors
    (parsed : EntryParsed)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
          transcript parsed = .ok (.Ok returnedTranscript)) :
    AcceptedFourFoldChallengeSuccessors parsed := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroResult, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroFlow, _, success⟩ := success
  cases zeroFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
  | Continue unitValue =>
      cases unitValue
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨pending, outerSuccess, success⟩ := success
      cases pending with
      | none => simp at success
      | some result =>
          have hResult : result = .Ok returnedTranscript :=
            Result.ok.inj success
          subst result
          simpa using outer_loop_success_has_four_fold_successors
            parsed parsed.gamma parsed.v5_fold_nonces parsed.v5_batch_nonce
            parsed.v5_private_roots parsed.v5_final_nonce parsed.v5_query_selector
            transcript returnedTranscript
            (by
              simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_ROUNDS]
                using outerSuccess)

/-! The fold projection above intentionally retains only the tail of each
relation round.  The next proposition retains the two successful active
sample bodies as well.  It is used to connect the eight OOD-mix challenges to
the values which the same accepted execution compares against the proof
bytes. -/

def AcceptedRoundOodMixBodies
    (parsed : EntryParsed) (round : Std.Usize) : Prop :=
  ∃ (q : EntryQM31) (nonces : Array Std.U64 4#usize)
      (batch : Std.U64) (roots : EntryRoots) (final : Std.U64)
      (selector : Std.U8) (before firstDone secondDone : EntryTranscript),
    V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
        parsed q nonces batch roots final selector round
        { start := 0#usize, «end» := 2#usize } before =
      .ok (.cont
        ({ start := 1#usize, «end» := 2#usize }, firstDone)) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
        parsed q nonces batch roots final selector round
        { start := 1#usize, «end» := 2#usize } firstDone =
      .ok (.cont
        ({ start := 2#usize, «end» := 2#usize }, secondDone))

def AcceptedFourRoundOodMixBodies (parsed : EntryParsed) : Prop :=
  AcceptedRoundOodMixBodies parsed 0#usize ∧
  AcceptedRoundOodMixBodies parsed 1#usize ∧
  AcceptedRoundOodMixBodies parsed 2#usize ∧
  AcceptedRoundOodMixBodies parsed 3#usize

private theorem inner_success_has_ood_mix_bodies
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (returnedRoots : EntryRoots)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed { start := 0#usize, «end» := 2#usize } transcript q nonces
          batch roots final selector round =
        .ok (returnedTranscript, returnedRoots, 1#u32)) :
    AcceptedRoundOodMixBodies parsed round := by
  obtain ⟨transcript1, body0, success1⟩ :=
    inner_loop_start0_success_steps parsed q nonces batch roots final selector
      round transcript returnedTranscript returnedRoots success
  obtain ⟨transcript2, body1, _⟩ :=
    inner_loop_start1_success_steps parsed q nonces batch roots final selector
      round transcript1 returnedTranscript returnedRoots success1
  exact ⟨q, nonces, batch, roots, final, selector, transcript,
    transcript1, transcript2, body0, body1⟩

theorem relation_success_has_four_ood_mix_bodies
    (parsed : EntryParsed)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
          transcript parsed = .ok (.Ok returnedTranscript)) :
    AcceptedFourRoundOodMixBodies parsed := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroResult, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨zeroFlow, _, success⟩ := success
  cases zeroFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
  | Continue unitValue =>
      cases unitValue
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨pending, outerSuccess, success⟩ := success
      cases pending with
      | none => simp at success
      | some result =>
          have hResult : result = .Ok returnedTranscript :=
            Result.ok.inj success
          subst result
          have outerSuccess' :
              V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0
                  parsed { start := 0#usize, «end» := 4#usize } transcript
                  parsed.gamma parsed.v5_fold_nonces parsed.v5_batch_nonce
                  parsed.v5_private_roots parsed.v5_final_nonce
                  parsed.v5_query_selector =
                .ok (some (.Ok returnedTranscript)) := by
            simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_ROUNDS]
              using outerSuccess
          obtain ⟨transcript1, roots1, inner0, loop1⟩ :=
            outer_loop_active_success_steps parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce
              parsed.v5_private_roots parsed.v5_final_nonce
              parsed.v5_query_selector
              { start := 0#usize, «end» := 4#usize }
              { start := 1#usize, «end» := 4#usize } 0#usize transcript
              returnedTranscript outer_range_next_0 outerSuccess'
          obtain ⟨transcript2, roots2, inner1, loop2⟩ :=
            outer_loop_active_success_steps parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots1
              parsed.v5_final_nonce parsed.v5_query_selector
              { start := 1#usize, «end» := 4#usize }
              { start := 2#usize, «end» := 4#usize } 1#usize transcript1
              returnedTranscript outer_range_next_1 loop1
          obtain ⟨transcript3, roots3, inner2, loop3⟩ :=
            outer_loop_active_success_steps parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots2
              parsed.v5_final_nonce parsed.v5_query_selector
              { start := 2#usize, «end» := 4#usize }
              { start := 3#usize, «end» := 4#usize } 2#usize transcript2
              returnedTranscript outer_range_next_2 loop2
          obtain ⟨transcript4, roots4, inner3, _⟩ :=
            outer_loop_active_success_steps parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots3
              parsed.v5_final_nonce parsed.v5_query_selector
              { start := 3#usize, «end» := 4#usize }
              { start := 4#usize, «end» := 4#usize } 3#usize transcript3
              returnedTranscript outer_range_next_3 loop3
          exact ⟨
            inner_success_has_ood_mix_bodies parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce
              parsed.v5_private_roots parsed.v5_final_nonce
              parsed.v5_query_selector 0#usize transcript transcript1 roots1
              inner0,
            inner_success_has_ood_mix_bodies parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots1
              parsed.v5_final_nonce parsed.v5_query_selector 1#usize
              transcript1 transcript2 roots2 inner1,
            inner_success_has_ood_mix_bodies parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots2
              parsed.v5_final_nonce parsed.v5_query_selector 2#usize
              transcript2 transcript3 roots3 inner2,
            inner_success_has_ood_mix_bodies parsed parsed.gamma
              parsed.v5_fold_nonces parsed.v5_batch_nonce roots3
              parsed.v5_final_nonce parsed.v5_query_selector 3#usize
              transcript3 transcript4 roots4 inner3⟩

def AcceptedFoldRequiredWork
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8) : Prop :=
  ∃ nonce beforeFold afterFold,
    Array.index_usize nonces round = .ok nonce ∧
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_fold_nonce
        beforeFold round nonce = .ok (.Ok (), afterFold) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeFold nonce bits = .ok (.Ok ())

def AcceptedFourFoldRequiredWork
    (nonces : Array Std.U64 4#usize) : Prop :=
  AcceptedFoldRequiredWork nonces 0#usize 34#u8 ∧
  AcceptedFoldRequiredWork nonces 1#usize 33#u8 ∧
  AcceptedFoldRequiredWork nonces 2#usize 30#u8 ∧
  AcceptedFoldRequiredWork nonces 3#usize 25#u8

theorem fold_helper_run_implies_required_work
    (nonces : Array Std.U64 4#usize) (round : Std.Usize)
    (bits : Std.U8)
    (difficulty :
      V5AcceptedEntryGenerated.v5_cu_probe.v5_fold_work_difficulty round =
        .ok (some bits))
    (run : AcceptedFoldHelperRun nonces round) :
    AcceptedFoldRequiredWork nonces round bits := by
  unfold AcceptedFoldHelperRun at run
  unfold AcceptedFoldRequiredWork
  obtain ⟨nonce, beforeFold, afterFold, nonceIndex, helperSuccess⟩ := run
  exact ⟨nonce, beforeFold, afterFold, nonceIndex, helperSuccess,
    fold_success_implies_required_work beforeFold afterFold round nonce bits
      difficulty helperSuccess⟩

theorem four_fold_runs_have_exact_required_work
    (nonces : Array Std.U64 4#usize)
    (runs : AcceptedFourFoldHelperRuns nonces) :
    AcceptedFourFoldRequiredWork nonces := by
  unfold AcceptedFourFoldHelperRuns at runs
  unfold AcceptedFourFoldRequiredWork
  rcases runs with ⟨round0, round1, round2, round3⟩
  exact ⟨
    fold_helper_run_implies_required_work nonces 0#usize 34#u8 (by rfl) round0,
    fold_helper_run_implies_required_work nonces 1#usize 33#u8 (by rfl) round1,
    fold_helper_run_implies_required_work nonces 2#usize 30#u8 (by rfl) round2,
    fold_helper_run_implies_required_work nonces 3#usize 25#u8 (by rfl) round3⟩

theorem relation_success_has_exact_fold_work
    (parsed : EntryParsed)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
          transcript parsed = .ok (.Ok returnedTranscript)) :
    AcceptedFourFoldRequiredWork parsed.v5_fold_nonces :=
  four_fold_runs_have_exact_required_work parsed.v5_fold_nonces
    (relation_success_has_four_fold_runs parsed transcript returnedTranscript success)

def AcceptedFinalRequiredWork (parsed : EntryParsed) : Prop :=
  ∃ beforeFinal afterFinal,
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_final_nonce
        beforeFinal parsed.v5_final_nonce = .ok (.Ok (), afterFinal) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeFinal parsed.v5_final_nonce 32#u8 = .ok (.Ok ())

theorem selected_query_success_has_exact_final_work
    (transcript : EntryTranscript) (parsed : EntryParsed)
    (point : Array EntryQM31 10#usize)
    (polynomial : Array EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    AcceptedFinalRequiredWork parsed := by
  unfold AcceptedFinalRequiredWork
  obtain ⟨beforeFinal, afterFinal, helperSuccess⟩ :=
    selected_query_success_has_final_work transcript parsed point polynomial
      queries success
  exact ⟨beforeFinal, afterFinal, helperSuccess,
    final_success_implies_difficulty_32_work beforeFinal afterFinal
      parsed.v5_final_nonce helperSuccess⟩

def AcceptedBatchRequiredWork (parsed : EntryParsed) : Prop :=
  ∃ beforeBatch afterBatch,
    V5AcceptedEntryGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
        beforeBatch parsed.v5_batch_nonce = .ok (.Ok (), afterBatch) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.require_real_v5_work
        beforeBatch parsed.v5_batch_nonce 37#u8 = .ok (.Ok ())

def AcceptedSixRequiredWork (parsed : EntryParsed) : Prop :=
  AcceptedBatchRequiredWork parsed ∧
  AcceptedFourFoldRequiredWork parsed.v5_fold_nonces ∧
  AcceptedFinalRequiredWork parsed

theorem accepted_call_facts_prove_six_work
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (verifiedPrefix : EntryVerifiedPrefix)
    (prefixTranscript : EntryTranscript)
    (verifiedTerminal : EntryVerifiedTerminal)
    (relationTranscript : EntryTranscript)
    (finalPolynomial : Array EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (alphas : Array EntryQM31 4#usize)
    (friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims)
    (relationSum phaseSum : EntryQM31)
    (facts : AcceptedCompositeCallFacts accountData parsed liveStatement
      statementDigest acceptedValue verifiedPrefix prefixTranscript
      verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
      preparedClaims relationSum phaseSum) :
    AcceptedSixRequiredWork parsed := by
  unfold AcceptedSixRequiredWork
  constructor
  · unfold AcceptedBatchRequiredWork
    exact accepted_prefix_proves_batch_work parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv verifiedPrefix prefixTranscript
      facts.prefixSuccess
  constructor
  · exact relation_success_has_exact_fold_work parsed prefixTranscript
      relationTranscript facts.relationSuccess
  · exact selected_query_success_has_exact_final_work relationTranscript parsed
      verifiedPrefix.round_challenges finalPolynomial queries facts.querySuccess

theorem accepted_composite_proves_six_work
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedSixRequiredWork parsed := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, facts⟩ :=
    accepted_composite_builds_call_chain accountData parsed liveStatement
      statementDigest acceptedValue success
  exact accepted_call_facts_prove_six_work accountData parsed liveStatement
    statementDigest acceptedValue verifiedPrefix prefixTranscript
    verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
    preparedClaims relationSum phaseSum facts


#print axioms fold_success_implies_required_work
#print axioms final_success_implies_difficulty_32_work
#print axioms relation_success_has_exact_fold_work
#print axioms selected_query_success_has_exact_final_work
#print axioms accepted_composite_proves_six_work

end AspisV5AcceptedEntrySourceBridge
