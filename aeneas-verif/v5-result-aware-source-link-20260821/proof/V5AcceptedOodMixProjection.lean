import V5AcceptedRemainingWorkBridge

/-!
# The eight OOD mixers used by one accepted relation replay

This file inverts the two active sample bodies in each of the four relation
rounds.  It retains the exact `challenge_qm31` result and the proof-body word
which the production caller immediately compares with that result.
-/

namespace AspisV5AcceptedOodMixProjection

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

private theorem usizeMulExact (x y z : Std.Usize)
    (hbound : x.val * y.val ≤ Std.Usize.max)
    (hval : z.val = x.val * y.val) :
    x * y = ok z := by
  have hspec := Std.Usize.mul_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeSubExact (x y z : Std.Usize)
    (hbound : y.val ≤ x.val)
    (hval : z.val = x.val - y.val) :
    x - y = ok z := by
  have hspec := Std.Usize.sub_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

@[local simp] private theorem mul_4_2 :
    (4#usize * 2#usize : Result Std.Usize) = .ok 8#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_8_16 :
    (8#usize * 16#usize : Result Std.Usize) = .ok 128#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem sub_4_1 :
    (4#usize - 1#usize : Result Std.Usize) = .ok 3#usize := by
  apply usizeSubExact <;> scalar_tac
@[local simp] private theorem mul_3_2 :
    (3#usize * 2#usize : Result Std.Usize) = .ok 6#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_6_16 :
    (6#usize * 16#usize : Result Std.Usize) = .ok 96#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_2_2 :
    (2#usize * 2#usize : Result Std.Usize) = .ok 4#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_4_16 :
    (4#usize * 16#usize : Result Std.Usize) = .ok 64#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_0_64 :
    (0#usize + 64#usize : Result Std.Usize) = .ok 64#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_64_96 :
    (64#usize + 96#usize : Result Std.Usize) = .ok 160#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_160_128 :
    (160#usize + 128#usize : Result Std.Usize) = .ok 288#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_0_2 :
    (0#usize * 2#usize : Result Std.Usize) = .ok 0#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_0_16 :
    (0#usize * 16#usize : Result Std.Usize) = .ok 0#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_0_0 :
    (0#usize + 0#usize : Result Std.Usize) = .ok 0#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_288_0 :
    (288#usize + 0#usize : Result Std.Usize) = .ok 288#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_0_1 :
    (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_1_16 :
    (1#usize * 16#usize : Result Std.Usize) = .ok 16#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_288_16 :
    (288#usize + 16#usize : Result Std.Usize) = .ok 304#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_1_2 :
    (1#usize * 2#usize : Result Std.Usize) = .ok 2#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_2_0 :
    (2#usize + 0#usize : Result Std.Usize) = .ok 2#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_2_1 :
    (2#usize + 1#usize : Result Std.Usize) = .ok 3#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_2_16 :
    (2#usize * 16#usize : Result Std.Usize) = .ok 32#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem mul_3_16 :
    (3#usize * 16#usize : Result Std.Usize) = .ok 48#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_288_32 :
    (288#usize + 32#usize : Result Std.Usize) = .ok 320#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_288_48 :
    (288#usize + 48#usize : Result Std.Usize) = .ok 336#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_4_0 :
    (4#usize + 0#usize : Result Std.Usize) = .ok 4#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_4_1 :
    (4#usize + 1#usize : Result Std.Usize) = .ok 5#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_5_16 :
    (5#usize * 16#usize : Result Std.Usize) = .ok 80#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_288_64 :
    (288#usize + 64#usize : Result Std.Usize) = .ok 352#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_288_80 :
    (288#usize + 80#usize : Result Std.Usize) = .ok 368#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_6_0 :
    (6#usize + 0#usize : Result Std.Usize) = .ok 6#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_6_1 :
    (6#usize + 1#usize : Result Std.Usize) = .ok 7#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem mul_7_16 :
    (7#usize * 16#usize : Result Std.Usize) = .ok 112#usize := by
  apply usizeMulExact <;> scalar_tac
@[local simp] private theorem add_288_96 :
    (288#usize + 96#usize : Result Std.Usize) = .ok 384#usize := by
  apply usizeAddExact <;> scalar_tac
@[local simp] private theorem add_288_112 :
    (288#usize + 112#usize : Result Std.Usize) = .ok 400#usize := by
  apply usizeAddExact <;> scalar_tac

abbrev EntryRoots :=
  V5AcceptedEntryGenerated.v5_cu_probe.private_openings.V5PrivateOpeningRoots

def roundUsize (round : Fin 4) : Std.Usize :=
  if round = 0 then 0#usize
  else if round = 1 then 1#usize
  else if round = 2 then 2#usize
  else 3#usize

def sampleUsize (sample : Fin 2) : Std.Usize :=
  if sample = 0 then 0#usize else 1#usize

def expectedMixOffset (round : Fin 4) (sample : Fin 2) : Std.Usize :=
  if round = 0 then
    if sample = 0 then 288#usize else 304#usize
  else if round = 1 then
    if sample = 0 then 320#usize else 336#usize
  else if round = 2 then
    if sample = 0 then 352#usize else 368#usize
  else
    if sample = 0 then 384#usize else 400#usize

def expectedObservation (round : Fin 4) (sample : Fin 2) : Std.Usize :=
  if round = 0 then
    if sample = 0 then 0#usize else 1#usize
  else if round = 1 then
    if sample = 0 then 2#usize else 3#usize
  else if round = 2 then
    if sample = 0 then 4#usize else 5#usize
  else
    if sample = 0 then 6#usize else 7#usize

def expectedObservationBytes (round : Fin 4) (sample : Fin 2) : Std.Usize :=
  if round = 0 then
    if sample = 0 then 0#usize else 16#usize
  else if round = 1 then
    if sample = 0 then 32#usize else 48#usize
  else if round = 2 then
    if sample = 0 then 64#usize else 80#usize
  else
    if sample = 0 then 96#usize else 112#usize

private theorem released_mix_base_exact :
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
      .ok 288#usize := by
  simp [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
    V5AcceptedEntryGenerated.v5_relation_stress.OOD_VALUES,
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
    V5AcceptedEntryGenerated.v5_relation_stress.LINE_POINTS,
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
    V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
    V5AcceptedEntryGenerated.v5_relation_stress.CIRCLE_COORDINATES,
    V5AcceptedEntryGenerated.v5_relation_stress.QM31_BYTES]

private theorem round_zero_observation_exact :
    (0#usize *
      V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES :
        Result Std.Usize) = .ok 0#usize := by
  simp [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]

private theorem zero_observation_bytes_exact :
    (0#usize * V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES :
      Result Std.Usize) = .ok 0#usize := by
  simp [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES]

private theorem inner_range_next_0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 2#usize } =
      .ok (some 0#usize, { start := 1#usize, «end» := 2#usize }) := by
  have hmax : (0#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 0 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

private theorem inner_range_next_1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 2#usize } =
      .ok (some 1#usize, { start := 2#usize, «end» := 2#usize }) := by
  have hmax : (1#usize).val < UScalar.max UScalarTy.Usize := by scalar_tac
  have hmaxNat : 1 < UScalar.max UScalarTy.Usize := by simpa using hmax
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    hmax, hmaxNat]

/-- One of the eight production relation bodies sampled this exact challenge
and accepted only after comparing it with the exact word at its released
stress-section offset. -/
def AcceptedOodMixCall
    (parsed : EntryParsed) (round : Fin 4) (sample : Fin 2) : Prop :=
  ∃ (q : EntryQM31) (nonces : Array Std.U64 4#usize)
      (batch : Std.U64) (roots : EntryRoots) (final : Std.U64)
      (selector : Std.U8) (initialTranscript finalTranscript : EntryTranscript)
      (beforeMix afterMix : EntryTranscript) (sampledMix : EntryQM31),
    V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
        parsed q nonces batch roots final selector (roundUsize round)
        { start := sampleUsize sample, «end» := 2#usize } initialTranscript =
      .ok (.cont
        ({ start := if sample = 0 then 1#usize else 2#usize,
           «end» := 2#usize }, finalTranscript)) ∧
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
        beforeMix = .ok (.Ok sampledMix, afterMix) ∧
    V5AcceptedEntryGenerated.v5_cu_probe.stress_qm31 parsed
        (expectedMixOffset round sample) = .ok (.Ok sampledMix)

private theorem circle_body_yields_raw_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (sample nextSample expectedObservationValue expectedObservationBytesValue
      expectedMixOffsetValue : Std.Usize)
    (before after : EntryTranscript)
    (rangeNext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sample, «end» := 2#usize } =
        .ok (some sample, { start := nextSample, «end» := 2#usize }))
    (roundSamplesExact :
      (0#usize *
        V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES :
          Result Std.Usize) = .ok 0#usize)
    (observationExact :
      (0#usize + sample : Result Std.Usize) = .ok expectedObservationValue)
    (observationBytesExact :
      (expectedObservationValue *
        V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES :
          Result Std.Usize) = .ok expectedObservationBytesValue)
    (mixOffsetExact :
      (288#usize + expectedObservationBytesValue : Result Std.Usize) =
        .ok expectedMixOffsetValue)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 0#usize
          { start := sample, «end» := 2#usize } before =
        .ok (.cont ({ start := nextSample, «end» := 2#usize }, after))) :
    ∃ beforeMix afterMix sampledMix,
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
          beforeMix = .ok (.Ok sampledMix, afterMix) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.stress_qm31 parsed
          expectedMixOffsetValue =
        .ok (.Ok sampledMix) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at success
  simp only [rangeNext, Aeneas.Std.bind_tc_ok, if_true] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pointPair, pointSuccess, success⟩ := success
  rcases pointPair with ⟨pointResult, pointTranscript⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨mappedPoint, mappedPointSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pointFlow, pointBranchSuccess, success⟩ := success
  cases pointFlow with
  | Break residual =>
    cases residual with
    | Ok impossible => nomatch impossible
    | Err error => simp at success
  | Continue point =>
    simp only at success
    rw [bind_eq_ok_iff] at success
    obtain ⟨twiceSample, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointByteOffset, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointOffset, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointXResult, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointXFlow, _, success⟩ := success
    cases pointXFlow with
    | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
    | Continue pointX =>
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨pointXDiffers, _, success⟩ := success
      cases pointXDiffers with
      | true => simp at success
      | false =>
        simp only [Bool.false_eq_true, if_false] at success
        rw [bind_eq_ok_iff] at success
        obtain ⟨pointYOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨pointYResult, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨pointYFlow, _, success⟩ := success
        cases pointYFlow with
        | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error => simp at success
        | Continue pointY =>
          simp only at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨pointYDiffers, _, success⟩ := success
          cases pointYDiffers with
          | true => simp at success
          | false =>
            simp only [Bool.false_eq_true, if_false] at success
            rw [bind_eq_ok_iff] at success
            obtain ⟨roundSamples, roundSamplesSuccess, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨observation, observationSuccess, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨observationBytes, observationBytesSuccess, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨oodBase, _, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨oodOffset, _, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨oodResult, _, success⟩ := success
            rw [bind_eq_ok_iff] at success
            obtain ⟨oodFlow, _, success⟩ := success
            cases oodFlow with
            | Break residual =>
              cases residual with
              | Ok impossible => nomatch impossible
              | Err error => simp at success
            | Continue oodValue =>
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨oodLabel, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨afterAbsorb, _, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨challengePair, challengeSuccess, success⟩ := success
              rcases challengePair with ⟨challengeResult, afterChallenge⟩
              rw [bind_eq_ok_iff] at success
              obtain ⟨mappedMix, mappedMixSuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨mixFlow, mixBranchSuccess, success⟩ := success
              cases mixFlow with
              | Break residual =>
                cases residual with
                | Ok impossible => nomatch impossible
                | Err error => simp at success
              | Continue sampledMix =>
                have hmappedMix := branch_eq_ok_of_continue
                  mappedMix sampledMix mixBranchSuccess
                rw [hmappedMix] at mappedMixSuccess
                cases challengeResult with
                | Err error =>
                    simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                      bind_eq_ok_iff] at mappedMixSuccess
                | Ok actualMix =>
                  simp [V5AcceptedEntryGenerated.core.result.Result.map_err]
                    at mappedMixSuccess
                  subst actualMix
                  simp only at success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨mixBase, mixBaseSuccess, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨mixOffset, mixOffsetSuccess, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨decodedResult, decodedSuccess, success⟩ := success
                  rw [bind_eq_ok_iff] at success
                  obtain ⟨decodedFlow, decodedBranchSuccess, success⟩ := success
                  cases decodedFlow with
                  | Break residual =>
                    cases residual with
                    | Ok impossible => nomatch impossible
                    | Err error => simp at success
                  | Continue decodedMix =>
                    have hdecoded := branch_eq_ok_of_continue
                      decodedResult decodedMix decodedBranchSuccess
                    rw [hdecoded] at decodedSuccess
                    simp only at success
                    rw [bind_eq_ok_iff] at success
                    obtain ⟨mixDiffers, mixComparison, success⟩ := success
                    cases mixDiffers with
                    | true => simp at success
                    | false =>
                      have hmix : decodedMix = sampledMix :=
                        accepted_entry_qm31_ne_false_implies_eq
                          decodedMix sampledMix mixComparison
                      subst decodedMix
                      have hRoundSamples : roundSamples = 0#usize :=
                        Result.ok.inj
                          (roundSamplesSuccess.symm.trans
                            roundSamplesExact)
                      subst roundSamples
                      have hObservation : observation = expectedObservationValue :=
                        Result.ok.inj
                          (observationSuccess.symm.trans observationExact)
                      subst observation
                      have hObservationBytes :
                          observationBytes = expectedObservationBytesValue :=
                        Result.ok.inj
                          (observationBytesSuccess.symm.trans
                            observationBytesExact)
                      subst observationBytes
                      have hMixBase : mixBase = 288#usize := by
                        exact Result.ok.inj
                          (mixBaseSuccess.symm.trans released_mix_base_exact)
                      subst mixBase
                      have hMixOffset : mixOffset = expectedMixOffsetValue := by
                        exact Result.ok.inj
                          (mixOffsetSuccess.symm.trans mixOffsetExact)
                      subst mixOffset
                      refine ⟨afterAbsorb, afterChallenge, sampledMix,
                        challengeSuccess, ?_⟩
                      simpa [V5AcceptedEntryGenerated.v5_cu_probe.stress_qm31]
                        using decodedSuccess

private theorem line_body_yields_raw_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (round sample nextSample roundSamplesValue expectedObservationValue
      expectedObservationBytesValue expectedMixOffsetValue : Std.Usize)
    (before after : EntryTranscript)
    (roundNeZero : round ≠ 0#usize)
    (rangeNext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          { start := sample, «end» := 2#usize } =
        .ok (some sample, { start := nextSample, «end» := 2#usize }))
    (roundSamplesExact :
      (round *
        V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES :
          Result Std.Usize) = .ok roundSamplesValue)
    (observationExact :
      (roundSamplesValue + sample : Result Std.Usize) =
        .ok expectedObservationValue)
    (observationBytesExact :
      (expectedObservationValue *
        V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES :
          Result Std.Usize) = .ok expectedObservationBytesValue)
    (mixOffsetExact :
      (288#usize + expectedObservationBytesValue : Result Std.Usize) =
        .ok expectedMixOffsetValue)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector round
          { start := sample, «end» := 2#usize } before =
        .ok (.cont ({ start := nextSample, «end» := 2#usize }, after))) :
    ∃ beforeMix afterMix sampledMix,
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
          beforeMix = .ok (.Ok sampledMix, afterMix) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.stress_qm31 parsed
          expectedMixOffsetValue = .ok (.Ok sampledMix) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body at success
  simp only [rangeNext, Aeneas.Std.bind_tc_ok, roundNeZero, if_false] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pointPair, pointSuccess, success⟩ := success
  rcases pointPair with ⟨pointResult, pointTranscript⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨mappedPoint, mappedPointSuccess, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨pointFlow, pointBranchSuccess, success⟩ := success
  cases pointFlow with
  | Break residual =>
    cases residual with
    | Ok impossible => nomatch impossible
    | Err error => simp at success
  | Continue point =>
    simp only at success
    rw [bind_eq_ok_iff] at success
    obtain ⟨roundMinus, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointRoundSamples, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointIndex, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointBytes, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨lineBase, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨pointOffset, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨decodedPointResult, _, success⟩ := success
    rw [bind_eq_ok_iff] at success
    obtain ⟨decodedPointFlow, _, success⟩ := success
    cases decodedPointFlow with
    | Break residual =>
      cases residual with
      | Ok impossible => nomatch impossible
      | Err error => simp at success
    | Continue decodedPoint =>
      simp only at success
      rw [bind_eq_ok_iff] at success
      obtain ⟨pointDiffers, _, success⟩ := success
      cases pointDiffers with
      | true => simp at success
      | false =>
        simp only [Bool.false_eq_true, if_false] at success
        rw [bind_eq_ok_iff] at success
        obtain ⟨roundSamples, roundSamplesSuccess, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨observation, observationSuccess, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨observationBytes, observationBytesSuccess, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨oodBase, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨oodOffset, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨oodResult, _, success⟩ := success
        rw [bind_eq_ok_iff] at success
        obtain ⟨oodFlow, _, success⟩ := success
        cases oodFlow with
        | Break residual =>
          cases residual with
          | Ok impossible => nomatch impossible
          | Err error => simp at success
        | Continue oodValue =>
          simp only [roundNeZero, if_false] at success
          rw [bind_eq_ok_iff] at success
          obtain ⟨oodLabel, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨afterAbsorb, _, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨challengePair, challengeSuccess, success⟩ := success
          rcases challengePair with ⟨challengeResult, afterChallenge⟩
          rw [bind_eq_ok_iff] at success
          obtain ⟨mappedMix, mappedMixSuccess, success⟩ := success
          rw [bind_eq_ok_iff] at success
          obtain ⟨mixFlow, mixBranchSuccess, success⟩ := success
          cases mixFlow with
          | Break residual =>
            cases residual with
            | Ok impossible => nomatch impossible
            | Err error => simp at success
          | Continue sampledMix =>
            have hmappedMix := branch_eq_ok_of_continue
              mappedMix sampledMix mixBranchSuccess
            rw [hmappedMix] at mappedMixSuccess
            cases challengeResult with
            | Err error =>
                simp [V5AcceptedEntryGenerated.core.result.Result.map_err,
                  bind_eq_ok_iff] at mappedMixSuccess
            | Ok actualMix =>
              simp [V5AcceptedEntryGenerated.core.result.Result.map_err]
                at mappedMixSuccess
              subst actualMix
              simp only at success
              rw [bind_eq_ok_iff] at success
              obtain ⟨mixBase, mixBaseSuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨mixOffset, mixOffsetSuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨decodedResult, decodedSuccess, success⟩ := success
              rw [bind_eq_ok_iff] at success
              obtain ⟨decodedFlow, decodedBranchSuccess, success⟩ := success
              cases decodedFlow with
              | Break residual =>
                cases residual with
                | Ok impossible => nomatch impossible
                | Err error => simp at success
              | Continue decodedMix =>
                have hdecoded := branch_eq_ok_of_continue
                  decodedResult decodedMix decodedBranchSuccess
                rw [hdecoded] at decodedSuccess
                simp only at success
                rw [bind_eq_ok_iff] at success
                obtain ⟨mixDiffers, mixComparison, success⟩ := success
                cases mixDiffers with
                | true => simp at success
                | false =>
                  have hmix : decodedMix = sampledMix :=
                    accepted_entry_qm31_ne_false_implies_eq
                      decodedMix sampledMix mixComparison
                  subst decodedMix
                  have hRoundSamples : roundSamples = roundSamplesValue :=
                    Result.ok.inj
                      (roundSamplesSuccess.symm.trans roundSamplesExact)
                  subst roundSamples
                  have hObservation : observation = expectedObservationValue :=
                    Result.ok.inj
                      (observationSuccess.symm.trans observationExact)
                  subst observation
                  have hObservationBytes :
                      observationBytes = expectedObservationBytesValue :=
                    Result.ok.inj
                      (observationBytesSuccess.symm.trans observationBytesExact)
                  subst observationBytes
                  have hMixBase : mixBase = 288#usize :=
                    Result.ok.inj
                      (mixBaseSuccess.symm.trans released_mix_base_exact)
                  subst mixBase
                  have hMixOffset : mixOffset = expectedMixOffsetValue :=
                    Result.ok.inj
                      (mixOffsetSuccess.symm.trans mixOffsetExact)
                  subst mixOffset
                  refine ⟨afterAbsorb, afterChallenge, sampledMix,
                    challengeSuccess, ?_⟩
                  simpa [V5AcceptedEntryGenerated.v5_cu_probe.stress_qm31]
                    using decodedSuccess

private theorem body_0_0_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 0#usize
          { start := 0#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 1#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 0 0 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    circle_body_yields_raw_mix parsed q nonces batch roots final selector
      0#usize 1#usize 0#usize 0#usize 288#usize before after
      inner_range_next_0 round_zero_observation_exact add_0_0
      zero_observation_bytes_exact add_288_0 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_0_1_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 0#usize
          { start := 1#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 2#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 0 1 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    circle_body_yields_raw_mix parsed q nonces batch roots final selector
      1#usize 2#usize 1#usize 16#usize 304#usize before after
      inner_range_next_1 round_zero_observation_exact add_0_1
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_1_16)
      add_288_16 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_1_0_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 1#usize
          { start := 0#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 1#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 1 0 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      1#usize 0#usize 1#usize 2#usize 2#usize 32#usize 320#usize
      before after (by scalar_tac) inner_range_next_0
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_1_2)
      add_2_0
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_2_16)
      add_288_32 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_1_1_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 1#usize
          { start := 1#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 2#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 1 1 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      1#usize 1#usize 2#usize 2#usize 3#usize 48#usize 336#usize
      before after (by scalar_tac) inner_range_next_1
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_1_2)
      add_2_1
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_3_16)
      add_288_48 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_2_0_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 2#usize
          { start := 0#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 1#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 2 0 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      2#usize 0#usize 1#usize 4#usize 4#usize 64#usize 352#usize
      before after (by scalar_tac) inner_range_next_0
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_2_2)
      add_4_0
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_4_16)
      add_288_64 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_2_1_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 2#usize
          { start := 1#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 2#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 2 1 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      2#usize 1#usize 2#usize 4#usize 5#usize 80#usize 368#usize
      before after (by scalar_tac) inner_range_next_1
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_2_2)
      add_4_1
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_5_16)
      add_288_80 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_3_0_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 3#usize
          { start := 0#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 1#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 3 0 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      3#usize 0#usize 1#usize 6#usize 6#usize 96#usize 384#usize
      before after (by scalar_tac) inner_range_next_0
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_3_2)
      add_6_0
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_6_16)
      add_288_96 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

private theorem body_3_1_yields_mix
    (parsed : EntryParsed) (q : EntryQM31)
    (nonces : Array Std.U64 4#usize) (batch : Std.U64)
    (roots : EntryRoots) (final : Std.U64) (selector : Std.U8)
    (before after : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed q nonces batch roots final selector 3#usize
          { start := 1#usize, «end» := 2#usize } before =
        .ok (.cont ({ start := 2#usize, «end» := 2#usize }, after))) :
    AcceptedOodMixCall parsed 3 1 := by
  obtain ⟨beforeMix, afterMix, sampledMix, challengeSuccess, decodedSuccess⟩ :=
    line_body_yields_raw_mix parsed q nonces batch roots final selector
      3#usize 1#usize 2#usize 6#usize 7#usize 112#usize 400#usize
      before after (by scalar_tac) inner_range_next_1
      (by simpa [V5AcceptedEntryGenerated.v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
        using mul_3_2)
      add_6_1
      (by simpa [V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES] using mul_7_16)
      add_288_112 success
  exact ⟨q, nonces, batch, roots, final, selector, before, after,
    beforeMix, afterMix, sampledMix, by simpa [roundUsize, sampleUsize] using success,
    challengeSuccess, by simpa [expectedMixOffset] using decodedSuccess⟩

/-- A successful production relation replay carries all eight OOD mixing
checks.  For each released round and each of its two samples, this theorem
retains the exact transcript challenge and the exact proof word which the
same execution accepted as equal to that challenge. -/
theorem accepted_relation_success_has_eight_ood_mix_calls
    (parsed : EntryParsed)
    (transcript returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.replay_real_v5_relation_rounds
          transcript parsed = .ok (.Ok returnedTranscript)) :
    ∀ round : Fin 4, ∀ sample : Fin 2,
      AcceptedOodMixCall parsed round sample := by
  obtain ⟨round0, round1, round2, round3⟩ :=
    AspisV5AcceptedEntrySourceBridge.relation_success_has_four_ood_mix_bodies
      parsed transcript returnedTranscript success
  rcases round0 with
    ⟨q0, nonces0, batch0, roots0, final0, selector0,
      before0, after00, after01, body00, body01⟩
  rcases round1 with
    ⟨q1, nonces1, batch1, roots1, final1, selector1,
      before1, after10, after11, body10, body11⟩
  rcases round2 with
    ⟨q2, nonces2, batch2, roots2, final2, selector2,
      before2, after20, after21, body20, body21⟩
  rcases round3 with
    ⟨q3, nonces3, batch3, roots3, final3, selector3,
      before3, after30, after31, body30, body31⟩
  have call00 := body_0_0_yields_mix parsed q0 nonces0 batch0 roots0 final0
    selector0 before0 after00 body00
  have call01 := body_0_1_yields_mix parsed q0 nonces0 batch0 roots0 final0
    selector0 after00 after01 body01
  have call10 := body_1_0_yields_mix parsed q1 nonces1 batch1 roots1 final1
    selector1 before1 after10 body10
  have call11 := body_1_1_yields_mix parsed q1 nonces1 batch1 roots1 final1
    selector1 after10 after11 body11
  have call20 := body_2_0_yields_mix parsed q2 nonces2 batch2 roots2 final2
    selector2 before2 after20 body20
  have call21 := body_2_1_yields_mix parsed q2 nonces2 batch2 roots2 final2
    selector2 after20 after21 body21
  have call30 := body_3_0_yields_mix parsed q3 nonces3 batch3 roots3 final3
    selector3 before3 after30 body30
  have call31 := body_3_1_yields_mix parsed q3 nonces3 batch3 roots3 final3
    selector3 after30 after31 body31
  intro round sample
  have hround :
      round = 0 ∨ round = 1 ∨ round = 2 ∨ round = 3 := by omega
  have hsample : sample = 0 ∨ sample = 1 := by omega
  rcases hround with rfl | rfl | rfl | rfl <;>
    rcases hsample with rfl | rfl <;> assumption

end AspisV5AcceptedOodMixProjection
