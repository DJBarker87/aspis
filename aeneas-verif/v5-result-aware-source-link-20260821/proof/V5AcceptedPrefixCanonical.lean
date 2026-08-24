import V5AcceptedPreparedClaimsCanonical
import V5AcceptedPrefixWorkBridge

/-!
# Canonical prefix challenges and inactive claim

This file proves the representation bounds needed by the accepted relation
caller directly from the translated prefix sampler and decoder.  In
particular, neither the transcript challenge nor the inactive claim is
introduced as a separately chosen canonical value.
-/

namespace AspisV5AcceptedPrefixCanonical

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedPreparedClaimsCanonical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev EntryTranscript :=
  V5AcceptedEntryGenerated.aspis_core.transcript.Transcript

/-- A successful prefix decoder obtained its result from the checked
16-byte field decoder. -/
theorem decode_prefix_qm31_success_from_le_bytes
    (bytes : Slice Std.U8) (offset : Std.Usize) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_prefix_qm31 bytes offset =
        .ok (.Ok value)) :
    ∃ selected : Slice Std.U8,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes selected =
        .ok (some value) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.decode_prefix_qm31 at success
  generalize hadd :
      offset + V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES = endResult
    at success
  cases endResult with
  | fail error => simp [hadd] at success
  | div => simp [hadd] at success
  | ok finish =>
      simp only [hadd, bind_tc_ok] at success
      generalize hslice :
          core.slice.Slice.get
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
            bytes { start := offset, «end» := finish } = sliceResult
        at success
      cases sliceResult with
      | fail error => simp [hslice] at success
      | div => simp [hslice] at success
      | ok selectedOption =>
          cases selectedOption with
          | none =>
              simp [hslice,
                V5AcceptedEntryGenerated.core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
          | some selected =>
              simp only [hslice,
                V5AcceptedEntryGenerated.core.option.Option.ok_or,
                bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
                at success
              generalize hdecode :
                  V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
                    selected = decodeResult at success
              cases decodeResult with
              | fail error => simp [hdecode] at success
              | div => simp [hdecode] at success
              | ok decodedOption =>
                  cases decodedOption with
                  | none =>
                      simp [hdecode,
                        V5AcceptedEntryGenerated.core.option.Option.ok_or]
                        at success
                  | some decoded =>
                      simp only [hdecode, bind_tc_ok,
                        V5AcceptedEntryGenerated.core.option.Option.ok_or]
                        at success
                      have hvalue : decoded = value :=
                        core.result.Result.Ok.inj (Result.ok.inj success)
                      subst value
                      exact ⟨selected, hdecode⟩

theorem decode_prefix_qm31_success_canonical
    (bytes : Slice Std.U8) (offset : Std.Usize) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_prefix_qm31 bytes offset =
        .ok (.Ok value)) :
    EntryCanonicalQM31 value := by
  obtain ⟨selected, decoded⟩ :=
    decode_prefix_qm31_success_from_le_bytes bytes offset value success
  exact decoder_success_entry_canonical selected value decoded

private def CanonicalSampleResult
    (result : core.result.Result
      (V5AcceptedEntryGenerated.aspis_core.field.M31 ×
        Array Std.U8 32#usize × Nat)
      V5AcceptedEntryGenerated.aspis_core.transcript.ChallengeSampleExhausted) :
    Prop :=
  match result with
  | .Ok (value, _, _) => value.val < 2147483647
  | .Err _ => True

/-- Every successful limb returned by the translated transcript rejection
sampler lies below the Mersenne-prime modulus. -/
theorem sampleLimbAux_success_canonical
    (retries : Nat) (transcript : EntryTranscript)
    (block : Array Std.U8 32#usize) (wordIndex : Nat)
    (value : V5AcceptedEntryGenerated.aspis_core.field.M31)
    (returnedBlock : Array Std.U8 32#usize) (returnedIndex : Nat)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux retries
          transcript block wordIndex =
        .ok (.Ok (value, returnedBlock, returnedIndex), returnedTranscript)) :
    value.val < 2147483647 := by
  induction retries generalizing transcript block wordIndex value
      returnedBlock returnedIndex returnedTranscript with
  | zero =>
      simp [V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux]
        at success
  | succ retries inductionHypothesis =>
      unfold V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux
        at success
      by_cases exhausted : wordIndex = 8
      · simp only [exhausted, if_true] at success
        generalize hsqueeze :
            V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
              transcript = squeezeResult at success
        cases squeezeResult with
        | fail error => simp [hsqueeze] at success
        | div => simp [hsqueeze] at success
        | ok squeezed =>
            rcases squeezed with ⟨nextBlock, nextTranscript⟩
            simp only [hsqueeze, bind_tc_ok] at success
            let word :=
              V5AcceptedEntryGenerated.aspis_core.transcript.word32
                (nextBlock.val.drop (4 * 0))
            let masked := word &&& 2147483647#u32
            simp only [Aeneas.Std.lift, bind_tc_ok] at success
            by_cases accepted : masked != 2147483647#u32
            · have acceptedActual :
                  (V5AcceptedEntryGenerated.aspis_core.transcript.word32
                      (nextBlock.val.drop (4 * 0)) &&& 2147483647#u32 !=
                    2147483647#u32) = true := by
                simpa [word, masked] using accepted
              rw [if_pos acceptedActual] at success
              have tripleEquality :
                  (masked, nextBlock, 0 + 1) =
                    (value, returnedBlock, returnedIndex) :=
                core.result.Result.Ok.inj
                  (congrArg Prod.fst (Result.ok.inj success))
              have valueEquality : value = masked := by
                exact (congrArg Prod.fst tripleEquality).symm
              subst value
              have bounded : masked.val ≤ 2147483647 := by
                change word.val &&& 2147483647 ≤ 2147483647
                exact Nat.and_le_right
              have distinct : masked.val ≠ 2147483647 := by
                intro equality
                have scalarEquality : masked = 2147483647#u32 :=
                  UScalar.eq_of_val_eq equality
                have scalarDistinct : masked ≠ 2147483647#u32 := by
                  simpa using accepted
                exact scalarDistinct scalarEquality
              exact Nat.lt_of_le_of_ne bounded distinct
            · have rejectedActual :
                  ¬ ((V5AcceptedEntryGenerated.aspis_core.transcript.word32
                      (nextBlock.val.drop (4 * 0)) &&& 2147483647#u32 !=
                    2147483647#u32) = true) := by
                simpa [word, masked] using accepted
              rw [if_neg rejectedActual] at success
              exact inductionHypothesis nextTranscript nextBlock 1 value
                returnedBlock returnedIndex returnedTranscript (by
                  simpa using success)
      · simp only [exhausted, if_false, bind_tc_ok] at success
        let word :=
          V5AcceptedEntryGenerated.aspis_core.transcript.word32
            (block.val.drop (4 * wordIndex))
        let masked := word &&& 2147483647#u32
        simp only [Aeneas.Std.lift, bind_tc_ok] at success
        by_cases accepted : masked != 2147483647#u32
        · have acceptedActual :
              (V5AcceptedEntryGenerated.aspis_core.transcript.word32
                  (block.val.drop (4 * wordIndex)) &&& 2147483647#u32 !=
                2147483647#u32) = true := by
            simpa [word, masked] using accepted
          rw [if_pos acceptedActual] at success
          have tripleEquality :
              (masked, block, wordIndex + 1) =
                (value, returnedBlock, returnedIndex) :=
            core.result.Result.Ok.inj
              (congrArg Prod.fst (Result.ok.inj success))
          have valueEquality : value = masked := by
            exact (congrArg Prod.fst tripleEquality).symm
          subst value
          have bounded : masked.val ≤ 2147483647 := by
            change word.val &&& 2147483647 ≤ 2147483647
            exact Nat.and_le_right
          have distinct : masked.val ≠ 2147483647 := by
            intro equality
            have scalarEquality : masked = 2147483647#u32 :=
              UScalar.eq_of_val_eq equality
            have scalarDistinct : masked ≠ 2147483647#u32 := by
              simpa using accepted
            exact scalarDistinct scalarEquality
          exact Nat.lt_of_le_of_ne bounded distinct
        · have rejectedActual :
              ¬ ((V5AcceptedEntryGenerated.aspis_core.transcript.word32
                  (block.val.drop (4 * wordIndex)) &&& 2147483647#u32 !=
                2147483647#u32) = true) := by
            simpa [word, masked] using accepted
          rw [if_neg rejectedActual] at success
          exact inductionHypothesis transcript block (wordIndex + 1) value
            returnedBlock returnedIndex returnedTranscript success

/-- Four successful limb draws make the translated transcript challenge a
canonical four-limb field value. -/
theorem challenge_qm31_success_canonical
    (transcript returnedTranscript : EntryTranscript) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
          transcript = .ok (.Ok value, returnedTranscript)) :
    EntryCanonicalQM31 value := by
  unfold
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
    at success
  generalize hsqueeze :
      V5TranscriptPrimitivesGenerated.aspis_core.transcript.Transcript.squeeze_block
        transcript = squeezeResult at success
  cases squeezeResult with
  | fail error => simp [hsqueeze] at success
  | div => simp [hsqueeze] at success
  | ok squeezed =>
      rcases squeezed with ⟨block0, transcript0⟩
      simp only [hsqueeze, bind_tc_ok] at success
      generalize h0 :
          V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux 8
            transcript0 block0 0 = result0 at success
      cases result0 with
      | fail error => simp [h0] at success
      | div => simp [h0] at success
      | ok pair0 =>
          rcases pair0 with ⟨sample0, transcript1⟩
          cases sample0 with
          | Err error => simp [h0] at success
          | Ok triple0 =>
              rcases triple0 with ⟨limb0, block1, wordIndex1⟩
              simp only [h0, bind_tc_ok] at success
              generalize h1 :
                  V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux 8
                    transcript1 block1 wordIndex1 = result1 at success
              cases result1 with
              | fail error => simp [h1] at success
              | div => simp [h1] at success
              | ok pair1 =>
                  rcases pair1 with ⟨sample1, transcript2⟩
                  cases sample1 with
                  | Err error => simp [h1] at success
                  | Ok triple1 =>
                      rcases triple1 with ⟨limb1, block2, wordIndex2⟩
                      simp only [h1, bind_tc_ok] at success
                      generalize h2 :
                          V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux 8
                            transcript2 block2 wordIndex2 = result2 at success
                      cases result2 with
                      | fail error => simp [h2] at success
                      | div => simp [h2] at success
                      | ok pair2 =>
                          rcases pair2 with ⟨sample2, transcript3⟩
                          cases sample2 with
                          | Err error => simp [h2] at success
                          | Ok triple2 =>
                              rcases triple2 with
                                ⟨limb2, block3, wordIndex3⟩
                              simp only [h2, bind_tc_ok] at success
                              generalize h3 :
                                  V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux 8
                                    transcript3 block3 wordIndex3 = result3
                                at success
                              cases result3 with
                              | fail error => simp [h3] at success
                              | div => simp [h3] at success
                              | ok pair3 =>
                                  rcases pair3 with ⟨sample3, transcript4⟩
                                  cases sample3 with
                                  | Err error => simp [h3] at success
                                  | Ok triple3 =>
                                      rcases triple3 with
                                        ⟨limb3, block4, wordIndex4⟩
                                      have canonical0 :=
                                        sampleLimbAux_success_canonical 8
                                          transcript0 block0 0 limb0 block1
                                          wordIndex1 transcript1 h0
                                      have canonical1 :=
                                        sampleLimbAux_success_canonical 8
                                          transcript1 block1 wordIndex1 limb1
                                          block2 wordIndex2 transcript2 h1
                                      have canonical2 :=
                                        sampleLimbAux_success_canonical 8
                                          transcript2 block2 wordIndex2 limb2
                                          block3 wordIndex3 transcript3 h2
                                      have canonical3 :=
                                        sampleLimbAux_success_canonical 8
                                          transcript3 block3 wordIndex3 limb3
                                          block4 wordIndex4 transcript4 h3
                                      simp only [h3, bind_tc_ok,
                                        Result.ok.injEq, Prod.mk.injEq,
                                        core.result.Result.Ok.injEq] at success
                                      rcases success with ⟨rfl, rfl⟩
                                      exact ⟨canonical0, canonical1,
                                        canonical2, canonical3⟩

private theorem challengeNonzeroAux_success_canonical
    (retries : Nat) (transcript returnedTranscript : EntryTranscript)
    (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.transcript.challengeNonzeroAux
          retries transcript = .ok (.Ok value, returnedTranscript)) :
    EntryCanonicalQM31 value := by
  induction retries generalizing transcript returnedTranscript value with
  | zero =>
      simp [V5AcceptedEntryGenerated.aspis_core.transcript.challengeNonzeroAux]
        at success
  | succ retries inductionHypothesis =>
      unfold V5AcceptedEntryGenerated.aspis_core.transcript.challengeNonzeroAux
        at success
      generalize hchallenge :
          V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
            transcript = challengeResult at success
      cases challengeResult with
      | fail error => simp [hchallenge] at success
      | div => simp [hchallenge] at success
      | ok pair =>
          rcases pair with ⟨sample, nextTranscript⟩
          cases sample with
          | Err error => simp [hchallenge] at success
          | Ok sampled =>
              simp only [hchallenge, bind_tc_ok] at success
              generalize hzero :
                  V5AcceptedEntryGenerated.aspis_core.field.QM31.is_zero
                    sampled = zeroResult at success
              cases zeroResult with
              | fail error => simp [hzero] at success
              | div => simp [hzero] at success
              | ok isZero =>
                  cases isZero with
                  | false =>
                      have equalOuter := Result.ok.inj success
                      have equalInner := core.result.Result.Ok.inj
                        (congrArg Prod.fst equalOuter)
                      have valueEquality : sampled = value := equalInner
                      have transcriptEquality :
                          nextTranscript = returnedTranscript :=
                        congrArg Prod.snd equalOuter
                      subst value
                      subst returnedTranscript
                      exact challenge_qm31_success_canonical transcript
                        nextTranscript sampled hchallenge
                  | true =>
                      exact inductionHypothesis nextTranscript
                        returnedTranscript value success

theorem challenge_nonzero_qm31_success_canonical
    (transcript returnedTranscript : EntryTranscript) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31
          transcript = .ok (.Ok value, returnedTranscript)) :
    EntryCanonicalQM31 value := by
  exact challengeNonzeroAux_success_canonical 3 transcript
    returnedTranscript value success

/-- The gamma and kappa challenges and inactive claim used by one accepted
prefix are canonical because that same execution sampled and decoded them. -/
theorem accepted_prefix_gamma_and_inactive_canonical
    (parsed : EntryParsed) (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize) (hash : PrefixHash)
    (verified : EntryVerifiedPrefix) (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    EntryCanonicalQM31 verified.gamma ∧
      EntryCanonicalQM31 verified.inactive_claim ∧
      EntryCanonicalQM31 verified.kappa := by
  obtain ⟨_, afterBatch, afterGamma, inactiveOffset, beforeKappa, afterKappa,
      _, gammaSuccess, inactiveSuccess, kappaSuccess⟩ :=
    accepted_prefix_has_batch_gamma_and_inactive_decode parsed liveStatement
      statementDigest hash verified returnedTranscript success
  exact ⟨
    challenge_nonzero_qm31_success_canonical afterBatch afterGamma
      verified.gamma gammaSuccess,
    decode_prefix_qm31_success_canonical parsed.v5_wire_prefix inactiveOffset
      verified.inactive_claim inactiveSuccess,
    challenge_nonzero_qm31_success_canonical beforeKappa afterKappa
      verified.kappa kappaSuccess⟩

#print axioms decode_prefix_qm31_success_canonical
#print axioms challenge_qm31_success_canonical
#print axioms challenge_nonzero_qm31_success_canonical
#print axioms accepted_prefix_gamma_and_inactive_canonical

end AspisV5AcceptedPrefixCanonical
