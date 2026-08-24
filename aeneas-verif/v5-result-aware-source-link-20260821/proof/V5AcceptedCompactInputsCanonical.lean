import V5AcceptedPrefixCanonical
import V5RelationPrepareCanonicalProof

/-!
# Canonical compact-state inputs from one accepted execution

The compact component-B constructor consumes the ten coordinates returned by
the streaming semantic sumcheck and the dense scale returned by relation
preparation.  This file derives canonical raw-field representations for both
values from the successful generated calls that produced them.
-/

namespace AspisV5AcceptedCompactInputsCanonical

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedPreparedClaimsCanonical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev EntryTranscript :=
  V5AcceptedEntryGenerated.aspis_core.transcript.Transcript

@[simp] private theorem prefixWord32_eq_word32 (bytes : List Std.U8) :
    V5AcceptedEntryGenerated.aspis_core.transcript.prefixWord32 bytes =
      V5AcceptedEntryGenerated.aspis_core.transcript.word32 bytes := by
  unfold V5AcceptedEntryGenerated.aspis_core.transcript.prefixWord32
    V5AcceptedEntryGenerated.aspis_core.transcript.word32
    V5AcceptedEntryGenerated.aspis_core.transcript.prefixU32
    V5AcceptedEntryGenerated.aspis_core.transcript.u32
  rfl

private theorem prefixSampleLimbAux_eq_sampleLimbAux
    (retries : Nat) (transcript : EntryTranscript)
    (block : Array Std.U8 32#usize) (wordIndex : Nat) :
    V5AcceptedEntryGenerated.aspis_core.transcript.prefixSampleLimbAux
        retries transcript block wordIndex =
      V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux
        retries transcript block wordIndex := by
  induction retries generalizing transcript block wordIndex with
  | zero => rfl
  | succ retries inductionHypothesis =>
      simp only [
        V5AcceptedEntryGenerated.aspis_core.transcript.prefixSampleLimbAux,
        V5AcceptedEntryGenerated.aspis_core.transcript.sampleLimbAux,
        prefixWord32_eq_word32, inductionHypothesis]

theorem prefixChallengeQm31_eq_challenge_qm31
    (transcript : EntryTranscript) :
    V5AcceptedEntryGenerated.aspis_core.transcript.prefixChallengeQm31
        transcript =
      V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31
        transcript := by
  simp only [
    V5AcceptedEntryGenerated.aspis_core.transcript.prefixChallengeQm31,
    V5AcceptedEntryGenerated.aspis_core.transcript.Transcript.challenge_qm31,
    prefixSampleLimbAux_eq_sampleLimbAux]

theorem prefixChallengeQm31_success_canonical
    (transcript returnedTranscript : EntryTranscript) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.transcript.prefixChallengeQm31
          transcript = .ok (.Ok value, returnedTranscript)) :
    EntryCanonicalQM31 value := by
  rw [prefixChallengeQm31_eq_challenge_qm31] at success
  exact AspisV5AcceptedPrefixCanonical.challenge_qm31_success_canonical
    transcript returnedTranscript value success

private theorem canonical_array_update
    (point output : Array EntryQM31 10#usize)
    (index : Std.Usize) (value : EntryQM31)
    (pointCanonical : EntryCanonicalArray point)
    (valueCanonical : EntryCanonicalQM31 value)
    (run : Array.update point index value = .ok output) :
    EntryCanonicalArray output := by
  have indexBound : index.val < point.length := by
    by_contra outOfBounds
    have listOutOfBounds : ¬ index.val < point.val.length := by
      simpa [Array.length_eq] using outOfBounds
    have missing : point.val[index.val]? = none := by
      exact List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt listOutOfBounds)
    unfold Array.update at run
    rw [Array.getElem?_Usize_eq] at run
    rw [missing] at run
    simp at run
  obtain ⟨expected, expectedRun, expectedExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec point index value indexBound)
  have outputExact : output = expected := by
    exact Result.ok.inj (run.symm.trans expectedRun)
  subst output
  rw [expectedExact]
  intro coordinate
  have indexListBound : index.val < point.val.length := by
    simpa [Array.length_eq] using indexBound
  by_cases same : coordinate.val = index.val
  · rw [Array.set_val_eq,
      List.set_getElem!_eq point.val index.val coordinate.val value
        ⟨by simpa [Array.length_eq] using coordinate.isLt, same.symm⟩]
    exact valueCanonical
  · rw [Array.set_val_eq,
      List.set_getElem!_ne point.val index.val coordinate.val value
        (Or.inl (Ne.symm same))]
    exact pointCanonical coordinate

/-- The semantic-round helper obtains its returned challenge from the same
bounded rejection sampler proved canonical above. -/
theorem absorb_state_only_sumcheck_round_success_canonical
    (transcript returnedTranscript : EntryTranscript)
    (round : Std.Usize) (encoded : Array Std.U8 448#usize)
    (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.absorb_state_only_sumcheck_round
          transcript round encoded = .ok (.Ok value, returnedTranscript)) :
    EntryCanonicalQM31 value := by
  unfold
    V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.absorb_state_only_sumcheck_round
    at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨payloadPair, _, success⟩ := success
  rcases payloadPair with ⟨payload, writeBack⟩
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨payloadOut, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨_, _, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨sampleTranscript, _, sampleSuccess⟩ := success
  exact prefixChallengeQm31_success_canonical sampleTranscript
    returnedTranscript value sampleSuccess

/-- Successful completion of the generated streaming loop preserves the
canonical representation of every coordinate in its point array. -/
private theorem verifyStreamingLoop_success_point_canonical
    (chunks : List (Slice Std.U8)) (remainder : Slice Std.U8)
    (count : Std.Usize) (transcript returnedTranscript : EntryTranscript)
    (point : Array EntryQM31 10#usize) (runningClaim : EntryQM31)
    (verification :
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.StateOnlySumcheckVerification)
    (pointCanonical : EntryCanonicalArray point)
    (run :
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verifyStreamingLoop
          { iter := { chunks := chunks, remainder := remainder }, count := count }
          transcript point runningClaim =
        .ok (.Ok verification, returnedTranscript)) :
    EntryCanonicalArray verification.point := by
  induction chunks generalizing count transcript point runningClaim with
  | nil =>
      unfold
        V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verifyStreamingLoop
        at run
      rw [Aeneas.Std.loop.eq_def] at run
      simp [
        V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verifyStreamingLoopBody,
        core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next] at run
      rcases run with ⟨rfl, _⟩
      exact pointCanonical
  | cons encoded tail inductionHypothesis =>
      unfold
        V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verifyStreamingLoop
        at run
      rw [Aeneas.Std.loop.eq_def] at run
      unfold
        V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verifyStreamingLoopBody
        at run
      simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next, bind_tc_ok] at run
      generalize countAdd : count + 1#usize = countResult at run
      cases countResult with
      | fail error => simp [countAdd] at run
      | div => simp [countAdd] at run
      | ok nextCount =>
        simp only [countAdd, bind_tc_ok] at run
        generalize decodeRun :
            V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.decode_state_only_polynomial
              count encoded = decodeResult at run
        cases decodeResult with
        | fail error => simp [decodeRun] at run
        | div => simp [decodeRun] at run
        | ok decoded =>
          cases decoded with
          | Err error => simp [decodeRun] at run
          | Ok polynomial =>
            simp only [decodeRun, bind_tc_ok] at run
            generalize boundaryRun :
                V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
                  polynomial = boundaryResult at run
            cases boundaryResult with
            | fail error => simp [boundaryRun] at run
            | div => simp [boundaryRun] at run
            | ok boundary =>
              simp only [boundaryRun, bind_tc_ok] at run
              generalize equalRun :
                  V5AcceptedEntryGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
                    boundary runningClaim = equalResult at run
              cases equalResult with
              | fail error => simp [equalRun] at run
              | div => simp [equalRun] at run
              | ok equal =>
                simp only [equalRun, bind_tc_ok] at run
                cases equal with
                | false => simp at run
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false] at run
                  generalize convertedRun :
                      core.array.TryFromSharedArraySlice.try_from 448#usize encoded =
                        convertedResult at run
                  cases convertedResult with
                  | fail error => simp [convertedRun] at run
                  | div => simp [convertedRun] at run
                  | ok converted =>
                    simp only [convertedRun, bind_tc_ok] at run
                    generalize expectRun :
                        core.result.Result.expect
                          core.fmt.DebugTryFromSliceError
                          converted (toStr "" (by decide)) = expectResult at run
                    cases expectResult with
                    | fail error => simp [expectRun] at run
                    | div => simp [expectRun] at run
                    | ok encodedArray =>
                      simp only [expectRun, bind_tc_ok] at run
                      generalize challengeRun :
                          V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.absorb_state_only_sumcheck_round
                            transcript count encodedArray = challengePairResult at run
                      cases challengePairResult with
                      | fail error => simp [challengeRun] at run
                      | div => simp [challengeRun] at run
                      | ok challengePair =>
                        rcases challengePair with ⟨challengeResult, nextTranscript⟩
                        cases challengeResult with
                        | Err error => simp [challengeRun] at run
                        | Ok challenge =>
                          simp only [challengeRun, bind_tc_ok] at run
                          have challengeCanonical :=
                            absorb_state_only_sumcheck_round_success_canonical
                              transcript nextTranscript count encodedArray challenge
                              challengeRun
                          generalize claimRun :
                              V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
                                polynomial challenge = claimResult at run
                          cases claimResult with
                          | fail error => simp [claimRun] at run
                          | div => simp [claimRun] at run
                          | ok nextClaim =>
                            simp only [claimRun, bind_tc_ok] at run
                            generalize pointRun :
                                Array.update point count challenge = pointResult at run
                            cases pointResult with
                            | fail error => simp [pointRun] at run
                            | div => simp [pointRun] at run
                            | ok nextPoint =>
                              simp only [pointRun, bind_tc_ok] at run
                              have nextPointCanonical := canonical_array_update
                                point nextPoint count challenge pointCanonical
                                challengeCanonical pointRun
                              exact inductionHypothesis nextCount nextTranscript nextPoint
                                nextClaim nextPointCanonical run

/-- A successful generated semantic-sumcheck verification returns ten
canonical field coordinates.  The point starts at the generated field zero
and every later coordinate is written only with a successful transcript
sample covered by the loop theorem above. -/
theorem verify_state_only_sumcheck_streaming_success_point_canonical
    (transcript returnedTranscript : EntryTranscript) (proof : Slice Std.U8)
    (initialClaim : EntryQM31)
    (verification :
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.StateOnlySumcheckVerification)
    (run :
      V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming
          transcript proof initialClaim =
        .ok (.Ok verification, returnedTranscript)) :
    EntryCanonicalArray verification.point := by
  unfold
    V5AcceptedEntryGenerated.aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming
    at run
  generalize lengthCheck : (Slice.len proof != 4480#usize) = badLength at run
  cases badLength with
  | true => simp [lengthCheck] at run
  | false =>
      simp only [lengthCheck, if_false] at run
      generalize zeroRun :
          V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult at run
      cases zeroResult with
      | fail error => simp [zeroRun] at run
      | div => simp [zeroRun] at run
      | ok zero =>
        simp only [zeroRun, bind_tc_ok] at run
        have zeroCanonical := entry_qm31_zero_success_canonical zero zeroRun
        have pointCanonical :
            EntryCanonicalArray (Array.repeat 10#usize zero) :=
          entryCanonicalArray_repeat 10#usize zero zeroCanonical
        generalize chunksRun :
            core.slice.Slice.chunks_exact proof 448#usize = chunksResult at run
        cases chunksResult with
        | fail error => simp [chunksRun] at run
        | div => simp [chunksRun] at run
        | ok chunks =>
          simp only [chunksRun, bind_tc_ok] at run
          generalize iterRun :
              core.iter.traits.iterator.Iterator.enumerate.trait_default
                (core.iter.traits.iterator.IteratorChunksExact Std.U8) chunks =
                  iterResult at run
          cases iterResult with
          | fail error => simp [iterRun] at run
          | div => simp [iterRun] at run
          | ok iter =>
            simp only [iterRun, bind_tc_ok] at run
            rcases chunks with ⟨chunksList, remainder⟩
            rcases iter with ⟨iterChunks, count⟩
            exact verifyStreamingLoop_success_point_canonical
              iterChunks.chunks iterChunks.remainder count transcript
              returnedTranscript (Array.repeat 10#usize zero) initialClaim
              verification pointCanonical run

/-- The ten coordinates stored in the accepted outer-prefix result are the
point returned by the successful streaming helper above, so their canonical
representation is a consequence of the accepted call itself. -/
theorem accepted_prefix_round_challenges_canonical
    (parsed : EntryParsed) (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (hash : PrefixHash) (verified : EntryVerifiedPrefix)
    (returnedTranscript : EntryTranscript)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_wire_prefix
          parsed liveStatement statementDigest hash =
        .ok (.Ok (verified, returnedTranscript))) :
    EntryCanonicalArray verified.round_challenges := by
  obtain ⟨beforeSemantic, afterSemantic, semanticProof, initialClaim,
      semanticVerification, _, _, _, _, _, _, semanticSuccess,
      verifiedPoint, _, _, _, _⟩ :=
    accepted_prefix_has_batch_gamma_and_inactive_decode parsed liveStatement
      statementDigest hash verified returnedTranscript success
  rw [verifiedPoint]
  exact verify_state_only_sumcheck_streaming_success_point_canonical
    beforeSemantic afterSemantic semanticProof initialClaim
    semanticVerification semanticSuccess

#print axioms prefixChallengeQm31_eq_challenge_qm31
#print axioms prefixChallengeQm31_success_canonical
#print axioms absorb_state_only_sumcheck_round_success_canonical
#print axioms verifyStreamingLoop_success_point_canonical
#print axioms verify_state_only_sumcheck_streaming_success_point_canonical
#print axioms accepted_prefix_round_challenges_canonical

end AspisV5AcceptedCompactInputsCanonical
