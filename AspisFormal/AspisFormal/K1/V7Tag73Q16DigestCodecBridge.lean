import AspisFormal.K1.V7Tag73Q16DigestDrawReindex
import AspisFormal.K1.V7Tag73Q16OperationalCodecBridge

/-!
# Deployed q16 digest blocks realize the ideal draw tape

The finite q16 probability theorem is indexed by sixty-four low-18 draws.
The production decoder instead traverses eight SHA-256 digests as eight
little-endian words per digest.  This module proves those two traversals have
the same row-major order and then reuses the operational codec theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16DigestCodecBridge

open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16OperationalCodecBridge
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5BoundedQuerySamplerUniformity

noncomputable section

theorem flattenedWords_ofFn_eq_idealDrawWords
    (blocks : CandidateDigestBlocks) :
    (flattenedWords (List.ofFn blocks)).map q16Candidate =
      idealDrawWords (deployedQ16DrawTape blocks) := by
  simp [flattenedWords, blockWords, idealDrawWords,
    blockWordIndexEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem deployed_digest_scan_eq_ideal_outputList
    (blocks : CandidateDigestBlocks) :
    (scanUniqueUntil 16 64
      (flattenedWords (List.ofFn blocks)) []).positions =
        (outputList 16 (deployedQ16DrawTape blocks)).map Fin.val := by
  rw [scanUniqueUntil_positions_eq_scanUntil 16 64
    (flattenedWords (List.ofFn blocks)) []
    (by simp [flattenedWords_length]) (by simp)]
  rw [flattenedWords_ofFn_eq_idealDrawWords]
  have ideal := ideal_scan_positions_eq_outputList_values
    (deployedQ16DrawTape blocks)
  rw [scanUniqueUntil_positions_eq_scanUntil 16 64
    (idealDrawWords (deployedQ16DrawTape blocks)) []
    (by simp [idealDrawWords]) (by simp)] at ideal
  rw [idealDrawWords_map_q16Candidate] at ideal
  exact ideal

theorem positionsEmbedding_ofFn_values
    (positions : List Nat) (lengthExact : positions.length = 16)
    (nodup : positions.Nodup)
    (bounded : ∀ position ∈ positions, position < q16Bound) :
    (List.ofFn
      (positionsEmbedding positions lengthExact nodup bounded)).map Fin.val =
        positions := by
  rw [← List.ofFn_comp']
  change
    List.ofFn (fun index : Fin 16 =>
      positions.get (Fin.cast lengthExact.symm index)) = positions
  rw [← List.ofFn_congr lengthExact positions.get]
  exact List.ofFn_get positions

theorem decoded_schedule_positions_are_scan_positions
    (counter : Fin 64) (blocks : List Digest256) (schedule : QuerySchedule)
    (run : decodeCandidateOutcome counter blocks =
      some (.schedule schedule)) :
    (List.ofFn schedule.positions).map Fin.val =
      (scanQ16 blocks).positions := by
  unfold decodeCandidateOutcome at run
  cases detailedEq : decodeCandidateDetailed counter blocks with
  | none => simp [detailedEq] at run
  | some decoded =>
      simp only [detailedEq, Option.map_some, Option.some.injEq] at run
      unfold decodeCandidateDetailed at detailedEq
      split at detailedEq
      next blockCap =>
        dsimp only at detailedEq
        split at detailedEq
        next lengthExact =>
          split at detailedEq
          next exactUse =>
            split at detailedEq
            next atLeastTwo =>
              simp only [Option.some.injEq] at detailedEq
              subst decoded
              injection run with scheduleEq
              subst schedule
              exact positionsEmbedding_ofFn_values
                (scanQ16 blocks).positions lengthExact
                (scanQ16_positions_nodup blocks)
                (scanQ16_positions_bounded blocks)
            next tooShort => simp at detailedEq
          next inexact => simp at detailedEq
        next incomplete =>
          split at detailedEq
          next abortExact =>
            simp only [Option.some.injEq] at detailedEq
            subst decoded
            simp at run
          next notAbort => simp at detailedEq
      next beyondCap => simp at detailedEq

/-- A production decoder may stop after the first exact block prefix that
contains sixteen distinct positions.  Extending that prefix to the candidate's
full eight-block digest table leaves the completed scan unchanged, so the
returned schedule is exactly the ideal sixty-four-draw output. -/
theorem decoded_extension_realizes_ideal_output
    (counter : Fin 64) (blocks suffix : List Digest256)
    (full : CandidateDigestBlocks) (schedule : QuerySchedule)
    (fullEq : blocks ++ suffix = List.ofFn full)
    (run : decodeCandidateOutcome counter blocks =
      some (.schedule schedule)) :
    q16CandidateOutput (deployedQ16DrawTape full) =
      some schedule.positions := by
  have decodedValues := decoded_schedule_positions_are_scan_positions
    counter blocks schedule run
  have complete : (scanQ16 blocks).positions.length = 16 := by
    rw [← decodedValues]
    simp
  have stable := scanQ16_append_of_complete blocks suffix complete
  have fullScan : scanQ16 (List.ofFn full) = scanQ16 blocks := by
    rw [← fullEq]
    exact stable
  apply (q16CandidateOutput_eq_some_iff_produces
    (deployedQ16DrawTape full) schedule.positions).2
  unfold Produces
  apply (List.map_inj_right Fin.val_injective).mp
  calc
    (outputList 16 (deployedQ16DrawTape full)).map Fin.val =
        (scanQ16 (List.ofFn full)).positions :=
      (deployed_digest_scan_eq_ideal_outputList full).symm
    _ = (scanQ16 blocks).positions := congrArg UniqueScan.positions fullScan
    _ = (List.ofFn schedule.positions).map Fin.val := decodedValues.symm

end

#print axioms flattenedWords_ofFn_eq_idealDrawWords
#print axioms deployed_digest_scan_eq_ideal_outputList
#print axioms positionsEmbedding_ofFn_values
#print axioms decoded_schedule_positions_are_scan_positions
#print axioms decoded_extension_realizes_ideal_output

end AspisK1.V7Tag73Q16DigestCodecBridge
