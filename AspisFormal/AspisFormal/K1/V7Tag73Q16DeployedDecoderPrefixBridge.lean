import AspisFormal.K1.V7Tag73IncrementalSamplerControl
import AspisFormal.K1.V7Tag73Q16DigestDrawReindex
import AspisFormal.V5QuerySamplerControl

/-!
# Exact deployed q16 decoder-prefix bridge

This file connects the production block decoder to the ideal sixty-four-draw
q16 experiment.  A completed deployed schedule is read from the consumed
block prefix.  The remaining blocks of the fixed eight-block candidate tape
are retained as nuisance data, and the proof below shows that they cannot
alter the first sixteen distinct draws or the returned ordered schedule.

No candidate success is required beyond the selected decoded prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisV5BoundedQuerySamplerUniformity
open AspisV5QuerySamplerControl

noncomputable section

/-! ## Chronological word/draw coordinates -/

theorem flattenedWords_candidateDigestBlocks_coordinates
    (blocks : CandidateDigestBlocks) :
    flattenedWords (List.ofFn blocks) =
      List.ofFn fun draw : Fin 64 =>
        littleEndianWord
          (blocks ⟨draw.val / 8, by omega⟩)
          ⟨draw.val % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  apply List.ext_getElem
  · simp [flattenedWords_length]
  · intro index leftBound rightBound
    simp only [List.length_ofFn] at rightBound
    simp [flattenedWords, blockWords]

theorem deployedQ16DrawTape_values
    (blocks : CandidateDigestBlocks) :
    List.ofFn (fun draw : Fin 64 =>
        ((deployedQ16DrawTape blocks draw : Fin (2 ^ 18)) : Nat)) =
      (flattenedWords (List.ofFn blocks)).map q16Candidate := by
  rw [flattenedWords_candidateDigestBlocks_coordinates]
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    have indexBound : index < 64 := by simpa using leftBound
    let draw : Fin 64 := ⟨index, indexBound⟩
    have coordinate :
        blockWordIndexEquiv.symm draw =
          (⟨index / 8, by omega⟩, ⟨index % 8, by omega⟩) := by
      apply Prod.ext <;> apply Fin.ext <;>
        simp [blockWordIndexEquiv, draw, finProdFinEquiv]
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [deployedQ16DrawTape_apply]
    rw [coordinate]

/-! ## The bounded scan is the first-occurrence scan -/

theorem scanUniqueUntil_positions_eq_scanUntil
    (needed fuel : Nat) (words seen : List Nat)
    (seenBound : seen.length ≤ needed) :
    (scanUniqueUntil needed fuel words seen).positions =
      scanUntil needed seen ((words.take fuel).map q16Candidate) := by
  induction fuel generalizing words seen with
  | zero => simp [scanUniqueUntil, scanUntil]
  | succ fuel ih =>
      cases words with
      | nil => simp [scanUniqueUntil, scanUntil]
      | cons word rest =>
          by_cases complete : needed ≤ seen.length
          · have exactLength : seen.length = needed :=
              Nat.le_antisymm seenBound complete
            simp [scanUniqueUntil, scanUntil, exactLength]
          · have strict : seen.length < needed :=
              Nat.lt_of_not_ge complete
            have nextBound :
                (keepFirst seen (q16Candidate word)).length ≤ needed := by
              unfold keepFirst
              split
              · exact seenBound
              · simp only [List.length_append, List.length_singleton]
                omega
            simpa [scanUniqueUntil, scanUntil, complete,
              Nat.ne_of_lt strict, keepIfNew, keepFirst] using
              ih rest (keepFirst seen (q16Candidate word)) nextBound

theorem scanQ16_positions_eq_firstUnique_take
    (blocks : List Digest256) :
    (scanQ16 blocks).positions =
      (AspisV5TranscriptConnection.firstUnique
        ((flattenedWords blocks).take 64 |>.map q16Candidate)).take 16 := by
  rw [scanQ16, scanUniqueUntil_positions_eq_scanUntil 16 64 _ [] (by simp)]
  rw [scanUntil_eq_take_firstUnique]

theorem firstUniqueAux_eq_reverse_dedup
    (seen values : List Nat) (seenNodup : seen.Nodup) :
    AspisV5TranscriptConnection.firstUniqueAux seen values =
      (values.reverse ++ seen.reverse).dedup.reverse := by
  induction values generalizing seen with
  | nil =>
      simp [AspisV5TranscriptConnection.firstUniqueAux,
        List.dedup_eq_self.mpr (List.nodup_reverse.mpr seenNodup)]
  | cons value rest ih =>
      simp only [AspisV5TranscriptConnection.firstUniqueAux]
      by_cases present : value ∈ seen
      · rw [if_pos present, ih seen seenNodup]
        simp only [List.reverse_cons, List.singleton_append,
          List.append_assoc, List.dedup_append]
        rw [List.dedup_cons_of_mem (by simpa using present)]
      · rw [if_neg present, ih (seen ++ [value])]
        · simp only [List.reverse_cons, List.singleton_append,
            List.reverse_append, List.reverse_nil, List.nil_append,
            List.append_assoc]
        · simpa using seenNodup.append (by simp) (by simpa)

theorem firstUnique_map_val_eq_firstOccurrences
    {n : Nat} (values : List (Fin n)) :
    AspisV5TranscriptConnection.firstUnique (values.map Fin.val) =
      (firstOccurrences values).map Fin.val := by
  rw [AspisV5TranscriptConnection.firstUnique]
  rw [firstUniqueAux_eq_reverse_dedup [] (values.map Fin.val) (by simp)]
  simp only [firstOccurrences, List.map_reverse, List.reverse_nil,
    List.append_nil]
  rw [← List.map_reverse]
  rw [List.dedup_map_of_injective Fin.val_injective]

theorem scanQ16_full_positions_eq_outputList_values
    (blocks : CandidateDigestBlocks) :
    (scanQ16 (List.ofFn blocks)).positions =
      (outputList 16 (deployedQ16DrawTape blocks)).map Fin.val := by
  rw [scanQ16_positions_eq_firstUnique_take]
  have fullLength : (flattenedWords (List.ofFn blocks)).length = 64 := by
    simp [flattenedWords_length]
  have takeFull :
      (flattenedWords (List.ofFn blocks)).take 64 =
        flattenedWords (List.ofFn blocks) := by
    rw [← fullLength]
    exact List.take_length
  rw [takeFull]
  rw [← deployedQ16DrawTape_values]
  have valuesList :
      List.ofFn (fun draw : Fin 64 =>
          ((deployedQ16DrawTape blocks draw : Fin (2 ^ 18)) : Nat)) =
        (List.ofFn (deployedQ16DrawTape blocks)).map Fin.val := by
    simp
  rw [valuesList]
  rw [firstUnique_map_val_eq_firstOccurrences]
  simp [outputList, List.map_take]

theorem list_ofFn_positionsEmbedding_values
    (positions : List Nat) (lengthExact : positions.length = 16)
    (nodup : positions.Nodup)
    (bounded : ∀ position ∈ positions, position < q16Bound) :
    (List.ofFn (positionsEmbedding positions lengthExact nodup bounded)).map
        Fin.val = positions := by
  change List.ofFn (fun index : Fin 16 =>
    positions.get (Fin.cast lengthExact.symm index)) = positions
  calc
    _ = List.ofFn positions.get :=
      (List.ofFn_congr lengthExact positions.get).symm
    _ = positions := List.ofFn_get positions

theorem decodeCandidateDetailed_schedule_positions
    (counter : Fin 64) (blocks : List Digest256)
    (decoded : CandidateDecode blocks) (schedule : QuerySchedule)
    (run : decodeCandidateDetailed counter blocks = some decoded)
    (outcome : decoded.outcome = .schedule schedule) :
    (List.ofFn schedule.positions).map Fin.val =
      (scanQ16 blocks).positions := by
  unfold decodeCandidateDetailed at run
  split at run
  next blockCap =>
    dsimp only at run
    split at run
    next lengthExact =>
      split at run
      next exactUse =>
        split at run
        next atLeastTwo =>
          cases run
          simp only [CandidateOutcome.schedule.injEq] at outcome
          subst schedule
          exact list_ofFn_positionsEmbedding_values
            (scanQ16 blocks).positions lengthExact
            (scanQ16_positions_nodup blocks)
            (scanQ16_positions_bounded blocks)
        next tooShort => simp at run
      next inexact => simp at run
    next incomplete =>
      split at run
      next abortExact =>
        cases run
        simp at outcome
      next notAbort => simp at run
  next beyondCap => simp at run

theorem decodeCandidateOutcome_schedule_positions
    (counter : Fin 64) (blocks : List Digest256) (schedule : QuerySchedule)
    (run : decodeCandidateOutcome counter blocks = some (.schedule schedule)) :
    (List.ofFn schedule.positions).map Fin.val =
      (scanQ16 blocks).positions := by
  unfold decodeCandidateOutcome at run
  cases detailedRun : decodeCandidateDetailed counter blocks with
  | none => simp [detailedRun] at run
  | some decoded =>
      simp only [detailedRun, Option.map_some, Option.some.injEq] at run
      exact decodeCandidateDetailed_schedule_positions counter blocks decoded
        schedule detailedRun run

theorem list_fin_eq_of_map_val_eq
    {n : Nat} {left right : List (Fin n)}
    (values : left.map Fin.val = right.map Fin.val) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at values
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at values
          have headEq : head = other := Fin.ext values.1
          subst other
          exact congrArg (List.cons head) (ih values.2)

/-! ## Consumed-prefix decoder to the ideal q16 output -/

/-- A production schedule decoded from the consumed block prefix is exactly
the schedule returned by the ideal sixty-four-draw experiment on the complete
eight-block tape.  The proof makes no claim about decoding the unread suffix. -/
theorem decodeCandidateOutcome_schedule_to_q16CandidateOutput
    (counter : Fin 64) (full : CandidateDigestBlocks)
    (blocks : List Digest256) (schedule : QuerySchedule)
    (prefixExact :
      blocks = (List.ofFn full).take schedule.blocksUsed)
    (decoded :
      decodeCandidateOutcome counter blocks = some (.schedule schedule)) :
    q16CandidateOutput (deployedQ16DrawTape full) =
      some schedule.positions := by
  have decodedPositions :=
    decodeCandidateOutcome_schedule_positions counter blocks schedule decoded
  have complete : (scanQ16 blocks).positions.length = 16 := by
    rw [← decodedPositions]
    simp
  let suffix := (List.ofFn full).drop schedule.blocksUsed
  have fullSplit : blocks ++ suffix = List.ofFn full := by
    rw [prefixExact]
    exact List.take_append_drop schedule.blocksUsed (List.ofFn full)
  have scanStable := scanQ16_append_of_complete blocks suffix complete
  have scanExact : scanQ16 (List.ofFn full) = scanQ16 blocks := by
    simpa [fullSplit] using scanStable
  have fullValues := scanQ16_full_positions_eq_outputList_values full
  have outputValues :
      (outputList 16 (deployedQ16DrawTape full)).map Fin.val =
        (List.ofFn schedule.positions).map Fin.val := by
    calc
      _ = (scanQ16 (List.ofFn full)).positions := fullValues.symm
      _ = (scanQ16 blocks).positions := congrArg UniqueScan.positions scanExact
      _ = _ := decodedPositions.symm
  apply (q16CandidateOutput_eq_some_iff_produces
    (deployedQ16DrawTape full) schedule.positions).2
  unfold Produces
  exact list_fin_eq_of_map_val_eq outputValues

theorem decodeCandidateOutcome_schedule_makes_full_tape_successful
    (counter : Fin 64) (full : CandidateDigestBlocks)
    (blocks : List Digest256) (schedule : QuerySchedule)
    (prefixExact :
      blocks = (List.ofFn full).take schedule.blocksUsed)
    (decoded :
      decodeCandidateOutcome counter blocks = some (.schedule schedule)) :
    Successful 16 (deployedQ16DrawTape full) := by
  apply successful_of_produces schedule.positions
  exact (q16CandidateOutput_eq_some_iff_produces
    (deployedQ16DrawTape full) schedule.positions).mp
      (decodeCandidateOutcome_schedule_to_q16CandidateOutput counter full
        blocks schedule prefixExact decoded)

/-- Changing every unread digest block preserves the selected ideal schedule.
Only equality of the literally consumed prefixes is used. -/
theorem decodeCandidateOutcome_unread_suffix_irrelevant
    (counter : Fin 64) (left right : CandidateDigestBlocks)
    (blocks : List Digest256) (schedule : QuerySchedule)
    (leftPrefix : blocks = (List.ofFn left).take schedule.blocksUsed)
    (rightPrefix : blocks = (List.ofFn right).take schedule.blocksUsed)
    (decoded :
      decodeCandidateOutcome counter blocks = some (.schedule schedule)) :
    q16CandidateOutput (deployedQ16DrawTape left) =
      q16CandidateOutput (deployedQ16DrawTape right) := by
  rw [decodeCandidateOutcome_schedule_to_q16CandidateOutput counter left
      blocks schedule leftPrefix decoded,
    decodeCandidateOutcome_schedule_to_q16CandidateOutput counter right
      blocks schedule rightPrefix decoded]

/-- Pointwise agreement with the routed candidate slots determines exactly
the chronological prefix consumed by the decoder. -/
theorem candidate_blocks_eq_full_tape_take_of_every_slot
    (full : CandidateDigestBlocks) (blocks : List Digest256)
    (withinTape : blocks.length ≤ 8)
    (slotExact : ∀ (block : Fin 8)
      (consumed : block.val < blocks.length),
      full block = blocks[block.val]'consumed) :
    blocks = (List.ofFn full).take blocks.length := by
  apply List.ext_getElem
  · simp [withinTape]
  · intro index leftBound rightBound
    have indexBound : index < 8 := Nat.lt_of_lt_of_le leftBound withinTape
    simp only [List.getElem_take, List.getElem_ofFn]
    exact (slotExact ⟨index, indexBound⟩ leftBound).symm

/-- Slot-by-slot causal-router realization is sufficient; callers need not
first package a list-level prefix equality. -/
theorem decodeCandidateOutcome_schedule_to_q16CandidateOutput_of_every_slot
    (counter : Fin 64) (full : CandidateDigestBlocks)
    (blocks : List Digest256) (schedule : QuerySchedule)
    (slotExact : ∀ (block : Fin 8)
      (consumed : block.val < blocks.length),
      full block = blocks[block.val]'consumed)
    (decoded :
      decodeCandidateOutcome counter blocks = some (.schedule schedule)) :
    q16CandidateOutput (deployedQ16DrawTape full) =
      some schedule.positions := by
  have uses := decodeCandidateOutcome_uses_exact_blocks counter blocks
    (.schedule schedule) decoded
  have lengthExact : blocks.length = schedule.blocksUsed := by
    simpa [CandidateUsesExactBlocks] using uses.symm
  have withinTape : blocks.length ≤ 8 := by
    rw [lengthExact]
    exact schedule.withinSixtyFourDraws
  have prefixAtLength := candidate_blocks_eq_full_tape_take_of_every_slot
    full blocks withinTape slotExact
  have prefixExact :
      blocks = (List.ofFn full).take schedule.blocksUsed := by
    rwa [← lengthExact]
  exact decodeCandidateOutcome_schedule_to_q16CandidateOutput counter full
    blocks schedule prefixExact decoded

/-! ## Audit -/

#print axioms flattenedWords_candidateDigestBlocks_coordinates
#print axioms deployedQ16DrawTape_values
#print axioms scanUniqueUntil_positions_eq_scanUntil
#print axioms scanQ16_positions_eq_firstUnique_take
#print axioms firstUniqueAux_eq_reverse_dedup
#print axioms firstUnique_map_val_eq_firstOccurrences
#print axioms scanQ16_full_positions_eq_outputList_values
#print axioms list_ofFn_positionsEmbedding_values
#print axioms decodeCandidateOutcome_schedule_positions
#print axioms list_fin_eq_of_map_val_eq
#print axioms decodeCandidateOutcome_schedule_to_q16CandidateOutput
#print axioms decodeCandidateOutcome_schedule_makes_full_tape_successful
#print axioms decodeCandidateOutcome_unread_suffix_irrelevant
#print axioms candidate_blocks_eq_full_tape_take_of_every_slot
#print axioms decodeCandidateOutcome_schedule_to_q16CandidateOutput_of_every_slot

end

end AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge
