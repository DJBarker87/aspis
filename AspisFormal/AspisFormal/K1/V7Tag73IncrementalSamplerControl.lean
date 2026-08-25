import AspisFormal.K1.V7Tag73SamplerDecoder

/-!
# Prefix-minimal incremental control for the exact Tag-73 samplers

The deployed verifier requests one paired duplex squeeze at a time and stops
the current sampler at its first exact successful block list.  This file
proves that this streaming control is justified by the concrete decoders,
rather than adding prefix minimality as an interface premise.

The key point is exact consumption.  A successful prefix decoder is stable
under appending blocks, but its `remainingBlocks` field grows by exactly the
appended suffix.  Consequently an exact decoder, which accepts only an empty
remainder, cannot accept both a block list and a strict extension.  The q16
decoder has a separate proof: once sixteen positions have been found its scan
is extension-stable, while exact block use makes every strict extension fail.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73IncrementalSamplerControl

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder

/-! ## Extension stability of the field decoders -/

@[simp] theorem flattenedWords_append (first second : List Digest256) :
    flattenedWords (first ++ second) =
      flattenedWords first ++ flattenedWords second := by
  simp [flattenedWords]

def appendLimbRest (decoded : LimbDecode) (suffix : List Nat) :
    LimbDecode :=
  { decoded with restWords := decoded.restWords ++ suffix }

def appendFourLimbRest (decoded : FourLimbDecode)
    (suffix : List Nat) : FourLimbDecode :=
  { decoded with restWords := decoded.restWords ++ suffix }

def appendOrdinaryRemaining
    (decoded : OrdinaryPrefixDecode) (suffix : List Digest256) :
    OrdinaryPrefixDecode :=
  { decoded with
      remainingBlocks := decoded.remainingBlocks ++ suffix }

theorem decodeLimb_append_of_some (fuel : Nat) (words suffix : List Nat)
    (decoded : LimbDecode) (run : decodeLimb fuel words = some decoded) :
    decodeLimb fuel (words ++ suffix) =
      some (appendLimbRest decoded suffix) := by
  induction fuel generalizing words decoded with
  | zero => simp [decodeLimb] at run
  | succ fuel ih =>
      cases words with
      | nil => simp [decodeLimb] at run
      | cons word rest =>
          by_cases rejected : maskedM31 word = m31Prime
          · simp only [decodeLimb, rejected, if_pos] at run ⊢
            cases recursive : decodeLimb fuel rest with
            | none => simp [recursive] at run
            | some tail =>
                simp only [recursive] at run
                cases run
                have extended := ih rest tail recursive
                simp [List.cons_append, decodeLimb, rejected, extended,
                  appendLimbRest]
          · simp only [decodeLimb, rejected, if_neg] at run ⊢
            cases run
            simp [List.cons_append, decodeLimb, rejected, appendLimbRest]

theorem decodeLimbs_append_of_some (count : Nat) (words suffix : List Nat)
    (decoded : FourLimbDecode)
    (run : decodeLimbs count words = some decoded) :
    decodeLimbs count (words ++ suffix) =
      some (appendFourLimbRest decoded suffix) := by
  induction count generalizing words decoded with
  | zero =>
      simp only [decodeLimbs, Option.some.injEq] at run ⊢
      subst decoded
      rfl
  | succ count ih =>
      cases firstRun : decodeLimb 8 words with
      | none => simp [decodeLimbs, firstRun] at run
      | some first =>
          cases restRun : decodeLimbs count first.restWords with
          | none => simp [decodeLimbs, firstRun, restRun] at run
          | some rest =>
              simp [decodeLimbs, firstRun, restRun] at run
              subst decoded
              have firstExtended :=
                decodeLimb_append_of_some 8 words suffix first firstRun
              have restExtended :=
                ih first.restWords rest restRun
              simp [decodeLimbs, firstExtended, appendLimbRest,
                restExtended, appendFourLimbRest]

theorem decodeOrdinaryPrefix_append_of_some
    (blocks suffix : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    decodeOrdinaryPrefix (blocks ++ suffix) =
      some (appendOrdinaryRemaining decoded suffix) := by
  cases blocks with
  | nil => simp [decodeOrdinaryPrefix] at run
  | cons block rest =>
      cases limbsRun : decodeLimbs 4
          (flattenedWords (block :: rest)) with
      | none => simp [decodeOrdinaryPrefix, limbsRun] at run
      | some limbs =>
          by_cases valid :
              0 < blocksNeededForWords limbs.wordsUsed ∧
                blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                blocksNeededForWords limbs.wordsUsed ≤
                  (block :: rest).length
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            have decodedEq :
                { value := encodeQm31Limbs limbs.limbs
                  limbs := limbs.limbs
                  wordsUsed := limbs.wordsUsed
                  blocksUsed := blocksNeededForWords limbs.wordsUsed
                  remainingBlocks := (block :: rest).drop
                    (blocksNeededForWords limbs.wordsUsed) } = decoded :=
              run.2
            cases decodedEq
            have limbsExtended := decodeLimbs_append_of_some 4
              (flattenedWords (block :: rest)) (flattenedWords suffix)
              limbs limbsRun
            have usedLe : blocksNeededForWords limbs.wordsUsed ≤
                (block :: rest).length := valid.2.2
            have dropped :
                ((block :: rest) ++ suffix).drop
                    (blocksNeededForWords limbs.wordsUsed) =
                  (block :: rest).drop
                      (blocksNeededForWords limbs.wordsUsed) ++ suffix :=
              List.drop_append_of_le_length usedLe
            have extendedValid :
                0 < blocksNeededForWords limbs.wordsUsed ∧
                  blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                  blocksNeededForWords limbs.wordsUsed ≤
                    ((block :: rest) ++ suffix).length := by
              simp only [List.length_append]
              omega
            have flattened :
                flattenedWords (block :: (rest ++ suffix)) =
                  flattenedWords (block :: rest) ++ flattenedWords suffix := by
              calc
                flattenedWords (block :: (rest ++ suffix)) =
                    flattenedWords ((block :: rest) ++ suffix) := rfl
                _ = _ := flattenedWords_append (block :: rest) suffix
            unfold decodeOrdinaryPrefix
            simp only [List.cons_append]
            rw [flattened, limbsExtended]
            simp [appendFourLimbRest, extendedValid,
              appendOrdinaryRemaining, dropped]
            constructor
            · have lengthBound := extendedValid.2.2
              simp only [List.length_cons, List.length_append] at lengthBound ⊢
              omega
            · exact dropped
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid (by simpa using run.1))

theorem decodeNonzeroPrefix_append_of_some (attempts : Nat)
    (blocks suffix : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix attempts blocks = some decoded) :
    decodeNonzeroPrefix attempts (blocks ++ suffix) =
      some (appendOrdinaryRemaining decoded suffix) := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeNonzeroPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeNonzeroPrefix, firstRun] at run
      | some first =>
          have firstExtended :=
            decodeOrdinaryPrefix_append_of_some blocks suffix first firstRun
          by_cases zero : first.value = zeroBytes 16
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            have recursive := ih first.remainingBlocks decoded run
            simpa [decodeNonzeroPrefix, firstExtended, zero,
              appendOrdinaryRemaining] using recursive
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            subst decoded
            simp [decodeNonzeroPrefix, firstExtended,
              appendOrdinaryRemaining, zero]

theorem decodeSecureCirclePrefix_append_of_some
    (circleMap : SecureCircleParameterMap) (attempts : Nat)
    (blocks suffix : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeSecureCirclePrefix circleMap attempts blocks =
      some decoded) :
    decodeSecureCirclePrefix circleMap attempts (blocks ++ suffix) =
      some (appendOrdinaryRemaining decoded suffix) := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeSecureCirclePrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeSecureCirclePrefix, firstRun] at run
      | some first =>
          have firstExtended :=
            decodeOrdinaryPrefix_append_of_some blocks suffix first firstRun
          cases mapped : circleMap first.value with
          | none =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              have recursive := ih first.remainingBlocks decoded run
              simpa [decodeSecureCirclePrefix, firstExtended, mapped,
                appendOrdinaryRemaining] using recursive
          | some point =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              subst decoded
              simp [decodeSecureCirclePrefix, firstExtended,
                appendOrdinaryRemaining, mapped]

/-! ## Exact field samplers are prefix-free -/

theorem decodeOrdinaryExact_witness (blocks : List Digest256)
    (value : Qm31Bytes) (run : decodeOrdinaryExact blocks = some value) :
    ∃ decoded : OrdinaryPrefixDecode,
      decodeOrdinaryPrefix blocks = some decoded ∧
      decoded.remainingBlocks = [] ∧ decoded.value = value := by
  unfold decodeOrdinaryExact at run
  split at run
  next withinCap =>
    cases prefixRun : decodeOrdinaryPrefix blocks with
    | none => simp [prefixRun] at run
    | some decoded =>
        simp only [prefixRun] at run
        split at run
        next noRemaining =>
          exact ⟨decoded, rfl, noRemaining,
            Option.some.inj run⟩
        next remaining => simp at run
  next beyondCap => simp at run

theorem decodeNonzeroExact_witness (blocks : List Digest256)
    (value : Qm31Bytes) (run : decodeNonzeroExact blocks = some value) :
    ∃ decoded : OrdinaryPrefixDecode,
      decodeNonzeroPrefix 3 blocks = some decoded ∧
      decoded.remainingBlocks = [] ∧ decoded.value = value := by
  unfold decodeNonzeroExact at run
  split at run
  next withinCap =>
    cases prefixRun : decodeNonzeroPrefix 3 blocks with
    | none => simp [prefixRun] at run
    | some decoded =>
        simp only [prefixRun] at run
        split at run
        next noRemaining =>
          exact ⟨decoded, rfl, noRemaining,
            Option.some.inj run⟩
        next remaining => simp at run
  next beyondCap => simp at run

theorem decodeSecureCircleParameterExact_witness
    (circleMap : SecureCircleParameterMap) (blocks : List Digest256)
    (value : Qm31Bytes)
    (run : decodeSecureCircleParameterExact circleMap blocks = some value) :
    ∃ decoded : OrdinaryPrefixDecode,
      decodeSecureCirclePrefix circleMap 3 blocks = some decoded ∧
      decoded.remainingBlocks = [] ∧ decoded.value = value := by
  unfold decodeSecureCircleParameterExact at run
  split at run
  next withinCap =>
    cases prefixRun : decodeSecureCirclePrefix circleMap 3 blocks with
    | none => simp [prefixRun] at run
    | some decoded =>
        simp only [prefixRun] at run
        split at run
        next noRemaining =>
          exact ⟨decoded, rfl, noRemaining,
            Option.some.inj run⟩
        next remaining => simp at run
  next beyondCap => simp at run

theorem decodeOrdinaryExact_accepted_prefix_suffix_nil
    (blocks suffix : List Digest256) (first second : Qm31Bytes)
    (prefixAccepted : decodeOrdinaryExact blocks = some first)
    (extensionAccepted : decodeOrdinaryExact (blocks ++ suffix) =
      some second) :
    suffix = [] := by
  obtain ⟨decoded, decodedAtPrefix, noRemaining, valueAtPrefix⟩ :=
    decodeOrdinaryExact_witness blocks first prefixAccepted
  obtain ⟨extended, decodedAtExtension, extensionEmpty,
      valueAtExtension⟩ :=
    decodeOrdinaryExact_witness (blocks ++ suffix) second extensionAccepted
  have stable := decodeOrdinaryPrefix_append_of_some
    blocks suffix decoded decodedAtPrefix
  rw [stable] at decodedAtExtension
  have equal := Option.some.inj decodedAtExtension
  have remainingEqual := congrArg OrdinaryPrefixDecode.remainingBlocks equal
  simpa [appendOrdinaryRemaining, noRemaining] using
    remainingEqual.trans extensionEmpty

theorem decodeNonzeroExact_accepted_prefix_suffix_nil
    (blocks suffix : List Digest256) (first second : Qm31Bytes)
    (prefixAccepted : decodeNonzeroExact blocks = some first)
    (extensionAccepted : decodeNonzeroExact (blocks ++ suffix) =
      some second) :
    suffix = [] := by
  obtain ⟨decoded, decodedAtPrefix, noRemaining, valueAtPrefix⟩ :=
    decodeNonzeroExact_witness blocks first prefixAccepted
  obtain ⟨extended, decodedAtExtension, extensionEmpty,
      valueAtExtension⟩ :=
    decodeNonzeroExact_witness (blocks ++ suffix) second extensionAccepted
  have stable := decodeNonzeroPrefix_append_of_some 3
    blocks suffix decoded decodedAtPrefix
  rw [stable] at decodedAtExtension
  have equal := Option.some.inj decodedAtExtension
  have remainingEqual := congrArg OrdinaryPrefixDecode.remainingBlocks equal
  simpa [appendOrdinaryRemaining, noRemaining] using
    remainingEqual.trans extensionEmpty

theorem decodeSecureCircleParameterExact_accepted_prefix_suffix_nil
    (circleMap : SecureCircleParameterMap)
    (blocks suffix : List Digest256) (first second : Qm31Bytes)
    (prefixAccepted : decodeSecureCircleParameterExact circleMap blocks =
      some first)
    (extensionAccepted : decodeSecureCircleParameterExact circleMap
      (blocks ++ suffix) = some second) :
    suffix = [] := by
  obtain ⟨decoded, decodedAtPrefix, noRemaining, valueAtPrefix⟩ :=
    decodeSecureCircleParameterExact_witness circleMap blocks first
      prefixAccepted
  obtain ⟨extended, decodedAtExtension, extensionEmpty,
      valueAtExtension⟩ :=
    decodeSecureCircleParameterExact_witness circleMap (blocks ++ suffix)
      second extensionAccepted
  have stable := decodeSecureCirclePrefix_append_of_some circleMap 3
    blocks suffix decoded decodedAtPrefix
  rw [stable] at decodedAtExtension
  have equal := Option.some.inj decodedAtExtension
  have remainingEqual := congrArg OrdinaryPrefixDecode.remainingBlocks equal
  simpa [appendOrdinaryRemaining, noRemaining] using
    remainingEqual.trans extensionEmpty

theorem decodeChallengeParameter_accepted_prefix_suffix_nil
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks suffix : List Digest256) (first second : Qm31Bytes)
    (prefixAccepted : decodeChallengeParameter circleMap id blocks =
      some first)
    (extensionAccepted : decodeChallengeParameter circleMap id
      (blocks ++ suffix) = some second) :
    suffix = [] := by
  cases mode : samplerMode id with
  | ordinaryQm31 =>
      simp [decodeChallengeParameter, mode] at prefixAccepted extensionAccepted
      exact decodeOrdinaryExact_accepted_prefix_suffix_nil
        blocks suffix first second prefixAccepted extensionAccepted
  | nonzeroQm31 =>
      simp [decodeChallengeParameter, mode] at prefixAccepted extensionAccepted
      exact decodeNonzeroExact_accepted_prefix_suffix_nil
        blocks suffix first second prefixAccepted extensionAccepted
  | secureCirclePoint =>
      simp [decodeChallengeParameter, mode] at prefixAccepted extensionAccepted
      exact decodeSecureCircleParameterExact_accepted_prefix_suffix_nil
        circleMap blocks suffix first second prefixAccepted extensionAccepted

/-! ## q16 scan stability and prefix-freedom -/

theorem scanUniqueUntil_append_of_complete (needed fuel : Nat)
    (words suffix seen : List Nat)
    (complete : needed ≤
      (scanUniqueUntil needed fuel words seen).positions.length) :
    scanUniqueUntil needed fuel (words ++ suffix) seen =
      scanUniqueUntil needed fuel words seen := by
  induction fuel generalizing words seen with
  | zero => rfl
  | succ fuel ih =>
      cases words with
      | nil =>
          cases suffix with
          | nil => rfl
          | cons word rest =>
              simpa [scanUniqueUntil, complete]
      | cons word rest =>
          by_cases already : needed ≤ seen.length
          · simp [scanUniqueUntil, already]
          · simp only [List.cons_append, scanUniqueUntil, already,
              if_false] at complete ⊢
            have tailStable := ih rest (keepFirst seen (q16Candidate word))
              complete
            rw [tailStable]

theorem scanQ16_append_of_complete (blocks suffix : List Digest256)
    (complete : (scanQ16 blocks).positions.length = 16) :
    scanQ16 (blocks ++ suffix) = scanQ16 blocks := by
  unfold scanQ16 at complete ⊢
  rw [flattenedWords_append]
  apply scanUniqueUntil_append_of_complete
  exact Nat.le_of_eq complete.symm

theorem decodeCandidateDetailed_block_cap (counter : Fin 64)
    (blocks : List Digest256) (decoded : CandidateDecode blocks)
    (run : decodeCandidateDetailed counter blocks = some decoded) :
    blocks.length ≤ 8 := by
  unfold decodeCandidateDetailed at run
  split at run
  · assumption
  · simp at run

theorem decodeCandidateDetailed_schedule_scan_complete (counter : Fin 64)
    (blocks : List Digest256) (decoded : CandidateDecode blocks)
    (schedule : QuerySchedule)
    (run : decodeCandidateDetailed counter blocks = some decoded)
    (outcome : decoded.outcome = .schedule schedule) :
    (scanQ16 blocks).positions.length = 16 := by
  unfold decodeCandidateDetailed at run
  split at run
  next blockCap =>
    dsimp only at run
    split at run
    next lengthExact => exact lengthExact
    next lengthNotExact =>
      split at run
      next abortExact =>
        cases run
        simp at outcome
      next notAbort => simp at run
  next beyondCap => simp at run

theorem decodeCandidateDetailed_schedule_exact_length (counter : Fin 64)
    (blocks : List Digest256) (decoded : CandidateDecode blocks)
    (schedule : QuerySchedule)
    (run : decodeCandidateDetailed counter blocks = some decoded)
    (outcome : decoded.outcome = .schedule schedule) :
    blocks.length = blocksNeededForWords (scanQ16 blocks).drawsUsed := by
  unfold decodeCandidateDetailed at run
  split at run
  next blockCap =>
    dsimp only at run
    split at run
    next lengthExact =>
      split at run
      next exactUse => exact exactUse
      next inexact => simp at run
    next lengthNotExact =>
      split at run
      next abortExact =>
        cases run
        simp at outcome
      next notAbort => simp at run
  next beyondCap => simp at run

theorem decodeCandidateDetailed_abort_scan_incomplete (counter : Fin 64)
    (blocks : List Digest256) (decoded : CandidateDecode blocks)
    (run : decodeCandidateDetailed counter blocks = some decoded)
    (outcome : decoded.outcome = .samplerAbort) :
    (scanQ16 blocks).positions.length ≠ 16 := by
  intro complete
  unfold decodeCandidateDetailed at run
  split at run
  next blockCap =>
    dsimp only at run
    split at run
    next lengthExact =>
      split at run
      · split at run
        · cases run
          simp at outcome
        · simp at run
      · simp at run
    next lengthNotExact => exact lengthNotExact complete
  next beyondCap => simp at run

theorem decodeCandidateOutcome_accepted_prefix_suffix_nil
    (counter : Fin 64) (blocks suffix : List Digest256)
    (first second : CandidateOutcome)
    (prefixAccepted : decodeCandidateOutcome counter blocks = some first)
    (extensionAccepted : decodeCandidateOutcome counter (blocks ++ suffix) =
      some second) :
    suffix = [] := by
  unfold decodeCandidateOutcome at prefixAccepted extensionAccepted
  cases prefixRun : decodeCandidateDetailed counter blocks with
  | none => simp [prefixRun] at prefixAccepted
  | some prefixDecoded =>
      simp only [prefixRun, Option.map_some, Option.some.injEq] at prefixAccepted
      subst first
      cases extensionRun : decodeCandidateDetailed counter (blocks ++ suffix) with
      | none => simp [extensionRun] at extensionAccepted
      | some extensionDecoded =>
          simp only [extensionRun, Option.map_some,
            Option.some.injEq] at extensionAccepted
          cases prefixOutcome : prefixDecoded.outcome with
          | samplerAbort =>
              have prefixEight : blocks.length = 8 := by
                have exactBlocks := prefixDecoded.exactBlocks
                rw [prefixOutcome] at exactBlocks
                exact exactBlocks
              have extensionCap : (blocks ++ suffix).length ≤ 8 :=
                decodeCandidateDetailed_block_cap counter (blocks ++ suffix)
                  extensionDecoded extensionRun
              simp only [List.length_append, prefixEight] at extensionCap
              have suffixLength : suffix.length = 0 := by omega
              exact List.eq_nil_of_length_eq_zero suffixLength
          | schedule schedule =>
              have prefixComplete : (scanQ16 blocks).positions.length = 16 :=
                decodeCandidateDetailed_schedule_scan_complete counter blocks
                  prefixDecoded schedule prefixRun prefixOutcome
              have prefixLength : blocks.length =
                  blocksNeededForWords (scanQ16 blocks).drawsUsed :=
                decodeCandidateDetailed_schedule_exact_length counter blocks
                  prefixDecoded schedule prefixRun prefixOutcome
              have scanStable := scanQ16_append_of_complete blocks suffix
                prefixComplete
              cases extensionOutcome : extensionDecoded.outcome with
              | samplerAbort =>
                  have extensionComplete :
                      (scanQ16 (blocks ++ suffix)).positions.length = 16 := by
                    simpa [scanStable] using prefixComplete
                  exact False.elim
                    (decodeCandidateDetailed_abort_scan_incomplete counter
                      (blocks ++ suffix) extensionDecoded extensionRun
                      extensionOutcome extensionComplete)
              | schedule extensionSchedule =>
                  have extensionLength : (blocks ++ suffix).length =
                      blocksNeededForWords
                        (scanQ16 (blocks ++ suffix)).drawsUsed :=
                    decodeCandidateDetailed_schedule_exact_length counter
                      (blocks ++ suffix) extensionDecoded extensionSchedule
                      extensionRun extensionOutcome
                  rw [scanStable, ← prefixLength] at extensionLength
                  have suffixLength : suffix.length = 0 := by
                    simp only [List.length_append] at extensionLength
                    omega
                  exact List.eq_nil_of_length_eq_zero suffixLength

/-! ## Prefix minimality stated in the form consumed by a controller -/

theorem list_drop_nonempty_of_lt_length {α : Type}
    (values : List α) (count : Nat) (strict : count < values.length) :
    values.drop count ≠ [] := by
  intro empty
  have lengthZero := congrArg List.length empty
  simp at lengthZero
  omega

theorem decodeChallengeParameter_accepted_is_prefix_minimal
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks : List Digest256) (value : Qm31Bytes)
    (accepted : decodeChallengeParameter circleMap id blocks = some value) :
    ∀ count, count < blocks.length →
      decodeChallengeParameter circleMap id (blocks.take count) = none := by
  intro count strict
  cases prefixRun : decodeChallengeParameter circleMap id
      (blocks.take count) with
  | none => rfl
  | some prefixValue =>
      have fullAsAppend : blocks.take count ++ blocks.drop count = blocks :=
        List.take_append_drop count blocks
      have suffixEmpty := decodeChallengeParameter_accepted_prefix_suffix_nil
        circleMap id (blocks.take count) (blocks.drop count)
          prefixValue value prefixRun (by simpa [fullAsAppend] using accepted)
      exact False.elim
        (list_drop_nonempty_of_lt_length blocks count strict suffixEmpty)

theorem decodeCandidateOutcome_accepted_is_prefix_minimal
    (counter : Fin 64) (blocks : List Digest256) (outcome : CandidateOutcome)
    (accepted : decodeCandidateOutcome counter blocks = some outcome) :
    ∀ count, count < blocks.length →
      decodeCandidateOutcome counter (blocks.take count) = none := by
  intro count strict
  cases prefixRun : decodeCandidateOutcome counter (blocks.take count) with
  | none => rfl
  | some prefixOutcome =>
      have fullAsAppend : blocks.take count ++ blocks.drop count = blocks :=
        List.take_append_drop count blocks
      have suffixEmpty := decodeCandidateOutcome_accepted_prefix_suffix_nil
        counter (blocks.take count) (blocks.drop count) prefixOutcome outcome
          prefixRun (by simpa [fullAsAppend] using accepted)
      exact False.elim
        (list_drop_nonempty_of_lt_length blocks count strict suffixEmpty)

/-! ## Executable one-block streaming decisions -/

inductive IncrementalSamplerDecision (Result : Type) where
  | needMore
  | accepted (result : Result)
  | rejectedAtCap
  deriving DecidableEq

def incrementalChallengeStep (circleMap : SecureCircleParameterMap)
    (id : ChallengeId) (prior : List Digest256) (next : Digest256) :
    IncrementalSamplerDecision Qm31Bytes :=
  let blocks := prior ++ [next]
  match decodeChallengeParameter circleMap id blocks with
  | some value => .accepted value
  | none =>
      if prior.length + 1 < samplerBlockCap (samplerMode id) then
        .needMore
      else
        .rejectedAtCap

def incrementalCandidateStep (counter : Fin 64)
    (prior : List Digest256) (next : Digest256) :
    IncrementalSamplerDecision CandidateOutcome :=
  let blocks := prior ++ [next]
  match decodeCandidateOutcome counter blocks with
  | some outcome => .accepted outcome
  | none =>
      if prior.length + 1 < 8 then .needMore else .rejectedAtCap

theorem incrementalChallengeStep_accept_iff
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (prior : List Digest256) (next : Digest256) (value : Qm31Bytes) :
    incrementalChallengeStep circleMap id prior next =
        .accepted value ↔
      decodeChallengeParameter circleMap id (prior ++ [next]) = some value := by
  unfold incrementalChallengeStep
  cases decoded : decodeChallengeParameter circleMap id (prior ++ [next]) with
  | none =>
      simp only [decoded]
      split <;> simp
  | some actual =>
      simp only [decoded, IncrementalSamplerDecision.accepted.injEq]
      constructor
      · intro equal
        subst actual
        rfl
      · exact Option.some.inj

theorem incrementalChallengeStep_needMore_iff
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (prior : List Digest256) (next : Digest256) :
    incrementalChallengeStep circleMap id prior next = .needMore ↔
      decodeChallengeParameter circleMap id (prior ++ [next]) = none ∧
      (prior ++ [next]).length < samplerBlockCap (samplerMode id) := by
  unfold incrementalChallengeStep
  cases decoded : decodeChallengeParameter circleMap id (prior ++ [next]) with
  | none =>
      simp [decoded, List.length_append]
  | some value => simp [decoded]

theorem incrementalChallengeStep_rejectedAtCap_iff
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (prior : List Digest256) (next : Digest256) :
    incrementalChallengeStep circleMap id prior next = .rejectedAtCap ↔
      decodeChallengeParameter circleMap id (prior ++ [next]) = none ∧
      samplerBlockCap (samplerMode id) ≤ (prior ++ [next]).length := by
  unfold incrementalChallengeStep
  cases decoded : decodeChallengeParameter circleMap id (prior ++ [next]) with
  | none => simp [decoded, List.length_append]
  | some value => simp [decoded]

theorem incrementalCandidateStep_accept_iff (counter : Fin 64)
    (prior : List Digest256) (next : Digest256) (outcome : CandidateOutcome) :
    incrementalCandidateStep counter prior next = .accepted outcome ↔
      decodeCandidateOutcome counter (prior ++ [next]) = some outcome := by
  unfold incrementalCandidateStep
  cases decoded : decodeCandidateOutcome counter (prior ++ [next]) with
  | none =>
      simp only [decoded]
      split <;> simp
  | some actual =>
      simp only [decoded, IncrementalSamplerDecision.accepted.injEq]
      constructor
      · intro equal
        subst actual
        rfl
      · exact Option.some.inj

theorem incrementalCandidateStep_needMore_iff (counter : Fin 64)
    (prior : List Digest256) (next : Digest256) :
    incrementalCandidateStep counter prior next = .needMore ↔
      decodeCandidateOutcome counter (prior ++ [next]) = none ∧
      (prior ++ [next]).length < 8 := by
  unfold incrementalCandidateStep
  cases decoded : decodeCandidateOutcome counter (prior ++ [next]) with
  | none =>
      simp [decoded, List.length_append]
      omega
  | some outcome => simp [decoded]

theorem incrementalCandidateStep_rejectedAtCap_iff (counter : Fin 64)
    (prior : List Digest256) (next : Digest256) :
    incrementalCandidateStep counter prior next = .rejectedAtCap ↔
      decodeCandidateOutcome counter (prior ++ [next]) = none ∧
      8 ≤ (prior ++ [next]).length := by
  unfold incrementalCandidateStep
  cases decoded : decodeCandidateOutcome counter (prior ++ [next]) with
  | none => simp [decoded, List.length_append]
  | some outcome => simp [decoded]

theorem incrementalChallengeStep_accept_is_first
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (prior : List Digest256) (next : Digest256) (value : Qm31Bytes)
    (step : incrementalChallengeStep circleMap id prior next =
      .accepted value) :
    ∀ count, count < (prior ++ [next]).length →
      decodeChallengeParameter circleMap id
        ((prior ++ [next]).take count) = none := by
  have accepted := (incrementalChallengeStep_accept_iff circleMap id
    prior next value).mp step
  exact decodeChallengeParameter_accepted_is_prefix_minimal
    circleMap id (prior ++ [next]) value accepted

theorem incrementalCandidateStep_accept_is_first
    (counter : Fin 64) (prior : List Digest256) (next : Digest256)
    (outcome : CandidateOutcome)
    (step : incrementalCandidateStep counter prior next =
      .accepted outcome) :
    ∀ count, count < (prior ++ [next]).length →
      decodeCandidateOutcome counter ((prior ++ [next]).take count) = none := by
  have accepted := (incrementalCandidateStep_accept_iff counter prior next
    outcome).mp step
  exact decodeCandidateOutcome_accepted_is_prefix_minimal counter
    (prior ++ [next]) outcome accepted

#print axioms decodeLimb_append_of_some
#print axioms decodeLimbs_append_of_some
#print axioms decodeOrdinaryPrefix_append_of_some
#print axioms decodeNonzeroPrefix_append_of_some
#print axioms decodeSecureCirclePrefix_append_of_some
#print axioms decodeOrdinaryExact_accepted_prefix_suffix_nil
#print axioms decodeNonzeroExact_accepted_prefix_suffix_nil
#print axioms decodeSecureCircleParameterExact_accepted_prefix_suffix_nil
#print axioms decodeChallengeParameter_accepted_prefix_suffix_nil
#print axioms scanUniqueUntil_append_of_complete
#print axioms scanQ16_append_of_complete
#print axioms decodeCandidateOutcome_accepted_prefix_suffix_nil
#print axioms decodeChallengeParameter_accepted_is_prefix_minimal
#print axioms decodeCandidateOutcome_accepted_is_prefix_minimal
#print axioms incrementalChallengeStep_accept_is_first
#print axioms incrementalCandidateStep_accept_is_first

end AspisK1.V7Tag73IncrementalSamplerControl
