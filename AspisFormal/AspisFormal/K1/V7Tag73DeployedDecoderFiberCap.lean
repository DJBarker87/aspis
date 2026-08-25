import AspisFormal.K1.V7Tag73AtomicPairProbabilityAudit
import AspisFormal.K1.V7Tag73IncrementalSamplerControl
import AspisFormal.K1.V7Tag73ResourceLazyOracle
import AspisFormal.K1.V7Tag73SecureCircleMap

/-!
# Exact finite decoder-fiber cap for an unqueried Tag-73 output block

An unqueried `H(S || 0x01)` answer is not generally a singleton prediction:
the deployed bounded sampler exposes only its decoded value.  This module
replaces the invalid singleton charge by an exact finite coefficient.

For every deployed challenge identifier, every legal strict block prefix, and
every possible decoded QM31 value, `challengeCompletionFiberCap` is the
maximum number of 256-bit blocks that complete that prefix with that value.
The definition is finite and executable in principle; no cryptographic or
compiler conclusion is a field.  The accompanying probability theorem is the
exact fiber cardinality divided by `2^256`, followed by the proved maximum
bound.

This deliberately does not pretend that the enormous maximum has already
been simplified to a convenient power of two.  A sharper closed-form count
can replace the coefficient without changing the coupling API.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73DeployedDecoderFiberCap

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AtomicPairProbabilityAudit
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7FsStateRestorationCoupling
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation

noncomputable section

/-! ## Exact eight-word representation of one deployed digest -/

/-- The inverse little-endian codec direction omitted by the older V5
sampler leaf.  Together with `decodeWordLE_encodeWordLE`, this makes the
byte/word conversion a genuine equivalence rather than a cardinality slogan. -/
theorem encodeWordLE_decodeWordLE_exact (wordBytes : WordBytes) :
    encodeWordLE (decodeWordLE wordBytes) = wordBytes := by
  have injective : Function.Injective encodeWordLE :=
    Function.LeftInverse.injective decodeWordLE_encodeWordLE
  have sameCard : Fintype.card RawWord = Fintype.card WordBytes := by
    simp [RawWord, WordBytes, rawWordCount]
  have surjective : Function.Surjective encodeWordLE :=
    ((Fintype.bijective_iff_injective_and_card encodeWordLE).2
      ⟨injective, sameCard⟩).2
  obtain ⟨word, encoded⟩ := surjective wordBytes
  rw [← encoded, decodeWordLE_encodeWordLE]

def wordBytesEquivRawWord : WordBytes ≃ RawWord where
  toFun := decodeWordLE
  invFun := encodeWordLE
  left_inv := encodeWordLE_decodeWordLE_exact
  right_inv := decodeWordLE_encodeWordLE

/-- Reindex the concrete 32-byte deployed digest into eight consecutive
four-byte little-endian chunks. -/
def digestByteIndexEquiv : Fin 8 × Fin 4 ≃ Fin 32 :=
  finProdFinEquiv

def digestBytesAsWordsEquiv :
    Digest256 ≃ (Fin 8 → WordBytes) where
  toFun block word byte :=
    uint8EquivFin256 (block (digestByteIndexEquiv (word, byte)))
  invFun words index :=
    uint8EquivFin256.symm
      (words (digestByteIndexEquiv.symm index).1
        (digestByteIndexEquiv.symm index).2)
  left_inv block := by
    funext index
    simp
  right_inv words := by
    funext word byte
    simp

/-- One SHA-256 output is exactly eight mathematical `u32` words, in the
same little-endian order consumed by `flattenedWords`. -/
def digestWordsEquiv : Digest256 ≃ (Fin 8 → RawWord) :=
  digestBytesAsWordsEquiv.trans
    (Equiv.piCongrRight fun _ => wordBytesEquivRawWord)

@[simp] theorem digestWordsEquiv_apply_val
    (block : Digest256) (word : Fin 8) :
    ((digestWordsEquiv block word : RawWord) : Nat) =
      littleEndianWord block word := by
  have index0 : digestByteIndexEquiv (word, 0) =
      (⟨4 * word.val, by omega⟩ : Fin 32) := by
    apply Fin.ext
    change 0 + 4 * word.val = 4 * word.val
    omega
  have index1 : digestByteIndexEquiv (word, 1) =
      (⟨1 + 4 * word.val, by omega⟩ : Fin 32) := by
    apply Fin.ext
    change 1 + 4 * word.val = 1 + 4 * word.val
    rfl
  have index2 : digestByteIndexEquiv (word, 2) =
      (⟨2 + 4 * word.val, by omega⟩ : Fin 32) := by
    apply Fin.ext
    change 2 + 4 * word.val = 2 + 4 * word.val
    rfl
  have index3 : digestByteIndexEquiv (word, 3) =
      (⟨3 + 4 * word.val, by omega⟩ : Fin 32) := by
    apply Fin.ext
    change 3 + 4 * word.val = 3 + 4 * word.val
    rfl
  simp [digestWordsEquiv, digestBytesAsWordsEquiv,
    wordBytesEquivRawWord, decodeWordLE, littleEndianWord,
    uint8EquivFin256, Nat.add_comm, index0, index1, index2, index3]

@[simp] theorem low31Candidate_digestWordsEquiv
    (block : Digest256) (word : Fin 8) :
    (low31Candidate (digestWordsEquiv block word) : Nat) =
      maskedM31 (littleEndianWord block word) := by
  simp [low31Candidate, maskedM31, rawCandidateCount, m31MaskModulus]

def low31RawWordFiberEquivHighBit (target : RawCandidate) :
    {word : RawWord // low31Candidate word = target} ≃ RawHighBit where
  toFun word := (rawCandidateHighBitEquiv.symm word.1).2
  invFun highBit :=
    ⟨rawCandidateHighBitEquiv (target, highBit), by simp⟩
  left_inv word := by
    apply Subtype.ext
    have firstComponent :
        (rawCandidateHighBitEquiv.symm word.1).1 = target :=
      (rawCandidateHighBitEquiv_symm_fst word.1).trans word.2
    change rawCandidateHighBitEquiv
      (target, (rawCandidateHighBitEquiv.symm word.1).2) = word.1
    calc
      rawCandidateHighBitEquiv
          (target, (rawCandidateHighBitEquiv.symm word.1).2) =
          rawCandidateHighBitEquiv
            ((rawCandidateHighBitEquiv.symm word.1).1,
              (rawCandidateHighBitEquiv.symm word.1).2) := by
                exact congrArg rawCandidateHighBitEquiv
                  (congrArg
                    (fun first =>
                      (first, (rawCandidateHighBitEquiv.symm word.1).2))
                    firstComponent.symm)
      _ = word.1 := rawCandidateHighBitEquiv.apply_symm_apply word.1
  right_inv highBit := by simp

def pairCoordinateFiberEquiv (slot : Fin 8) (target : RawCandidate) :
    {pair : RawWord × ({index : Fin 8 // index ≠ slot} → RawWord) //
        low31Candidate pair.1 = target} ≃
      {word : RawWord // low31Candidate word = target} ×
        ({index : Fin 8 // index ≠ slot} → RawWord) where
  toFun pair := (⟨pair.1.1, pair.2⟩, pair.1.2)
  invFun pair := ⟨(pair.1.1, pair.2), pair.1.2⟩
  left_inv pair := by cases pair; rfl
  right_inv pair := by cases pair; rfl

def splitCoordinateFiberEquiv (slot : Fin 8) (target : RawCandidate) :
    {words : Fin 8 → RawWord // low31Candidate (words slot) = target} ≃
      {word : RawWord // low31Candidate word = target} ×
        ({index : Fin 8 // index ≠ slot} → RawWord) :=
  ((Equiv.funSplitAt slot RawWord).subtypeEquiv fun _ => Iff.rfl).trans
    (pairCoordinateFiberEquiv slot target)

def low31CoordinateFiberEquiv (slot : Fin 8) (target : RawCandidate) :
    {words : Fin 8 → RawWord // low31Candidate (words slot) = target} ≃
      RawHighBit × ({index : Fin 8 // index ≠ slot} → RawWord) :=
  (splitCoordinateFiberEquiv slot target).trans
    ((low31RawWordFiberEquivHighBit target).prodCongr
      (Equiv.refl _))

theorem fin_eight_without_one_card (slot : Fin 8) :
    Fintype.card {index : Fin 8 // index ≠ slot} = 7 := by
  classical
  rw [Fintype.card_subtype_compl]
  simp

/-- Fixing the low 31 bits of one of the eight deployed words leaves exactly
one high bit and seven unconstrained `u32` words: `2 * (2^32)^7 = 2^225`. -/
theorem low31_coordinate_fiber_card_exact
    (slot : Fin 8) (target : RawCandidate) :
    Fintype.card
        {words : Fin 8 → RawWord // low31Candidate (words slot) = target} =
      2 ^ 225 := by
  rw [Fintype.card_congr (low31CoordinateFiberEquiv slot target)]
  simp [fin_eight_without_one_card, RawHighBit, RawWord, rawWordCount]

def digestLow31CoordinateFiberEquiv (slot : Fin 8)
    (target : RawCandidate) :
    {block : Digest256 //
        low31Candidate (digestWordsEquiv block slot) = target} ≃
      {words : Fin 8 → RawWord // low31Candidate (words slot) = target} :=
  digestWordsEquiv.subtypeEquiv fun _ => Iff.rfl

theorem digest_low31_coordinate_fiber_card_exact
    (slot : Fin 8) (target : RawCandidate) :
    Fintype.card
        {block : Digest256 //
          low31Candidate (digestWordsEquiv block slot) = target} =
      2 ^ 225 := by
  rw [Fintype.card_congr (digestLow31CoordinateFiberEquiv slot target)]
  exact low31_coordinate_fiber_card_exact slot target

/-! ## The accepted fourth limb occurs in the completing block -/

/-- A successful bounded limb scan consumes a concrete rejected prefix and
then one accepted word.  This is the operational trace fact hidden by the
`Option` result of `decodeLimb`. -/
theorem decodeLimb_success_trace (fuel : Nat) (words : List Nat)
    (decoded : LimbDecode) (run : decodeLimb fuel words = some decoded) :
    ∃ before accepted after,
      words = before ++ accepted :: after ∧
      decoded.value = maskedM31 accepted ∧
      decoded.restWords = after ∧
      decoded.attemptsUsed = before.length + 1 := by
  induction fuel generalizing words decoded with
  | zero => simp [decodeLimb] at run
  | succ fuel ih =>
      cases words with
      | nil => simp [decodeLimb] at run
      | cons word rest =>
          by_cases rejected : maskedM31 word = m31Prime
          · simp only [decodeLimb, rejected, if_pos] at run
            cases recursive : decodeLimb fuel rest with
            | none => simp [recursive] at run
            | some tail =>
                simp only [recursive, Option.some.injEq] at run
                subst decoded
                obtain ⟨before, accepted, after, decomposition, value,
                    remaining, attempts⟩ := ih rest tail recursive
                refine ⟨word :: before, accepted, after, ?_, value, remaining, ?_⟩
                · simp [decomposition]
                · simp [attempts, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm]
          · simp only [decodeLimb, rejected, if_neg,
              Option.some.injEq] at run
            simp at run
            rcases run with rfl
            exact ⟨[], word, rest, by simp, rfl, rfl, by simp⟩

/-- The four-limb decoder's last accepted word is exposed together with the
exact number of consumed words. -/
theorem decodeLimbs_four_success_trace (words : List Nat)
    (decoded : FourLimbDecode)
    (run : decodeLimbs 4 words = some decoded) :
    ∃ before accepted after,
      words = before ++ accepted :: after ∧
      decoded.restWords = after ∧
      decoded.wordsUsed = before.length + 1 ∧
      decoded.limbs.length = 4 ∧
      listValue decoded.limbs 3 = maskedM31 accepted := by
  cases firstRun : decodeLimb 8 words with
  | none => simp [decodeLimbs, firstRun] at run
  | some first =>
      cases secondRun : decodeLimb 8 first.restWords with
      | none => simp [decodeLimbs, firstRun, secondRun] at run
      | some second =>
          cases thirdRun : decodeLimb 8 second.restWords with
          | none =>
              simp [decodeLimbs, firstRun, secondRun, thirdRun] at run
          | some third =>
              cases fourthRun : decodeLimb 8 third.restWords with
              | none =>
                  simp [decodeLimbs, firstRun, secondRun, thirdRun,
                    fourthRun] at run
              | some fourth =>
                  simp [decodeLimbs, firstRun, secondRun, thirdRun,
                    fourthRun] at run
                  subst decoded
                  obtain ⟨before1, accepted1, after1, words1, value1,
                      rest1, attempts1⟩ :=
                    decodeLimb_success_trace 8 words first firstRun
                  obtain ⟨before2, accepted2, after2, words2, value2,
                      rest2, attempts2⟩ :=
                    decodeLimb_success_trace 8 first.restWords second secondRun
                  obtain ⟨before3, accepted3, after3, words3, value3,
                      rest3, attempts3⟩ :=
                    decodeLimb_success_trace 8 second.restWords third thirdRun
                  obtain ⟨before4, accepted4, after4, words4, value4,
                      rest4, attempts4⟩ :=
                    decodeLimb_success_trace 8 third.restWords fourth fourthRun
                  let before := before1 ++ [accepted1] ++ before2 ++
                    [accepted2] ++ before3 ++ [accepted3] ++ before4
                  refine ⟨before, accepted4, after4, ?_, ?_, ?_, by simp,
                    ?_⟩
                  · simp only [before]
                    rw [words1, ← rest1, words2, ← rest2, words3, ← rest3,
                      words4]
                    simp [List.append_assoc]
                  · exact rest4
                  · simp only [before, List.length_append,
                      List.length_singleton]
                    omega
                  · simp [listValue, value4]

/-- Every successful ordinary prefix exposes the final (fourth) accepted
limb and its exact position in the flattened word stream. -/
theorem decodeOrdinaryPrefix_fourth_limb_trace
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    ∃ before accepted after,
      flattenedWords blocks = before ++ accepted :: after ∧
      decoded.wordsUsed = before.length + 1 ∧
      decoded.limbs.length = 4 ∧
      listValue decoded.limbs 3 = maskedM31 accepted ∧
      decoded.value = encodeQm31Limbs decoded.limbs ∧
      decoded.blocksUsed = blocksNeededForWords decoded.wordsUsed ∧
      decoded.remainingBlocks = blocks.drop decoded.blocksUsed ∧
      decoded.blocksUsed ≤ blocks.length := by
  cases blocks with
  | nil => simp [decodeOrdinaryPrefix] at run
  | cons block rest =>
      cases limbsRun : decodeLimbs 4 (flattenedWords (block :: rest)) with
      | none => simp [decodeOrdinaryPrefix, limbsRun] at run
      | some limbs =>
          by_cases valid :
              0 < blocksNeededForWords limbs.wordsUsed ∧
                blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                blocksNeededForWords limbs.wordsUsed ≤ (block :: rest).length
          · simp [decodeOrdinaryPrefix, limbsRun, valid] at run
            rcases run with ⟨_runLe, decodedEq⟩
            subst decoded
            obtain ⟨before, accepted, after, decomposition, remaining,
                wordsUsed, limbCount, finalLimb⟩ :=
              decodeLimbs_four_success_trace
                (flattenedWords (block :: rest)) limbs limbsRun
            exact ⟨before, accepted, after, decomposition, wordsUsed,
              limbCount, finalLimb, rfl, rfl, rfl, valid.2.2⟩
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid run.1)

/-- Concrete prefix decodes always leave a suffix of the supplied block
stream. -/
theorem decodeOrdinaryPrefix_take_remaining
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    blocks.take decoded.blocksUsed ++ decoded.remainingBlocks = blocks := by
  obtain ⟨before, accepted, after, decomposition, wordsUsed, limbCount,
      finalLimb, value, blocksUsed, remaining, blocksUsedLe⟩ :=
    decodeOrdinaryPrefix_fourth_limb_trace blocks decoded run
  rw [remaining]
  exact List.take_append_drop decoded.blocksUsed blocks

theorem decodeOrdinaryPrefix_blocks_nonempty
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) : blocks ≠ [] := by
  intro empty
  subst blocks
  simp [decodeOrdinaryPrefix] at run

/-- A nonzero retry result is an actual ordinary decode on a suffix of the
original stream; the skipped attempts are not merged into the final call. -/
theorem decodeNonzeroPrefix_ordinary_suffix (attempts : Nat)
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix attempts blocks = some decoded) :
    ∃ discarded suffix,
      blocks = discarded ++ suffix ∧
      decodeOrdinaryPrefix suffix = some decoded := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeNonzeroPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeNonzeroPrefix, firstRun] at run
      | some first =>
          by_cases zero : first.value = zeroBytes 16
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            obtain ⟨discarded, suffix, decomposition, finalRun⟩ :=
              ih first.remainingBlocks decoded run
            refine ⟨blocks.take first.blocksUsed ++ discarded, suffix,
              ?_, finalRun⟩
            calc
              blocks = blocks.take first.blocksUsed ++
                  first.remainingBlocks :=
                (decodeOrdinaryPrefix_take_remaining blocks first
                  firstRun).symm
              _ = (blocks.take first.blocksUsed ++ discarded) ++ suffix := by
                rw [decomposition, List.append_assoc]
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            subst decoded
            exact ⟨[], blocks, by simp, firstRun⟩

/-- The same suffix property for secure-circle retries. -/
theorem decodeSecureCirclePrefix_ordinary_suffix
    (circleMap : SecureCircleParameterMap) (attempts : Nat)
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeSecureCirclePrefix circleMap attempts blocks =
      some decoded) :
    ∃ discarded suffix,
      blocks = discarded ++ suffix ∧
      decodeOrdinaryPrefix suffix = some decoded := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeSecureCirclePrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeSecureCirclePrefix, firstRun] at run
      | some first =>
          cases mapped : circleMap first.value with
          | none =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              obtain ⟨discarded, suffix, decomposition, finalRun⟩ :=
                ih first.remainingBlocks decoded run
              refine ⟨blocks.take first.blocksUsed ++ discarded, suffix,
                ?_, finalRun⟩
              calc
                blocks = blocks.take first.blocksUsed ++
                    first.remainingBlocks :=
                  (decodeOrdinaryPrefix_take_remaining blocks first
                    firstRun).symm
                _ = (blocks.take first.blocksUsed ++ discarded) ++ suffix := by
                  rw [decomposition, List.append_assoc]
          | some point =>
              simp [decodeSecureCirclePrefix, firstRun, mapped] at run
              subst decoded
              exact ⟨[], blocks, by simp, firstRun⟩

/-- A nonempty suffix of a list ending in `last` itself ends in `last`. -/
theorem nonempty_suffix_of_append_singleton_ends_in_last
    {alpha : Type} (discarded suffix initial : List alpha) (last : alpha)
    (decomposition : discarded ++ suffix = initial ++ [last])
    (nonempty : suffix ≠ []) :
    ∃ suffixInitial, suffix = suffixInitial ++ [last] := by
  have lastValue : suffix.getLast? = some last := by
    have ends := congrArg List.getLast? decomposition
    simpa [List.getLast?_append, nonempty] using ends
  refine ⟨suffix.dropLast, ?_⟩
  exact (List.dropLast_append_getLast? last (by simp [lastValue])).symm

/-- If rounding `wordsUsed` up to eight-word blocks yields the successor
block, then the consumed word lies strictly after all preceding blocks. -/
theorem eight_mul_lt_of_blocksNeededForWords_eq_succ
    (wordsUsed precedingBlocks : Nat)
    (rounded : blocksNeededForWords wordsUsed = precedingBlocks + 1) :
    8 * precedingBlocks < wordsUsed := by
  have lower := Nat.mul_div_le (wordsUsed + 7) 8
  unfold blocksNeededForWords at rounded
  rw [rounded] at lower
  omega

/-- In an exact ordinary decode ending at `output`, the accepted fourth limb
is one of the eight little-endian words of that final block. -/
theorem ordinary_exact_completion_fourth_limb_in_final_block
    (initial : List Digest256) (output : Digest256)
    (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (initial ++ [output]) = some decoded)
    (noRemaining : decoded.remainingBlocks = []) :
    ∃ slot : Fin 8,
      maskedM31 (littleEndianWord output slot) =
        listValue decoded.limbs 3 := by
  obtain ⟨before, accepted, after, decomposition, wordsUsed, limbCount,
      finalLimb, value, blocksUsed, remaining, blocksUsedLe⟩ :=
    decodeOrdinaryPrefix_fourth_limb_trace
      (initial ++ [output]) decoded run
  have dropEmpty : (initial ++ [output]).drop decoded.blocksUsed = [] := by
    rw [← remaining]
    exact noRemaining
  have usedAtLeastLength : (initial ++ [output]).length ≤
      decoded.blocksUsed := (List.drop_eq_nil_iff.mp dropEmpty)
  have usedAtMostLength : decoded.blocksUsed ≤
      (initial ++ [output]).length := blocksUsedLe
  have exactBlocks : decoded.blocksUsed = initial.length + 1 := by
    simp only [List.length_append, List.length_singleton]
      at usedAtLeastLength usedAtMostLength
    omega
  have wordAfterInitial : 8 * initial.length ≤ before.length := by
    have strict := eight_mul_lt_of_blocksNeededForWords_eq_succ
      decoded.wordsUsed initial.length (by
        rw [← exactBlocks, blocksUsed])
    omega
  have flattenedInitialLength : (flattenedWords initial).length =
      8 * initial.length := flattenedWords_length initial
  have wordAfterInitial' : (flattenedWords initial).length ≤ before.length := by
    rw [flattenedInitialLength]
    exact wordAfterInitial
  have dropped := congrArg
    (List.drop (flattenedWords initial).length) decomposition
  have blockDecomposition :
      blockWords output =
        before.drop (flattenedWords initial).length ++ accepted :: after := by
    rw [List.drop_append_of_le_length wordAfterInitial'] at dropped
    simpa [flattenedWords_append, flattenedWords] using dropped
  have acceptedMember : accepted ∈ blockWords output := by
    rw [blockDecomposition]
    simp
  rw [blockWords, List.mem_ofFn] at acceptedMember
  obtain ⟨slot, slotValue⟩ := acceptedMember
  refine ⟨slot, ?_⟩
  rw [slotValue, finalLimb]

/-- The successful ordinary suffix selected by any deployed challenge mode. -/
theorem decodeChallengeParameter_ordinary_suffix
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks : List Digest256) (value : Qm31Bytes)
    (run : decodeChallengeParameter circleMap id blocks = some value) :
    ∃ discarded suffix decoded,
      blocks = discarded ++ suffix ∧
      decodeOrdinaryPrefix suffix = some decoded ∧
      decoded.remainingBlocks = [] ∧
      decoded.value = value := by
  cases mode : samplerMode id with
  | ordinaryQm31 =>
      simp [decodeChallengeParameter, mode] at run
      obtain ⟨decoded, prefixRun, remaining, decodedValue⟩ :=
        decodeOrdinaryExact_witness blocks value run
      exact ⟨[], blocks, decoded, by simp, prefixRun, remaining,
        decodedValue⟩
  | nonzeroQm31 =>
      simp [decodeChallengeParameter, mode] at run
      obtain ⟨decoded, prefixRun, remaining, decodedValue⟩ :=
        decodeNonzeroExact_witness blocks value run
      obtain ⟨discarded, suffix, decomposition, ordinaryRun⟩ :=
        decodeNonzeroPrefix_ordinary_suffix 3 blocks decoded prefixRun
      exact ⟨discarded, suffix, decoded, decomposition, ordinaryRun,
        remaining, decodedValue⟩
  | secureCirclePoint =>
      simp [decodeChallengeParameter, mode] at run
      obtain ⟨decoded, prefixRun, remaining, decodedValue⟩ :=
        decodeSecureCircleParameterExact_witness circleMap blocks value run
      obtain ⟨discarded, suffix, decomposition, ordinaryRun⟩ :=
        decodeSecureCirclePrefix_ordinary_suffix circleMap 3 blocks decoded
          prefixRun
      exact ⟨discarded, suffix, decoded, decomposition, ordinaryRun,
        remaining, decodedValue⟩

/-- For every deployed ordinary/nonzero/circle challenge, a successful exact
completion fixes the low 31 bits of some word in the appended output block to
the fourth decoded limb.  q16 uses a different decoder and is intentionally
not part of this statement. -/
theorem challenge_completion_fourth_limb_in_output
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (initial : List Digest256) (output : Digest256) (value : Qm31Bytes)
    (run : decodeChallengeParameter circleMap id (initial ++ [output]) =
      some value) :
    ∃ slot : Fin 8, ∃ decoded : OrdinaryPrefixDecode,
      decoded.value = value ∧
      decoded.value = encodeQm31Limbs decoded.limbs ∧
      decoded.limbs.length = 4 ∧
      maskedM31 (littleEndianWord output slot) =
        listValue decoded.limbs 3 := by
  obtain ⟨discarded, suffix, decoded, decomposition, ordinaryRun,
      noRemaining, decodedValue⟩ :=
    decodeChallengeParameter_ordinary_suffix circleMap id
      (initial ++ [output]) value run
  have suffixNonempty :=
    decodeOrdinaryPrefix_blocks_nonempty suffix decoded ordinaryRun
  obtain ⟨suffixInitial, suffixEnds⟩ :=
    nonempty_suffix_of_append_singleton_ends_in_last discarded suffix initial
      output (by simpa [decomposition]) suffixNonempty
  subst suffix
  obtain ⟨slot, finalLimb⟩ :=
    ordinary_exact_completion_fourth_limb_in_final_block
      suffixInitial output decoded ordinaryRun noRemaining
  obtain ⟨before, accepted, after, wordTrace, wordsUsed, limbCount,
      acceptedLimb, valueEncoding, blocksUsed, remaining, blocksUsedLe⟩ :=
    decodeOrdinaryPrefix_fourth_limb_trace
      (suffixInitial ++ [output]) decoded ordinaryRun
  exact ⟨slot, decoded, decodedValue, valueEncoding, limbCount, finalLimb⟩

/-! ## The fixed fourth-limb target encoded in the returned QM31 bytes -/

def qm31FourthWordBytes (value : Qm31Bytes) : WordBytes := fun byte =>
  uint8EquivFin256 (value ⟨12 + byte.val, by omega⟩)

def qm31FourthLow31 (value : Qm31Bytes) : RawCandidate :=
  low31Candidate (decodeWordLE (qm31FourthWordBytes value))

theorem qm31FourthWordBytes_encodeQm31Limbs (limbs : List Nat)
    (bound : listValue limbs 3 < 2 ^ 31) :
    qm31FourthWordBytes (encodeQm31Limbs limbs) =
      encodeWordLE
        (⟨listValue limbs 3, by
          exact bound.trans (by norm_num [rawWordCount])⟩ : RawWord) := by
  apply wordBytesEquivRawWord.injective
  change decodeWordLE (qm31FourthWordBytes (encodeQm31Limbs limbs)) =
    decodeWordLE (encodeWordLE ⟨listValue limbs 3, _⟩)
  rw [decodeWordLE_encodeWordLE]
  apply Fin.ext
  simp [decodeWordLE, qm31FourthWordBytes, encodeQm31Limbs,
    uint8EquivFin256]
  omega

theorem qm31FourthLow31_encodeQm31Limbs_val (limbs : List Nat)
    (bound : listValue limbs 3 < 2 ^ 31) :
    (qm31FourthLow31 (encodeQm31Limbs limbs) : Nat) =
      listValue limbs 3 := by
  rw [qm31FourthLow31, qm31FourthWordBytes_encodeQm31Limbs limbs bound,
    decodeWordLE_encodeWordLE]
  change listValue limbs 3 % m31MaskModulus = listValue limbs 3
  have boundModulus : listValue limbs 3 < m31MaskModulus := by
    change listValue limbs 3 < 2 ^ 31
    exact bound
  exact Nat.mod_eq_of_lt boundModulus

/-- The decoder trace now has a fixed target depending only on the returned
QM31 bytes, not on the completing digest. -/
theorem challenge_completion_fixes_one_low31_coordinate
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (initial : List Digest256) (output : Digest256) (value : Qm31Bytes)
    (run : decodeChallengeParameter circleMap id (initial ++ [output]) =
      some value) :
    ∃ slot : Fin 8,
      low31Candidate (digestWordsEquiv output slot) =
        qm31FourthLow31 value := by
  obtain ⟨slot, decoded, decodedValue, valueEncoding, limbCount,
      finalLimb⟩ :=
    challenge_completion_fourth_limb_in_output circleMap id initial output
      value run
  have bound : listValue decoded.limbs 3 < 2 ^ 31 := by
    rw [← finalLimb]
    exact maskedM31_lt_modulus (littleEndianWord output slot)
  refine ⟨slot, ?_⟩
  apply Fin.ext
  rw [low31Candidate_digestWordsEquiv, ← decodedValue, valueEncoding,
    qm31FourthLow31_encodeQm31Limbs_val decoded.limbs bound]
  exact finalLimb

/-- A chronological block prefix whose length is strictly below `cap`.
Unlike `List Digest256`, this representation is manifestly finite. -/
structure BoundedBlockPrefix (cap : Nat) where
  count : Fin cap
  blocks : Fin count.val → Digest256

def boundedBlockPrefixEquivSigma (cap : Nat) :
    BoundedBlockPrefix cap ≃
      (Σ count : Fin cap, Fin count.val → Digest256) where
  toFun blockPrefix := ⟨blockPrefix.count, blockPrefix.blocks⟩
  invFun data :=
    { count := data.1
      blocks := data.2 }
  left_inv blockPrefix := by cases blockPrefix; rfl
  right_inv data := by cases data; rfl

noncomputable instance (cap : Nat) : Fintype (BoundedBlockPrefix cap) :=
  Fintype.ofEquiv (Σ count : Fin cap, Fin count.val → Digest256)
    (boundedBlockPrefixEquivSigma cap).symm

def BoundedBlockPrefix.toList {cap : Nat}
    (blockPrefix : BoundedBlockPrefix cap) : List Digest256 :=
  List.ofFn blockPrefix.blocks

@[simp] theorem boundedBlockPrefix_toList_length {cap : Nat}
    (blockPrefix : BoundedBlockPrefix cap) :
    blockPrefix.toList.length = blockPrefix.count.val := by
  simp [BoundedBlockPrefix.toList]

theorem boundedBlockPrefix_length_lt_cap {cap : Nat}
    (blockPrefix : BoundedBlockPrefix cap) :
    blockPrefix.toList.length < cap := by
  rw [boundedBlockPrefix_toList_length]
  exact blockPrefix.count.isLt

/-- The exact deployed decoder after appending one previously unqueried raw
output block to a fixed chronological prefix. -/
def challengeCompletionDecode (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (output : Digest256) : Option Qm31Bytes :=
  exactDeterministicDecoders.qm31Parameter id
    (blockPrefix.toList ++ [output])

/-- Exact size of one accepted completion fiber. -/
noncomputable def challengeCompletionFiberCard (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) : Nat :=
  Fintype.card
    {output : Digest256 // challengeCompletionDecode id blockPrefix output =
      some value}

/-- Maximum accepted completion-fiber size for one deployed challenge kind.
Both maxima range over explicit finite types. -/
noncomputable def challengeCompletionFiberCap (id : ChallengeId) : Nat :=
  Finset.univ.sup fun
      blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)) =>
    Finset.univ.sup fun value : Qm31Bytes =>
      challengeCompletionFiberCard id blockPrefix value

/-! ## Closed-form `2^228` completion-fiber bound -/

noncomputable def completionFiberSlot (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes)
    (output : {output : Digest256 //
      challengeCompletionDecode id blockPrefix output = some value}) : Fin 8 :=
  Classical.choose (challenge_completion_fixes_one_low31_coordinate
    exactSecureCircleParameterMap id blockPrefix.toList output.1 value (by
      simpa [challengeCompletionDecode] using output.2))

theorem completionFiberSlot_fixes_target (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes)
    (output : {output : Digest256 //
      challengeCompletionDecode id blockPrefix output = some value}) :
    low31Candidate
        (digestWordsEquiv output.1
          (completionFiberSlot id blockPrefix value output)) =
      qm31FourthLow31 value := by
  exact Classical.choose_spec
    (challenge_completion_fixes_one_low31_coordinate
      exactSecureCircleParameterMap id blockPrefix.toList output.1 value (by
        simpa [challengeCompletionDecode] using output.2))

noncomputable def completionFiberEmbedding (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    {output : Digest256 //
      challengeCompletionDecode id blockPrefix output = some value} ↪
      (Σ slot : Fin 8,
        {output : Digest256 //
          low31Candidate (digestWordsEquiv output slot) =
            qm31FourthLow31 value}) where
  toFun output :=
    ⟨completionFiberSlot id blockPrefix value output,
      ⟨output.1, completionFiberSlot_fixes_target id blockPrefix value
        output⟩⟩
  inj' := by
    intro first second equal
    apply Subtype.ext
    exact congrArg (fun encoded => encoded.2.1) equal

/-- The slot tag costs three bits; each fixed low-31 coordinate leaves exactly
`225` free bits. -/
theorem completion_target_sigma_card_exact (value : Qm31Bytes) :
    Fintype.card
        (Σ slot : Fin 8,
          {output : Digest256 //
            low31Candidate (digestWordsEquiv output slot) =
              qm31FourthLow31 value}) =
      2 ^ 228 := by
  rw [Fintype.card_sigma]
  simp only [digest_low31_coordinate_fiber_card_exact, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    8 * 2 ^ 225 = 2 ^ 3 * 2 ^ 225 := by norm_num
    _ = 2 ^ (3 + 225) := (pow_add 2 3 225).symm
    _ = 2 ^ 228 := by norm_num

/-- Sharp closed-form bound obtained from the exact deployed decoder trace:
at most one of eight word positions carries the fixed fourth-limb target. -/
theorem challenge_completion_fiber_card_le_two_pow_228 (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    challengeCompletionFiberCard id blockPrefix value ≤ 2 ^ 228 := by
  unfold challengeCompletionFiberCard
  calc
    Fintype.card
        {output : Digest256 //
          challengeCompletionDecode id blockPrefix output = some value} ≤
        Fintype.card
          (Σ slot : Fin 8,
            {output : Digest256 //
              low31Candidate (digestWordsEquiv output slot) =
                qm31FourthLow31 value}) :=
      Fintype.card_le_of_injective
        (completionFiberEmbedding id blockPrefix value)
        (completionFiberEmbedding id blockPrefix value).injective
    _ = 2 ^ 228 := completion_target_sigma_card_exact value

theorem challenge_completion_fiber_cap_le_two_pow_228 (id : ChallengeId) :
    challengeCompletionFiberCap id ≤ 2 ^ 228 := by
  classical
  unfold challengeCompletionFiberCap
  apply Finset.sup_le
  intro blockPrefix _blockPrefixMember
  apply Finset.sup_le
  intro value _valueMember
  exact challenge_completion_fiber_card_le_two_pow_228 id blockPrefix value

theorem challenge_completion_fiber_card_le_cap (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    challengeCompletionFiberCard id blockPrefix value ≤
      challengeCompletionFiberCap id := by
  classical
  have valueBound :
      challengeCompletionFiberCard id blockPrefix value ≤
        Finset.univ.sup (fun candidate : Qm31Bytes =>
          challengeCompletionFiberCard id blockPrefix candidate) :=
    Finset.le_sup (s := Finset.univ)
      (f := fun candidate : Qm31Bytes =>
        challengeCompletionFiberCard id blockPrefix candidate) (by simp)
  have prefixBound :
      Finset.univ.sup (fun candidate : Qm31Bytes =>
          challengeCompletionFiberCard id blockPrefix candidate) ≤
        challengeCompletionFiberCap id := by
    unfold challengeCompletionFiberCap
    exact Finset.le_sup (s := Finset.univ)
      (f := fun
        candidate : BoundedBlockPrefix
          (samplerBlockCap (samplerMode id)) =>
          Finset.univ.sup fun value : Qm31Bytes =>
            challengeCompletionFiberCard id candidate value) (by simp)
  exact valueBound.trans prefixBound

/-- No decoder fiber can contain more raw blocks than the complete deployed
256-bit output space.  This is a sanity bound, not the intended security
estimate. -/
theorem challenge_completion_fiber_cap_le_full_space (id : ChallengeId) :
    challengeCompletionFiberCap id ≤ 2 ^ 256 := by
  classical
  unfold challengeCompletionFiberCap
  apply Finset.sup_le
  intro blockPrefix _blockPrefixMember
  apply Finset.sup_le
  intro value _valueMember
  unfold challengeCompletionFiberCard
  exact (Fintype.card_subtype_le
    (fun output : Digest256 =>
      challengeCompletionDecode id blockPrefix output = some value)).trans_eq
        deployed_digest_256_cardinality

/-- Exact uniform probability of one concrete deployed completion fiber. -/
theorem uniform_challenge_completion_fiber_probability_exact
    (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    uniformRawDigestLaw.toOuterMeasure
        (decodedFiber (challengeCompletionDecode id blockPrefix) (some value)) =
      (challengeCompletionFiberCard id blockPrefix value : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  exact uniform_decoded_fiber_probability_exact
    (challengeCompletionDecode id blockPrefix) (some value)

/-- First-principles upper bound for an unqueried output block that must
complete the live bounded sampler with one fixed decoded value. -/
theorem uniform_challenge_completion_fiber_probability_le_cap
    (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    uniformRawDigestLaw.toOuterMeasure
        (decodedFiber (challengeCompletionDecode id blockPrefix) (some value)) ≤
      (challengeCompletionFiberCap id : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  rw [uniform_challenge_completion_fiber_probability_exact]
  apply ENNReal.div_le_div_right
  exact_mod_cast challenge_completion_fiber_card_le_cap id blockPrefix value

/-- Closed-form fallback charge for one fixed decoded challenge completion.
This is `2^228 / 2^256`; it is intentionally not asserted to be needed when
an operational output-oblivious replay lemma applies. -/
theorem uniform_challenge_completion_fiber_probability_le_two_pow_228
    (id : ChallengeId)
    (blockPrefix : BoundedBlockPrefix (samplerBlockCap (samplerMode id)))
    (value : Qm31Bytes) :
    uniformRawDigestLaw.toOuterMeasure
        (decodedFiber (challengeCompletionDecode id blockPrefix) (some value)) ≤
      ((2 : ENNReal) ^ 228) / ((2 : ENNReal) ^ 256) := by
  rw [uniform_challenge_completion_fiber_probability_exact]
  apply ENNReal.div_le_div_right
  exact_mod_cast challenge_completion_fiber_card_le_two_pow_228
    id blockPrefix value

/-- Sum of the exact per-occurrence caps in deployed challenge order.  The
list contains 36 entries, including both circle samples and all four alpha
rounds; q16 is deliberately not folded into this coefficient. -/
noncomputable def deployedChallengePredictionFiberCoefficient : Nat :=
  (deployedChallengeIds.map challengeCompletionFiberCap).sum

theorem deployed_challenge_prediction_coefficient_has_36_terms :
    (deployedChallengeIds.map challengeCompletionFiberCap).length = 36 := by
  simp [deployed_challenge_occurrence_count]

theorem deployed_challenge_prediction_coefficient_le_trivial_full_spaces :
    deployedChallengePredictionFiberCoefficient ≤ 36 * (2 ^ 256) := by
  unfold deployedChallengePredictionFiberCoefficient
  calc
    (deployedChallengeIds.map challengeCompletionFiberCap).sum ≤
        (deployedChallengeIds.map fun _ => 2 ^ 256).sum := by
      apply List.sum_le_sum
      intro id _idMember
      exact challenge_completion_fiber_cap_le_full_space id
    _ = 36 * (2 ^ 256) := by
      simp [deployed_challenge_occurrence_count]

theorem deployed_challenge_prediction_coefficient_le_36_mul_two_pow_228 :
    deployedChallengePredictionFiberCoefficient ≤ 36 * (2 ^ 228) := by
  unfold deployedChallengePredictionFiberCoefficient
  calc
    (deployedChallengeIds.map challengeCompletionFiberCap).sum ≤
        (deployedChallengeIds.map fun _ => 2 ^ 228).sum := by
      apply List.sum_le_sum
      intro id _idMember
      exact challenge_completion_fiber_cap_le_two_pow_228 id
    _ = 36 * (2 ^ 228) := by
      simp [deployed_challenge_occurrence_count]

#print axioms boundedBlockPrefix_length_lt_cap
#print axioms challenge_completion_fixes_one_low31_coordinate
#print axioms challenge_completion_fiber_card_le_two_pow_228
#print axioms challenge_completion_fiber_cap_le_two_pow_228
#print axioms challenge_completion_fiber_card_le_cap
#print axioms challenge_completion_fiber_cap_le_full_space
#print axioms uniform_challenge_completion_fiber_probability_exact
#print axioms uniform_challenge_completion_fiber_probability_le_cap
#print axioms uniform_challenge_completion_fiber_probability_le_two_pow_228
#print axioms deployed_challenge_prediction_coefficient_has_36_terms
#print axioms deployed_challenge_prediction_coefficient_le_trivial_full_spaces
#print axioms deployed_challenge_prediction_coefficient_le_36_mul_two_pow_228

end

end AspisK1.V7Tag73DeployedDecoderFiberCap
