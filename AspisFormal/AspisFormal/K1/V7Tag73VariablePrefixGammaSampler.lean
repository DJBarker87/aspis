import AspisFormal.K1.V7Tag73RawNonzeroSamplerFactorization
import AspisFormal.K1.V7Tag73SamplerExactValue
import AspisFormal.K1.V7Tag73SemanticTranscriptBridge

/-!
# Exact variable-prefix Tag-73 gamma sampler

The production nonzero wrapper supplies at most twelve duplex blocks and
stops after the first ordinary QM31 call which returns a nonzero value.  In
particular, an ordinary call which is never reached need not decode.  This
file keeps that distinction explicit.

The first part states the stopping semantics on one chronological twelve
block tape, directly through `decodeNonzeroPrefix`.  It then retains the
literal stopping index and proves that the three branches are disjoint and
cover every successful production run.  The final note isolates the still
missing adaptive finite reindex needed for an exact product factorization;
no fixed four-block-attempt model is substituted for that proof.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73VariablePrefixGammaSampler

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerDecoderExact
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Flat chronological production tape -/

/-- Twelve possible squeeze outputs and their paired duplex-advance answers.
The execution reads only a prefix; the remaining coordinates are fixed ghost
randomness, not additional successful sampler calls. -/
abbrev TotalGammaDuplexTape :=
  (Fin 12 → Digest256) × (Fin 12 → Digest256)

def gammaOutputBlocks (tape : TotalGammaDuplexTape) : List Digest256 :=
  List.ofFn tape.1

/-- Literal production outer loop on the full possible output tape.  This is
`decodeNonzeroPrefix`, rather than `decodeNonzeroExact`: a successful stopping
prefix is allowed to leave an unread suffix. -/
def runGammaPrefix
    (tape : TotalGammaDuplexTape) : Option OrdinaryPrefixDecode :=
  decodeNonzeroPrefix 3 (gammaOutputBlocks tape)

def GammaPrefixSucceeds (tape : TotalGammaDuplexTape) : Prop :=
  (runGammaPrefix tape).isSome

instance (tape : TotalGammaDuplexTape) : Decidable (GammaPrefixSucceeds tape) := by
  unfold GammaPrefixSucceeds
  infer_instance

abbrev SuccessfulGammaPrefixTape :=
  {tape : TotalGammaDuplexTape // GammaPrefixSucceeds tape}

/-! ## Exact locality of the bounded word machine -/

/-- A successful limb decoder can be rerun on exactly the words it consumed;
the returned value and attempt count are unchanged and the remaining word
list is empty. -/
theorem decodeLimb_take_attemptsUsed
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    decodeLimb fuel (words.take decoded.attemptsUsed) =
      some { decoded with restWords := [] } := by
  obtain ⟨rejected, accepted, rest, wordsEq, rejectedLt,
      prefixRejected, acceptedCanonical, valueEq, restEq, attemptsEq⟩ :=
    decodeLimb_success_first_accepted fuel words decoded run
  let extraFuel := fuel - (rejected.length + 1)
  have fuelEq : rejected.length + 1 + extraFuel = fuel := by
    dsimp [extraFuel]
    omega
  have takeEq :
      words.take decoded.attemptsUsed = rejected ++ [accepted] := by
    rw [wordsEq, attemptsEq]
    simpa using
      (List.take_append_length (l₁ := rejected ++ [accepted]) (l₂ := rest))
  have exactRun := decodeLimb_of_first_accepted rejected accepted []
    extraFuel prefixRejected acceptedCanonical
  rw [fuelEq] at exactRun
  rw [takeEq]
  rw [exactRun]
  congr
  rcases decoded with ⟨decodedValue, decodedRest, decodedAttempts⟩
  simp_all
  omega

/-- A successful multi-limb decoder depends on exactly its `wordsUsed`
prefix.  This is the trimming lemma needed to route short ordinary attempts
without asking any unread word to decode. -/
theorem decodeLimbs_take_wordsUsed
    (count : Nat) (words : List Nat) (decoded : FourLimbDecode)
    (run : decodeLimbs count words = some decoded) :
    decodeLimbs count (words.take decoded.wordsUsed) =
      some { decoded with restWords := [] } := by
  induction count generalizing words decoded with
  | zero =>
      simp only [decodeLimbs, Option.some.injEq] at run
      subst decoded
      rfl
  | succ count ih =>
      cases firstRun : decodeLimb 8 words with
      | none => simp [decodeLimbs, firstRun] at run
      | some first =>
          cases tailRun : decodeLimbs count first.restWords with
          | none => simp [decodeLimbs, firstRun, tailRun] at run
          | some tail =>
              have decodedEq :
                  { limbs := first.value :: tail.limbs
                    restWords := tail.restWords
                    wordsUsed := first.attemptsUsed + tail.wordsUsed } =
                    decoded := by
                apply Option.some.inj
                simpa [decodeLimbs, firstRun, tailRun] using run
              subst decoded
              obtain ⟨rejected, accepted, rest, wordsEq, rejectedLt,
                  prefixRejected, acceptedCanonical, valueEq, restEq,
                  attemptsEq⟩ :=
                decodeLimb_success_first_accepted 8 words first firstRun
              have trimmedTail := ih first.restWords tail tailRun
              have restTakeEq :
                  first.restWords.take tail.wordsUsed =
                    rest.take tail.wordsUsed := by rw [restEq]
              have takeEq :
                  words.take (first.attemptsUsed + tail.wordsUsed) =
                    rejected ++ accepted :: rest.take tail.wordsUsed := by
                rw [wordsEq, attemptsEq]
                simp [List.take_add, Nat.add_assoc]
              let extraFuel := 8 - (rejected.length + 1)
              have fuelEq : rejected.length + 1 + extraFuel = 8 := by
                dsimp [extraFuel]
                omega
              have firstTrimmed := decodeLimb_of_first_accepted rejected
                accepted (rest.take tail.wordsUsed) extraFuel
                prefixRejected acceptedCanonical
              rw [fuelEq] at firstTrimmed
              rw [takeEq]
              simp [decodeLimbs, firstTrimmed]
              rw [← restTakeEq, trimmedTail]
              simp [valueEq, attemptsEq]

/-- Flattening fixed-size digest blocks commutes with taking a block prefix.
Each block contributes exactly eight chronological little-endian words. -/
theorem flattenedWords_take_blocks (blocks : List Digest256) (count : Nat) :
    flattenedWords (blocks.take count) =
      (flattenedWords blocks).take (8 * count) := by
  induction blocks generalizing count with
  | nil => simp [flattenedWords]
  | cons block rest ih =>
      cases count with
      | zero => simp [flattenedWords]
      | succ count =>
          simp only [List.take_succ_cons, flattenedWords, List.flatMap_cons]
          change blockWords block ++ flattenedWords (rest.take count) =
            (blockWords block ++ flattenedWords rest).take (8 * (count + 1))
          rw [ih]
          calc
            blockWords block ++ (flattenedWords rest).take (8 * count) =
                (blockWords block ++ flattenedWords rest).take
                  ((blockWords block).length + 8 * count) :=
              (List.take_length_add_append (l₁ := blockWords block)
                (l₂ := flattenedWords rest) (8 * count)).symm
            _ = (blockWords block ++ flattenedWords rest).take
                  (8 * (count + 1)) := by
              rw [blockWords_length]
              have arithmetic : 8 + 8 * count = 8 * (count + 1) := by
                omega
              rw [arithmetic]

/-- One ordinary attempt can be rerun on exactly its consumed block prefix.
Unused words in the final consumed block remain present, while every later
block is observationally irrelevant and removed. -/
theorem decodeOrdinaryPrefix_take_blocksUsed
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    decodeOrdinaryPrefix (blocks.take decoded.blocksUsed) =
      some { decoded with remainingBlocks := [] } := by
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
                blocksNeededForWords limbs.wordsUsed ≤ (block :: rest).length
          · have decodedEq :
                { value := encodeQm31Limbs limbs.limbs
                  limbs := limbs.limbs
                  wordsUsed := limbs.wordsUsed
                  blocksUsed := blocksNeededForWords limbs.wordsUsed
                  remainingBlocks := (block :: rest).drop
                    (blocksNeededForWords limbs.wordsUsed) } = decoded := by
              have simplified := run
              simp [decodeOrdinaryPrefix, limbsRun, valid] at simplified
              exact simplified.2
            subst decoded
            let used := blocksNeededForWords limbs.wordsUsed
            let fullWords := flattenedWords (block :: rest)
            let consumedWords := flattenedWords ((block :: rest).take used)
            have wordsFit : limbs.wordsUsed ≤ 8 * used := by
              have division := Nat.div_add_mod (limbs.wordsUsed + 7) 8
              have remainder : (limbs.wordsUsed + 7) % 8 < 8 :=
                Nat.mod_lt _ (by norm_num)
              dsimp [used, blocksNeededForWords]
              omega
            have consumedWordLength : consumedWords.length = 8 * used := by
              dsimp [consumedWords]
              rw [flattenedWords_length, List.length_take_of_le valid.2.2]
            have consumedTake :
                consumedWords.take limbs.wordsUsed =
                  fullWords.take limbs.wordsUsed := by
              dsimp [consumedWords, fullWords]
              rw [flattenedWords_take_blocks, List.take_take]
              simp [Nat.min_eq_left wordsFit]
            have trimmed := decodeLimbs_take_wordsUsed 4 fullWords limbs
              limbsRun
            have extended := decodeLimbs_append_of_some 4
              (fullWords.take limbs.wordsUsed)
              (consumedWords.drop limbs.wordsUsed)
              { limbs with restWords := [] } trimmed
            have reconstructed :
                fullWords.take limbs.wordsUsed ++
                    consumedWords.drop limbs.wordsUsed = consumedWords := by
              rw [← consumedTake]
              exact List.take_append_drop limbs.wordsUsed consumedWords
            rw [reconstructed] at extended
            have consumedNonempty : (block :: rest).take used ≠ [] := by
              intro empty
              have lengthZero := congrArg List.length empty
              rw [List.length_take_of_le valid.2.2] at lengthZero
              dsimp [used] at lengthZero
              omega
            have consumedLength : ((block :: rest).take used).length = used :=
              List.length_take_of_le valid.2.2
            dsimp [consumedWords] at extended
            simp only [appendFourLimbRest, List.nil_append] at extended
            cases consumed : (block :: rest).take used with
            | nil => exact False.elim (consumedNonempty consumed)
            | cons head tail =>
                rw [consumed] at extended consumedLength
                simp [decodeOrdinaryPrefix, extended, consumedLength,
                  used, valid]
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid run.1)

/-- Every successful outer-prefix run has a literal consumed block prefix on
which the same bounded outer machine returns with no remainder.  This theorem
does not inspect or decode the unread suffix. -/
theorem decodeNonzeroPrefix_exact_consumed
    (attempts : Nat) (blocks : List Digest256)
    (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix attempts blocks = some decoded) :
    ∃ consumed : List Digest256,
      blocks = consumed ++ decoded.remainingBlocks ∧
      decodeNonzeroPrefix attempts consumed =
        some { decoded with remainingBlocks := [] } := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeNonzeroPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeNonzeroPrefix, firstRun] at run
      | some first =>
          let firstConsumed := blocks.take first.blocksUsed
          have firstExact :
              decodeOrdinaryPrefix firstConsumed =
                some { first with remainingBlocks := [] } := by
            exact decodeOrdinaryPrefix_take_blocksUsed blocks first firstRun
          have firstSplit :
              blocks = firstConsumed ++ first.remainingBlocks := by
            exact (decodeOrdinaryPrefix_take_remaining blocks first
              firstRun).symm
          by_cases zero : first.value = zeroBytes 16
          · have recursive :
                decodeNonzeroPrefix attempts first.remainingBlocks =
                  some decoded := by
              simpa [decodeNonzeroPrefix, firstRun, zero] using run
            obtain ⟨tailConsumed, tailSplit, tailExact⟩ :=
              ih first.remainingBlocks decoded recursive
            have firstExtended := decodeOrdinaryPrefix_append_of_some
              firstConsumed tailConsumed
              { first with remainingBlocks := [] } firstExact
            have firstExtendedExact :
                decodeOrdinaryPrefix (firstConsumed ++ tailConsumed) =
                  some { first with remainingBlocks := tailConsumed } := by
              simpa [appendOrdinaryRemaining] using firstExtended
            refine ⟨firstConsumed ++ tailConsumed, ?_, ?_⟩
            · calc
                blocks = firstConsumed ++ first.remainingBlocks := firstSplit
                _ = firstConsumed ++
                    (tailConsumed ++ decoded.remainingBlocks) := by
                      rw [tailSplit]
                _ = (firstConsumed ++ tailConsumed) ++
                    decoded.remainingBlocks := by rw [List.append_assoc]
            · simpa [decodeNonzeroPrefix, firstExtendedExact, zero]
                using tailExact
          · have decodedEq : first = decoded := by
              simpa [decodeNonzeroPrefix, firstRun, zero] using run
            subst decoded
            refine ⟨firstConsumed, firstSplit, ?_⟩
            simp [decodeNonzeroPrefix, firstExact, zero]

/-- A successful nonzero prefix leaves exactly a suffix of the supplied block
list.  The prefix is nonempty because at least one ordinary call ran. -/
theorem decodeNonzeroPrefix_consumed_prefix
    (attempts : Nat) (blocks : List Digest256)
    (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix attempts blocks = some decoded) :
    ∃ consumed : List Digest256,
      blocks = consumed ++ decoded.remainingBlocks ∧ consumed ≠ [] := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeNonzeroPrefix] at run
  | succ attempts ih =>
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp [decodeNonzeroPrefix, firstRun] at run
      | some first =>
          have firstSplit :=
            decodeOrdinaryPrefix_take_remaining blocks first firstRun
          by_cases zero : first.value = zeroBytes 16
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            obtain ⟨tail, tailSplit, tailNonempty⟩ :=
              ih first.remainingBlocks decoded run
            refine ⟨blocks.take first.blocksUsed ++ tail, ?_, ?_⟩
            · calc
                blocks = blocks.take first.blocksUsed ++
                    first.remainingBlocks := firstSplit.symm
                _ = (blocks.take first.blocksUsed ++ tail) ++
                    decoded.remainingBlocks := by
                      rw [tailSplit, List.append_assoc]
            · have firstNonempty : blocks.take first.blocksUsed ≠ [] := by
                have positive : 0 < first.blocksUsed := by
                  obtain ⟨before, accepted, after, decomposition, wordsUsed,
                      limbCount, finalLimb, value, blocksUsed, remaining,
                      blocksUsedLe⟩ :=
                    decodeOrdinaryPrefix_fourth_limb_trace blocks first firstRun
                  rw [blocksUsed]
                  unfold blocksNeededForWords
                  omega
                intro empty
                have lengthZero := congrArg List.length empty
                simp at lengthZero
                have blocksNonempty :=
                  decodeOrdinaryPrefix_blocks_nonempty blocks first firstRun
                rcases lengthZero with usedZero | blocksEmpty
                · omega
                · exact blocksNonempty blocksEmpty
              simp [firstNonempty]
          · simp [decodeNonzeroPrefix, firstRun, zero] at run
            subst decoded
            refine ⟨blocks.take first.blocksUsed, firstSplit.symm, ?_⟩
            obtain ⟨before, accepted, after, decomposition, wordsUsed,
                limbCount, finalLimb, value, blocksUsed, remaining,
                blocksUsedLe⟩ :=
              decodeOrdinaryPrefix_fourth_limb_trace blocks first firstRun
            have positive : 0 < first.blocksUsed := by
              rw [blocksUsed]
              unfold blocksNeededForWords
              omega
            intro empty
            have lengthZero := congrArg List.length empty
            simp at lengthZero
            have blocksNonempty :=
              decodeOrdinaryPrefix_blocks_nonempty blocks first firstRun
            rcases lengthZero with usedZero | blocksEmpty
            · omega
            · exact blocksNonempty blocksEmpty

/-- The offline production decoder reads the consumed prefix and is
observationally independent of every appended output block.  The returned
bytes and already-computed fields are unchanged; only the unread remainder
is extended. -/
theorem runGammaPrefix_unread_suffix_irrelevant
    (blocks suffix : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix 3 blocks = some decoded) :
    decodeNonzeroPrefix 3 (blocks ++ suffix) =
      some (appendOrdinaryRemaining decoded suffix) :=
  decodeNonzeroPrefix_append_of_some 3 blocks suffix decoded run

/-- The value returned by the chronological production prefix is the literal
value decoded at its stopping ordinary branch. -/
theorem runGammaPrefix_returned_value_exact
    (tape : TotalGammaDuplexTape) (decoded : OrdinaryPrefixDecode)
    (run : runGammaPrefix tape = some decoded) :
    ∃ value : QM31Exact,
      decodeTagQM31ExactLE decoded.value = some value ∧
      decoded.value ≠ zeroBytes 16 := by
  obtain ⟨discarded, suffix, decomposition, ordinaryRun⟩ :=
    decodeNonzeroPrefix_ordinary_suffix 3 (gammaOutputBlocks tape) decoded run
  obtain ⟨value, exactValue⟩ :=
    decodeOrdinaryPrefix_value_has_exact_tower_value suffix decoded ordinaryRun
  exact ⟨value, exactValue,
    decodeNonzeroPrefix_value_ne_zero 3 (gammaOutputBlocks tape) decoded run⟩

/-! ## Offline/online production equality -/

/-- The offline prefix run exposes the exact first block count accepted by
the deployed gamma decoder. -/
theorem runGammaPrefix_to_incremental_gamma
    (tape : TotalGammaDuplexTape) (decoded : OrdinaryPrefixDecode)
    (run : runGammaPrefix tape = some decoded) :
    ∃ count : Nat,
      0 < count ∧ count ≤ 12 ∧
      decodeChallengeParameter exactSecureCircleParameterMap .gamma
          ((gammaOutputBlocks tape).take count) = some decoded.value ∧
      ∀ prior, prior < count →
        decodeChallengeParameter exactSecureCircleParameterMap .gamma
          ((gammaOutputBlocks tape).take prior) = none := by
  obtain ⟨consumed, decomposition, exactRun⟩ :=
    decodeNonzeroPrefix_exact_consumed 3 (gammaOutputBlocks tape) decoded run
  have consumedNonempty : consumed ≠ [] := by
    intro empty
    subst consumed
    simp [decodeNonzeroPrefix, decodeOrdinaryPrefix] at exactRun
  have consumedLength : consumed.length ≤ 12 := by
    have totalLength : (gammaOutputBlocks tape).length = 12 := by
      simp [gammaOutputBlocks]
    rw [decomposition] at totalLength
    simp only [List.length_append] at totalLength
    omega
  have takeExact :
      (gammaOutputBlocks tape).take consumed.length = consumed := by
    rw [decomposition]
    exact List.take_append_length
  have accepted :
      decodeChallengeParameter exactSecureCircleParameterMap .gamma consumed =
        some decoded.value := by
    have withinCap : consumed.length ≤ 12 := consumedLength
    simp only [decodeChallengeParameter, samplerMode, decodeNonzeroExact]
    simp [withinCap, exactRun]
  have consumedPositive : 0 < consumed.length := by
    cases consumed with
    | nil => exact False.elim (consumedNonempty rfl)
    | cons head tail => simp
  refine ⟨consumed.length, consumedPositive,
    consumedLength, ?_, ?_⟩
  · simpa [takeExact] using accepted
  · intro prior strict
    have minimalConsumed := decodeChallengeParameter_accepted_is_prefix_minimal
      exactSecureCircleParameterMap .gamma
        consumed decoded.value accepted
          prior strict
    rw [decomposition,
      List.take_append_of_le_length (Nat.le_of_lt strict)]
    exact minimalConsumed

/-- Running fewer duplex blocks returns the chronological prefix of the
outputs returned by any longer run from the same state. -/
theorem squeezeBlocks_outputs_take
    (oracle : HashOracle) (state : MachineState)
    (count total : Nat) (within : count ≤ total) :
    (squeezeBlocks oracle count state).1 =
      (squeezeBlocks oracle total state).1.take count := by
  induction total generalizing count state with
  | zero =>
      have countZero : count = 0 := by omega
      subst count
      rfl
  | succ total ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [squeezeBlocks, List.take_succ_cons, List.cons.injEq,
            true_and]
          exact ih (squeezeBlock oracle state).2 count (by omega)

/-- A twelve-block counterfactual duplex tape whose output half matches the
literal oracle execution reproduces the actual online first-success gamma
sampler.  Only the consumed prefix is run; no unread suffix call is made. -/
theorem runGammaPrefix_matches_sampleChallenge
    (oracle : HashOracle) (state : MachineState)
    (tape : TotalGammaDuplexTape) (decoded : OrdinaryPrefixDecode)
    (run : runGammaPrefix tape = some decoded)
    (outputsExact :
      (squeezeBlocks oracle 12 state).1 = gammaOutputBlocks tape) :
    ∃ count finalState,
      0 < count ∧ count ≤ 12 ∧
      sampleChallenge oracle .gamma state =
        some (decoded.value, finalState) ∧
      squeezeBlocks oracle count state =
        ((gammaOutputBlocks tape).take count, finalState) := by
  obtain ⟨count, positive, within, accepted, minimal⟩ :=
    runGammaPrefix_to_incremental_gamma tape decoded run
  let finalState := (squeezeBlocks oracle count state).2
  have outputPrefix :
      (squeezeBlocks oracle count state).1 =
        (gammaOutputBlocks tape).take count := by
    rw [squeezeBlocks_outputs_take oracle state count 12 within, outputsExact]
  have squeezed :
      squeezeBlocks oracle count state =
        ((gammaOutputBlocks tape).take count, finalState) := by
    apply Prod.ext
    · exact outputPrefix
    · rfl
  have outputLength :
      ((gammaOutputBlocks tape).take count).length = count := by
    exact List.length_take_of_le (by
      simpa [gammaOutputBlocks] using within)
  have outputNonempty : (gammaOutputBlocks tape).take count ≠ [] := by
    intro empty
    have lengthZero := congrArg List.length empty
    rw [outputLength] at lengthZero
    simp at lengthZero
    omega
  have outputWithin :
      ((gammaOutputBlocks tape).take count).length ≤ 12 := by
    rw [outputLength]
    exact within
  have outputMinimal : ∀ priorCount,
      priorCount < ((gammaOutputBlocks tape).take count).length →
      decodeChallengeParameter exactSecureCircleParameterMap .gamma
        ([] ++ ((gammaOutputBlocks tape).take count).take priorCount) = none := by
    intro priorCount strict
    have strictCount : priorCount < count := by simpa [outputLength] using strict
    have old := minimal priorCount strictCount
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt strictCount)]
      using old
  have squeezedByLength :
      squeezeBlocks oracle ((gammaOutputBlocks tape).take count).length state =
        ((gammaOutputBlocks tape).take count, finalState) := by
    rw [outputLength]
    exact squeezed
  have sampled := sampleChallengeFrom_of_squeezeBlocks oracle .gamma []
    ((gammaOutputBlocks tape).take count) state finalState decoded.value 12
    outputNonempty outputWithin squeezedByLength (by simpa using accepted)
      outputMinimal
  have sampledChallenge :
      sampleChallenge oracle .gamma state =
        some (decoded.value, finalState) := by
    simpa [sampleChallenge, samplerMode, samplerBlockCap] using sampled
  exact ⟨count, finalState, positive, within, sampledChallenge, squeezed⟩

/-! ## Exact stopping index on the flat tape -/

/-- The production decoder with its outer stopping index retained.  Index
zero is the first ordinary call; recursive zero branches increment it. -/
def decodeNonzeroPrefixIndexed : (attempts : Nat) → List Digest256 →
    Option (Fin attempts × OrdinaryPrefixDecode)
  | 0, _ => none
  | attempts + 1, blocks => do
      let decoded ← decodeOrdinaryPrefix blocks
      if decoded.value = zeroBytes 16 then
        (decodeNonzeroPrefixIndexed attempts decoded.remainingBlocks).map
          fun result => (result.1.succ, result.2)
      else
        pure (0, decoded)

/-- Exact recursive witness for the outer nonzero stopping branch.  A `next`
constructor records one literal zero-valued ordinary attempt and its dynamic
remaining-block suffix; `stop` records the first literal nonzero attempt. -/
inductive GammaPrefixTrace :
    (attempts : Nat) → List Digest256 → Fin attempts →
      OrdinaryPrefixDecode → Prop
  | stop
      {attempts : Nat} {blocks : List Digest256}
      {decoded : OrdinaryPrefixDecode}
      (ordinary : decodeOrdinaryPrefix blocks = some decoded)
      (nonzero : decoded.value ≠ zeroBytes 16) :
      GammaPrefixTrace (attempts + 1) blocks 0 decoded
  | next
      {attempts : Nat} {blocks : List Digest256}
      {first decoded : OrdinaryPrefixDecode} {index : Fin attempts}
      (ordinary : decodeOrdinaryPrefix blocks = some first)
      (zero : first.value = zeroBytes 16)
      (tail : GammaPrefixTrace attempts first.remainingBlocks index decoded) :
      GammaPrefixTrace (attempts + 1) blocks index.succ decoded

/-- The indexed executable decoder succeeds exactly when the recursive trace
records the same stopping index and returned ordinary decode. -/
theorem decodeNonzeroPrefixIndexed_iff_trace
    (attempts : Nat) (blocks : List Digest256)
    (index : Fin attempts) (decoded : OrdinaryPrefixDecode) :
    decodeNonzeroPrefixIndexed attempts blocks = some (index, decoded) ↔
      GammaPrefixTrace attempts blocks index decoded := by
  induction attempts generalizing blocks decoded with
  | zero => exact Fin.elim0 index
  | succ attempts ih =>
      constructor
      · intro run
        cases firstRun : decodeOrdinaryPrefix blocks with
        | none => simp [decodeNonzeroPrefixIndexed, firstRun] at run
        | some first =>
            by_cases isZero : first.value = zeroBytes 16
            · cases tailRun :
                decodeNonzeroPrefixIndexed attempts first.remainingBlocks with
              | none =>
                  simp [decodeNonzeroPrefixIndexed, firstRun, isZero,
                    tailRun] at run
              | some tailResult =>
                  rcases tailResult with ⟨tailIndex, tailDecoded⟩
                  have pairEq :
                      (tailIndex.succ, tailDecoded) = (index, decoded) := by
                    apply Option.some.inj
                    simpa [decodeNonzeroPrefixIndexed, firstRun, isZero,
                      tailRun] using run
                  have tailTrace :=
                    (ih first.remainingBlocks tailIndex tailDecoded).mp tailRun
                  cases pairEq
                  exact GammaPrefixTrace.next firstRun isZero
                    tailTrace
            · have pairEq :
                  ((0 : Fin (attempts + 1)), first) = (index, decoded) := by
                apply Option.some.inj
                simpa [decodeNonzeroPrefixIndexed, firstRun, isZero] using run
              cases pairEq
              exact GammaPrefixTrace.stop firstRun isZero
      · intro trace
        cases trace with
        | stop ordinary nonzero =>
            simp [decodeNonzeroPrefixIndexed, ordinary, nonzero]
        | next ordinary isZero tail =>
            have tailRun := (ih _ _ _).mpr tail
            simp [decodeNonzeroPrefixIndexed, ordinary, isZero, tailRun]

/-- Forgetting the stopping index gives exactly the production decoder. -/
theorem decodeNonzeroPrefixIndexed_forget
    (attempts : Nat) (blocks : List Digest256) :
    (decodeNonzeroPrefixIndexed attempts blocks).map Prod.snd =
      decodeNonzeroPrefix attempts blocks := by
  induction attempts generalizing blocks with
  | zero => rfl
  | succ attempts ih =>
      simp only [decodeNonzeroPrefixIndexed, decodeNonzeroPrefix]
      cases firstRun : decodeOrdinaryPrefix blocks with
      | none => simp
      | some first =>
          by_cases zero : first.value = zeroBytes 16
          · simp [zero, Option.map_map, Function.comp_def, ih]
          · simp [zero]

def GammaPrefixStopsAt (index : Fin 3)
    (tape : TotalGammaDuplexTape) : Prop :=
  (decodeNonzeroPrefixIndexed 3 (gammaOutputBlocks tape)).map Prod.fst =
    some index

instance (index : Fin 3) (tape : TotalGammaDuplexTape) :
    Decidable (GammaPrefixStopsAt index tape) := by
  unfold GammaPrefixStopsAt
  infer_instance

/-- The three indexed branches cover every and only successful production
prefix executions. -/
theorem gamma_prefix_success_iff_stopping_branch
    (tape : TotalGammaDuplexTape) :
    GammaPrefixSucceeds tape ↔ ∃ index, GammaPrefixStopsAt index tape := by
  unfold GammaPrefixSucceeds runGammaPrefix GammaPrefixStopsAt
  rw [← decodeNonzeroPrefixIndexed_forget 3 (gammaOutputBlocks tape)]
  cases run : decodeNonzeroPrefixIndexed 3 (gammaOutputBlocks tape) with
  | none => simp
  | some result =>
      rcases result with ⟨index, decoded⟩
      constructor
      · intro _
        exact ⟨index, by simp⟩
      · intro _
        simp

/-- Two successful indexed branches of the same production tape cannot be
different. -/
theorem gamma_prefix_stopping_branches_disjoint
    (tape : TotalGammaDuplexTape) (left right : Fin 3)
    (leftStops : GammaPrefixStopsAt left tape)
    (rightStops : GammaPrefixStopsAt right tape) : left = right := by
  unfold GammaPrefixStopsAt at leftStops rightStops
  rw [leftStops] at rightStops
  exact Option.some.inj rightStops

/-! The remaining exact-product step must use the flat chronological tape.
Three fixed four-block `Tag73RawStream`s are not a production model: after a
short ordinary call the next call starts at `decoded.blocksUsed`, rather than
at a reserved four-block boundary.  The missing finite equivalence must move
each executed call's unused padding into the common unread suffix, prove this
adaptive reindex bijective, and then transport `digestWordsEquiv` and
`successfulOrdinaryRawFactorization` across it.  No routed-product theorem is
claimed here without that proof. -/

#print axioms decodeNonzeroPrefix_consumed_prefix
#print axioms decodeLimb_take_attemptsUsed
#print axioms decodeLimbs_take_wordsUsed
#print axioms flattenedWords_take_blocks
#print axioms decodeOrdinaryPrefix_take_blocksUsed
#print axioms decodeNonzeroPrefix_exact_consumed
#print axioms runGammaPrefix_unread_suffix_irrelevant
#print axioms runGammaPrefix_returned_value_exact
#print axioms runGammaPrefix_to_incremental_gamma
#print axioms squeezeBlocks_outputs_take
#print axioms runGammaPrefix_matches_sampleChallenge
#print axioms decodeNonzeroPrefixIndexed_iff_trace
#print axioms decodeNonzeroPrefixIndexed_forget
#print axioms gamma_prefix_success_iff_stopping_branch
#print axioms gamma_prefix_stopping_branches_disjoint

end

end AspisK1.V7Tag73VariablePrefixGammaSampler
