import AspisFormal.K1.V7Tag73EightRetrySamplerLaw
import AspisFormal.K1.V7Tag73SamplerDecoderExact

/-!
# Word-for-word bridge from the uniform sampler to the deployed decoder

The probability leaf works with mathematical `Fin (2^32)` words.  The
deployed decoder works with their natural-number values.  This file proves
that both eight-retry stopping machines take the same branches, return the
same canonical residues, consume the same words, and leave the same suffix.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73EightRetryDecoderBridge

open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerDecoderExact
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler

def rawWordsToNat (words : List RawWord) : List Nat :=
  words.map Fin.val

@[simp] theorem rawWordsToNat_length (words : List RawWord) :
    (rawWordsToNat words).length = words.length := by
  simp [rawWordsToNat]

@[simp] theorem low31Candidate_val_eq_maskedM31 (word : RawWord) :
    (low31Candidate word : Nat) = maskedM31 word.val := by
  simp [low31Candidate, maskedM31, rawCandidateCount, m31MaskModulus]

theorem rawWordResult_eq_none_iff_rejected (word : RawWord) :
    rawWordResult word = none ↔ maskedM31 word.val = m31Prime := by
  rw [rawWordResult, candidateResult_eq_none_iff]
  constructor
  · intro equal
    have valueEqual := congrArg Fin.val equal
    simpa [rejectedCandidate, m31Modulus, rawCandidateCount, m31Prime]
      using valueEqual
  · intro equal
    apply Fin.ext
    simpa [rejectedCandidate, m31Modulus, rawCandidateCount, m31Prime]
      using equal

def acceptedRawValue (word : RawWord)
    (accepted : maskedM31 word.val ≠ m31Prime) : M31Value :=
  ⟨maskedM31 word.val, by
    have bound := maskedM31_lt_modulus word.val
    norm_num [m31Modulus, rawCandidateCount, m31MaskModulus, m31Prime] at bound accepted ⊢
    omega⟩

theorem rawWordResult_eq_some_acceptedRawValue (word : RawWord)
    (accepted : maskedM31 word.val ≠ m31Prime) :
    rawWordResult word = some (acceptedRawValue word accepted) := by
  have resultNotNone : rawWordResult word ≠ none :=
    mt (rawWordResult_eq_none_iff_rejected word).mp accepted
  obtain ⟨value, result⟩ := Option.ne_none_iff_exists'.mp resultNotNone
  rw [result]
  congr
  apply Fin.ext
  have resultValue : (value : Nat) = maskedM31 word.val := by
    unfold rawWordResult at result
    unfold candidateResult at result
    split at result <;> rename_i h
    · simpa [acceptedValue, low31Candidate_val_eq_maskedM31] using
        (congrArg Fin.val (Option.some.inj result)).symm
    · simp at result
  exact resultValue

theorem consumeFirstSuccess_suffix_length_le
    (fuel : Nat) (words : List RawWord) (value : M31Value)
    (suffix : List RawWord)
    (run : consumeFirstSuccess fuel words = some (value, suffix)) :
    suffix.length ≤ words.length := by
  induction fuel generalizing words with
  | zero => simp [consumeFirstSuccess] at run
  | succ fuel ih =>
      cases words with
      | nil => simp [consumeFirstSuccess] at run
      | cons word rest =>
          cases hword : rawWordResult word with
          | none =>
              simp only [consumeFirstSuccess, hword] at run
              exact (ih rest run).trans (Nat.le_succ _)
          | some head =>
              simp only [consumeFirstSuccess, hword, Option.some.injEq] at run
              rcases run with ⟨rfl, rfl⟩
              exact Nat.le_succ _

theorem runSequentialCallsWithFuel_length_le
    (fuel callCount : Nat) (words : List RawWord)
    (values : Fin callCount → M31Value) (suffix : List RawWord)
    (run : runSequentialCallsWithFuel fuel callCount words =
      some (values, suffix)) :
    suffix.length ≤ words.length := by
  induction callCount generalizing words suffix with
  | zero =>
      simp only [runSequentialCallsWithFuel, Option.some.injEq] at run
      exact Nat.le_of_eq (congrArg (fun result => result.2.length) run).symm
  | succ callCount ih =>
      simp only [runSequentialCallsWithFuel] at run
      cases hhead : consumeFirstSuccess fuel words with
      | none => simp [hhead] at run
      | some head =>
          rcases head with ⟨headValue, rest⟩
          simp only [hhead] at run
          cases htail : runSequentialCallsWithFuel fuel callCount rest with
          | none => simp [htail] at run
          | some tail =>
              rcases tail with ⟨tailValues, tailSuffix⟩
              simp only [htail, Option.some.injEq] at run
              have suffixEq : suffix = tailSuffix :=
                (congrArg (fun result => result.2) run).symm
              rw [suffixEq]
              exact (ih rest tailValues tailSuffix htail).trans
                (consumeFirstSuccess_suffix_length_le fuel words headValue rest hhead)

def limbDecodeOfRawSuccess (input : List RawWord)
    (result : M31Value × List RawWord) : LimbDecode :=
  { value := result.1.val
    restWords := rawWordsToNat result.2
    attemptsUsed := input.length - result.2.length }

/-- Exact one-limb control-flow equality, including the untouched suffix and
attempt count. -/
theorem decodeLimb_rawWordsToNat
    (fuel : Nat) (words : List RawWord) :
    decodeLimb fuel (rawWordsToNat words) =
      (consumeFirstSuccess fuel words).map (limbDecodeOfRawSuccess words) := by
  induction fuel generalizing words with
  | zero => rfl
  | succ fuel ih =>
      cases words with
      | nil => rfl
      | cons word rest =>
          by_cases rejected : maskedM31 word.val = m31Prime
          · have rawRejected : rawWordResult word = none :=
              (rawWordResult_eq_none_iff_rejected word).2 rejected
            simp only [rawWordsToNat, List.map_cons, decodeLimb,
              consumeFirstSuccess, rawRejected]
            rw [if_pos rejected]
            have ihRest := ih rest
            simp only [rawWordsToNat] at ihRest
            rw [ihRest]
            cases htail : consumeFirstSuccess fuel rest with
            | none => rfl
            | some result =>
                rcases result with ⟨value, suffix⟩
                simp only [Option.map_some]
                congr 2
                unfold limbDecodeOfRawSuccess
                simp only [List.length_cons]
                have suffixLe :=
                  consumeFirstSuccess_suffix_length_le fuel rest value suffix htail
                omega
          · have rawAccepted :=
              rawWordResult_eq_some_acceptedRawValue word rejected
            simp only [rawWordsToNat, List.map_cons, decodeLimb,
              consumeFirstSuccess, rawAccepted]
            rw [if_neg rejected]
            simp only [Option.map_some]
            congr 2
            simp

def limbsDecodeOfRawSuccess {count : Nat} (input : List RawWord)
    (result : (Fin count → M31Value) × List RawWord) :
    FourLimbDecode :=
  { limbs := List.ofFn result.1 |>.map Fin.val
    restWords := rawWordsToNat result.2
    wordsUsed := input.length - result.2.length }

/-- Consecutive eight-retry calls are exactly the deployed limb decoder after
converting each mathematical `u32` to its natural value. -/
theorem decodeLimbs_rawWordsToNat (count : Nat) (words : List RawWord) :
    decodeLimbs count (rawWordsToNat words) =
      (runSequentialCallsWithFuel 8 count words).map
        (limbsDecodeOfRawSuccess words) := by
  induction count generalizing words with
  | zero =>
      simp [decodeLimbs, runSequentialCallsWithFuel,
        limbsDecodeOfRawSuccess, rawWordsToNat]
  | succ count ih =>
      simp only [decodeLimbs, runSequentialCallsWithFuel]
      rw [decodeLimb_rawWordsToNat]
      cases hhead : consumeFirstSuccess 8 words with
      | none => rfl
      | some headResult =>
          rcases headResult with ⟨head, rest⟩
          have ihRest := ih rest
          cases htail : runSequentialCallsWithFuel 8 count rest with
          | none =>
              have decodeNone :
                  decodeLimbs count (rawWordsToNat rest) = none := by
                simpa [htail] using ihRest
              simp [limbDecodeOfRawSuccess, decodeNone, htail]
          | some tailResult =>
              rcases tailResult with ⟨tail, suffix⟩
              have decodeSome :
                  decodeLimbs count (rawWordsToNat rest) =
                    some (limbsDecodeOfRawSuccess rest (tail, suffix)) := by
                simpa [htail] using ihRest
              simp [limbDecodeOfRawSuccess, limbsDecodeOfRawSuccess,
                decodeSome, htail]
              have restLe :=
                consumeFirstSuccess_suffix_length_le 8 words head rest hhead
              have suffixLe : suffix.length ≤ rest.length := by
                have runLength :=
                  runSequentialCallsWithFuel_length_le 8 count rest tail suffix htail
                exact runLength
              omega

/-- Four consecutive calls instantiate the deployed Tag-73 shape. -/
theorem decodeFourLimbs_rawWordsToNat (words : List RawWord) :
    decodeLimbs 4 (rawWordsToNat words) =
      (runSequentialCallsWithFuel tag73LimbRetryLimit tag73LimbCount words).map
        (limbsDecodeOfRawSuccess words) := by
  simpa [tag73LimbRetryLimit, tag73LimbCount] using
    decodeLimbs_rawWordsToNat 4 words

#print axioms decodeLimb_rawWordsToNat
#print axioms decodeFourLimbs_rawWordsToNat

end AspisK1.V7Tag73EightRetryDecoderBridge
