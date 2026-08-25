import AspisFormal.K1.V7Tag73SamplerDecoder

/-!
# Exact stopping behavior of the deployed Tag-73 M31 decoder

These lemmas expose the facts used by the source bridge without adding a
probabilistic or cryptographic premise: a limb stops at its first canonical
31-bit candidate, failure means that all eight allowed candidates rejected,
and four successful limbs consume at most thirty-two words (four blocks).
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SamplerDecoderExact

open AspisK1.V7Tag73SamplerDecoder

def RejectedWord (word : Nat) : Prop :=
  maskedM31 word = m31Prime

/-- A successful limb decode has a unique rejected prefix followed by the
first accepted word.  `restWords` is exactly the untouched suffix. -/
theorem decodeLimb_success_first_accepted
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    ∃ rejected accepted rest,
      words = rejected ++ accepted :: rest ∧
      rejected.length < fuel ∧
      (∀ word ∈ rejected, RejectedWord word) ∧
      ¬ RejectedWord accepted ∧
      decoded.value = maskedM31 accepted ∧
      decoded.restWords = rest ∧
      decoded.attemptsUsed = rejected.length + 1 := by
  induction fuel generalizing words decoded with
  | zero => simp [decodeLimb] at run
  | succ fuel ih =>
      cases words with
      | nil => simp [decodeLimb] at run
      | cons word rest =>
          by_cases rejected : RejectedWord word
          · simp only [decodeLimb, RejectedWord] at rejected run
            rw [if_pos rejected] at run
            cases tailRun : decodeLimb fuel rest with
            | none => simp [tailRun] at run
            | some tailDecoded =>
                simp only [tailRun, Option.some.injEq] at run
                subst decoded
                obtain ⟨rejectedPrefix, accepted, suffix, wordsEq, prefixLt,
                  prefixRejected, acceptedCanonical, valueEq, restEq,
                  attemptsEq⟩ := ih rest tailDecoded tailRun
                refine ⟨word :: rejectedPrefix, accepted, suffix, ?_, ?_, ?_,
                  acceptedCanonical, valueEq, restEq, ?_⟩
                · simp [wordsEq]
                · simp
                  omega
                · intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rejected
                  · exact prefixRejected candidate member
                · simp [attemptsEq]
          · simp only [decodeLimb, RejectedWord] at rejected run
            rw [if_neg rejected] at run
            simp only [Option.some.injEq] at run
            subst decoded
            exact ⟨[], word, rest, by simp, by simp, by simp,
              rejected, rfl, rfl, by simp⟩

/-- Conversely, an explicitly rejected prefix shorter than the fuel followed
by a canonical word determines the exact successful decoder result. -/
theorem decodeLimb_of_first_accepted
    (rejected : List Nat) (accepted : Nat) (rest : List Nat)
    (extraFuel : Nat)
    (prefixRejected : ∀ word ∈ rejected, RejectedWord word)
    (acceptedCanonical : ¬ RejectedWord accepted) :
    decodeLimb (rejected.length + 1 + extraFuel)
        (rejected ++ accepted :: rest) =
      some
        { value := maskedM31 accepted
          restWords := rest
          attemptsUsed := rejected.length + 1 } := by
  induction rejected generalizing extraFuel with
  | nil =>
      have acceptedNe : maskedM31 accepted ≠ m31Prime := by
        simpa [RejectedWord] using acceptedCanonical
      simp only [List.length_nil, List.nil_append, Nat.zero_add, Nat.one_add]
      simp [decodeLimb, acceptedNe]
  | cons word tail ih =>
      have headRejected : RejectedWord word :=
        prefixRejected word (by simp)
      have tailRejected : ∀ candidate ∈ tail, RejectedWord candidate := by
        intro candidate member
        exact prefixRejected candidate (by simp [member])
      simp only [List.length_cons, List.cons_append, Nat.add_assoc,
        Nat.succ_add, decodeLimb, RejectedWord] at headRejected ⊢
      rw [if_pos headRejected]
      have fuelEq : tail.length + (extraFuel + 1) =
          tail.length + 1 + extraFuel := by omega
      rw [fuelEq, ih (extraFuel := extraFuel) tailRejected]

theorem decodeLimb_attempts_positive
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    0 < decoded.attemptsUsed := by
  obtain ⟨rejected, accepted, rest, wordsEq, prefixLt, prefixRejected,
    acceptedCanonical, valueEq, restEq, attemptsEq⟩ :=
    decodeLimb_success_first_accepted fuel words decoded run
  omega

theorem decodeLimb_attempts_le_fuel
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    decoded.attemptsUsed ≤ fuel := by
  obtain ⟨rejected, accepted, rest, wordsEq, prefixLt, prefixRejected,
    acceptedCanonical, valueEq, restEq, attemptsEq⟩ :=
    decodeLimb_success_first_accepted fuel words decoded run
  omega

theorem decodeLimb_length_accounting
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    decoded.attemptsUsed + decoded.restWords.length = words.length := by
  obtain ⟨rejected, accepted, rest, wordsEq, prefixLt, prefixRejected,
    acceptedCanonical, valueEq, restEq, attemptsEq⟩ :=
    decodeLimb_success_first_accepted fuel words decoded run
  rw [restEq, attemptsEq, wordsEq]
  simp only [List.length_append, List.length_cons]
  omega

theorem decodeLimb_value_canonical
    (fuel : Nat) (words : List Nat) (decoded : LimbDecode)
    (run : decodeLimb fuel words = some decoded) :
    decoded.value < m31Prime := by
  obtain ⟨rejected, accepted, rest, wordsEq, prefixLt, prefixRejected,
    acceptedCanonical, valueEq, restEq, attemptsEq⟩ :=
    decodeLimb_success_first_accepted fuel words decoded run
  rw [valueEq]
  have bounded := maskedM31_lt_modulus accepted
  unfold RejectedWord at acceptedCanonical
  unfold m31Prime at acceptedCanonical ⊢
  unfold m31MaskModulus at bounded
  norm_num at acceptedCanonical bounded ⊢
  omega

/-- With at least `fuel` available words, exhaustion is exactly rejection of
all first `fuel` candidates. -/
theorem decodeLimb_none_iff_take_all_rejected
    (fuel : Nat) (words : List Nat) (enough : fuel ≤ words.length) :
    decodeLimb fuel words = none ↔
      ∀ word ∈ words.take fuel, RejectedWord word := by
  induction fuel generalizing words with
  | zero => simp [decodeLimb]
  | succ fuel ih =>
      cases words with
      | nil => simp at enough
      | cons word rest =>
          have enoughTail : fuel ≤ rest.length := by
            simpa using enough
          by_cases rejected : RejectedWord word
          · have rejectedEq : maskedM31 word = m31Prime := rejected
            simp only [decodeLimb]
            rw [if_pos rejectedEq]
            have matchNone :
                (match decodeLimb fuel rest with
                  | none => none
                  | some decoded =>
                      some { decoded with
                        attemptsUsed := decoded.attemptsUsed + 1 }) = none ↔
                  decodeLimb fuel rest = none := by
              cases decodeLimb fuel rest <;> simp
            exact matchNone.trans <|
              (ih rest enoughTail).trans (by simp [rejected])
          · have acceptedNe : maskedM31 word ≠ m31Prime := by
              simpa [RejectedWord] using rejected
            simp [decodeLimb, acceptedNe, rejected]

theorem decodeLimb_eight_exhaustion
    (words : List Nat) (enough : 8 ≤ words.length) :
    decodeLimb 8 words = none ↔
      ∀ word ∈ words.take 8, maskedM31 word = m31Prime := by
  simpa [RejectedWord] using
    decodeLimb_none_iff_take_all_rejected 8 words enough

/-- Every successful `count`-limb decode returns exactly `count` canonical
limbs and consumes between `count` and `8*count` words. -/
theorem decodeLimbs_success_bounds
    (count : Nat) (words : List Nat) (decoded : FourLimbDecode)
    (run : decodeLimbs count words = some decoded) :
    decoded.limbs.length = count ∧
      decoded.wordsUsed + decoded.restWords.length = words.length ∧
      count ≤ decoded.wordsUsed ∧
      decoded.wordsUsed ≤ 8 * count ∧
      ∀ limb ∈ decoded.limbs, limb < m31Prime := by
  induction count generalizing words decoded with
  | zero =>
      simp [decodeLimbs] at run
      subst decoded
      simp
  | succ count ih =>
      unfold decodeLimbs at run
      cases firstRun : decodeLimb 8 words with
      | none => simp [firstRun] at run
      | some first =>
          cases restRun : decodeLimbs count first.restWords with
          | none => simp [firstRun, restRun] at run
          | some tail =>
              simp [firstRun, restRun] at run
              subst decoded
              obtain ⟨tailLength, tailAccounting, tailLower, tailUpper,
                tailCanonical⟩ := ih first.restWords tail restRun
              have firstPositive := decodeLimb_attempts_positive 8 words first firstRun
              have firstUpper := decodeLimb_attempts_le_fuel 8 words first firstRun
              have firstAccounting := decodeLimb_length_accounting 8 words first firstRun
              have firstCanonical := decodeLimb_value_canonical 8 words first firstRun
              change
                (first.value :: tail.limbs).length = count + 1 ∧
                  (first.attemptsUsed + tail.wordsUsed) +
                      tail.restWords.length = words.length ∧
                  count + 1 ≤ first.attemptsUsed + tail.wordsUsed ∧
                  first.attemptsUsed + tail.wordsUsed ≤ 8 * (count + 1) ∧
                  ∀ limb ∈ first.value :: tail.limbs, limb < m31Prime
              constructor
              · simp [tailLength]
              constructor
              · omega
              constructor
              · omega
              constructor
              · omega
              · intro limb member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact firstCanonical
                · exact tailCanonical limb member

theorem decodeFourLimbs_word_cap
    (words : List Nat) (decoded : FourLimbDecode)
    (run : decodeLimbs 4 words = some decoded) :
    decoded.limbs.length = 4 ∧
      4 ≤ decoded.wordsUsed ∧ decoded.wordsUsed ≤ 32 ∧
      ∀ limb ∈ decoded.limbs, limb < m31Prime := by
  obtain ⟨length, accounting, lower, upper, canonical⟩ :=
    decodeLimbs_success_bounds 4 words decoded run
  norm_num at upper
  exact ⟨length, lower, upper, canonical⟩

#print axioms decodeLimb_success_first_accepted
#print axioms decodeLimb_of_first_accepted
#print axioms decodeLimb_eight_exhaustion
#print axioms decodeFourLimbs_word_cap

end AspisK1.V7Tag73SamplerDecoderExact
