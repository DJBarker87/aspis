import AspisFormal.K1.V7Tag73SamplerDecoder
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Exact deployed Tag-73 secure-circle parameter map

This file discharges the algebraic parameter left explicit by
`V7Tag73SamplerDecoder`.  It uses the literal deployed QM31 tower and follows
the Rust control flow in `secure_ood_circle_point_from_parameter`:

1. decode the canonical little-endian QM31 parameter;
2. compute the optimized square and `1 + t^2`;
3. call the non-panicking inverse and reject a singular denominator;
4. only after that, reject `t.im = 0` (the CM31 subfield); and
5. return the canonical encodings of
   `x = (1 - t^2) / (1 + t^2)` and
   `y = (t + t) / (1 + t^2)`.

The order of the two rejection checks is observable for `t = ±i`, so it is
represented by the nested match/if rather than collapsed into a conjunction.
No cryptographic assumption or source-correspondence assumption occurs here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SecureCircleMap

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisV5ComponentCQM31TowerExact

/-! ## Explicit byte-representation seam -/

/-- The exact tower's codec uses mathematical bytes (`Fin 256`), whereas the
Tag-73 transcript uses runtime bytes (`UInt8`). -/
abbrev ExactQm31Bytes :=
  AspisV5ComponentCQM31Representation.QM31Bytes

/-- The concrete, choice-free equivalence between a runtime byte and a
mathematical byte. -/
def tagByteEquivExactByte : UInt8 ≃ Fin 256 :=
  ({ toFun := UInt8.toFin
     invFun := UInt8.ofFin
     left_inv := UInt8.ofFin_toFin
     right_inv := UInt8.toFin_ofFin } : UInt8 ≃ Fin UInt8.size).trans
    (finCongr (by decide : UInt8.size = 256))

def tagQm31BytesToExact (encoded : Qm31Bytes) : ExactQm31Bytes :=
  fun index => tagByteEquivExactByte (encoded index)

def exactQm31BytesToTag (encoded : ExactQm31Bytes) : Qm31Bytes :=
  fun index => tagByteEquivExactByte.symm (encoded index)

@[simp] theorem tagQm31BytesToExact_exactQm31BytesToTag
    (encoded : ExactQm31Bytes) :
    tagQm31BytesToExact (exactQm31BytesToTag encoded) = encoded := by
  funext index
  exact tagByteEquivExactByte.apply_symm_apply (encoded index)

@[simp] theorem exactQm31BytesToTag_tagQm31BytesToExact
    (encoded : Qm31Bytes) :
    exactQm31BytesToTag (tagQm31BytesToExact encoded) = encoded := by
  funext index
  exact tagByteEquivExactByte.symm_apply_apply (encoded index)

/-- Exact-tower decoding with the byte representation made explicit. -/
def decodeTagQM31ExactLE (encoded : Qm31Bytes) : Option QM31Exact :=
  decodeQM31ExactLE (tagQm31BytesToExact encoded)

/-- Exact-tower encoding returned in the transcript's runtime-byte type. -/
def encodeTagQM31ExactLE (value : QM31Exact) : Qm31Bytes :=
  exactQm31BytesToTag (encodeQM31ExactLE value)

theorem decodeTagQM31ExactLE_encodeTagQM31ExactLE (value : QM31Exact) :
    decodeTagQM31ExactLE (encodeTagQM31ExactLE value) = some value := by
  simp [decodeTagQM31ExactLE, encodeTagQM31ExactLE,
    decodeQM31ExactLE_encodeQM31ExactLE]

/-! ## Literal rational-map output -/

/-- Encode the two coordinates obtained after Rust's successful `try_inv`.
The arguments retain the already-computed square and inverse so the enclosing
decoder has the same evaluation order as the source. -/
def encodeExactSecureCirclePoint
    (parameter square inverseDenominator : QM31Exact) :
    SecureCirclePointBytes where
  x := encodeTagQM31ExactLE
    (qm31Karatsuba ((1 : QM31Exact) - square) inverseDenominator)
  y := encodeTagQM31ExactLE
    (qm31Karatsuba (parameter + parameter) inverseDenominator)

@[simp] theorem encodeExactSecureCirclePoint_x
    (parameter square inverseDenominator : QM31Exact) :
    (encodeExactSecureCirclePoint parameter square inverseDenominator).x =
      encodeTagQM31ExactLE
        (qm31Karatsuba ((1 : QM31Exact) - square) inverseDenominator) := by
  rfl

@[simp] theorem encodeExactSecureCirclePoint_y
    (parameter square inverseDenominator : QM31Exact) :
    (encodeExactSecureCirclePoint parameter square inverseDenominator).y =
      encodeTagQM31ExactLE
        (qm31Karatsuba (parameter + parameter) inverseDenominator) := by
  rfl

theorem decode_encodeExactSecureCirclePoint_x
    (parameter square inverseDenominator : QM31Exact) :
    decodeTagQM31ExactLE
        (encodeExactSecureCirclePoint parameter square inverseDenominator).x =
      some (qm31Karatsuba
        ((1 : QM31Exact) - square) inverseDenominator) := by
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _

theorem decode_encodeExactSecureCirclePoint_y
    (parameter square inverseDenominator : QM31Exact) :
    decodeTagQM31ExactLE
        (encodeExactSecureCirclePoint parameter square inverseDenominator).y =
      some (qm31Karatsuba
        (parameter + parameter) inverseDenominator) := by
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _

/-! ## Deployed check order -/

/-- Exact decoded-value helper.  The `qm31TryInv` match syntactically precedes
the `parameter.im` check, matching the Rust `?` followed by the OOD policy. -/
def exactSecureCirclePointFromDecoded (parameter : QM31Exact) :
    Option SecureCirclePointBytes :=
  let square := qm31Square parameter
  let denominator := (1 : QM31Exact) + square
  match qm31TryInv denominator with
  | none => none
  | some inverseDenominator =>
      if parameter.im = (0 : CM31Exact) then
        none
      else
        some (encodeExactSecureCirclePoint
          parameter square inverseDenominator)

/-- A singular denominator is rejected before the subfield condition is
inspected.  In particular this theorem does not require `parameter.im ≠ 0`. -/
theorem exactSecureCirclePointFromDecoded_rejects_singular_first
    (parameter : QM31Exact)
    (singular : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = none) :
    exactSecureCirclePointFromDecoded parameter = none := by
  simp [exactSecureCirclePointFromDecoded, singular]

theorem exactSecureCirclePointFromDecoded_rejects_cm31
    (parameter inverseDenominator : QM31Exact)
    (invertible : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = some inverseDenominator)
    (inSubfield : parameter.im = (0 : CM31Exact)) :
    exactSecureCirclePointFromDecoded parameter = none := by
  simp [exactSecureCirclePointFromDecoded, invertible, inSubfield]

theorem exactSecureCirclePointFromDecoded_success
    (parameter inverseDenominator : QM31Exact)
    (invertible : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = some inverseDenominator)
    (outsideSubfield : parameter.im ≠ (0 : CM31Exact)) :
    exactSecureCirclePointFromDecoded parameter =
      some (encodeExactSecureCirclePoint
        parameter (qm31Square parameter) inverseDenominator) := by
  simp [exactSecureCirclePointFromDecoded, invertible, outsideSubfield]

/-- A successful deployed `try_inv` returns the mathematical field inverse.
This turns the source-form success equation into the usual rational equation
without assuming inversion correctness. -/
theorem successful_qm31TryInv_is_inverse
    (denominator inverseDenominator : QM31Exact)
    (success : qm31TryInv denominator = some inverseDenominator) :
    inverseDenominator = denominator⁻¹ := by
  rw [qm31TryInv_eq] at success
  split at success
  · simp_all
  · exact (Option.some.inj success).symm

/-! ## Byte-level map and decoder record -/

/-- Exact implementation of the sampler decoder's remaining parameter.  A
non-canonical 16-byte field encoding is rejected at the decode step. -/
def exactSecureCircleParameterMap : SecureCircleParameterMap :=
  fun encodedParameter =>
    match decodeTagQM31ExactLE encodedParameter with
    | none => none
    | some parameter => exactSecureCirclePointFromDecoded parameter

theorem exactSecureCircleParameterMap_rejects_noncanonical
    (encodedParameter : Qm31Bytes)
    (invalid : decodeTagQM31ExactLE encodedParameter = none) :
    exactSecureCircleParameterMap encodedParameter = none := by
  simp [exactSecureCircleParameterMap, invalid]

theorem exactSecureCircleParameterMap_rejects_singular
    (encodedParameter : Qm31Bytes) (parameter : QM31Exact)
    (decoded : decodeTagQM31ExactLE encodedParameter = some parameter)
    (singular : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = none) :
    exactSecureCircleParameterMap encodedParameter = none := by
  simp [exactSecureCircleParameterMap, decoded,
    exactSecureCirclePointFromDecoded, singular]

theorem exactSecureCircleParameterMap_rejects_cm31
    (encodedParameter : Qm31Bytes)
    (parameter inverseDenominator : QM31Exact)
    (decoded : decodeTagQM31ExactLE encodedParameter = some parameter)
    (invertible : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = some inverseDenominator)
    (inSubfield : parameter.im = (0 : CM31Exact)) :
    exactSecureCircleParameterMap encodedParameter = none := by
  simp [exactSecureCircleParameterMap, decoded,
    exactSecureCirclePointFromDecoded, invertible, inSubfield]

/-- Exact source-form success equation, including the optimized square and
Karatsuba multiplication used by Rust. -/
theorem exactSecureCircleParameterMap_success
    (encodedParameter : Qm31Bytes)
    (parameter inverseDenominator : QM31Exact)
    (decoded : decodeTagQM31ExactLE encodedParameter = some parameter)
    (invertible : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = some inverseDenominator)
    (outsideSubfield : parameter.im ≠ (0 : CM31Exact)) :
    exactSecureCircleParameterMap encodedParameter =
      some (encodeExactSecureCirclePoint
        parameter (qm31Square parameter) inverseDenominator) := by
  simp [exactSecureCircleParameterMap, decoded,
    exactSecureCirclePointFromDecoded, invertible, outsideSubfield]

theorem exactSecureCircleParameterMap_encode_success
    (parameter inverseDenominator : QM31Exact)
    (invertible : qm31TryInv
      ((1 : QM31Exact) + qm31Square parameter) = some inverseDenominator)
    (outsideSubfield : parameter.im ≠ (0 : CM31Exact)) :
    exactSecureCircleParameterMap (encodeTagQM31ExactLE parameter) =
      some (encodeExactSecureCirclePoint
        parameter (qm31Square parameter) inverseDenominator) := by
  exact exactSecureCircleParameterMap_success
    (encodeTagQM31ExactLE parameter) parameter inverseDenominator
    (decodeTagQM31ExactLE_encodeTagQM31ExactLE parameter)
    invertible outsideSubfield

theorem exactSecureCircleParameterMap_functional
    (encodedParameter : Qm31Bytes) (first second : SecureCirclePointBytes)
    (firstRun : exactSecureCircleParameterMap encodedParameter = some first)
    (secondRun : exactSecureCircleParameterMap encodedParameter = some second) :
    first = second := by
  rw [firstRun] at secondRun
  exact Option.some.inj secondRun

/-- Fully concrete deterministic decoders for the byte-level Tag-73 trace. -/
def exactDeterministicDecoders : DeterministicDecoders :=
  deterministicDecoders exactSecureCircleParameterMap

@[simp] theorem exactDeterministicDecoders_qm31Parameter
    (id : ChallengeId) (blocks : List Digest256) :
    exactDeterministicDecoders.qm31Parameter id blocks =
      decodeChallengeParameter exactSecureCircleParameterMap id blocks := by
  rfl

@[simp] theorem exactDeterministicDecoders_secureCirclePoint
    (parameter : Qm31Bytes) :
    exactDeterministicDecoders.secureCirclePoint parameter =
      exactSecureCircleParameterMap parameter := by
  rfl

@[simp] theorem exactDeterministicDecoders_candidate
    (counter : Fin 64) (blocks : List Digest256) :
    exactDeterministicDecoders.candidate counter blocks =
      decodeCandidateOutcome counter blocks := by
  rfl

/-! ## Low-bit interpretation of the sampler's modulo masks -/

/-- Reduction modulo a power of two is the unique low part in the standard
high/low decomposition.  This is the arithmetic semantics needed for a
bit-mask bridge; a separate source-refinement theorem can identify Rust's
`u32 & (2^bits-1)` with this low part. -/
theorem mod_two_pow_is_low_part (word bits : Nat) :
    word = 2 ^ bits * (word / 2 ^ bits) + word % 2 ^ bits ∧
    word % 2 ^ bits < 2 ^ bits := by
  constructor
  · exact (Nat.div_add_mod word (2 ^ bits)).symm
  · exact Nat.mod_lt word (by positivity)

theorem maskedM31_is_low31 (word : Nat) :
    word = 2 ^ 31 * (word / 2 ^ 31) + maskedM31 word ∧
    maskedM31 word < 2 ^ 31 := by
  simpa [maskedM31, m31MaskModulus] using
    (mod_two_pow_is_low_part word 31)

theorem q16Candidate_is_low18 (word : Nat) :
    word = 2 ^ 18 * (word / 2 ^ 18) + q16Candidate word ∧
    q16Candidate word < 2 ^ 18 := by
  simpa [q16Candidate, q16Bound] using
    (mod_two_pow_is_low_part word 18)

/-- The sampler's arithmetic low-31 operation is exactly the corresponding
bitwise mask.  This reuses the same theorem as the exact tower's
`rustLow31BitAnd_eq_low31Candidate`. -/
theorem bitAnd_low31_eq_maskedM31 (word : Nat) :
    word &&& (2 ^ 31 - 1) = maskedM31 word := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem bitAnd_low18_eq_q16Candidate (word : Nat) :
    word &&& (2 ^ 18 - 1) = q16Candidate word := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-! ## Axiom audit -/

#print axioms decode_encodeExactSecureCirclePoint_x
#print axioms decode_encodeExactSecureCirclePoint_y
#print axioms tagQm31BytesToExact_exactQm31BytesToTag
#print axioms exactQm31BytesToTag_tagQm31BytesToExact
#print axioms decodeTagQM31ExactLE_encodeTagQM31ExactLE
#print axioms exactSecureCirclePointFromDecoded_rejects_singular_first
#print axioms exactSecureCirclePointFromDecoded_rejects_cm31
#print axioms exactSecureCirclePointFromDecoded_success
#print axioms successful_qm31TryInv_is_inverse
#print axioms exactSecureCircleParameterMap_rejects_noncanonical
#print axioms exactSecureCircleParameterMap_rejects_singular
#print axioms exactSecureCircleParameterMap_rejects_cm31
#print axioms exactSecureCircleParameterMap_success
#print axioms exactSecureCircleParameterMap_encode_success
#print axioms exactSecureCircleParameterMap_functional
#print axioms maskedM31_is_low31
#print axioms q16Candidate_is_low18
#print axioms bitAnd_low31_eq_maskedM31
#print axioms bitAnd_low18_eq_q16Candidate

end AspisK1.V7Tag73SecureCircleMap
