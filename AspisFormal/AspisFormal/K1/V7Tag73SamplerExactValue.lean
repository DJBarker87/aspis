import AspisFormal.K1.V7Tag73DeployedDecoderFiberCap
import AspisFormal.K1.V7Tag73SamplerDecoderExact

/-!
# Exact field value of every successful Tag-73 sampler output

The deployed sampler assembles four accepted low-31-bit limbs into sixteen
runtime bytes.  This file proves that those bytes are exactly the canonical
encoding of one value in the literal QM31 tower.  The result applies to all
three challenge modes because nonzero and secure-circle retries finish with
an ordinary four-limb decode on a suffix of the consumed block stream.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73SamplerExactValue

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerDecoderExact
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7FsStateRestorationCoupling
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact

theorem tagQm31BytesToExact_injective :
    Function.Injective tagQm31BytesToExact := by
  intro left right equal
  apply_fun exactQm31BytesToTag at equal
  simpa using equal

/-- Turn the four canonical natural limbs returned by the deployed decoder
into the literal tower's pinned limb family. -/
def exactLimbsOfList (limbs : List Nat) (lengthExact : limbs.length = 4)
    (canonical : ∀ limb ∈ limbs, limb < m31Prime) : QM31Limbs :=
  fun index =>
    ⟨listValue limbs index.val, by
      have indexLtFour : index.val < 4 := by
        simpa [qm31LimbCount] using index.isLt
      have indexLt : index.val < limbs.length := by omega
      rw [listValue, List.getD_eq_getElem limbs 0 indexLt]
      exact canonical limbs[index.val] (List.getElem_mem indexLt)⟩

@[simp] theorem exactLimbsOfList_value
    (limbs : List Nat) (lengthExact : limbs.length = 4)
    (canonical : ∀ limb ∈ limbs, limb < m31Prime) (index : Fin 4) :
    (exactLimbsOfList limbs lengthExact canonical index : Nat) =
      listValue limbs index.val := by
  rfl

/-- One runtime-encoded limb is byte-for-byte the mathematical little-endian
encoding of the same canonical natural value. -/
theorem runtime_limb_bytes_eq_encodeM31LE
    (limbs : List Nat) (lengthExact : limbs.length = 4)
    (canonical : ∀ limb ∈ limbs, limb < m31Prime) (limb : Fin 4) :
    qm31LimbBytes (tagQm31BytesToExact (encodeQm31Limbs limbs)) limb =
      encodeM31LE (exactLimbsOfList limbs lengthExact canonical limb) := by
  have bound : listValue limbs limb.val < 2 ^ 31 := by
    have indexLtFour : limb.val < 4 := by omega
    have indexLt : limb.val < limbs.length := by omega
    rw [listValue, List.getD_eq_getElem limbs 0 indexLt]
    have primeBound := canonical limbs[limb.val] (List.getElem_mem indexLt)
    norm_num [m31Prime] at primeBound ⊢
    omega
  apply wordBytesEquivRawWord.injective
  change decodeWordLE
      (qm31LimbBytes (tagQm31BytesToExact (encodeQm31Limbs limbs)) limb) =
    decodeWordLE
      (encodeM31LE (exactLimbsOfList limbs lengthExact canonical limb))
  unfold encodeM31LE
  rw [decodeWordLE_encodeWordLE]
  apply Fin.ext
  fin_cases limb <;>
    simp [decodeWordLE, qm31LimbBytes, limbByteIndex_val, encodeQm31Limbs,
      tagQm31BytesToExact, tagByteEquivExactByte, m31AsRawWord,
      exactLimbsOfList, listValue] at bound ⊢ <;>
    omega

/-- The complete sixteen-byte runtime assembly equals the pinned exact-tower
encoding of its four decoded limbs. -/
theorem encodeQm31Limbs_eq_exact_encoding
    (limbs : List Nat) (lengthExact : limbs.length = 4)
    (canonical : ∀ limb ∈ limbs, limb < m31Prime) :
    encodeQm31Limbs limbs =
      encodeTagQM31ExactLE
        (qm31ExactLimbEquiv (exactLimbsOfList limbs lengthExact canonical)) := by
  apply tagQm31BytesToExact_injective
  unfold encodeTagQM31ExactLE
  rw [tagQm31BytesToExact_exactQm31BytesToTag]
  unfold encodeQM31ExactLE
  rw [Equiv.symm_apply_apply]
  have allLimbs : ∀ limb : Fin 4,
      qm31LimbBytes (tagQm31BytesToExact (encodeQm31Limbs limbs)) limb =
        qm31LimbBytes
          (encodeQM31LE (exactLimbsOfList limbs lengthExact canonical)) limb := by
    intro limb
    rw [qm31LimbBytes_encodeQM31LE]
    exact runtime_limb_bytes_eq_encodeM31LE limbs lengthExact canonical limb
  funext offset
  let position : Fin 4 × Fin 4 := finProdFinEquiv.symm offset
  have byteEq := congrFun (allLimbs position.1) position.2
  have indexEq : limbByteIndex position.1 position.2 = offset := by
    exact (finProdFinEquiv (m := 4) (n := 4)).apply_symm_apply offset
  simpa [qm31LimbBytes, indexEq] using byteEq

theorem decodeTagQM31ExactLE_encodeQm31Limbs
    (limbs : List Nat) (lengthExact : limbs.length = 4)
    (canonical : ∀ limb ∈ limbs, limb < m31Prime) :
    decodeTagQM31ExactLE (encodeQm31Limbs limbs) =
      some (qm31ExactLimbEquiv
        (exactLimbsOfList limbs lengthExact canonical)) := by
  rw [encodeQm31Limbs_eq_exact_encoding limbs lengthExact canonical]
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _

/-- Every successful ordinary prefix returns a canonical encoding in the
literal QM31 tower. -/
theorem decodeOrdinaryPrefix_value_has_exact_tower_value
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    ∃ value : QM31Exact,
      decodeTagQM31ExactLE decoded.value = some value := by
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
            rcases run with ⟨_valid, decodedEq⟩
            subst decoded
            obtain ⟨lengthExact, _lower, _upper, canonical⟩ :=
              decodeFourLimbs_word_cap (flattenedWords (block :: rest)) limbs
                limbsRun
            refine ⟨qm31ExactLimbEquiv
              (exactLimbsOfList limbs.limbs lengthExact canonical), ?_⟩
            exact decodeTagQM31ExactLE_encodeQm31Limbs limbs.limbs
              lengthExact canonical
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid (by simpa using run.1))

/-- Consequently every successful deployed challenge decode—ordinary,
nonzero, or secure-circle—returns one canonical exact-tower value. -/
theorem decodeChallengeParameter_has_exact_tower_value
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks : List Digest256) (encoded : Qm31Bytes)
    (run : decodeChallengeParameter circleMap id blocks = some encoded) :
    ∃ value : QM31Exact,
      decodeTagQM31ExactLE encoded = some value := by
  obtain ⟨discarded, suffix, decoded, decomposition, ordinaryRun,
      noRemaining, valueEq⟩ :=
    decodeChallengeParameter_ordinary_suffix circleMap id blocks encoded run
  obtain ⟨value, exactDecode⟩ :=
    decodeOrdinaryPrefix_value_has_exact_tower_value suffix decoded ordinaryRun
  refine ⟨value, ?_⟩
  rw [← valueEq]
  exact exactDecode

/-! ## Nonzero-mode value preservation -/

/-- The bounded nonzero retry loop can return only a byte string different
from the all-zero QM31 encoding.  This follows from the executable retry
branch itself, not from a distributional assumption. -/
theorem decodeNonzeroPrefix_value_ne_zero
    (attempts : Nat) (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeNonzeroPrefix attempts blocks = some decoded) :
    decoded.value ≠ zeroBytes 16 := by
  induction attempts generalizing blocks decoded with
  | zero => simp [decodeNonzeroPrefix] at run
  | succ attempts ih =>
      simp only [decodeNonzeroPrefix] at run
      obtain ⟨first, firstRun, run⟩ := Option.bind_eq_some_iff.mp run
      by_cases zero : first.value = zeroBytes 16
      · rw [if_pos zero] at run
        exact ih first.remainingBlocks decoded run
      · rw [if_neg zero] at run
        have decodedEq : first = decoded := Option.some.inj run
        simpa [← decodedEq] using zero

/-- Exact completion of the nonzero sampler preserves the same executable
nonzero check. -/
theorem decodeNonzeroExact_value_ne_zero
    (blocks : List Digest256) (encoded : Qm31Bytes)
    (run : decodeNonzeroExact blocks = some encoded) :
    encoded ≠ zeroBytes 16 := by
  obtain ⟨decoded, prefixRun, _remaining, valueEq⟩ :=
    decodeNonzeroExact_witness blocks encoded run
  rw [← valueEq]
  exact decodeNonzeroPrefix_value_ne_zero 3 blocks decoded prefixRun

#print axioms runtime_limb_bytes_eq_encodeM31LE
#print axioms encodeQm31Limbs_eq_exact_encoding
#print axioms decodeTagQM31ExactLE_encodeQm31Limbs
#print axioms decodeOrdinaryPrefix_value_has_exact_tower_value
#print axioms decodeChallengeParameter_has_exact_tower_value
#print axioms decodeNonzeroPrefix_value_ne_zero
#print axioms decodeNonzeroExact_value_ne_zero

end AspisK1.V7Tag73SamplerExactValue
