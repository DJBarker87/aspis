import AspisFormal.K1.V7Tag73DeterministicRefinement
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore

/-!
# Exact 34-bit final-work digest probability

This module counts the literal deployed `bigEndianHead64` predicate.  It
splits a 32-byte digest into an eight-byte big-endian head and a 24-byte tail,
then identifies the accepted head with `Fin (2^30)`.  Thus the accepted
digest subtype has exactly `2^222` values and uniform acceptance probability
`2^-34`.  SHA-256/random-oracle security remains external.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FinalWorkDigestProbability

open MeasureTheory
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev FinalWorkHeadBytes := Fin 8 → UInt8
abbrev FinalWorkTailBytes := Fin 24 → UInt8

def digestIndexSplitEquiv : Fin 8 ⊕ Fin 24 ≃ Fin 32 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

def digestHeadTailEquiv :
    Digest256 ≃ FinalWorkHeadBytes × FinalWorkTailBytes :=
  (Equiv.piCongrLeft (fun _ : Fin 32 ↦ UInt8)
      digestIndexSplitEquiv).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin 8 ⊕ Fin 24 ↦ UInt8))

def uint8EquivFin256 : UInt8 ≃ Fin 256 :=
  ({ toFun := UInt8.toFin
     invFun := UInt8.ofFin
     left_inv := UInt8.ofFin_toFin
     right_inv := UInt8.toFin_ofFin } : UInt8 ≃ Fin UInt8.size).trans
    (finCongr (by decide : UInt8.size = 256))

/-- The explicit base-256 value of the eight deployed bytes, with byte zero
as the most significant byte. -/
def bigEndianHeadBytesEquiv : FinalWorkHeadBytes ≃ Fin (2 ^ 64) :=
  ((Equiv.piCongrLeft (fun _ : Fin 8 ↦ UInt8) Fin.revPerm).symm.trans
    (Equiv.arrowCongr (Equiv.refl (Fin 8)) uint8EquivFin256)).trans
      (finFunctionFinEquiv.trans (finCongr (by norm_num)))

theorem foldl_base256_eq_ofDigits_reverse (digits : List Nat) :
    digits.foldl (fun value digit => value * 256 + digit) 0 =
      Nat.ofDigits 256 digits.reverse := by
  rw [List.foldl_eq_foldr_reverse, Nat.ofDigits_eq_foldr]
  generalize digits.reverse = reversed
  induction reversed with
  | nil => rfl
  | cons digit rest ih =>
      simp only [List.foldr_cons]
      rw [ih]
      simp [Nat.add_comm, Nat.mul_comm]

theorem reverse_ofFn_eq_ofFn_rev {α : Type} {count : Nat}
    (values : Fin count → α) :
    (List.ofFn values).reverse =
      List.ofFn (fun index => values (Fin.rev index)) := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    simp [Fin.rev]
    apply congrArg values
    apply Fin.ext
    simp [Nat.sub_sub, Nat.add_comm]

theorem finFunctionFinEquiv_val_eq_ofDigits {base count : Nat}
    (digits : Fin count → Fin base) :
    (finFunctionFinEquiv digits).val =
      Nat.ofDigits base (List.ofFn fun index => (digits index).val) := by
  rw [finFunctionFinEquiv_apply, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro index _
  congr 2

theorem digestHeadTailEquiv_head_apply
    (digest : Digest256) (index : Fin 8) :
    (digestHeadTailEquiv digest).1 index =
      digest ⟨index.val, by omega⟩ := by
  rfl

theorem bigEndianHeadBytesEquiv_val
    (head : FinalWorkHeadBytes) :
    (bigEndianHeadBytesEquiv head).val =
      (List.ofFn head).foldl
        (fun value byte => value * 256 + byte.toNat) 0 := by
  change
    (finFunctionFinEquiv
      (fun index : Fin 8 => uint8EquivFin256 (head (Fin.rev index)))).val = _
  rw [finFunctionFinEquiv_val_eq_ofDigits]
  have mappedFold :
      (List.ofFn head).foldl
          (fun value byte => value * 256 + byte.toNat) 0 =
        ((List.ofFn head).map UInt8.toNat).foldl
          (fun value digit => value * 256 + digit) 0 := by
    rw [List.foldl_map]
  rw [mappedFold, foldl_base256_eq_ofDigits_reverse]
  congr 1

theorem bigEndianHead64_eq_head_equiv
    (digest : Digest256) :
    bigEndianHead64 digest =
      (bigEndianHeadBytesEquiv (digestHeadTailEquiv digest).1).val := by
  rw [bigEndianHeadBytesEquiv_val]
  congr 1

/-- The literal deployed final-work predicate, as a proposition. -/
def FinalWork34Accepted (digest : Digest256) : Prop :=
  workDigestAccepted .final digest = true

theorem final_work_34_accepted_iff_head_lt
    (digest : Digest256) :
    FinalWork34Accepted digest ↔
      (bigEndianHeadBytesEquiv (digestHeadTailEquiv digest).1).val < 2 ^ 30 := by
  rw [FinalWork34Accepted, work_digest_accepted_iff,
    bigEndianHead64_eq_head_equiv]
  norm_num [workBits]

def finInitialSegmentEquiv (small large : Nat) (bounded : small ≤ large) :
    Fin small ≃ {value : Fin large // value.val < small} where
  toFun value :=
    ⟨⟨value.val, value.isLt.trans_le bounded⟩, value.isLt⟩
  invFun value := ⟨value.1.val, value.2⟩
  left_inv value := by ext; rfl
  right_inv value := by ext; rfl

abbrev FinalWork34AcceptedDigest :=
  {digest : Digest256 // FinalWork34Accepted digest}

def finalWork34AcceptedDigestEquiv :
    FinalWork34AcceptedDigest ≃ Fin (2 ^ 30) × FinalWorkTailBytes where
  toFun digest :=
    let split := digestHeadTailEquiv digest.1
    let head := bigEndianHeadBytesEquiv split.1
    (⟨head.val, (final_work_34_accepted_iff_head_lt digest.1).mp digest.2⟩,
      split.2)
  invFun coordinates :=
    let head : Fin (2 ^ 64) :=
      ⟨coordinates.1.val, coordinates.1.isLt.trans_le (by norm_num)⟩
    let digest := digestHeadTailEquiv.symm
      (bigEndianHeadBytesEquiv.symm head, coordinates.2)
    ⟨digest, (final_work_34_accepted_iff_head_lt digest).mpr (by
      simp [digest, head])⟩
  left_inv digest := by
    apply Subtype.ext
    apply digestHeadTailEquiv.injective
    apply Prod.ext
    · apply bigEndianHeadBytesEquiv.injective
      apply Fin.ext
      simp
    · simp
  right_inv coordinates := by
    apply Prod.ext
    · apply Fin.ext
      simp
    · simp

noncomputable instance finalWork34AcceptedDigestFintype :
    Fintype FinalWork34AcceptedDigest :=
  Fintype.ofEquiv
    (Fin (2 ^ 30) × FinalWorkTailBytes)
    finalWork34AcceptedDigestEquiv.symm

def finalWorkTailBytesEquiv : FinalWorkTailBytes ≃ Fin (2 ^ 192) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 24)) uint8EquivFin256).trans
    (finFunctionFinEquiv.trans (finCongr (by
      rw [show 256 = 2 ^ 8 by norm_num, ← pow_mul])))

def finalWork34AcceptedDigestPackedEquiv :
    FinalWork34AcceptedDigest ≃ Fin (2 ^ 222) :=
  finalWork34AcceptedDigestEquiv.trans
    ((Equiv.prodCongr (Equiv.refl (Fin (2 ^ 30)))
      finalWorkTailBytesEquiv).trans
        (finProdFinEquiv.trans (finCongr (by rw [← pow_add]))))

def digest256PackedEquiv : Digest256 ≃ Fin (2 ^ 256) :=
  digestHeadTailEquiv.trans
    ((Equiv.prodCongr bigEndianHeadBytesEquiv
      finalWorkTailBytesEquiv).trans
        (finProdFinEquiv.trans (finCongr (by rw [← pow_add]))))

theorem final_work_34_accepted_digest_card :
    Fintype.card FinalWork34AcceptedDigest = 2 ^ 222 := by
  rw [Fintype.card_congr finalWork34AcceptedDigestPackedEquiv,
    Fintype.card_fin]

def finalWork34AcceptedEvent : Set Digest256 :=
  {digest | FinalWork34Accepted digest}

def finalWork34AcceptedEventSubtypeEquiv :
    {digest : Digest256 // digest ∈ finalWork34AcceptedEvent} ≃
      FinalWork34AcceptedDigest :=
  Equiv.refl _

noncomputable instance finalWork34AcceptedEventFintype :
    Fintype {digest : Digest256 // digest ∈ finalWork34AcceptedEvent} :=
  Fintype.ofEquiv FinalWork34AcceptedDigest
    finalWork34AcceptedEventSubtypeEquiv.symm

theorem uniform_final_work_34_probability_exact :
    (PMF.uniformOfFintype Digest256).toOuterMeasure
        finalWork34AcceptedEvent =
      (1 : ENNReal) / (2 : ENNReal) ^ 34 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_congr finalWork34AcceptedEventSubtypeEquiv,
    final_work_34_accepted_digest_card]
  have digestCard : Fintype.card Digest256 = 2 ^ 256 := by
    rw [Fintype.card_congr digest256PackedEquiv, Fintype.card_fin]
  rw [digestCard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show 256 = 222 + 34 by norm_num, pow_add]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by positivity))
    (ENNReal.div_ne_top (by simp) (by positivity))).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  rw [div_mul_eq_div_div]
  simp

end

#print axioms bigEndianHeadBytesEquiv_val
#print axioms bigEndianHead64_eq_head_equiv
#print axioms final_work_34_accepted_iff_head_lt
#print axioms finalWork34AcceptedDigestEquiv
#print axioms final_work_34_accepted_digest_card
#print axioms uniform_final_work_34_probability_exact

end AspisK1.V7Tag73FinalWorkDigestProbability
