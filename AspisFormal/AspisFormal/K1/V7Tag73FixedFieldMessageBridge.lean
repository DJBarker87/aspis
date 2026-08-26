import AspisFormal.K1.V7Tag73RawProverMessages
import AspisFormal.K1.V7Tag73SecureCircleMap
import AspisFormal.V6AcceptedPathObligations

/-!
# Exact Tag-73 fixed-field message bridge

The deployed verifier reads 641 canonical QM31 encodings from six physically
separate prover-message sections.  The algebraic verifier instead consumes one
`Fin 641` family.  This file gives the choice-free layout map between those two
views and proves that successful canonical decoding exposes exactly the
`FixedFieldView` used by the semantic and relation proofs.

There is no soundness assumption here.  `FixedFieldDecodeExact` is the precise
decoder-success fact that the accepted Rust reader/source bridge must supply.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73FixedFieldMessageBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SecureCircleMap
open AspisV5ComponentCQM31TowerExact
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations

/-- Reassemble the exact wire-order family of 641 fixed QM31 encodings from
the prover-controlled Tag-73 message record. -/
def rawFixedFieldBytes (raw : RawTag73ProverMessages) (index : Fin 641) :
    Qm31Bytes :=
  if index.val = 0 then
    raw.initialClaim
  else if hSemantic : index.val < 271 then
    raw.semanticSent
      ⟨(index.val - 1) / 27, by omega⟩
      ⟨(index.val - 1) % 27, by omega⟩
  else if hPoint : index.val < 358 then
    raw.pointClaims
      ⟨(index.val - 271) / 29, by omega⟩
      ⟨(index.val - 271) % 29, by omega⟩
  else if index.val = 358 then
    raw.inactiveClaim
  else if hOod : index.val < 361 then
    raw.oodValue ⟨index.val - 359, by omega⟩
  else if hRelation : index.val < 385 then
    raw.relationSent
      ⟨(index.val - 361) / 6, by omega⟩
      ⟨(index.val - 361) % 6, by omega⟩
  else
    raw.finalValues ⟨index.val - 385, by omega⟩

@[simp] theorem rawFixedFieldBytes_initial
    (raw : RawTag73ProverMessages) :
    rawFixedFieldBytes raw ⟨0, by omega⟩ = raw.initialClaim := by
  rfl

@[simp] theorem rawFixedFieldBytes_semantic
    (raw : RawTag73ProverMessages) (round : Fin 10) (sent : Fin 27) :
    rawFixedFieldBytes raw (semanticFieldIndex round sent) =
      raw.semanticSent round sent := by
  have hNonzero : 1 + round.val * 27 + sent.val ≠ 0 := by omega
  have hSemantic : 1 + round.val * 27 + sent.val < 271 := by omega
  simp only [rawFixedFieldBytes, semanticFieldIndex, Fin.val_mk,
    if_neg hNonzero, dif_pos hSemantic]
  congr 1 <;> apply Fin.ext <;> simp <;> omega

@[simp] theorem rawFixedFieldBytes_pointClaim
    (raw : RawTag73ProverMessages) (row : Fin 3) (column : Fin 29) :
    rawFixedFieldBytes raw (pointClaimFieldIndex row column) =
      raw.pointClaims row column := by
  have hNonzero : 271 + row.val * 29 + column.val ≠ 0 := by omega
  have hNotSemantic : ¬ (271 + row.val * 29 + column.val < 271) := by omega
  have hPoint : 271 + row.val * 29 + column.val < 358 := by omega
  simp only [rawFixedFieldBytes, pointClaimFieldIndex, Fin.val_mk,
    if_neg hNonzero, dif_neg hNotSemantic, dif_pos hPoint]
  congr 1 <;> apply Fin.ext <;> simp <;> omega

@[simp] theorem rawFixedFieldBytes_inactive
    (raw : RawTag73ProverMessages) :
    rawFixedFieldBytes raw ⟨358, by omega⟩ = raw.inactiveClaim := by
  rfl

@[simp] theorem rawFixedFieldBytes_ood
    (raw : RawTag73ProverMessages) (sample : Fin 2) :
    rawFixedFieldBytes raw (oodFieldIndex sample) = raw.oodValue sample := by
  have hNonzero : 359 + sample.val ≠ 0 := by omega
  have hNotSemantic : ¬ (359 + sample.val < 271) := by omega
  have hNotPoint : ¬ (359 + sample.val < 358) := by omega
  have hNotInactive : 359 + sample.val ≠ 358 := by omega
  have hOod : 359 + sample.val < 361 := by omega
  simp only [rawFixedFieldBytes, oodFieldIndex, Fin.val_mk,
    if_neg hNonzero, dif_neg hNotSemantic, dif_neg hNotPoint,
    if_neg hNotInactive, dif_pos hOod]
  congr 1
  simp

@[simp] theorem rawFixedFieldBytes_relation
    (raw : RawTag73ProverMessages) (round : Fin 4) (sent : Fin 6) :
    rawFixedFieldBytes raw (relationFieldIndex round sent) =
      raw.relationSent round sent := by
  have hNonzero : 361 + round.val * 6 + sent.val ≠ 0 := by omega
  have hNotSemantic : ¬ (361 + round.val * 6 + sent.val < 271) := by omega
  have hNotPoint : ¬ (361 + round.val * 6 + sent.val < 358) := by omega
  have hNotInactive : 361 + round.val * 6 + sent.val ≠ 358 := by omega
  have hNotOod : ¬ (361 + round.val * 6 + sent.val < 361) := by omega
  have hRelation : 361 + round.val * 6 + sent.val < 385 := by omega
  simp only [rawFixedFieldBytes, relationFieldIndex, Fin.val_mk,
    if_neg hNonzero, dif_neg hNotSemantic, dif_neg hNotPoint,
    if_neg hNotInactive, dif_neg hNotOod, dif_pos hRelation]
  congr 1 <;> apply Fin.ext <;> simp <;> omega

@[simp] theorem rawFixedFieldBytes_final
    (raw : RawTag73ProverMessages) (coefficient : Fin 256) :
    rawFixedFieldBytes raw (finalFieldIndex coefficient) =
      raw.finalValues coefficient := by
  have hNonzero : 385 + coefficient.val ≠ 0 := by omega
  have hNotSemantic : ¬ (385 + coefficient.val < 271) := by omega
  have hNotPoint : ¬ (385 + coefficient.val < 358) := by omega
  have hNotInactive : 385 + coefficient.val ≠ 358 := by omega
  have hNotOod : ¬ (385 + coefficient.val < 361) := by omega
  have hNotRelation : ¬ (385 + coefficient.val < 385) := by omega
  simp only [rawFixedFieldBytes, finalFieldIndex, Fin.val_mk,
    if_neg hNonzero, dif_neg hNotSemantic, dif_neg hNotPoint,
    if_neg hNotInactive, dif_neg hNotOod, dif_neg hNotRelation]
  congr 1
  simp

/-- Every fixed-field byte string was accepted by the exact canonical QM31
decoder, with `decoded` recording its unique mathematical value. -/
def FixedFieldDecodeExact (raw : RawTag73ProverMessages)
    (decoded : Fin 641 → QM31Exact) : Prop :=
  ∀ index, decodeTagQM31ExactLE (rawFixedFieldBytes raw index) =
    some (decoded index)

theorem fixedFieldDecodeExact_unique
    {raw : RawTag73ProverMessages} {left right : Fin 641 → QM31Exact}
    (hLeft : FixedFieldDecodeExact raw left)
    (hRight : FixedFieldDecodeExact raw right) :
    left = right := by
  funext index
  exact Option.some.inj ((hLeft index).symm.trans (hRight index))

theorem decode_initial_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded) :
    decodeTagQM31ExactLE raw.initialClaim =
      some (decodedFixedFieldView decoded).initialClaim := by
  have h := hDecode ⟨0, by omega⟩
  rw [rawFixedFieldBytes_initial] at h
  exact h

theorem decode_semantic_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded)
    (round : Fin 10) (sent : Fin 27) :
    decodeTagQM31ExactLE (raw.semanticSent round sent) =
      some ((decodedFixedFieldView decoded).semanticSent round sent) := by
  simpa [decodedFixedFieldView] using
    hDecode (semanticFieldIndex round sent)

theorem decode_pointClaim_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded)
    (row : Fin 3) (column : Fin 29) :
    decodeTagQM31ExactLE (raw.pointClaims row column) =
      some ((decodedFixedFieldView decoded).pointClaim row column) := by
  simpa [decodedFixedFieldView] using
    hDecode (pointClaimFieldIndex row column)

theorem decode_inactive_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded) :
    decodeTagQM31ExactLE raw.inactiveClaim =
      some (decodedFixedFieldView decoded).inactiveClaim := by
  have h := hDecode ⟨358, by omega⟩
  rw [rawFixedFieldBytes_inactive] at h
  exact h

theorem decode_ood_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded) (sample : Fin 2) :
    decodeTagQM31ExactLE (raw.oodValue sample) =
      some ((decodedFixedFieldView decoded).oodValue sample) := by
  simpa [decodedFixedFieldView] using hDecode (oodFieldIndex sample)

theorem decode_relation_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded)
    (round : Fin 4) (sent : Fin 6) :
    decodeTagQM31ExactLE (raw.relationSent round sent) =
      some ((decodedFixedFieldView decoded).relationSent round sent) := by
  simpa [decodedFixedFieldView] using
    hDecode (relationFieldIndex round sent)

theorem decode_final_of_fixedFieldDecodeExact
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (hDecode : FixedFieldDecodeExact raw decoded) (coefficient : Fin 256) :
    decodeTagQM31ExactLE (raw.finalValues coefficient) =
      some ((decodedFixedFieldView decoded).finalCoefficient coefficient) := by
  simpa [decodedFixedFieldView] using hDecode (finalFieldIndex coefficient)

#print axioms rawFixedFieldBytes_semantic
#print axioms rawFixedFieldBytes_pointClaim
#print axioms rawFixedFieldBytes_relation
#print axioms fixedFieldDecodeExact_unique
#print axioms decode_initial_of_fixedFieldDecodeExact
#print axioms decode_semantic_of_fixedFieldDecodeExact
#print axioms decode_pointClaim_of_fixedFieldDecodeExact
#print axioms decode_inactive_of_fixedFieldDecodeExact
#print axioms decode_ood_of_fixedFieldDecodeExact
#print axioms decode_relation_of_fixedFieldDecodeExact
#print axioms decode_final_of_fixedFieldDecodeExact

end AspisK1.V7Tag73FixedFieldMessageBridge
