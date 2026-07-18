import AspisFormal.V5ComponentCConcreteDownstream
import AspisFormal.V5ComponentCQM31Representation

/-!
# v5 Component C: pinned 58-field relation-tail byte codec

The direct Component-C theorem consumes 36 logical relation rows, while the
host artifact serializes 58 QM31 fields.  `V5ComponentCConcreteDownstream`
already proves the non-contiguous 58-to-36 field selection.  This leaf pins the
remaining mathematical byte layout: 58 consecutive fields, sixteen bytes per
field, with each field encoded in `(c0.a,c0.b,c1.a,c1.b)` little-endian order.

The final Rust equality remains an explicit premise.  No fixed transcript or
KAT is promoted to a universal correspondence theorem.
-/

namespace AspisV5ComponentCRelationTailCodec

open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCRelationRowLinearity

def qm31EncodedByteCount : Nat := 16

theorem relationTailEncodedByteCount_eq :
    physicalRelationTailFieldCount * qm31EncodedByteCount = 928 := by
  decide

abbrev RelationTailBytes :=
  Fin (physicalRelationTailFieldCount * qm31EncodedByteCount) → Byte

/-- Field-major byte indexing: `16 * field + byte`. -/
def relationTailByteIndexEquiv :
    (Fin physicalRelationTailFieldCount × Fin qm31EncodedByteCount) ≃
      Fin (physicalRelationTailFieldCount * qm31EncodedByteCount) :=
  finProdFinEquiv

@[simp] theorem relationTailByteIndexEquiv_val
    (field : Fin physicalRelationTailFieldCount)
    (byte : Fin qm31EncodedByteCount) :
    (relationTailByteIndexEquiv (field, byte)).val =
      qm31EncodedByteCount * field.val + byte.val := by
  change byte.val + 16 * field.val = 16 * field.val + byte.val
  omega

/-- Flatten 58 already-canonical QM31 limb vectors into 928 bytes. -/
def encodeRelationTailFields
    (fields : Fin physicalRelationTailFieldCount → QM31Limbs) :
    RelationTailBytes :=
  fun index =>
    let fieldByte := relationTailByteIndexEquiv.symm index
    encodeQM31LE (fields fieldByte.1) fieldByte.2

/-- Extract one consecutive sixteen-byte field from a flat relation tail. -/
def relationTailFieldBytes (bytes : RelationTailBytes)
    (field : Fin physicalRelationTailFieldCount) : QM31Bytes :=
  fun byte => bytes (relationTailByteIndexEquiv (field, byte))

theorem relationTailFieldBytes_encodeRelationTailFields
    (fields : Fin physicalRelationTailFieldCount → QM31Limbs)
    (field : Fin physicalRelationTailFieldCount) :
    relationTailFieldBytes (encodeRelationTailFields fields) field =
      encodeQM31LE (fields field) := by
  funext byte
  simp only [relationTailFieldBytes, encodeRelationTailFields,
    Equiv.symm_apply_apply]

theorem decodeRelationTailField_encode
    (fields : Fin physicalRelationTailFieldCount → QM31Limbs)
    (field : Fin physicalRelationTailFieldCount) :
    decodeQM31LE
        (relationTailFieldBytes (encodeRelationTailFields fields) field) =
      some (fields field) := by
  rw [relationTailFieldBytes_encodeRelationTailFields,
    decodeQM31LE_encodeQM31LE]

/-- Encode field values through the same limb equivalence used by the sampler
and tower-arithmetic correspondence. -/
noncomputable def encodeRelationTailValues {K : Type*}
    (e : QM31Limbs ≃ K)
    (tail : Fin physicalRelationTailFieldCount → K) : RelationTailBytes :=
  encodeRelationTailFields (fun field => e.symm (tail field))

/-- Total decoder used by the deployment correspondence.  Malformed fields
map to zero; the round-trip theorem below shows this branch is unreachable for
the canonical encoder. -/
noncomputable def decodeRelationTailValues {K : Type*} [Zero K]
    (e : QM31Limbs ≃ K) (bytes : RelationTailBytes) :
    Fin physicalRelationTailFieldCount → K :=
  fun field =>
    ((decodeQM31LE (relationTailFieldBytes bytes field)).map e).getD 0

theorem decodeRelationTailValues_encode {K : Type*} [Zero K]
    (e : QM31Limbs ≃ K)
    (tail : Fin physicalRelationTailFieldCount → K) :
    decodeRelationTailValues e (encodeRelationTailValues e tail) = tail := by
  funext field
  simp only [decodeRelationTailValues, encodeRelationTailValues,
    decodeRelationTailField_encode, Option.map_some, Equiv.apply_symm_apply,
    Option.getD_some]

/-! ## A canonical extension of the 36 logical rows to 58 physical fields -/

def logicalPhysicalIndex (logical : RelationIndex) :
    Fin physicalRelationTailFieldCount :=
  physicalRelationIndex (relationTaggedIndexEquiv.symm logical)

theorem physicalRelationIndex_injective :
    Function.Injective physicalRelationIndex := by
  intro left right h
  rcases left with ⟨leftRound, leftIndex⟩
  rcases right with ⟨rightRound, rightIndex⟩
  cases leftIndex with
  | inl leftSample =>
      cases rightIndex with
      | inl rightSample =>
          have hval := congrArg Fin.val h
          change 10 + 2 * leftRound.val + leftSample.val =
            10 + 2 * rightRound.val + rightSample.val at hval
          have hround : leftRound = rightRound := by
            apply Fin.ext
            omega
          have hsample : leftSample = rightSample := by
            apply Fin.ext
            omega
          rw [hround, hsample]
      | inr rightDegree =>
          have hval := congrArg Fin.val h
          change 10 + 2 * leftRound.val + leftSample.val =
            26 + 7 * rightRound.val + rightDegree.val at hval
          omega
  | inr leftDegree =>
      cases rightIndex with
      | inl rightSample =>
          have hval := congrArg Fin.val h
          change 26 + 7 * leftRound.val + leftDegree.val =
            10 + 2 * rightRound.val + rightSample.val at hval
          omega
      | inr rightDegree =>
          have hval := congrArg Fin.val h
          change 26 + 7 * leftRound.val + leftDegree.val =
            26 + 7 * rightRound.val + rightDegree.val at hval
          have hround : leftRound = rightRound := by
            apply Fin.ext
            omega
          have hdegree : leftDegree = rightDegree := by
            apply Fin.ext
            omega
          rw [hround, hdegree]

theorem logicalPhysicalIndex_injective :
    Function.Injective logicalPhysicalIndex :=
  physicalRelationIndex_injective.comp relationTaggedIndexEquiv.symm.injective

/-- Fill the 22 public/non-witness physical fields with zero and place each of
the 36 logical rows at its exact deployed field position. -/
noncomputable def embedLogicalRelationRows {K : Type*} [Zero K]
    (rows : RelationIndex → K) : Fin physicalRelationTailFieldCount → K :=
  Function.extend logicalPhysicalIndex rows (fun _ => 0)

theorem reorderPhysicalRelationTail_embedLogicalRelationRows
    {K : Type*} [Zero K] (rows : RelationIndex → K) :
    reorderPhysicalRelationTail (embedLogicalRelationRows rows) = rows := by
  funext logical
  change embedLogicalRelationRows rows (logicalPhysicalIndex logical) =
    rows logical
  exact logicalPhysicalIndex_injective.extend_apply rows (fun _ => 0) logical

/-! ## Exact remaining Rust/code-model edge and composition -/

/-- The Rust serializer must equal the pinned 928-byte mathematical encoder
on every input.  This is an exact function equality, not a codec slogan. -/
def RustRelationTailEncoderMatchesPinnedCodec {K : Type*}
    (e : QM31Limbs ≃ K)
    (rustTailBytes : CWord K → RelationTailBytes)
    (modelTail : CWord K → Fin physicalRelationTailFieldCount → K) : Prop :=
  rustTailBytes = fun c => encodeRelationTailValues e (modelTail c)

/-- The model tail places the actual schedule's 36 witness-dependent rows at
the exact physical indices. -/
def ModelRelationTailMatchesSchedule {F K : Type*}
    [Field F] [Field K] [Algebra F K]
    (schedule : CompleteFixedSchedule F K)
    (modelTail : CWord K → Fin physicalRelationTailFieldCount → K) : Prop :=
  ∀ c, reorderPhysicalRelationTail (modelTail c) =
    relationRows schedule.relation c

/-- Universal byte-to-row correspondence.  The mathematical byte codec and
58-to-36 extraction are discharged; only the exact Rust serializer equality
and semantic tail construction are inputs. -/
theorem physicalRustRelationTailCorresponds_of_pinned_codec
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (schedule : CompleteFixedSchedule F K)
    (e : QM31Limbs ≃ K)
    (rustTailBytes : CWord K → RelationTailBytes)
    (modelTail : CWord K → Fin physicalRelationTailFieldCount → K)
    (hbytes : RustRelationTailEncoderMatchesPinnedCodec e rustTailBytes modelTail)
    (hmodel : ModelRelationTailMatchesSchedule schedule modelTail) :
    UnmetDeployment.PhysicalRustRelationTailCorresponds schedule rustTailBytes
      (decodeRelationTailValues e) := by
  intro c
  rw [hbytes, decodeRelationTailValues_encode]
  exact hmodel c

/-- The two remaining premises are jointly satisfiable for the explicit
mathematical serializer and the canonical 36-to-58 embedding. -/
theorem pinnedRelationTailCorrespondence_nonvacuous
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (schedule : CompleteFixedSchedule F K) (e : QM31Limbs ≃ K) :
    UnmetDeployment.PhysicalRustRelationTailCorresponds schedule
      (fun c => encodeRelationTailValues e
        (embedLogicalRelationRows (relationRows schedule.relation c)))
      (decodeRelationTailValues e) := by
  apply physicalRustRelationTailCorresponds_of_pinned_codec schedule e
    (fun c => encodeRelationTailValues e
      (embedLogicalRelationRows (relationRows schedule.relation c)))
    (fun c => embedLogicalRelationRows (relationRows schedule.relation c))
  · rfl
  · intro c
    exact reorderPhysicalRelationTail_embedLogicalRelationRows _

/-! ## Order tooth -/

/-- The first witness-dependent OOD field is physical field 10, not 11. -/
theorem first_ood_physical_index_is_loadBearing :
    (physicalRelationIndex ((0 : Fin 4), Sum.inl (0 : Fin 2))).val = 10 ∧
    (physicalRelationIndex ((0 : Fin 4), Sum.inl (0 : Fin 2))).val ≠ 11 := by
  decide

/-! ## Axiom audit -/

#print axioms relationTailFieldBytes_encodeRelationTailFields
#print axioms decodeRelationTailField_encode
#print axioms decodeRelationTailValues_encode
#print axioms physicalRelationIndex_injective
#print axioms reorderPhysicalRelationTail_embedLogicalRelationRows
#print axioms physicalRustRelationTailCorresponds_of_pinned_codec
#print axioms pinnedRelationTailCorrespondence_nonvacuous
#print axioms first_ood_physical_index_is_loadBearing

end AspisV5ComponentCRelationTailCodec
