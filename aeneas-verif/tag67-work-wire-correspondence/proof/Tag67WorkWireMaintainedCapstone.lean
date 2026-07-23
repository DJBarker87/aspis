import Tag67WorkWireProof
import AspisFormal.V5NonceWorkAuthentication

open Aeneas Aeneas.Std Result

namespace AspisTag67WorkWireMaintained

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open aspis_verifier.v5_cu_probe

def modelNonceToU64 (nonce : Nonce64) : Std.U64 :=
  Std.U64.ofNatCore nonce.val (by exact nonce.isLt)

def modelByteToU8
    (byte : AspisFormal.V5ExactRuntimeWireRepair.Byte) : Std.U8 :=
  Std.U8.ofNatCore byte.val (by exact byte.isLt)

def serializedRuntimeSlice (shape : RuntimeShape)
    (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max) : Slice Std.U8 :=
  ⟨(serializeRuntimeExact shape wire).map modelByteToU8, by
    rw [List.length_map]
    change wire.val.length ≤ Std.Usize.max
    rw [wire.property]
    exact hfit⟩

/-- The generated finite maps agree with the maintained work-position model.
This closes labels, difficulties, and all six global positions independently
of the still-external hash/random-oracle execution interface. -/
theorem generated_maps_match_maintained_work_model :
    (11080 = WorkKind.offset .batch ∧ 37 = WorkKind.difficulty .batch ∧
      28 = WorkKind.label .batch) ∧
    (∀ round : Fin 4,
      11048 + 8 * round.val = WorkKind.offset (.fold round) ∧
      [34, 33, 30, 25][round.val]! = WorkKind.difficulty (.fold round) ∧
      20 = WorkKind.label (.fold round)) ∧
    (19127 = WorkKind.offset .finalQuery ∧
      32 = WorkKind.difficulty .finalQuery ∧
      5 = WorkKind.label .finalQuery) := by
  constructor
  · decide
  constructor
  · intro round
    fin_cases round <;> decide
  · decide

#print axioms generated_maps_match_maintained_work_model

end AspisTag67WorkWireMaintained
