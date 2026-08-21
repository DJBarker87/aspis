import V5MerkleUnchangedPublicAcceptanceBridge
import V5FriConsumerObservationBridge

/-!
# Structural bridge from the unchanged Merkle return value to the FRI snapshot

The Merkle driver and FRI consumer were translated in separate Aeneas runs,
so Lean gives their copies of the same Rust structs different names.  This
file performs only the field-for-field conversion between those copies and
proves that their maintained `V5DriverOutput` observations are identical.

There is no cryptographic premise here.  The separate caller proof must still
show that production passes the value returned by the Merkle driver to the
FRI consumer; this module makes the value equality itself explicit.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleFriReturnedOutputBridge

namespace Merkle
open V5MerkleUnchangedFull

abbrev Opening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev OpeningOffsets :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningOffsets
abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices
abbrev Verified := private_openings.VerifiedV5PrivateOpenings

end Merkle

namespace Fri
open V5FriConsumerExact

abbrev Opening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev OpeningOffsets :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningOffsets
abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices
abbrev Verified := private_openings.VerifiedV5PrivateOpenings

end Fri

def mapArray {A B : Type*} {n : Std.Usize} (f : A → B)
    (values : Array A n) : Array B n :=
  ⟨values.val.map f, by simpa using values.property⟩

def toFriOffsets (offsets : Merkle.OpeningOffsets) : Fri.OpeningOffsets where
  count := offsets.count
  records := offsets.records
  frontier_count := offsets.frontier_count
  frontier := offsets.frontier
  «end» := offsets.end

def toFriOpening (opening : Merkle.Opening) : Fri.Opening where
  count := opening.count
  value_width := opening.value_width
  records := opening.records
  frontier := opening.frontier
  offsets := toFriOffsets opening.offsets

def toFriQueryIndices (indices : Merkle.QueryIndices) : Fri.QueryIndices where
  layer0 := indices.layer0
  later := indices.later

def toFriVerified (verified : Merkle.Verified) : Fri.Verified where
  c1 := toFriOpening verified.c1
  c2 := toFriOpening verified.c2
  later := mapArray toFriOpening verified.later
  indices := toFriQueryIndices verified.indices
  bytes_consumed := verified.bytes_consumed

@[simp] theorem toFriOpening_driver_view (opening : Merkle.Opening) :
    AspisV5FriConsumerObservationBridge.generatedOpeningToReturned
        (toFriOpening opening) =
      AspisV5MerkleUnchangedFullSectionCallBridge.generatedOpeningToReturned
        opening := by
  rfl

@[simp] theorem toFriQueryIndices_layer0 (indices : Merkle.QueryIndices) :
    (toFriQueryIndices indices).layer0 = indices.layer0 := rfl

@[simp] theorem toFriQueryIndices_later (indices : Merkle.QueryIndices) :
    (toFriQueryIndices indices).later = indices.later := rfl

@[simp] theorem generatedU8ToByte_views_equal (byte : Std.U8) :
    AspisV5FriConsumerObservationBridge.generatedU8ToByte byte =
      AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte byte := by
  apply Fin.ext
  rfl

/-- The two independent Aeneas snapshots expose exactly the same returned
opening bytes, offsets, index lists, and consumed-byte count after structural
conversion. -/
theorem converted_driver_output_eq (verified : Merkle.Verified) :
    AspisV5FriConsumerObservationBridge.generatedDriverOutput
        (toFriVerified verified) =
      AspisV5MerkleUnchangedPublicAcceptanceBridge.generatedDriverOutput
        verified := by
  rcases verified with ⟨c1, c2, later, indices, bytesConsumed⟩
  simp [AspisV5FriConsumerObservationBridge.generatedDriverOutput,
    AspisV5MerkleUnchangedPublicAcceptanceBridge.generatedDriverOutput,
    toFriVerified, toFriOpening, toFriOffsets, toFriQueryIndices, mapArray,
    AspisV5FriConsumerObservationBridge.generatedOpeningToReturned,
    AspisV5MerkleUnchangedFullSectionCallBridge.generatedOpeningToReturned,
    AspisV5FriConsumerObservationBridge.generatedIndicesToNat,
    AspisV5MerkleUnchangedPublicAcceptanceBridge.generatedIndicesToNat]

/-- Therefore the exact output theorem for the unchanged Merkle driver is
already in the precise form consumed by the accepted FRI proof. -/
theorem converted_driver_output_eq_run
    {sha256 roots queries}
    (run : AspisV5MerkleRustBridge.ExactV5Run sha256 roots queries)
    (verified : Merkle.Verified)
    (houtput :
      AspisV5MerkleUnchangedPublicAcceptanceBridge.generatedDriverOutput
          verified =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run []) :
    AspisV5FriConsumerObservationBridge.generatedDriverOutput
        (toFriVerified verified) =
      AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [] :=
  (converted_driver_output_eq verified).trans houtput

#print axioms converted_driver_output_eq
#print axioms converted_driver_output_eq_run

end AspisV5MerkleFriReturnedOutputBridge
