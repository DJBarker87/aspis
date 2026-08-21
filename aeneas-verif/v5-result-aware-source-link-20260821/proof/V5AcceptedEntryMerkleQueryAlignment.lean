import V5AcceptedEntryMerkleEndToEnd
import V5AcceptedTranscriptQueryBridge
import V5MerkleUnchangedPublicAcceptanceBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedEntryMerkleQueryAlignment

open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedTranscriptQueryBridge
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open V5MerkleQueryReuseProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The scalar value projection is injective on generated `u32` values. -/
def u32ValueEmbedding : Std.U32 ↪ Nat where
  toFun := UScalar.val
  inj' := fun _ _ equality => UScalar.eq_of_val_eq equality

/-- Sorting and deduplicating generated `u32` queries and then projecting
their values is the same as sorting and deduplicating the projected natural
numbers. -/
theorem expectedLayer0_values
    (values : List Std.U32) :
    (expectedLayer0 values).map (fun value => value.val) =
      (values.map (fun value => value.val)).toFinset.sort (.≤.) := by
  unfold expectedLayer0
  calc
    (values.toFinset.sort (.≤.)).map (fun value => value.val) =
        (values.toFinset.map u32ValueEmbedding).sort (.≤.) := by
      simpa [u32ValueEmbedding] using
        (Finset.map_sort u32ValueEmbedding values.toFinset (.≤.) (.≤.)
          (by intro left _ right _; rfl))
    _ = (values.map (fun value => value.val)).toFinset.sort (.≤.) := by
      congr 1
      ext value
      simp [u32ValueEmbedding]

/-- The exact query set decoded from the accepted sampler contains precisely
the natural-number values in the returned 18-element Rust array. -/
theorem decodedQuerySet_value_image
    (blocks : List (AspisV5TranscriptConnection.FixedBytes 32))
    (queries : Array Std.U32 18#usize)
    (hdecode : AspisV5TranscriptConnection.derive18Queries blocks =
      some (queries.val.map UScalar.val)) :
    (decodedQuerySet blocks (queries.val.map UScalar.val) hdecode).image
        (fun query => query.val) =
      (queries.val.map UScalar.val).toFinset := by
  ext value
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨query, queryMember, rfl⟩
    exact List.mem_toFinset.mpr
      ((mem_decodedQuerySet_iff blocks
        (queries.val.map UScalar.val) hdecode query).mp queryMember)
  · intro member
    have listMember : value ∈ queries.val.map UScalar.val :=
      List.mem_toFinset.mp member
    have valueBound : value < 131072 :=
      (AspisV5TranscriptConnection.derive18Queries_success_is_exact
        blocks (queries.val.map UScalar.val) hdecode).2.2 value listMember
    let query : V5Query := ⟨value, valueBound⟩
    refine Finset.mem_image.mpr ⟨query, ?_, rfl⟩
    exact (mem_decodedQuerySet_iff blocks
      (queries.val.map UScalar.val) hdecode query).mpr listMember

/-- The model query set constructed from the accepted without-replacement
sampler has exactly the layer-zero ordering expected by the unchanged Merkle
translation. -/
theorem accepted_queries_model_exact_merkle_layer_zero
    (blocks : List (AspisV5TranscriptConnection.FixedBytes 32))
    (queries : Array Std.U32 18#usize)
    (hdecode : AspisV5TranscriptConnection.derive18Queries blocks =
      some (queries.val.map UScalar.val)) :
    (expectedLayer0 (Array.to_slice queries).val).map
        (fun index => index.val) =
      sharedLevelIndices
        (decodedQuerySet blocks (queries.val.map UScalar.val) hdecode) 0 := by
  rw [Aeneas.Std.Array.val_to_slice, expectedLayer0_values,
    ← decodedQuerySet_value_image blocks queries hdecode]
  rfl

end AspisV5AcceptedEntryMerkleQueryAlignment
