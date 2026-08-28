import V7ForestLaneInvariant.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- Solana account checks happen in the production caller immediately before
    this extracted pure decoder. They stay explicit here instead of being
    silently attributed to the projection. -/
structure CallerSideSolanaLaneChecks : Type where
  owner_is_pool_program : Prop
  account_is_writable : Prop
  required_signers_present : Prop
  lane_pda_matches_master_and_lane : Prop

/-- A successful translated hot decode necessarily consumed the explicit
    program-owned-state capability and the exact 768-byte account image. -/
theorem hot_decode_success_requires_capability_and_exact_length
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize)
    (program_owned_invariant : Bool)
    (lane : LaneState)
    (hrun :
      hot_decode_projected bytes expected_master expected_lane empty_roots
          program_owned_invariant = ok (.Ok lane)) :
    program_owned_invariant = true ∧
      Slice.len bytes = 768#usize := by
  cases program_owned_invariant with
  | false =>
      simp [hot_decode_projected] at hrun
  | true =>
      constructor
      · rfl
      · by_contra hlength
        have hneVal :
            (Slice.len bytes).val ≠ (768#usize).val :=
          (UScalar.neq_to_neq_val).mp hlength
        have hneLen : bytes.length ≠ 768 := by simpa using hneVal
        have haccount : LANE_ACCOUNT_BYTES = ok 768#usize := by
          unfold LANE_ACCOUNT_BYTES LANE_HEADER_BYTES TREE_STATE_BYTES
          change UScalar.add (80#usize) (688#usize) = ok 768#usize
          simp [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
            UScalar.inBounds]
          cases System.Platform.numBits_eq <;> simp [*]
        unfold hot_decode_projected at hrun
        simp only [haccount] at hrun
        simp [hneLen] at hrun

/-- The missing capability is rejected before parsing any attacker-controlled
    bytes. -/
theorem hot_decoder_rejects_missing_program_owned_invariant
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize) :
    hot_decode_projected bytes expected_master expected_lane empty_roots false =
      ok (.Err LaneSourceError.MissingProgramOwnedInvariant) := by
  simp [hot_decode_projected]

#print axioms hot_decode_success_requires_capability_and_exact_length
#print axioms hot_decoder_rejects_missing_program_owned_invariant

end V7ForestLaneInvariantGenerated
