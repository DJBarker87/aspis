import V7ForestLaneInvariant.Funs
import V7ForestLaneHotDecodeBridge
import V7ForestLaneWriterInvariant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- Exact direct-invocation gate mirrored from the feature-gated six-account
    verifier reader. No single owner/PDA/request field is treated as the
    release capability. -/
def ExactDirectAsq8ReleaseAuthentication
    (authentication : DirectAsq8ReleaseAuthentication) : Prop :=
  authentication.exact_six_accounts = true ∧
  authentication.all_accounts_distinct = true ∧
  authentication.proof_exact_verifier_owned_readonly = true ∧
  authentication.pool_accounts_exact_release_owned_readonly = true ∧
  authentication.pool_program_matches_immutable_release = true ∧
  authentication.master_codec_identity_pda_and_all_lanes = true ∧
  authentication.checkpoint_codec_pda_and_deployment = true ∧
  authentication.policy_matches_immutable_registry_root = true ∧
  authentication.registry_accounts_exact_program_owned_readonly = true ∧
  authentication.registry_pda_codec_policy_immutable_unpaused = true ∧
  authentication.entry_pda_codec_and_active_slot = true ∧
  authentication.entry_exact_pool_verifier_profile_release_version = true ∧
  authentication.selected_lane_pda_master_and_lane = true

/-- Successful translated execution exposes every release/authentication gate,
    consumes the separately named Pool-owned-lane capability, and retains the
    exact 768-byte lane image requirement. -/
theorem direct_asq8_lane_read_success_has_exact_gate_and_capability
    (authentication : DirectAsq8ReleaseAuthentication)
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize)
    (program_owned_lane_invariant : Bool)
    (lane : LaneState)
    (hrun :
      direct_asq8_lane_read_projected authentication bytes expected_master
          expected_lane empty_roots program_owned_lane_invariant =
        ok (.Ok lane)) :
    ExactDirectAsq8ReleaseAuthentication authentication ∧
      program_owned_lane_invariant = true ∧
      Slice.len bytes = 768#usize := by
  unfold direct_asq8_lane_read_projected at hrun
  have h1 : authentication.exact_six_accounts = true := by
    cases h : authentication.exact_six_accounts
    · simp [h] at hrun
    · rfl
  simp only [h1, if_true] at hrun
  have h2 : authentication.all_accounts_distinct = true := by
    cases h : authentication.all_accounts_distinct
    · simp [h] at hrun
    · rfl
  simp only [h2, if_true] at hrun
  have h3 : authentication.proof_exact_verifier_owned_readonly = true := by
    cases h : authentication.proof_exact_verifier_owned_readonly
    · simp [h] at hrun
    · rfl
  simp only [h3, if_true] at hrun
  have h4 : authentication.pool_accounts_exact_release_owned_readonly = true := by
    cases h : authentication.pool_accounts_exact_release_owned_readonly
    · simp [h] at hrun
    · rfl
  simp only [h4, if_true] at hrun
  have h5 : authentication.pool_program_matches_immutable_release = true := by
    cases h : authentication.pool_program_matches_immutable_release
    · simp [h] at hrun
    · rfl
  simp only [h5, if_true] at hrun
  have h6 : authentication.master_codec_identity_pda_and_all_lanes = true := by
    cases h : authentication.master_codec_identity_pda_and_all_lanes
    · simp [h] at hrun
    · rfl
  simp only [h6, if_true] at hrun
  have h7 : authentication.checkpoint_codec_pda_and_deployment = true := by
    cases h : authentication.checkpoint_codec_pda_and_deployment
    · simp [h] at hrun
    · rfl
  simp only [h7, if_true] at hrun
  have h8 : authentication.policy_matches_immutable_registry_root = true := by
    cases h : authentication.policy_matches_immutable_registry_root
    · simp [h] at hrun
    · rfl
  simp only [h8, if_true] at hrun
  have h9 : authentication.registry_accounts_exact_program_owned_readonly = true := by
    cases h : authentication.registry_accounts_exact_program_owned_readonly
    · simp [h] at hrun
    · rfl
  simp only [h9, if_true] at hrun
  have h10 : authentication.registry_pda_codec_policy_immutable_unpaused = true := by
    cases h : authentication.registry_pda_codec_policy_immutable_unpaused
    · simp [h] at hrun
    · rfl
  simp only [h10, if_true] at hrun
  have h11 : authentication.entry_pda_codec_and_active_slot = true := by
    cases h : authentication.entry_pda_codec_and_active_slot
    · simp [h] at hrun
    · rfl
  simp only [h11, if_true] at hrun
  have h12 : authentication.entry_exact_pool_verifier_profile_release_version = true := by
    cases h : authentication.entry_exact_pool_verifier_profile_release_version
    · simp [h] at hrun
    · rfl
  simp only [h12, if_true] at hrun
  have h13 : authentication.selected_lane_pda_master_and_lane = true := by
    cases h : authentication.selected_lane_pda_master_and_lane
    · simp [h] at hrun
    · rfl
  simp only [h13, if_true] at hrun
  have hsource := hot_decode_success_requires_capability_and_exact_length
    bytes expected_master expected_lane empty_roots
    program_owned_lane_invariant lane hrun
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩,
    hsource⟩

/-- The verifier fast reader accepts only fresh-PDA activation. The current
    source has no migration instruction, so a checked-migration witness is not
    an admissible input to this composition theorem. -/
structure FreshInitializedVerifierLaneCapability
    (capability : ProgramOwnedLaneInvariantCapability)
    (lane : LaneState) : Type where
  activated : ActivatedProgramOwnedLane capability lane
  fresh_initialized_only :
    activated.boundary = LaneInvariantActivationBoundary.newlyInitializedPda

/-- Strongest direct-reader theorem. It starts from literal translated reader
    success plus an explicitly fresh activated lane; it never derives the
    invariant from ownership, a PDA, the request, or even the registry alone. -/
theorem translated_direct_asq8_reader_consumes_fresh_pool_invariant
    (capability : ProgramOwnedLaneInvariantCapability)
    (authentication : DirectAsq8ReleaseAuthentication)
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize)
    (program_owned_lane_invariant : Bool)
    (lane : LaneState)
    (fresh : FreshInitializedVerifierLaneCapability capability lane)
    (hrun :
      direct_asq8_lane_read_projected authentication bytes expected_master
          expected_lane empty_roots program_owned_lane_invariant =
        ok (.Ok lane)) :
    ExactDirectAsq8ReleaseAuthentication authentication ∧
      program_owned_lane_invariant = true ∧
      Slice.len bytes = 768#usize ∧
      capability.Holds lane ∧
      fresh.activated.boundary =
        LaneInvariantActivationBoundary.newlyInitializedPda := by
  have hsource := direct_asq8_lane_read_success_has_exact_gate_and_capability
    authentication bytes expected_master expected_lane empty_roots
    program_owned_lane_invariant lane hrun
  exact ⟨hsource.1, hsource.2.1, hsource.2.2,
    fresh.activated.invariant_holds, fresh.fresh_initialized_only⟩

/-- Even a completely authenticated released Pool/registry universe is
    rejected without the separately supplied lane invariant capability. This
    is stronger than merely showing that owner alone is insufficient. -/
theorem exact_release_authentication_without_lane_invariant_rejected
    (authentication : DirectAsq8ReleaseAuthentication)
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize)
    (hauth : ExactDirectAsq8ReleaseAuthentication authentication) :
    direct_asq8_lane_read_projected authentication bytes expected_master
        expected_lane empty_roots false =
      ok (.Err LaneSourceError.MissingProgramOwnedInvariant) := by
  rcases hauth with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  simp [direct_asq8_lane_read_projected, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, h12, h13, hot_decode_projected]

#print axioms direct_asq8_lane_read_success_has_exact_gate_and_capability
#print axioms translated_direct_asq8_reader_consumes_fresh_pool_invariant
#print axioms exact_release_authentication_without_lane_invariant_rejected

end V7ForestLaneInvariantGenerated
