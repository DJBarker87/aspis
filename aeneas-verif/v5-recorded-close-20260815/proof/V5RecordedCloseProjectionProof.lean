import V5RecordedCloseProjection.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5RecordedCloseProjectionProof

open V5RecordedCloseProjectionGenerated

structure ChecksHold (checks : CloseChecks) : Prop where
  uploadedBoundsValid : checks.uploaded_bounds_valid = true
  proofFinalized : checks.proof_finalized = true
  proofOwnedByProgram : checks.proof_owned_by_program = true
  refundSystemOwned : checks.refund_system_owned = true
  proofSigner : checks.proof_signer = true
  refundSigner : checks.refund_signer = true
  proofWritable : checks.proof_writable = true
  refundWritable : checks.refund_writable = true
  distinctAddresses : checks.distinct_addresses = true
  dataHasFourBytes : checks.data_has_four_bytes = true

theorem checked_add_exact_of_bound (left right : Std.U64)
    (bound : left.val + right.val < 2 ^ 64) :
    ∃ sum,
      U64.checked_add left right = some sum ∧
      sum.val = left.val + right.val := by
  have spec := U64.checked_add_bv_spec left right
  cases h : U64.checked_add left right with
  | none =>
      simp [h, U64.max, U64.numBits] at spec
      omega
  | some sum =>
      simp [h] at spec
      exact ⟨sum, rfl, spec.2.1⟩

def successfulOutput {A S : Type} (proofAddress refundAddress : A)
    (state : CloseState S) (sum : Std.U64) : CloseOutput A S :=
  { proof_address := proofAddress
    refund_recipient := refundAddress
    proof_prefix := Array.make 4#usize [65#u8, 83#u8, 80#u8, 67#u8]
    proof_suffix := state.proof_suffix
    proof_lamports := 0#u64
    refund_lamports := sum }

theorem generated_successful_path_is_exact
    {A S : Type} (checks : CloseChecks)
    (proofAddress refundAddress : A) (state : CloseState S)
    (checksHold : ChecksHold checks)
    (positive : state.proof_lamports ≠ 0#u64)
    (bound : state.refund_lamports.val + state.proof_lamports.val < 2 ^ 64) :
    ∃ sum,
      source_shaped_close checks proofAddress refundAddress state =
        .ok (.Ok (successfulOutput proofAddress refundAddress state sum)) ∧
      sum.val = state.refund_lamports.val + state.proof_lamports.val ∧
      (successfulOutput proofAddress refundAddress state sum).proof_address =
        proofAddress ∧
      (successfulOutput proofAddress refundAddress state sum).refund_recipient =
        refundAddress ∧
      (successfulOutput proofAddress refundAddress state sum).proof_prefix.val =
        [65#u8, 83#u8, 80#u8, 67#u8] ∧
      (successfulOutput proofAddress refundAddress state sum).proof_suffix =
        state.proof_suffix ∧
      (successfulOutput proofAddress refundAddress state sum).proof_lamports =
        0#u64 ∧
      (successfulOutput proofAddress refundAddress state sum).refund_lamports =
        sum := by
  obtain ⟨sum, addEq, sumValue⟩ :=
    checked_add_exact_of_bound state.refund_lamports state.proof_lamports bound
  refine ⟨sum, ?_, sumValue, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [source_shaped_close, checksHold.uploadedBoundsValid,
    checksHold.proofFinalized, checksHold.proofOwnedByProgram,
    checksHold.refundSystemOwned, checksHold.proofSigner,
    checksHold.refundSigner, checksHold.proofWritable,
    checksHold.refundWritable, checksHold.distinctAddresses,
    checksHold.dataHasFourBytes, positive, addEq, successfulOutput, Std.lift]

theorem current_required_nullifier_bump_is_255 :
    current_required_nullifier_bump = .ok 255#u8 := by
  unfold current_required_nullifier_bump CURRENT_REQUIRED_NULLIFIER_BUMP
  congr 1

theorem current_bump_gate_accepts_iff_255 (derivedBump : Std.U8) :
    current_nullifier_bump_is_accepted derivedBump = .ok true ↔
      derivedBump.val = 255 := by
  simp [current_nullifier_bump_is_accepted, current_required_nullifier_bump,
    CURRENT_REQUIRED_NULLIFIER_BUMP, UScalar.eq_equiv, U8.rMax]

#print axioms checked_add_exact_of_bound
#print axioms generated_successful_path_is_exact
#print axioms current_required_nullifier_bump_is_255
#print axioms current_bump_gate_accepts_iff_255

end V5RecordedCloseProjectionProof
