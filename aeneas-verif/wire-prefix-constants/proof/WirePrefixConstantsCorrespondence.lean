import WirePrefixConstantsExact
import AspisFormal.V5RepairedRuntimeWireClassification

namespace AspisV5WirePrefixConstantsCorrespondence

open Aeneas Aeneas.Std Result
open AspisV5WirePrefixConstantsExact
open AspisFormal.V5ExactRuntimeWireRepair
open AspisFormal.V5RepairedRuntimeWireClassification

/-- A checked Rust offset lands on the start of the named maintained segment,
relative to the start of the real-host prefix. -/
def OffsetMatches (offset : Result Std.Usize)
    (segment : FixedSemanticSegment) : Prop :=
  ∃ value, offset = .ok value ∧
    wirePrefixOffset + value.val = segment.start

/-- A checked Rust byte count equals the maintained byte count. -/
def BytesMatch (bytes : Result Std.Usize) (expected : Nat) : Prop :=
  ∃ value, bytes = .ok value ∧ value.val = expected

theorem extracted_header_bytes_match :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES.val =
      FixedSemanticSegment.bytes .prefixHeader := by
  rw [header_bytes]
  norm_num [FixedSemanticSegment.bytes]

theorem extracted_c1_root_offset_matches :
    OffsetMatches
      (.ok aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET)
      .prefixC1Root := by
  refine ⟨23#usize, ?_, ?_⟩
  · rw [c1_root_offset]
  · norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_c2_root_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
      .prefixC2Root := by
  refine ⟨55#usize, c2_root_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_initial_claim_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET
      .prefixInitialBClaim := by
  refine ⟨87#usize, initial_claim_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_sumcheck_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_OFFSET
      .prefixBSumcheck := by
  refine ⟨103#usize, sumcheck_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_claims_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_OFFSET
      .prefixPointClaims := by
  refine ⟨4583#usize, claims_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_terminals_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINALS_OFFSET
      .prefixTerminalReal := by
  refine ⟨5799#usize, terminals_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_inactive_claim_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET
      .prefixInactiveClaim := by
  refine ⟨5847#usize, inactive_claim_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_public_salts_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET
      .prefixPublicFsSalts := by
  refine ⟨5863#usize, public_salts_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_zero_reserve_offset_matches :
    OffsetMatches
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_OFFSET
      .prefixZeroReserve := by
  refine ⟨6023#usize, zero_reserve_offset, ?_⟩
  norm_num [wirePrefixOffset, FixedSemanticSegment.start]

theorem extracted_sumcheck_bytes_match :
    BytesMatch
      (.ok aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_BYTES)
      (FixedSemanticSegment.bytes .prefixBSumcheck) := by
  refine ⟨4480#usize, ?_, ?_⟩
  · rw [sumcheck_bytes]
  · norm_num [FixedSemanticSegment.bytes]

theorem extracted_claims_bytes_match :
    BytesMatch aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_BYTES
      (FixedSemanticSegment.bytes .prefixPointClaims) := by
  refine ⟨1216#usize, claims_bytes, ?_⟩
  norm_num [FixedSemanticSegment.bytes]

theorem extracted_terminal_bytes_match :
    BytesMatch aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINAL_BYTES
      (FixedSemanticSegment.bytes .prefixTerminalReal +
        FixedSemanticSegment.bytes .prefixTerminalMask +
        FixedSemanticSegment.bytes .prefixTerminalMasked) := by
  refine ⟨48#usize, terminal_bytes, ?_⟩
  norm_num [FixedSemanticSegment.bytes]

theorem extracted_public_salts_bytes_match :
    BytesMatch
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES
      (FixedSemanticSegment.bytes .prefixPublicFsSalts) := by
  refine ⟨160#usize, public_salts_bytes, ?_⟩
  norm_num [FixedSemanticSegment.bytes]

theorem extracted_zero_reserve_bytes_match :
    BytesMatch
      aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_BYTES
      (FixedSemanticSegment.bytes .prefixZeroReserve) := by
  refine ⟨400#usize, zero_reserve_bytes, ?_⟩
  norm_num [FixedSemanticSegment.bytes]

/-- The total extracted Rust prefix ends exactly where the maintained repaired
wire begins its atomic terminal context. -/
theorem extracted_prefix_total_matches_repaired_wire :
    wirePrefixOffset +
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_BYTES.val =
      atomicContextOffset := by
  rw [prefix_bytes]
  norm_num [wirePrefixOffset, atomicContextOffset]

/-- Source-authentic capstone for the real-host fixed prefix.  This closes the
constant/layout edge only; it does not authenticate serializer or parser code. -/
theorem extracted_prefix_constants_match_repaired_wire :
    OffsetMatches
        (.ok aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET)
        .prefixC1Root ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
        .prefixC2Root ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET
        .prefixInitialBClaim ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_OFFSET
        .prefixBSumcheck ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_OFFSET
        .prefixPointClaims ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINALS_OFFSET
        .prefixTerminalReal ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET
        .prefixInactiveClaim ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET
        .prefixPublicFsSalts ∧
      OffsetMatches
        aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_OFFSET
        .prefixZeroReserve ∧
      wirePrefixOffset +
          aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_BYTES.val =
        atomicContextOffset := by
  exact ⟨extracted_c1_root_offset_matches,
    extracted_c2_root_offset_matches,
    extracted_initial_claim_offset_matches,
    extracted_sumcheck_offset_matches,
    extracted_claims_offset_matches,
    extracted_terminals_offset_matches,
    extracted_inactive_claim_offset_matches,
    extracted_public_salts_offset_matches,
    extracted_zero_reserve_offset_matches,
    extracted_prefix_total_matches_repaired_wire⟩

#print axioms extracted_header_bytes_match
#print axioms extracted_c1_root_offset_matches
#print axioms extracted_c2_root_offset_matches
#print axioms extracted_initial_claim_offset_matches
#print axioms extracted_sumcheck_offset_matches
#print axioms extracted_claims_offset_matches
#print axioms extracted_terminals_offset_matches
#print axioms extracted_inactive_claim_offset_matches
#print axioms extracted_public_salts_offset_matches
#print axioms extracted_zero_reserve_offset_matches
#print axioms extracted_sumcheck_bytes_match
#print axioms extracted_claims_bytes_match
#print axioms extracted_terminal_bytes_match
#print axioms extracted_public_salts_bytes_match
#print axioms extracted_zero_reserve_bytes_match
#print axioms extracted_prefix_total_matches_repaired_wire
#print axioms extracted_prefix_constants_match_repaired_wire

end AspisV5WirePrefixConstantsCorrespondence
