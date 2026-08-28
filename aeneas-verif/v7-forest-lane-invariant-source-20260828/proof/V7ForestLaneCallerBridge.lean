import V7ForestLaneInvariant.Funs
import V7ForestLaneHotDecodeBridge
import V7ForestLaneEncoderBridge
import V7ForestLaneWriterInvariant

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- Complete fast-decoder boundary. Owner/writable/signer/PDA checks are
    caller-side, while invariant activation must separately be traced to fresh
    initialization or checked one-time migration. -/
structure ActivatedFastDecodeCallerInput
    (capability : ProgramOwnedLaneInvariantCapability)
    (lane : LaneState) : Type where
  solana_checks : CallerSideSolanaLaneChecks
  activated_lane : ActivatedProgramOwnedLane capability lane

/-- Strongest translated caller theorem in this focused bridge. It does not
    infer the invariant from ownership: activation is an explicit input. The
    translated decoder itself proves fail-closed capability use and exact
    account size, while the inductive writer capability supplies the sole
    omitted active root↔frontier reconstruction fact. -/
theorem translated_hot_decode_has_complete_activation_boundary
    (capability : ProgramOwnedLaneInvariantCapability)
    (bytes : Slice Std.U8)
    (expected_master : Array Std.U8 32#usize)
    (expected_lane : Std.U8)
    (empty_roots : Array Digest 21#usize)
    (program_owned_invariant : Bool)
    (lane : LaneState)
    (caller : ActivatedFastDecodeCallerInput capability lane)
    (hrun :
      hot_decode_projected bytes expected_master expected_lane empty_roots
          program_owned_invariant = ok (.Ok lane)) :
    program_owned_invariant = true ∧
      Slice.len bytes = 768#usize ∧
      capability.Holds lane ∧
      Nonempty CallerSideSolanaLaneChecks := by
  have hsource := hot_decode_success_requires_capability_and_exact_length
    bytes expected_master expected_lane empty_roots program_owned_invariant
    lane hrun
  exact ⟨hsource.1, hsource.2, caller.activated_lane.invariant_holds,
    ⟨caller.solana_checks⟩⟩

/-- Every successful production mutation can be fed directly back into the
    activated fast-decoder boundary without broadening the activation modes. -/
def translated_write_to_fast_decode_activation
    (capability : ProgramOwnedLaneInvariantCapability)
    (write : ProductionLaneWrite)
    (empty_roots : Array Digest 21#usize)
    (out : LaneState)
    (checks : CallerSideSolanaLaneChecks)
    (activation : ProductionWriteActivationInput capability write)
    (hrun : apply_production_lane_write write empty_roots = ok (.Ok out)) :
    ActivatedFastDecodeCallerInput capability out :=
  ⟨checks, translated_write_renews_activation capability write empty_roots out
    activation hrun⟩

#print axioms translated_hot_decode_has_complete_activation_boundary
#print axioms translated_write_to_fast_decode_activation

end V7ForestLaneInvariantGenerated
