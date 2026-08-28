import V7ForestLaneInvariant.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ForestLaneInvariantGenerated

/-- The source strict encoder and the invariant fast encoder return byte-for-byte
    identical lane account images whenever the strict root/frontier check holds.
    The fast path does not change the codec; it replaces exactly that check with
    the named program-owned-state capability. -/
theorem valid_strict_encoder_bytes_equal_fast_encoder_bytes
    (lane : LaneState)
    (empty_roots : Array Digest 21#usize)
    (bytes : Array Std.U8 768#usize)
    (hstrict :
      strict_encode_projected lane empty_roots true =
        ok (.Ok bytes)) :
    fast_encode_projected lane empty_roots true = ok (.Ok bytes) := by
  simpa [strict_encode_projected] using hstrict

/-- Conversely, any successful fast encoding is exactly the successful strict
    encoding once the strict active-root reconstruction has been discharged. -/
theorem fast_encoder_bytes_are_strict_encoder_bytes
    (lane : LaneState)
    (empty_roots : Array Digest 21#usize)
    (bytes : Array Std.U8 768#usize)
    (hfast :
      fast_encode_projected lane empty_roots true =
        ok (.Ok bytes)) :
    strict_encode_projected lane empty_roots true = ok (.Ok bytes) := by
  simpa [strict_encode_projected] using hfast

/-- The capability is fail-closed: without it the fast encoder cannot return a
    byte image. -/
theorem fast_encoder_rejects_missing_program_owned_invariant
    (lane : LaneState)
    (empty_roots : Array Digest 21#usize) :
    fast_encode_projected lane empty_roots false =
      ok (.Err LaneSourceError.MissingProgramOwnedInvariant) := by
  simp [fast_encode_projected]

#print axioms valid_strict_encoder_bytes_equal_fast_encoder_bytes
#print axioms fast_encoder_bytes_are_strict_encoder_bytes
#print axioms fast_encoder_rejects_missing_program_owned_invariant

end V7ForestLaneInvariantGenerated
