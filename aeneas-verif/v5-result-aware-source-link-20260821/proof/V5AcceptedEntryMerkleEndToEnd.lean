import V5AcceptedSameRunRelationFriSnapshot

/-!
# Accepted entry to the exact Merkle run

This file closes the remaining implementation join in the accepted V5 path.
The accepted-entry translation now calls the unchanged full Merkle translation
directly.  A successful private-suffix result can therefore be inverted into
the exact returned opening, with no source-equality premise between the two
translations.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedEntryMerkleEndToEnd

open AspisV5AcceptedEntryFriPhaseBridge
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedSameRunRelationFriSnapshot

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev EntryParsed :=
  V5AcceptedEntryGenerated.v5_cu_probe.ParsedProbeData
abbrev EntryOpenings :=
  V5AcceptedEntryGenerated.v5_cu_probe.private_openings.VerifiedV5PrivateOpenings
abbrev ExactOpenings :=
  V5MerkleUnchangedFull.private_openings.VerifiedV5PrivateOpenings

/-- A successful accepted-entry private-suffix call is literally a successful
call of the unchanged full Merkle translation.  The returned value and the two
record-equality guards are retained exactly. -/
theorem private_suffix_success_yields_exact_merkle
    (parsed : EntryParsed)
    (queries : Array Std.U32 18#usize)
    (openings : EntryOpenings)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_private_suffix
          parsed queries = .ok (.Ok openings)) :
    ∃ exactOpening : ExactOpenings,
      V5MerkleUnchangedFull.private_openings.verify_v5_private_openings
          V5AcceptedEntryGenerated.verify.sbf_hashv_totalized
          (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.rootsToExact
            parsed.v5_private_roots)
          (Array.to_slice queries) parsed.v5_private_proof =
        .ok (.Ok exactOpening) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact
          exactOpening = openings ∧
      openings.c1.records = parsed.candidate_c1 ∧
      openings.c2.records = parsed.c2 := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.verify_v5_private_suffix at success
  simp only [Std.lift, bind_tc_ok] at success
  generalize hverify :
      V5MerkleUnchangedFull.private_openings.verify_v5_private_openings
        V5AcceptedEntryGenerated.verify.sbf_hashv_totalized
        (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.rootsToExact
          parsed.v5_private_roots)
        (Array.to_slice queries) parsed.v5_private_proof = verifyResult
      at success
  cases verifyResult with
  | fail error => simp at success
  | div => simp at success
  | ok result =>
      cases result with
      | Err error => simp at success
      | Ok exactOpening =>
          simp only [bind_tc_ok] at success
          by_cases hc1 :
              (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact
                exactOpening).c1.records = parsed.candidate_c1
          · rw [if_pos hc1] at success
            by_cases hc2 :
                (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact
                  exactOpening).c2.records = parsed.c2
            · simp only [hc2, if_true, Result.ok.injEq,
                core.result.Result.Ok.injEq] at success
              subst openings
              exact ⟨exactOpening, rfl, rfl, hc1, hc2⟩
            · rw [if_neg hc2] at success
              simp at success
          · rw [if_neg hc1] at success
            simp at success

end AspisV5AcceptedEntryMerkleEndToEnd
