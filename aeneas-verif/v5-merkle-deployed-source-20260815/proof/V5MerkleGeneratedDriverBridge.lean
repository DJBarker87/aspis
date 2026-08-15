import V5MerkleDeployedSource.Funs
import AspisFormal.V5MerkleRustBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedDriverBridge

open V5MerkleDeployedSource

/-- The generated top-level verifier accepts exactly when the generated
`from_proof` driver returns a successful value with an empty remainder.  This
is the final trailing-byte check; it does not assign mathematical meaning to
the five Merkle helper calls inside `from_proof`. -/
theorem generated_verify_success_iff_from_proof_success_empty
    (roots : private_openings.V5PrivateOpeningRoots)
    (queries : Slice Std.U32) (proofBytes : Slice Std.U8)
    (verified : private_openings.VerifiedV5PrivateOpenings) :
    private_openings.verify_v5_private_openings roots queries proofBytes =
        .ok (.Ok verified) ↔
      ∃ remainder : Slice Std.U8,
        private_openings.verify_v5_private_openings_from_proof
            roots queries proofBytes = .ok (.Ok (verified, remainder)) ∧
          remainder.val = [] := by
  unfold private_openings.verify_v5_private_openings
  generalize hrun :
    private_openings.verify_v5_private_openings_from_proof
      roots queries proofBytes = run
  cases run with
  | fail error => simp
  | div => simp
  | ok result =>
      cases result with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok pair =>
          rcases pair with ⟨returned, remainder⟩
          by_cases hempty : remainder.val = []
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.slice.Slice.is_empty, hempty]
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.slice.Slice.is_empty, hempty]

#print axioms generated_verify_success_iff_from_proof_success_empty

end AspisV5MerkleGeneratedDriverBridge
