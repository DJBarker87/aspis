import RetryCap
import AspisFormal.V5SelectionHidingAbort

namespace AspisV5RetryCapCorrespondence

/-- The cap extracted from the real feature-gated host source is exactly 17. -/
theorem extracted_retry_cap_eq_seventeen :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_HOST_GOOD_RETRY_CAP.val = 17 := by
  simp [aspis_prover.v5_mask.real_host_proof.V5_REAL_HOST_GOOD_RETRY_CAP]

/-- The extracted Rust cap is definitionally the cap used by the maintained
selection-hiding/abort model. This authenticates the bound, not the callback
loop or any production caller. -/
theorem extracted_retry_cap_matches_maintained_model :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_HOST_GOOD_RETRY_CAP.val =
      AspisV5SelectionHidingAbort.spendRetryCap := by
  rw [AspisV5SelectionHidingAbort.spendRetryCap_eq]
  exact extracted_retry_cap_eq_seventeen

#print axioms extracted_retry_cap_eq_seventeen
#print axioms extracted_retry_cap_matches_maintained_model

end AspisV5RetryCapCorrespondence
