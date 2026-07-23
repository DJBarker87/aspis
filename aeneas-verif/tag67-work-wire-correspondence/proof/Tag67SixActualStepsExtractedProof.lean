import Tag67SixActualStepsExtractedCore
import Tag67SixActualStepsProof
import AspisFormal.V5NonceWorkAuthentication

open Aeneas Aeneas.Std Result

namespace AspisTag67SixActualStepsExtracted

open AspisV5NonceWorkAuthentication
open tag67_six_actual_steps
open AspisTag67SixActualSteps

def nonceToU64 (nonce : Nonce64) : Std.U64 :=
  Std.U64.ofNatCore nonce.val (by exact nonce.isLt)

def extractedMaintainedStep (kind : WorkKind) (nonce : Nonce64) :
    Tag67ProofWorkStep :=
  match kind with
  | .batch => ⟨0#u8, 37#u8, 28#u8, 255#u8, nonceToU64 nonce, 0#u8⟩
  | .fold round =>
    if round = 0 then ⟨1#u8, 34#u8, 20#u8, 0#u8, nonceToU64 nonce, 1#u8⟩
    else if round = 1 then ⟨2#u8, 33#u8, 20#u8, 1#u8, nonceToU64 nonce, 2#u8⟩
    else if round = 2 then ⟨3#u8, 30#u8, 20#u8, 2#u8, nonceToU64 nonce, 3#u8⟩
    else ⟨4#u8, 25#u8, 20#u8, 3#u8, nonceToU64 nonce, 4#u8⟩
  | .finalQuery => ⟨5#u8, 32#u8, 5#u8, 255#u8, nonceToU64 nonce, 5#u8⟩

def roundToUsize (round : Fin 4) : Std.Usize :=
  if round = 0 then 0#usize
  else if round = 1 then 1#usize
  else if round = 2 then 2#usize
  else 3#usize

def extractedMaintainedTrace (view : WorkWireView) :
    Array Tag67ProofWorkStep 6#usize :=
  Array.make 6#usize
    [ extractedMaintainedStep .batch (view.nonces .batch),
      extractedMaintainedStep (.fold 0) (view.nonces (.fold 0)),
      extractedMaintainedStep (.fold 1) (view.nonces (.fold 1)),
      extractedMaintainedStep (.fold 2) (view.nonces (.fold 2)),
      extractedMaintainedStep (.fold 3) (view.nonces (.fold 3)),
      extractedMaintainedStep .finalQuery (view.nonces .finalQuery) ]

theorem extracted_require_is_exact (computedOK : Bool) :
    tag67_proof_require_real_v5_work computedOK =
      ok (if computedOK then some () else none) := by
  cases computedOK <;> rfl

theorem extracted_individual_helpers_are_exact (view : WorkWireView) :
    tag67_proof_check_and_absorb_batch true (nonceToU64 (view.nonces .batch)) =
        ok (some (extractedMaintainedStep .batch (view.nonces .batch))) ∧
      (∀ round : Fin 4,
        tag67_proof_check_and_absorb_fold true
            (roundToUsize round)
            (nonceToU64 (view.nonces (.fold round))) =
          ok (some (extractedMaintainedStep (.fold round)
            (view.nonces (.fold round))))) ∧
      tag67_proof_check_and_absorb_final true
          (nonceToU64 (view.nonces .finalQuery)) =
        ok (some (extractedMaintainedStep .finalQuery
          (view.nonces .finalQuery))) := by
  constructor
  · simp [tag67_proof_check_and_absorb_batch,
      tag67_proof_require_real_v5_work, extractedMaintainedStep, nonceToU64]
  constructor
  · intro round
    fin_cases round <;>
      simp [tag67_proof_check_and_absorb_fold,
        tag67_proof_require_real_v5_work, extractedMaintainedStep, nonceToU64,
        roundToUsize]
  · simp [tag67_proof_check_and_absorb_final,
      tag67_proof_require_real_v5_work, extractedMaintainedStep, nonceToU64]

/-- Direct theorem about the source-extracted six-deep Option/Result chain. -/
theorem extracted_six_actual_steps_exact_success (view : WorkWireView) :
    tag67_proof_six_actual_steps true true true true true true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) =
        ok (some (extractedMaintainedTrace view)) := by
  simp [tag67_proof_six_actual_steps,
    tag67_proof_check_and_absorb_batch,
    tag67_proof_check_and_absorb_fold,
    tag67_proof_check_and_absorb_final,
    tag67_proof_require_real_v5_work,
    extractedMaintainedTrace, extractedMaintainedStep,
    nonceToU64]

/-- Direct short-circuit teeth for the extracted six-deep chain. -/
theorem extracted_failure_before_corresponding_absorb
    (view : WorkWireView) :
    tag67_proof_six_actual_steps false true true true true true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none ∧
    tag67_proof_six_actual_steps true false true true true true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none ∧
    tag67_proof_six_actual_steps true true false true true true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none ∧
    tag67_proof_six_actual_steps true true true false true true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none ∧
    tag67_proof_six_actual_steps true true true true false true
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none ∧
    tag67_proof_six_actual_steps true true true true true false
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) = ok none := by
  simp [tag67_proof_six_actual_steps,
    tag67_proof_check_and_absorb_batch,
    tag67_proof_check_and_absorb_fold,
    tag67_proof_check_and_absorb_final,
    tag67_proof_require_real_v5_work]

/-- The pinned-source extracted Result/Option chain and the maintained
control-flow view have exactly the same success event.  This is the bridge
used by the state-level six-position theorem; it introduces no hash premise. -/
theorem extracted_success_iff_maintained_success
    (checks : SixComputedWorkChecks) (view : WorkWireView) :
    tag67_proof_six_actual_steps
      checks.batch checks.fold0 checks.fold1 checks.fold2 checks.fold3
      checks.finalQuery
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) =
        ok (some (extractedMaintainedTrace view)) ↔
      runProofFacingSixSteps checks view = some (maintainedSixStepTrace view) := by
  rw [generated_six_steps_success_iff]
  cases checks with
  | mk batch fold0 fold1 fold2 fold3 finalQuery =>
      cases batch <;> cases fold0 <;> cases fold1 <;> cases fold2 <;>
        cases fold3 <;> cases finalQuery <;>
        simp [tag67_proof_six_actual_steps,
          tag67_proof_check_and_absorb_batch,
          tag67_proof_check_and_absorb_fold,
          tag67_proof_check_and_absorb_final,
          tag67_proof_require_real_v5_work,
          extractedMaintainedTrace, extractedMaintainedStep, nonceToU64]

#print axioms extracted_require_is_exact
#print axioms extracted_individual_helpers_are_exact
#print axioms extracted_six_actual_steps_exact_success
#print axioms extracted_failure_before_corresponding_absorb
#print axioms extracted_success_iff_maintained_success

end AspisTag67SixActualStepsExtracted
