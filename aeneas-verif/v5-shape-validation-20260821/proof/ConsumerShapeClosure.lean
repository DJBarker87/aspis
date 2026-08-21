import ShapePreservesInput
import V5FriConsumerEndToEndProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5ShapeValidationProof

/-- The consumer's former shape-validation premise follows directly from the
transparent Aeneas translation of the production Rust validator. -/
theorem validationSuccessPreservesShape :
    AspisV5FriConsumerExactProof.ValidationSuccessPreservesShape := by
  intro input output h
  apply generatedValidationSuccessPreservesInput input output
  simpa [
    V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsShape.validate,
    V5ShapeValidationSource.circle_pcs_shape.formal_validate_shape
  ] using h

#print axioms validationSuccessPreservesShape

end V5ShapeValidationProof
