import RuntimeScheduleValidatorCorrespondence
import RuntimeScheduleCorrespondence

set_option autoImplicit false

/-!
# Generated Component-C validator to maintained schedule bounds

Three successful calls of the source-authentic runtime validator discharge the
maintained later-fibre range predicate and all three `q18` count bounds.  This
is the exact bridge needed by the downstream model; it introduces no evaluator
or field-arithmetic premise.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeValidatedScheduleBridge

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimeScheduleProof
open ComponentCRuntimeScheduleValidatorProof

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

abbrev laterSlice1 (indices : QueryIndices) : Slice Std.U32 :=
  alloc.vec.Vec.deref (later1 indices)

abbrev laterSlice2 (indices : QueryIndices) : Slice Std.U32 :=
  alloc.vec.Vec.deref (later2 indices)

abbrev laterSlice3 (indices : QueryIndices) : Slice Std.U32 :=
  alloc.vec.Vec.deref (later3 indices)

/-- The exact conjunction of the three generated calls made by the runtime
schedule constructor. -/
def GeneratedLaterValidatorsAccept (indices : QueryIndices) : Prop :=
  v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
      (laterSlice1 indices) 1#u8 32768#u32 =
    ok (core.result.Result.Ok ()) ∧
  v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
      (laterSlice2 indices) 2#u8 8192#u32 =
    ok (core.result.Result.Ok ()) ∧
  v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
      (laterSlice3 indices) 3#u8 2048#u32 =
    ok (core.result.Result.Ok ())

/-- Successful execution of the exact three Rust validation calls supplies
the maintained range predicate and the three runtime count bounds. -/
theorem generated_validators_supply_schedule_contract
    (indices : QueryIndices)
    (hrun1 :
      v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
          (laterSlice1 indices) 1#u8 32768#u32 =
        ok (core.result.Result.Ok ()))
    (hrun2 :
      v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
          (laterSlice2 indices) 2#u8 8192#u32 =
        ok (core.result.Result.Ok ()))
    (hrun3 :
      v5_mask.component_c_runtime.validate_component_c_runtime_later_layer
          (laterSlice3 indices) 3#u8 2048#u32 =
        ok (core.result.Result.Ok ())) :
    GeneratedLaterFibresInRange indices ∧
      (later1 indices).length ≤ 18 ∧
      (later2 indices).length ≤ 18 ∧
      (later3 indices).length ≤ 18 := by
  rcases extracted_validator_success_implies_contract
      (laterSlice1 indices) 1#u8 32768#u32 hrun1 with ⟨hcount1, hrange1⟩
  rcases extracted_validator_success_implies_contract
      (laterSlice2 indices) 2#u8 8192#u32 hrun2 with ⟨hcount2, hrange2⟩
  rcases extracted_validator_success_implies_contract
      (laterSlice3 indices) 3#u8 2048#u32 hrun3 with ⟨hcount3, hrange3⟩
  refine ⟨⟨?_, ?_, ?_⟩, hcount1, hcount2, hcount3⟩
  · intro i
    have hmem : (later1 indices).val[i.val] ∈ (laterSlice1 indices).val := by
      exact List.getElem_mem i.isLt
    simpa [layer2Symbols] using
      hrange1 ((later1 indices).val[i.val]) hmem
  · intro i
    have hmem : (later2 indices).val[i.val] ∈ (laterSlice2 indices).val := by
      exact List.getElem_mem i.isLt
    simpa [layer3Symbols] using
      hrange2 ((later2 indices).val[i.val]) hmem
  · intro i
    have hmem : (later3 indices).val[i.val] ∈ (laterSlice3 indices).val := by
      exact List.getElem_mem i.isLt
    simpa [layer4Symbols] using
      hrange3 ((later3 indices).val[i.val]) hmem

/-- Conjunction form matching the constructor call site. -/
theorem generated_validator_acceptance_supplies_schedule_contract
    (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    GeneratedLaterFibresInRange indices ∧
      (later1 indices).length ≤ 18 ∧
      (later2 indices).length ≤ 18 ∧
      (later3 indices).length ≤ 18 :=
  generated_validators_supply_schedule_contract indices
    haccept.1 haccept.2.1 haccept.2.2

/-- The maintained schedule whose later fields are justified by the actual
generated validation calls. -/
def withValidatedLaterFibres
    (base : DeployedRuntimeSchedule F K)
    (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    DeployedRuntimeSchedule F K :=
  withGeneratedLaterFibres base indices
    (generated_validator_acceptance_supplies_schedule_contract
      indices haccept).1

@[simp] theorem withValidatedLaterFibres_later1Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    (withValidatedLaterFibres base indices haccept).later1Count =
      (later1 indices).length := rfl

@[simp] theorem withValidatedLaterFibres_later2Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    (withValidatedLaterFibres base indices haccept).later2Count =
      (later2 indices).length := rfl

@[simp] theorem withValidatedLaterFibres_later3Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    (withValidatedLaterFibres base indices haccept).later3Count =
      (later3 indices).length := rfl

/-- The q18 count bound is now a consequence of executable validation. -/
theorem withValidatedLaterFibres_count_bounds
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (haccept : GeneratedLaterValidatorsAccept indices) :
    RuntimeLaterCountBounds
      (withValidatedLaterFibres base indices haccept) := by
  have hcontract :=
    generated_validator_acceptance_supplies_schedule_contract indices haccept
  exact ⟨hcontract.2.1, hcontract.2.2.1, hcontract.2.2.2⟩

#print axioms generated_validators_supply_schedule_contract
#print axioms generated_validator_acceptance_supplies_schedule_contract
#print axioms withValidatedLaterFibres_later1Count
#print axioms withValidatedLaterFibres_later2Count
#print axioms withValidatedLaterFibres_later3Count
#print axioms withValidatedLaterFibres_count_bounds

end aspis_prover.ComponentCRuntimeValidatedScheduleBridge
