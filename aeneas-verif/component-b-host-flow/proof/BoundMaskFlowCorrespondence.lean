import BoundMaskFlow

open Aeneas Aeneas.Std Result

namespace AspisComponentBHostFlow

namespace Extracted

abbrev M31 := ComponentBHostFlowGenerated.aspis_core.field.M31
abbrev CM31 := ComponentBHostFlowGenerated.aspis_core.field.CM31
abbrev QM31 := ComponentBHostFlowGenerated.aspis_core.field.QM31
abbrev Mask := ComponentBHostFlowGenerated.v5_sumcheck_mask.V5SumcheckMask
abbrev BoundMask :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask

abbrev bind :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask.new
abbrev forCommitment :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask.for_commitment
abbrev forInitialClaim :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask.for_initial_claim
abbrev forSumcheck :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask.for_sumcheck
abbrev forTerminal :=
  ComponentBHostFlowGenerated.v5_mask.real_host_proof.V5RealHostBoundSumcheckMask.for_terminal

structure HostMaskRoles where
  commitment : Mask
  initialClaim : Mask
  sumcheck : Mask
  terminal : Mask

def roles (mask : Mask) : Result HostMaskRoles := do
  let bound ← bind mask
  let commitment ← forCommitment bound
  let initialClaim ← forInitialClaim bound
  let sumcheck ← forSumcheck bound
  let terminal ← forTerminal bound
  ok { commitment, initialClaim, sumcheck, terminal }

theorem extracted_bind_returns_exact_mask (mask : Mask) :
    bind mask = ok { mask := mask } := by
  rfl

theorem extracted_commitment_role_is_source (mask : Mask) :
    roles mask = ok
      { commitment := mask
        initialClaim := mask
        sumcheck := mask
        terminal := mask } := by
  rfl

theorem extracted_all_roles_are_one_immutable_source (mask : Mask) :
    ∃ bound,
      bind mask = ok bound ∧
      forCommitment bound = ok mask ∧
      forInitialClaim bound = ok mask ∧
      forSumcheck bound = ok mask ∧
      forTerminal bound = ok mask := by
  exact ⟨{ mask := mask }, rfl, rfl, rfl, rfl, rfl⟩

/-- Source-authentic object-flow provenance from the caller-provided mask.

This theorem does not claim that the real host samples the mask, nor that the
caller's source is uniform.  It proves only that the one mask supplied by the
caller is the same immutable value returned for all four consuming roles. -/
theorem V5RealHostInputsSumcheckMaskProvenanceAndFlow (mask : Mask) :
    ∃ bound,
      bind mask = ok bound ∧
      forCommitment bound = ok mask ∧
      forInitialClaim bound = ok mask ∧
      forSumcheck bound = ok mask ∧
      forTerminal bound = ok mask :=
  extracted_all_roles_are_one_immutable_source mask

def wrongTerminalSubstitution (commitment terminal : Mask) : HostMaskRoles :=
  { commitment
    initialClaim := commitment
    sumcheck := commitment
    terminal }

theorem terminal_substitution_changes_roles
    (commitment terminal : Mask) (h : commitment ≠ terminal) :
    wrongTerminalSubstitution commitment terminal ≠
      { commitment := commitment
        initialClaim := commitment
        sumcheck := commitment
        terminal := commitment } := by
  intro heq
  apply h
  exact congrArg HostMaskRoles.terminal heq |>.symm

def zeroCM31 : CM31 :=
  { a := 0#u32, b := 0#u32 }

def zeroQM31 : QM31 :=
  { c0 := zeroCM31, c1 := zeroCM31 }

def oneQM31 : QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := zeroCM31 }

def zeroClaimMask (rounds : Array (Array QM31 28#usize) 10#usize) : Mask :=
  { initial_claim := zeroQM31, zero_boundary_rounds := rounds }

def oneClaimMask (rounds : Array (Array QM31 28#usize) 10#usize) : Mask :=
  { initial_claim := oneQM31, zero_boundary_rounds := rounds }

theorem zeroClaimMask_ne_oneClaimMask
    (rounds : Array (Array QM31 28#usize) 10#usize) :
    zeroClaimMask rounds ≠ oneClaimMask rounds := by
  intro h
  have hval := congrArg (fun mask => mask.initial_claim.c0.a.val) h
  simp [zeroClaimMask, oneClaimMask, zeroQM31, oneQM31, zeroCM31] at hval

theorem concrete_terminal_swap_is_detected
    (rounds : Array (Array QM31 28#usize) 10#usize) :
    wrongTerminalSubstitution (zeroClaimMask rounds) (oneClaimMask rounds) ≠
      { commitment := zeroClaimMask rounds
        initialClaim := zeroClaimMask rounds
        sumcheck := zeroClaimMask rounds
        terminal := zeroClaimMask rounds } := by
  exact terminal_substitution_changes_roles _ _ (zeroClaimMask_ne_oneClaimMask rounds)

#print axioms extracted_bind_returns_exact_mask
#print axioms extracted_commitment_role_is_source
#print axioms extracted_all_roles_are_one_immutable_source
#print axioms V5RealHostInputsSumcheckMaskProvenanceAndFlow
#print axioms terminal_substitution_changes_roles
#print axioms zeroClaimMask_ne_oneClaimMask
#print axioms concrete_terminal_swap_is_detected

end Extracted

end AspisComponentBHostFlow
