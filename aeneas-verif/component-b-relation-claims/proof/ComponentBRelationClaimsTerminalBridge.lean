import ComponentBRelationClaimsProof
import AspisFormal.V5CompactTerminal

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace aspis_prover.ComponentBRelationClaimsTerminalBridge

open aspis_prover.MultilinearEvalProofs
open aspis_prover.ComponentBRelationClaimsProof
open AspisV5CompactTerminal

abbrev GeneratedQM31 := aspis_core.field.QM31
abbrev ExactQM31 := aspis_prover.MultilinearEvalProofs.ExactQM31

local instance : Inhabited GeneratedQM31 :=
  ⟨aspis_core.field.QM31.ZERO⟩

instance exactRootlessInstance : Fact
    (∀ z : aspis_prover.MultilinearEvalProofs.ExactCM31,
      z ^ 2 ≠ aspis_prover.MultilinearEvalProofs.exactQm31R + 0 * z) := by
  change Fact
    (∀ z : AspisV5ComponentCQM31TowerExact.CM31Exact,
      z ^ 2 ≠ AspisV5ComponentCQM31TowerExact.qm31R + 0 * z)
  infer_instance

noncomputable instance exactFieldInstance : Field ExactQM31 := by
  infer_instance

/-- Exact maintained-field rows selected from the committed Component-B
message, in increasing physical-row order. -/
def exactCommittedBMessageRows
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize) :
    Fin 1024 → ExactQM31 :=
  fun row ↦ generatedQm31ToExact
    (generatedComponentBMessage c2Messages).val[(row : Nat)]!

/-- Exact maintained-field rows of the terminal covector supplied to the
production consumer. -/
def exactTerminalCovectorRows
    (terminalCovector : Slice GeneratedQM31) : Fin 1024 → ExactQM31 :=
  fun row ↦ generatedQm31ToExact terminalCovector.val[(row : Nat)]!

/-- The Nat-indexed accumulation proved for the source loop is literally the
maintained 1,024-row dense dot product. -/
theorem extracted_terminal_sum_eq_maintained_dot
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize)
    (terminalCovector : Slice GeneratedQM31) :
    (∑ row ∈ Finset.Ico 0 1024,
      exactSliceEntry terminalCovector row *
        generatedQm31ToExact (generatedComponentBMessage c2Messages).val[row]!) =
      dot
        (exactTerminalCovectorRows terminalCovector)
        (exactCommittedBMessageRows c2Messages) := by
  let summand := fun row : Nat ↦
    exactSliceEntry terminalCovector row *
      generatedQm31ToExact (generatedComponentBMessage c2Messages).val[row]!
  rw [Nat.Ico_zero_eq_range]
  change (∑ row ∈ Finset.range 1024, summand row) =
    ∑ row : Fin 1024, summand row.val
  exact (Fin.sum_univ_eq_sum_range summand 1024).symm

/-- The exact source-authentic consumer reaches the maintained ten-round
terminal graph once the physical covector is identified with the public
weights and the committed message agrees with the maintained sparse message
after multiplication by those weights.  The latter deliberately permits the
deployed pad and pivot rows, which lie outside terminal support.

These are deliberately concrete row equalities, not a generic `Faithful`
predicate.  They are the remaining Rust-constructor interface. -/
theorem extracted_component_b_terminal_eq_tenRoundTerminal_of_layout
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize)
    (points : Array (Array GeneratedQM31 10#usize) 3#usize)
    (terminalCovector : Slice GeneratedQM31)
    (messageLength : (generatedComponentBMessage c2Messages).val.length = 1024)
    (covectorLength : terminalCovector.val.length = 1024)
    (messageCanonical :
      GeneratedCanonicalQM31List (generatedComponentBMessage c2Messages).val)
    (point0Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 0#usize).val)
    (point1Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 1#usize).val)
    (point2Canonical :
      GeneratedCanonicalQM31List (generatedRelationPoint points 2#usize).val)
    (covectorCanonical : GeneratedCanonicalQM31List terminalCovector.val)
    (point : Round → ExactQM31) (initial : ExactQM31)
    (tails : Round → TailDegree → ExactQM31)
    (weightedMessageRows : ∀ row,
      exactTerminalCovectorRows terminalCovector row *
          exactCommittedBMessageRows c2Messages row =
        exactTerminalCovectorRows terminalCovector row *
          rowMessage initial tails row)
    (covectorRows : ∀ row,
      exactTerminalCovectorRows terminalCovector row =
        terminalWeights point 1 row) :
    ∃ out0 out1 out2 terminal,
      v5_mask.split_layer_zero.evaluate_component_b_relation_claims
          c2Messages points terminalCovector =
        ok (generatedClaimsArray out0 out1 out2 terminal) ∧
      generatedQm31ToExact terminal =
        AspisV5SumcheckCommitment.tenRoundTerminal initial tails point := by
  obtain ⟨out0, out1, out2, terminal, run, _, _, _, _, _, _, _, terminalExact⟩ :=
    extracted_component_b_relation_claims_exact c2Messages points
      terminalCovector messageLength covectorLength messageCanonical
      point0Canonical point1Canonical point2Canonical covectorCanonical
  refine ⟨out0, out1, out2, terminal, run, ?_⟩
  rw [terminalExact,
    extracted_terminal_sum_eq_maintained_dot c2Messages terminalCovector]
  have covectorEq :
      exactTerminalCovectorRows terminalCovector = terminalWeights point 1 :=
    funext covectorRows
  have weightedDotEq :
      dot (exactTerminalCovectorRows terminalCovector)
          (exactCommittedBMessageRows c2Messages) =
        dot (exactTerminalCovectorRows terminalCovector)
          (rowMessage initial tails) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro row _
    exact weightedMessageRows row
  rw [weightedDotEq, covectorEq,
    dot_terminalWeights_rowMessage_eq_tenRoundTerminal]
  exact one_mul _

/-- A concrete ordering tooth: choosing committed C2 slot zero instead of
slot one changes the selected exact row whenever those messages differ at a
row. -/
theorem lane_zero_substitution_changes_selected_row
    (c2Messages : Array (alloc.vec.Vec GeneratedQM31) 3#usize)
    (row : Fin 1024)
    (different :
      generatedQm31ToExact c2Messages.val[(0#usize).val]!.val[(row : Nat)]! ≠
        generatedQm31ToExact c2Messages.val[(1#usize).val]!.val[(row : Nat)]!) :
    generatedQm31ToExact c2Messages.val[(0#usize).val]!.val[(row : Nat)]! ≠
      exactCommittedBMessageRows c2Messages row := by
  exact different

#print axioms extracted_terminal_sum_eq_maintained_dot
#print axioms extracted_component_b_terminal_eq_tenRoundTerminal_of_layout
#print axioms lane_zero_substitution_changes_selected_row

end aspis_prover.ComponentBRelationClaimsTerminalBridge
