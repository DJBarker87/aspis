import GoodMatricesCurrent.ConcreteProbeTerminalMatrixDischarge

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier
open Matrix Polynomial

namespace GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone

open AspisV5AtomicComponentACorrespondence
open AspisCircleRectangularMasking
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness
open AspisV5ComponentATerminalRankPredicate
open AspisV5FreezeAScheduleAvailability
open GoodMatricesCurrent.ConcreteProbeTerminalMatrixDischarge
open GoodMatricesCurrent.ProbeTerminalMatrixAssembly
open GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput
open GoodMatricesCurrent.SourceExtractedGoodAModelBridge
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator

abbrev Base := AspisV5ComponentADeployedTerminalApplicability.Base
abbrev Tower := AspisV5ComponentADeployedTerminalApplicability.Tower

private def nextShift (direction : Fin 11) : Fin 12 :=
  ⟨direction.val + 1, by omega⟩

private theorem deployedAEncoder_apply_explicit
    (coins : AspisV5ComponentADeployedTerminalApplicability.TowerSource) :
    deployedAEncoder coins =
      alignedReserveEmbed Tower (deployedAConversion coins) := by
  change ((alignedReserveEmbed Tower).comp deployedAConversion) coins = _
  exact LinearMap.comp_apply _ _ coins

private theorem kernelDirection_x (direction : Fin 11) :
    kernelDirection naturalQ18 (0, direction) =
      xBlockOrdinary
        (polynomialBlock
          (AspisV5ComponentARankCompletion.kernelShift naturalQ18
            (nextShift direction).val)) := by
  simp [kernelDirection, ordinaryPolynomialDirection, xBlockOrdinary,
    nextShift]

private theorem kernelDirection_y_zero :
    kernelDirection naturalQ18 (1, 0) =
      yBlockOrdinary
        (polynomialBlock
          (AspisV5ComponentARankCompletion.kernelShift naturalQ18 1)) := by
  simp [kernelDirection, ordinaryPolynomialDirection, yBlockOrdinary]

private theorem deployedTerminal_x (direction : Fin 11) (terminal : Fin 3) :
    deployedTerminalModel probePoint
        (liftBaseCoins (kernelDirection naturalQ18 (0, direction))) terminal =
      aPForTerminal terminal *
        (dotsForTerminal terminal (nextShift direction) -
          dotsForTerminal terminal 0) := by
  rw [deployedTerminalModel_apply, deployedMessageTerminal_apply,
    multilinearEvalAt_apply, kernelDirection_x,
    deployedAEncoder_apply_explicit]
  fin_cases terminal
  · simpa [deployedRelationPoint, aPForTerminal, dotsForTerminal] using
      aligned_x_kernelShift_eval_base (nextShift direction)
  · simpa [deployedRelationPoint, aPForTerminal, dotsForTerminal] using
      aligned_x_kernelShift_eval_successor (nextShift direction)
  · simpa [deployedRelationPoint, aPForTerminal, dotsForTerminal] using
      aligned_x_kernelShift_eval_xor (nextShift direction)

private theorem deployedTerminal_y_zero (terminal : Fin 3) :
    deployedTerminalModel probePoint
        (liftBaseCoins (kernelDirection naturalQ18 (1, 0))) terminal =
      aQForTerminal terminal *
        (dotsForTerminal terminal 1 - dotsForTerminal terminal 0) := by
  rw [deployedTerminalModel_apply, deployedMessageTerminal_apply,
    multilinearEvalAt_apply, kernelDirection_y_zero,
    deployedAEncoder_apply_explicit]
  fin_cases terminal
  · simpa [deployedRelationPoint, aQForTerminal, dotsForTerminal] using
      aligned_y_kernelShift_eval_base (1 : Fin 12)
  · simpa [deployedRelationPoint, aQForTerminal, dotsForTerminal] using
      aligned_y_kernelShift_eval_successor (1 : Fin 12)
  · simpa [deployedRelationPoint, aQForTerminal, dotsForTerminal] using
      aligned_y_kernelShift_eval_xor (1 : Fin 12)

private theorem deployedTerminal_selected
    (terminal : Fin 3) (column : TerminalLimb) :
    deployedTerminalModel probePoint
        (liftBaseCoins
          (kernelDirection naturalQ18
            (fixedFirstTwelveDirection column))) terminal =
      assembledTerminalValue terminal (terminalLimbOrdinal column) := by
  by_cases hcolumn : (terminalLimbOrdinal column).val < 11
  · have hcolumnIndex : (terminalLimbIndex column).val < 11 := by
      simpa [terminalLimbOrdinal] using hcolumn
    unfold fixedFirstTwelveDirection
    rw [dif_pos hcolumnIndex]
    rw [deployedTerminal_x]
    unfold assembledTerminalValue
    rw [dif_pos hcolumn]
    rfl
  · have hcolumnIndex : ¬(terminalLimbIndex column).val < 11 := by
      simpa [terminalLimbOrdinal] using hcolumn
    unfold fixedFirstTwelveDirection
    rw [dif_neg hcolumnIndex]
    rw [deployedTerminal_y_zero]
    unfold assembledTerminalValue
    rw [dif_neg hcolumn]

private theorem exactQM31Limb_eq_towerCoordinates
    (value : Tower) (limb : Fin 4) :
    exactQM31Limb value limb = towerCoordinates value limb := by
  fin_cases limb <;> rfl

private theorem terminalPoint_from_ordinal (output : TerminalLimb) :
    (⟨(terminalLimbOrdinal output).val / 4, by
      have hpoint := output.1.isLt
      have hlimb := output.2.isLt
      simp [terminalLimbOrdinal, terminalLimbIndex]
      omega⟩ : Fin 3) = output.1 := by
  apply Fin.ext
  simp [terminalLimbOrdinal, terminalLimbIndex]
  omega

private theorem terminalLimb_from_ordinal (output : TerminalLimb) :
    (⟨(terminalLimbOrdinal output).val % 4, Nat.mod_lt _ (by omega)⟩ :
      Fin 4) = output.2 := by
  apply Fin.ext
  simp [terminalLimbOrdinal, terminalLimbIndex]

private theorem selectedTerminalMinor_apply
    (schedule : PublicTerminalSchedule Tower) (row column : TerminalLimb) :
    selectedTerminalMinor schedule row column =
      deployedTerminalLimbMap schedule.point
        (kernelDirection schedule.q18
          (fixedFirstTwelveDirection column)) row := by
  unfold selectedTerminalMinor
  rw [Matrix.submatrix_apply]
  unfold terminalDirectionMatrix
  simp only [id_eq]

theorem selectedTerminalMinor_entry_eq_assembled
    (row column : TerminalLimb) :
    selectedTerminalMinor concreteSchedule row column =
      assembledTerminalMatrixFin (terminalLimbOrdinal row)
        (terminalLimbOrdinal column) := by
  rw [selectedTerminalMinor_apply]
  rw [deployedTerminalLimbMap_apply]
  dsimp only [concreteSchedule]
  rw [deployedTerminal_selected]
  unfold assembledTerminalMatrixFin
  rw [terminalPoint_from_ordinal, terminalLimb_from_ordinal]
  exact (exactQM31Limb_eq_towerCoordinates _ _).symm

/-- The maintained concrete selected minor is exactly the generated/printed
12-by-12 matrix, with no correspondence premise. -/
theorem concreteProbeTerminalMatrixEquality_unconditional :
    ConcreteProbeTerminalMatrixEquality := by
  unfold ConcreteProbeTerminalMatrixEquality
  ext row column
  rw [selectedTerminalMinor_entry_eq_assembled]
  rw [show assembledTerminalMatrixFin = printedTerminalMatrixFin by
    exact assembledTerminalMatrixFin_eq_printed]
  rfl

/-- Concrete non-vacuity of the maintained Component-A gate. -/
theorem concreteProbe_goodA_unconditional : GoodA concreteSchedule :=
  concreteProbe_goodA_of_terminal_matrix_equality
    concreteProbeTerminalMatrixEquality_unconditional

/-- Source-authentic generated matrix construction and maintained GoodA meet
at the same exact printed matrix. -/
theorem generated_and_maintained_goodA_capstone :
    (∃ finalA finalB,
      v5_cu_probe.good_gate_probe.good_matrices
          GoodMatricesCurrent.ProbeGeneratedConcrete.kernel
          GoodMatricesCurrent.ProbeGeneratedConcrete.point =
        .ok (finalA, finalB) ∧
      aMatrixToExact finalA = printedTerminalMatrixFin) ∧
    ConcreteProbeTerminalMatrixEquality ∧
    GoodA concreteSchedule := by
  exact ⟨generated_good_matrices_a_projection_eq_printed,
    concreteProbeTerminalMatrixEquality_unconditional,
    concreteProbe_goodA_unconditional⟩

#print axioms selectedTerminalMinor_entry_eq_assembled
#print axioms concreteProbeTerminalMatrixEquality_unconditional
#print axioms concreteProbe_goodA_unconditional
#print axioms generated_and_maintained_goodA_capstone

end GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone
