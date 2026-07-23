import GoodMatricesCurrent.ProbeTerminalMatrix

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.ProbeTerminalMatrixAssembly

open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.ProbeTerminalMatrix
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator
open GoodMatricesCurrent.SourceExtractedTerminalWeights

abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev LocalPoint := GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalPoint

def exactAPFor (localPoint : LocalPoint) : ExactQM31 :=
  pointToExact localPoint 0 * pointToExact localPoint 1 *
    pointToExact localPoint 2 * (1 - pointToExact localPoint 9)

def exactAQFor (localPoint : LocalPoint) : ExactQM31 :=
  pointToExact localPoint 0 * pointToExact localPoint 1 *
    pointToExact localPoint 2 * pointToExact localPoint 9

def baseAPExact : ExactQM31 :=
  exactQ 1448075947 1910648760 1009516554 1327781710

def baseAQExact : ExactQM31 :=
  exactQ 2034665348 1441486141 1963349307 2053039176

def successorAPExact : ExactQM31 :=
  exactQ 650537147 2029027087 1278193916 600030510

def successorAQExact : ExactQM31 :=
  exactQ 338524148 1540559722 1381412340 560420705

theorem point_aP_exact : exactAPFor point = baseAPExact := by
  decide

theorem point_aQ_exact : exactAQFor point = baseAQExact := by
  decide

theorem successor_aP_exact : exactAPFor successor = successorAPExact := by
  decide

theorem successor_aQ_exact : exactAQFor successor = successorAQExact := by
  decide

def dotsForTerminal : Fin 3 → Fin 12 → ExactQM31 :=
  ![baseDotsExact, successorDotsExact, xorDotsExact]

def aPForTerminal : Fin 3 → ExactQM31 :=
  ![baseAPExact, successorAPExact, baseAPExact]

def aQForTerminal : Fin 3 → ExactQM31 :=
  ![baseAQExact, successorAQExact, baseAQExact]

def assembledTerminalValue (terminal : Fin 3) (column : Fin 12) :
    ExactQM31 :=
  if hcolumn : column.val < 11 then
    aPForTerminal terminal *
      (dotsForTerminal terminal ⟨column.val + 1, by omega⟩ -
        dotsForTerminal terminal 0)
  else
    aQForTerminal terminal *
      (dotsForTerminal terminal 1 - dotsForTerminal terminal 0)

def assembledTerminalMatrixFin : Matrix (Fin 12) (Fin 12)
    AspisV5ComponentCQM31TowerExact.M31Exact :=
  fun row column =>
    exactQM31Limb
      (assembledTerminalValue ⟨row.val / 4, by omega⟩ column)
      ⟨row.val % 4, Nat.mod_lt _ (by omega)⟩

theorem assembledTerminalMatrixFin_eq_printed :
    assembledTerminalMatrixFin =
      AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness.printedTerminalMatrixFin := by
  decide

end GoodMatricesCurrent.ProbeTerminalMatrixAssembly
