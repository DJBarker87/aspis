import AspisFormal.V6AcceptedPathObligations
import AspisFormal.V5ComponentADeployedTerminalApplicability

/-!
# V7 statement-point compatibility

The one-fold accepted-path model and the deployed semantic-terminal model were
developed in different namespaces.  This file proves that their three
ten-coordinate point schedules are literally the same polynomial maps.  The
result removes a definitional seam before binding the selected V7 component
evaluations to the point claims parsed from the Tag-73 transcript.
-/

set_option autoImplicit false

namespace AspisPool.V7StatementPointCompatibility

open AspisV5ComponentADeployedTerminalApplicability
open AspisV6AcceptedPathObligations

variable {K : Type*} [Field K]

theorem successorCarry_eq_deployed
    (point : Fin 10 → K) (coordinate : Fin 10) :
    AspisV6AcceptedPathObligations.successorCarry point coordinate =
      AspisV5ComponentADeployedTerminalApplicability.successorCarry
        point coordinate := by
  unfold AspisV6AcceptedPathObligations.successorCarry
    AspisV5ComponentADeployedTerminalApplicability.successorCarry
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro later _
  by_cases laterAfter : coordinate < later
  · have laterAfterVal : coordinate.val < later.val := laterAfter
    rw [if_pos laterAfterVal, if_pos laterAfter]
  · have laterNotAfterVal : ¬ coordinate.val < later.val := laterAfter
    rw [if_neg laterNotAfterVal, if_neg laterAfter]

theorem successorPoint_eq_deployed (point : Fin 10 → K) :
    AspisV6AcceptedPathObligations.successorPoint point =
      deployedSuccessorPoint point := by
  funext coordinate
  simp only [AspisV6AcceptedPathObligations.successorPoint,
    deployedSuccessorPoint]
  rw [successorCarry_eq_deployed]

theorem xor12Point_eq_deployed (point : Fin 10 → K) :
    AspisV6AcceptedPathObligations.xor12Point point =
      deployedXor12Point point := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

theorem statementPoint_eq_deployedRelationPoint
    (point : Fin 10 → K) (which : Fin 3) :
    AspisV6AcceptedPathObligations.statementPoint point which =
      deployedRelationPoint point which := by
  fin_cases which
  · rfl
  · exact successorPoint_eq_deployed point
  · exact xor12Point_eq_deployed point

#print axioms successorCarry_eq_deployed
#print axioms successorPoint_eq_deployed
#print axioms xor12Point_eq_deployed
#print axioms statementPoint_eq_deployedRelationPoint

end AspisPool.V7StatementPointCompatibility
