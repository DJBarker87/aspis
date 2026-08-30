import AspisFormal.Pool.V7SelectedEvaluatorSparsitySourceBridge

/-!
# Static inactive-schedule bridge for the selected V7 verifier

Production revision `6702cfcc987e29381085039d9da8715dafbbfce8`
replaces runtime iterator/dedup reconstruction with the exact two generated
tables below.  The tables are generated from the same Copy registry already
covered by `V7SelectedEvaluatorSparsitySourceBridge`; this module proves that
the selected lookup remains the exact complement of every active row mask.
-/

set_option autoImplicit false

namespace AspisPool.V7StaticInactiveScheduleBridge

open V7SelectedEvaluatorSparsityEquivalence
open V7SelectedEvaluatorSparsitySourceBridge

/-- Exact production revision whose Rust caller consumes the static tables. -/
def productionRevision : String :=
  "6702cfcc987e29381085039d9da8715dafbbfce8"

/-- Exact `constants::INACTIVE_ROW_GROUPS`. -/
def inactiveRowGroup : Fin 64 → Fin 7 := activeMaskCoordinate

/-- Exact `constants::INACTIVE_GROUP_MASKS`, in first-occurrence order. -/
def inactiveGroupMask : Fin 7 → Fin 65536 :=
  ![59391, 59390, 61438, 63487, 63486, 39321, 63786]

theorem inactiveGroupMask_injective : Function.Injective inactiveGroupMask := by
  decide

/-- Every emitted inactive mask is the exact 16-bit complement of its active
mask.  Writing the identity as a sum avoids importing a machine-bitwise model:
both operands are bounded by `2^16`, so their sum being `65535` uniquely fixes
the complement. -/
theorem inactiveGroupMask_complements_activeMask (group : Fin 7) :
    (inactiveGroupMask group).val + (copyActiveMask group).val = 65535 := by
  fin_cases group <;> decide

/-- End-to-end lookup identity for every one of the 64 generated row blocks. -/
theorem inactiveSchedule_lookup_complements_activeRow (block : Fin 64) :
    (inactiveGroupMask (inactiveRowGroup block)).val +
        (activeRowMask block).val = 65535 := by
  rw [activeRowMask_eq_basis]
  exact inactiveGroupMask_complements_activeMask (activeMaskCoordinate block)

#print axioms inactiveGroupMask_injective
#print axioms inactiveGroupMask_complements_activeMask
#print axioms inactiveSchedule_lookup_complements_activeRow

end AspisPool.V7StaticInactiveScheduleBridge
