import Mathlib

/-!
# V7 split-tensor Phase-1 profile

This leaf freezes only the algebraic lane inventory and padding used by the
reference implementation.  It does not enable or certify a V7 wire format.
The literal SHA-256 string binds
`manifests/v7-split-tensor-profile-r0.json` (1,548 bytes).
-/

namespace AspisV7SplitTensorProfile

def algebraProfileRevision : String := "r0-phase1-algebra"

def algebraProfileSha256Hex : String :=
  "871fd1518b1548d7daca2a48e88ef97ec05a6f5390c959d0df8af4067c89bbe0"

def rowVariables : Nat := 10
def rowCoefficients : Nat := 2 ^ rowVariables
def stageASourceLanes : Nat := 26
def stageALaneVariables : Nat := 5
def stageAPaddedLanes : Nat := 2 ^ stageALaneVariables
def qm31Limbs : Nat := 4
def stageBQM31Lanes : Nat := 3
def stageBSourceLimbs : Nat := stageBQM31Lanes * qm31Limbs
def stageBLaneVariables : Nat := 4
def stageBPaddedLanes : Nat := 2 ^ stageBLaneVariables
def stageBOuterGammaPower : Nat := stageASourceLanes
def combinedLanes : Nat := stageASourceLanes + stageBQM31Lanes
def v6FinalCoefficients : Nat := 256

theorem rowCoefficients_eq : rowCoefficients = 1024 := by norm_num [rowCoefficients, rowVariables]
theorem stageAPaddedLanes_eq : stageAPaddedLanes = 32 := by
  norm_num [stageAPaddedLanes, stageALaneVariables]
theorem stageBSourceLimbs_eq : stageBSourceLimbs = 12 := by
  norm_num [stageBSourceLimbs, stageBQM31Lanes, qm31Limbs]
theorem stageBPaddedLanes_eq : stageBPaddedLanes = 16 := by
  norm_num [stageBPaddedLanes, stageBLaneVariables]
theorem combinedLanes_eq : combinedLanes = 29 := by
  norm_num [combinedLanes, stageASourceLanes, stageBQM31Lanes]
theorem stageAZeroPaddingCount : stageAPaddedLanes - stageASourceLanes = 6 := by
  norm_num [stageAPaddedLanes, stageALaneVariables, stageASourceLanes]
theorem stageBZeroPaddingCount : stageBPaddedLanes - stageBSourceLimbs = 4 := by
  norm_num [stageBPaddedLanes, stageBLaneVariables, stageBSourceLimbs,
    stageBQM31Lanes, qm31Limbs]
theorem gammaBatchDegree : combinedLanes - 1 = 28 := by
  norm_num [combinedLanes, stageASourceLanes, stageBQM31Lanes]

end AspisV7SplitTensorProfile

