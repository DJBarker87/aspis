import GoodMatricesCurrent.ProbeGeneratedConcrete

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.ProbeShift

open GoodMatricesCurrent.ProbeGeneratedConcrete

abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact

theorem base_zero_exact :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
      baseDirection (0 : Fin 48) = (1447460119 : ExactM31) := by
  norm_num [baseDirection, v, Aeneas.Std.Array.make,
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact,
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
    GoodMatricesCurrent.SourceExtractedField.m31ToExact]

def direction1Local : GoodMatricesCurrent.ProbeGeneratedConcrete.LocalVector :=
  v [0#u32,1447460119#u32,0#u32,615059998#u32,0#u32,79177021#u32,
    0#u32,264360387#u32,0#u32,175677395#u32,0#u32,690316057#u32,
    0#u32,1940922128#u32,0#u32,1980834973#u32,0#u32,244042458#u32,
    0#u32,1373926702#u32,0#u32,926559219#u32,0#u32,1646207007#u32,
    0#u32,542340637#u32,0#u32,1581685827#u32,0#u32,496267907#u32,
    0#u32,29599140#u32,0#u32,1471327346#u32,0#u32,1038083065#u32,
    0#u32,268435456#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32]

example :
    GoodMatricesCurrent.SourceExtractedFixedSupport.sourceTerm
      baseDirection 0 (0 : Fin 48) = 0 := by
  have hcoefficient :
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
          baseDirection
          (AspisV5GoodGateSparseShift.sourceIndex (0 : Fin 47)) =
        (1447460119 : ExactM31) := by
    simpa [AspisV5GoodGateSparseShift.sourceIndex] using base_zero_exact
  unfold GoodMatricesCurrent.SourceExtractedFixedSupport.sourceTerm
  rw [dif_pos (by omega)]
  change
    (GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
          baseDirection
          (AspisV5GoodGateSparseShift.sourceIndex (0 : Fin 47)) •
        AspisV5GoodGateSparseShift.sparseBasis (0 : Fin 47))
      (0 : Fin 48) = 0
  rw [hcoefficient]
  classical
  simp [AspisV5GoodGateSparseShift.sparseBasis,
    AspisV5GoodGateSparseShift.successorIndex]

example :
    v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support
      baseDirection 0#usize = .ok direction1Local := by
  decide

end GoodMatricesCurrent.ProbeShift
