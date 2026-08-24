import V5RelationCompactFoldKernelProof
import V5RelationCompactFoldFieldProjection
import V5RelationCompactFoldPreparedSum
import V5RelationCompactFoldPreparedSum3
import V5RelationLinkedFoldArithmetic
import AspisFormal.V5CompactTerminalOptimized

/-!
# Exact semantics of the compact four-fold state machine

This file connects the arithmetic block programs extracted from production
Rust to the four maintained compact-fold transitions.  The generated prepared
multiplier kernels are discharged by their exact arbitrary-input theorems; no
test vector or released-proof fixture is used here.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactFoldStateSemantics

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldKernelProof
open AspisV5RelationCompactFoldFieldProjection

abbrev Raw := aspis_core.field.QM31
abbrev Prepared := aspis_core.field.PreparedQm31Multiplier
abbrev Block := v5_cu_probe.CompactBTerminalBlock
abbrev State := v5_cu_probe.CompactBTerminalWeights
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited Raw := ⟨aspis_core.field.QM31.ZERO⟩
local instance : Inhabited Prepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩
local instance : Inhabited Block :=
  ⟨{ scale := aspis_core.field.QM31.ZERO
     power_lo := aspis_core.field.QM31.ZERO
     power_hi := aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

def Canonical := CanonicalQM31
def toK := toMaintainedExact

@[simp] private theorem oldMap_toK (value : Raw) :
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained
        (AspisV5RelationCompactFoldFieldProjection.toExact value) =
      toK value := by
  rfl

def CanonicalBlock (block : Block) : Prop :=
  Canonical block.scale ∧ Canonical block.power_lo ∧
    Canonical block.power_hi

def CanonicalState (state : State) : Prop :=
  (∀ index : Fin 10, CanonicalBlock state.blocks.val[index.val]!) ∧
    Canonical state.delta_scale

def projectBlock (block : Block) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  { scale := toK block.scale
    powerLo := toK block.power_lo
    powerHi := toK block.power_hi
    selector := block.selector.val }

def projectState (state : State) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  { blocks := fun index => projectBlock state.blocks.val[index.val]!
    deltaScale := toK state.delta_scale }

@[simp] theorem zero_canonical : Canonical aspis_core.field.QM31.ZERO := by
  norm_num [Canonical, CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    aspis_core.field.QM31.ZERO]

@[simp] theorem one_canonical : Canonical aspis_core.field.QM31.ONE := by
  norm_num [Canonical, CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    aspis_core.field.QM31.ONE]

@[simp] theorem zero_exact : toK aspis_core.field.QM31.ZERO = 0 := by
  norm_num [toK, toMaintainedExact, aspis_core.field.QM31.ZERO]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp
  · apply QuadraticAlgebra.ext <;> simp

@[simp] theorem one_exact : toK aspis_core.field.QM31.ONE = 1 := by
  norm_num [toK, toMaintainedExact, aspis_core.field.QM31.ONE]
  change (⟨⟨1, 0⟩, ⟨0, 0⟩⟩ : K) = ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
  rfl

private theorem optimizedBlock_ext
    {left right : AspisV5CompactTerminalOptimized.OptimizedBlock K}
    (scale : left.scale = right.scale)
    (powerLo : left.powerLo = right.powerLo)
    (powerHi : left.powerHi = right.powerHi)
    (selector : left.selector = right.selector) : left = right := by
  cases left
  cases right
  simp_all

theorem half_run_exact (input output : Raw) (canonical : Canonical input)
    (run : aspis_core.field.QM31.half input = ok output) :
    Canonical output ∧ toK output = toK input / 2 := by
  have h := generated_qm31_half_run_corresponds input output canonical run
  refine ⟨h.1, ?_⟩
  have twoNeZero : (2 : K) ≠ 0 := by decide
  apply (eq_div_iff twoNeZero).2
  rw [mul_two]
  have exactM := congrArg
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained h.2
  simpa only [oldMap_toK,
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_add] using exactM

theorem add_run_exact (left right output : Raw)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right)
    (run : aspis_core.field.QM31.add left right = ok output) :
    Canonical output ∧ toK output = toK left + toK right := by
  have h := generated_qm31_add_run_corresponds left right output
    leftCanonical rightCanonical run
  refine ⟨h.1, ?_⟩
  have exactM := congrArg
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained h.2
  simpa only [oldMap_toK,
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_add] using exactM

theorem mul_run_exact (left right output : Raw)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right)
    (run : aspis_core.field.QM31.mul left right = ok output) :
    Canonical output ∧ toK output = toK left * toK right := by
  have h := generated_qm31_mul_run_corresponds left right output
    leftCanonical rightCanonical run
  refine ⟨h.1, ?_⟩
  have exactM := congrArg
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained h.2
  simpa only [oldMap_toK,
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_mul] using exactM

theorem square_run_exact (input output : Raw) (canonical : Canonical input)
    (run : aspis_core.field.QM31.square input = ok output) :
    Canonical output ∧ toK output = toK input ^ 2 := by
  have h := generated_qm31_square_run_corresponds input output canonical run
  refine ⟨h.1, ?_⟩
  have exactM := congrArg
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained h.2
  simpa only [oldMap_toK, pow_two,
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_mul] using exactM

def PreparedTriple (prepared : Array Prepared 3#usize)
    (alpha3 alpha2 alpha : Raw) : Prop :=
  AspisV5RelationCompactFoldPreparedSum.RepresentsPrepared
      prepared.val[0]! alpha3 ∧
    AspisV5RelationCompactFoldPreparedSum.RepresentsPrepared
      prepared.val[1]! alpha2 ∧
    AspisV5RelationCompactFoldPreparedSum.RepresentsPrepared
      prepared.val[2]! alpha

theorem preparedTriple_semantic (prepared : Array Prepared 3#usize)
    (alpha3 alpha2 alpha : Raw)
    (canonical3 : Canonical alpha3) (canonical2 : Canonical alpha2)
    (canonical1 : Canonical alpha)
    (represented : PreparedTriple prepared alpha3 alpha2 alpha) :
    AspisV5RelationCompactFoldPreparedSum3.PreparedArrayRepresents prepared
      (fun index => if index = 0 then toK alpha3
        else if index = 1 then toK alpha2 else toK alpha) := by
  intro index indexLt
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · have semantic :=
      AspisV5RelationCompactFoldPreparedSum.representsPrepared_implies_preparedFor
        prepared.val[0]! alpha3 represented.1 canonical3
    simpa [AspisV5RelationCompactFoldPreparedSum3.PreparedRepresents,
      AspisV5RelationCompactFoldPreparedSum.PreparedFor,
      AspisV5RelationCompactFoldPreparedSum3.canonicalM31,
      AspisV5RelationCompactFoldPreparedSum3.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum3.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum3.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum.cachedChannel,
      AspisV5RelationCompactFoldPreparedSum.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum3.qm31View,
      AspisLane5QM31SumProductsProof.channelM31,
      toK] using semantic
  · have semantic :=
      AspisV5RelationCompactFoldPreparedSum.representsPrepared_implies_preparedFor
        prepared.val[1]! alpha2 represented.2.1 canonical2
    simpa [AspisV5RelationCompactFoldPreparedSum3.PreparedRepresents,
      AspisV5RelationCompactFoldPreparedSum.PreparedFor,
      AspisV5RelationCompactFoldPreparedSum3.canonicalM31,
      AspisV5RelationCompactFoldPreparedSum3.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum3.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum3.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum.cachedChannel,
      AspisV5RelationCompactFoldPreparedSum.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum3.qm31View,
      AspisLane5QM31SumProductsProof.channelM31,
      toK] using semantic
  · have semantic :=
      AspisV5RelationCompactFoldPreparedSum.representsPrepared_implies_preparedFor
        prepared.val[2]! alpha represented.2.2 canonical1
    simpa [AspisV5RelationCompactFoldPreparedSum3.PreparedRepresents,
      AspisV5RelationCompactFoldPreparedSum.PreparedFor,
      AspisV5RelationCompactFoldPreparedSum3.canonicalM31,
      AspisV5RelationCompactFoldPreparedSum3.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum3.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum3.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum.cachedChannel,
      AspisV5RelationCompactFoldPreparedSum.exactInputChannel,
      AspisV5RelationCompactFoldPreparedSum.exactQMComponent,
      AspisV5RelationCompactFoldPreparedSum.exactCMChannel,
      AspisV5RelationCompactFoldPreparedSum3.qm31View,
      AspisLane5QM31SumProductsProof.channelM31,
      toK] using semantic

def optimizedZeroBlock (alpha : K)
    (block : AspisV5CompactTerminalOptimized.OptimizedBlock K) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  let newPowerLo := block.powerHi ^ 2
  { scale := block.scale *
      ((1 + (alpha ^ 3 * block.powerLo + alpha ^ 2 * block.powerHi +
        alpha * (block.powerHi * block.powerLo))) / 4)
    powerLo := newPowerLo
    powerHi := newPowerLo ^ 2
    selector := block.selector }

theorem foldZeroBlock_corresponds
    (prepared : Array Prepared 3#usize) (alpha alpha2 alpha3 : Raw)
    (block output : Block)
    (alphaCanonical : Canonical alpha)
    (alpha2Canonical : Canonical alpha2)
    (alpha3Canonical : Canonical alpha3)
    (alpha2Exact : toK alpha2 = toK alpha ^ 2)
    (alpha3Exact : toK alpha3 = toK alpha ^ 3)
    (represented : PreparedTriple prepared alpha3 alpha2 alpha)
    (blockCanonical : CanonicalBlock block)
    (run : foldZeroBlock prepared block = ok output) :
    CanonicalBlock output ∧
      projectBlock output = optimizedZeroBlock (toK alpha) (projectBlock block) := by
  unfold foldZeroBlock at run
  generalize highRun : aspis_core.field.QM31.mul block.power_hi block.power_lo = highResult at run
  cases highResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok high =>
    simp only [bind_tc_ok] at run
    have highSem := mul_run_exact block.power_hi block.power_lo high
      blockCanonical.2.2 blockCanonical.2.1 highRun
    generalize weightedRun :
        aspis_core.field.qm31_sum_products3_prepared prepared
          (Array.make 3#usize [block.power_lo, block.power_hi, high]) = weightedResult at run
    cases weightedResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok weighted =>
      simp only [bind_tc_ok] at run
      have rightCanonical :
          AspisV5RelationCompactFoldPreparedSum3.CanonicalQM31Array3
            (Array.make 3#usize [block.power_lo, block.power_hi, high]) := by
        intro index indexLt
        have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
        rcases cases with rfl | rfl | rfl
        · simpa [AspisV5RelationCompactFoldPreparedSum3.canonicalQM31,
            Array.make, Canonical] using blockCanonical.2.1
        · simpa [AspisV5RelationCompactFoldPreparedSum3.canonicalQM31,
            Array.make, Canonical] using blockCanonical.2.2
        · simpa [AspisV5RelationCompactFoldPreparedSum3.canonicalQM31,
            Array.make, Canonical] using highSem.1
      have preparedSemantic := preparedTriple_semantic prepared alpha3 alpha2 alpha
        alpha3Canonical alpha2Canonical alphaCanonical represented
      obtain ⟨expectedWeighted, expectedWeightedRun, weightedCanonical,
          weightedExact⟩ :=
        AspisV5RelationCompactFoldPreparedSum3.qm31_sum_products3_prepared_corresponds
          prepared (Array.make 3#usize [block.power_lo, block.power_hi, high])
          (fun index => if index = 0 then toK alpha3
            else if index = 1 then toK alpha2 else toK alpha)
          preparedSemantic rightCanonical
      rw [weightedRun] at expectedWeightedRun
      cases expectedWeightedRun
      generalize factorRun : aspis_core.field.QM31.add aspis_core.field.QM31.ONE weighted = factorResult at run
      cases factorResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok factor =>
        simp only [bind_tc_ok] at run
        have factorSem := add_run_exact aspis_core.field.QM31.ONE weighted factor
          one_canonical weightedCanonical factorRun
        generalize powerLoRun : aspis_core.field.QM31.square block.power_hi = powerLoResult at run
        cases powerLoResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok powerLo =>
          simp only [bind_tc_ok] at run
          have powerLoSem := square_run_exact block.power_hi powerLo
            blockCanonical.2.2 powerLoRun
          generalize powerHiRun : aspis_core.field.QM31.square powerLo = powerHiResult at run
          cases powerHiResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok powerHi =>
            simp only [bind_tc_ok] at run
            have powerHiSem := square_run_exact powerLo powerHi powerLoSem.1 powerHiRun
            generalize halfRun : aspis_core.field.QM31.half factor = halfResult at run
            cases halfResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok half =>
              simp only [bind_tc_ok] at run
              have halfSem := half_run_exact factor half factorSem.1 halfRun
              generalize quarterRun : aspis_core.field.QM31.half half = quarterResult at run
              cases quarterResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok quarter =>
                simp only [bind_tc_ok] at run
                have quarterSem := half_run_exact half quarter halfSem.1 quarterRun
                generalize scaleRun : aspis_core.field.QM31.mul block.scale quarter = scaleResult at run
                cases scaleResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                | div => simp [Bind.bind, Aeneas.Std.bind] at run
                | ok scale =>
                  simp only [bind_tc_ok] at run
                  have scaleSem := mul_run_exact block.scale quarter scale
                    blockCanonical.1 quarterSem.1 scaleRun
                  cases run
                  constructor
                  · exact ⟨scaleSem.1, powerLoSem.1, powerHiSem.1⟩
                  · apply optimizedBlock_ext
                    · have weightedExactK : toK weighted =
                          AspisV5RelationCompactFoldPreparedSum3.exactPreparedProductDot
                            (fun index => if index = 0 then toK alpha3
                              else if index = 1 then toK alpha2 else toK alpha)
                            (Array.make 3#usize
                              [block.power_lo, block.power_hi, high]) :=
                        weightedExact
                      simp only [projectBlock, optimizedZeroBlock]
                      rw [scaleSem.2, quarterSem.2, halfSem.2, factorSem.2,
                        one_exact, weightedExactK]
                      simp [highSem.2, alpha2Exact, alpha3Exact, Array.make,
                        AspisV5RelationCompactFoldPreparedSum3.exactPreparedProductDot,
                        AspisV5RelationCompactFoldPreparedSum3.qm31View,
                        toK, Finset.sum_range_succ]
                      field_simp
                      left
                      have alpha3M : toMaintainedExact alpha3 =
                          toMaintainedExact alpha ^ 3 := alpha3Exact
                      have alpha2M : toMaintainedExact alpha2 =
                          toMaintainedExact alpha ^ 2 := alpha2Exact
                      have highM : toMaintainedExact high =
                          toMaintainedExact block.power_hi *
                            toMaintainedExact block.power_lo := highSem.2
                      rw [alpha3M, alpha2M, highM]
                      ring
                    · simp [projectBlock, optimizedZeroBlock, powerLoSem.2]
                    · simp [projectBlock, optimizedZeroBlock, powerHiSem.2,
                        powerLoSem.2]
                    · rfl

#print axioms foldZeroBlock_corresponds

end AspisV5CompactFoldStateSemantics
