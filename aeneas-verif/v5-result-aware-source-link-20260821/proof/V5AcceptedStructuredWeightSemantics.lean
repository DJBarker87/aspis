import V5AcceptedAccumulatorCanonicalSchedule
import V5RelationLinkedTensorFold

/-!
# Exact mathematical weights of structured accumulator components

The production accumulator stores multilinear and tensor covectors as a
scale followed by an even-length vector of field elements.  This file gives
those compact values a radix-four meaning.  The last two stored elements are
the lowest radix-four digit, exactly matching the pair consumed by the
extracted arity-four fold helpers.
-/

namespace AspisV5AcceptedStructuredWeightSemantics

open Aeneas Aeneas.Std Result
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedPreparedSum
open AspisV5RelationLinkedStructuredFold
open AspisV5RelationLinkedSupportedFold
open AspisV5RelationLinkedTensorFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

/-- The two compact structured encodings used by the released main
accumulator. -/
inductive StructuredWeightKind where
  | multilinear
  | tensor
deriving DecidableEq

/-- One radix-four digit represented by one consecutive pair in the compact
vector.  Pair zero is the highest retained terminal pair; the recursive
weight definition below consumes the pairs from the end. -/
def structuredPairWeights (kind : StructuredWeightKind)
    (values : List RawQM31) (pair : Nat) : Fin 4 → ExactQM31 :=
  let high := toMaintainedExact values[2 * pair]!
  let low := toMaintainedExact values[2 * pair + 1]!
  match kind with
  | .multilinear => multilinearFibreWeights high low
  | .tensor => tensorFibreWeights high low

/-- Unscaled radix-four product.  Its lowest digit is stored in the last
pair used by the recursion, so a consecutive-four fold removes exactly that
pair. -/
def structuredBasisWeightNat (kind : StructuredWeightKind)
    (values : List RawQM31) : Nat → Nat → ExactQM31
  | 0, _ => 1
  | rounds + 1, index =>
      structuredBasisWeightNat kind values rounds (index / 4) *
        structuredPairWeights kind values rounds
          ⟨index % 4, Nat.mod_lt _ (by decide)⟩

/-- Radix-four domain size, written recursively so one fold's input type is
definitionally `Fin (4 * radix4Size rounds)`. -/
def radix4Size : Nat → Nat
  | 0 => 1
  | rounds + 1 => 4 * radix4Size rounds

/-- Exact covector represented by a compact structured component with
`2 * rounds` stored elements. -/
def structuredComponentWeights (kind : StructuredWeightKind)
    (rounds : Nat) (scale : RawQM31) (values : List RawQM31) :
    Fin (radix4Size rounds) → ExactQM31 :=
  fun index =>
    toMaintainedExact scale *
      structuredBasisWeightNat kind values rounds index.val

private theorem childIndex_div_four {n : Nat}
    (fibre : Fin n) (slot : Fin 4) :
    (childIndex fibre slot).val / 4 = fibre.val := by
  change (4 * fibre.val + slot.val) / 4 = fibre.val
  omega

private theorem childIndex_mod_four {n : Nat}
    (fibre : Fin n) (slot : Fin 4) :
    (childIndex fibre slot).val % 4 = slot.val := by
  simp [childIndex]

/-- One maintained dual fold of a structured radix-four covector removes its
lowest stored pair and multiplies the remaining product by that pair's exact
dual factor. -/
theorem dualWeightFoldLayer_structuredComponentWeights
    (kind : StructuredWeightKind) (rounds : Nat)
    (scale alpha : RawQM31) (values : List RawQM31) :
    dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
        (structuredComponentWeights kind (rounds + 1) scale values) =
      fun fibre =>
        structuredComponentWeights kind rounds scale values fibre *
          dualWeightFoldValue (toMaintainedExact alpha)
            (structuredPairWeights kind values rounds) := by
  funext fibre
  unfold dualWeightFoldLayer dualWeightFoldValue
    structuredComponentWeights
  simp only [structuredBasisWeightNat, childIndex_div_four,
    childIndex_mod_four]
  ring

/-- The radix-four basis only reads the first `2 * rounds` entries. -/
theorem structuredBasisWeightNat_congr_prefix
    (kind : StructuredWeightKind) (left right : List RawQM31)
    (rounds index : Nat)
    (samePrefix : ∀ position, position < 2 * rounds →
      left[position]! = right[position]!) :
    structuredBasisWeightNat kind left rounds index =
      structuredBasisWeightNat kind right rounds index := by
  induction rounds generalizing index with
  | zero => rfl
  | succ rounds ih =>
      have recursivePrefix : ∀ position, position < 2 * rounds →
          left[position]! = right[position]! := by
        intro position bound
        exact samePrefix position (by omega)
      have recursive := ih (index := index / 4) recursivePrefix
      have highExact : left[2 * rounds]! = right[2 * rounds]! :=
        samePrefix (2 * rounds) (by omega)
      have lowExact : left[2 * rounds + 1]! = right[2 * rounds + 1]! :=
        samePrefix (2 * rounds + 1) (by omega)
      have pairExact : structuredPairWeights kind left rounds =
          structuredPairWeights kind right rounds := by
        cases kind <;> funext slot <;>
          simp [structuredPairWeights, highExact, lowExact]
      simp only [structuredBasisWeightNat]
      rw [recursive, pairExact]

/-- Truncating a compact vector exactly after the entries used by a stage
does not change that stage's represented radix-four basis. -/
theorem structuredBasisWeightNat_take
    (kind : StructuredWeightKind) (values : List RawQM31)
    (rounds index : Nat) :
    structuredBasisWeightNat kind (values.take (2 * rounds)) rounds index =
      structuredBasisWeightNat kind values rounds index := by
  apply structuredBasisWeightNat_congr_prefix
  intro position bound
  simp [List.getElem!_eq_getElem?_getD, bound]

/-- A successful extracted multilinear helper call transports the complete
radix-four meaning through exactly one maintained dual fold. -/
theorem extracted_multilinear_fold_transports_weights
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31) (rounds : Nat)
    (hpointLength : point.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : CanonicalQM31 scale)
    (hpoint : AspisV5RelationLinkedStructuredFold.CanonicalList point.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3)
    (scaleOut : RawQM31) (pointOut : alloc.vec.Vec RawQM31)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut)) :
    CanonicalQM31 scaleOut ∧
      AspisV5RelationLinkedStructuredFold.CanonicalList pointOut.val ∧
      pointOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
          (structuredComponentWeights .multilinear (rounds + 1) scale
            point.val) =
        structuredComponentWeights .multilinear rounds scaleOut pointOut.val := by
  have pointLength : point.val.length = 2 * rounds + 2 := by omega
  obtain ⟨expectedScale, expectedPoint, expectedRun, expectedCanonical,
      expectedPointCanonical, expectedPointExact, expectedScaleExact⟩ :=
    extracted_multilinear_fold_exact scale point alpha alpha2 alpha3
      (2 * rounds) pointLength (by omega) hscale hpoint halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  rw [success] at expectedRun
  have outputExact : (expectedScale, expectedPoint) =
      (scaleOut, pointOut) := Result.ok.inj expectedRun.symm
  have scaleExact : expectedScale = scaleOut := congrArg Prod.fst outputExact
  have pointExact : expectedPoint = pointOut := congrArg Prod.snd outputExact
  subst scaleOut
  subst pointOut
  refine ⟨expectedCanonical, expectedPointCanonical, ?_, ?_⟩
  · rw [expectedPointExact, List.length_take, hpointLength]
    omega
  ·
    rw [dualWeightFoldLayer_structuredComponentWeights]
    funext fibre
    unfold structuredComponentWeights
    rw [expectedPointExact, structuredBasisWeightNat_take]
    rw [expectedScaleExact]
    simp only [multilinearDualFactor, structuredPairWeights]
    ring

/-- A successful extracted tensor helper call transports the complete
radix-four meaning through exactly one maintained dual fold. -/
theorem extracted_tensor_fold_transports_weights
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (rounds : Nat)
    (hfactorsLength : factors.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : CanonicalQM31 scale)
    (hfactors : AspisV5RelationLinkedTensorFold.CanonicalList factors.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (hpreparedAlpha :
      AspisV5RelationLinkedPreparedSum.RepresentsPrepared preparedAlpha alpha)
    (hpreparedAlpha2 :
      AspisV5RelationLinkedPreparedSum.RepresentsPrepared preparedAlpha2 alpha2)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3)
    (scaleOut : RawQM31) (factorsOut : alloc.vec.Vec RawQM31)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut)) :
    CanonicalQM31 scaleOut ∧
      AspisV5RelationLinkedTensorFold.CanonicalList factorsOut.val ∧
      factorsOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
          (structuredComponentWeights .tensor (rounds + 1) scale factors.val) =
        structuredComponentWeights .tensor rounds scaleOut factorsOut.val := by
  have factorsLength : factors.val.length = 2 * rounds + 2 := by omega
  obtain ⟨expectedScale, expectedFactors, expectedRun, expectedCanonical,
      expectedFactorsCanonical, expectedFactorsExact, expectedScaleExact⟩ :=
    extracted_tensor_fold_exact scale factors alpha alpha2 alpha3
      preparedAlpha preparedAlpha2 (2 * rounds) factorsLength (by omega)
      hscale hfactors halpha halpha2 halpha3 hpreparedAlpha hpreparedAlpha2
      halpha2Exact halpha3Exact
  rw [success] at expectedRun
  have outputExact : (expectedScale, expectedFactors) =
      (scaleOut, factorsOut) := Result.ok.inj expectedRun.symm
  have scaleExact : expectedScale = scaleOut := congrArg Prod.fst outputExact
  have factorsExact : expectedFactors = factorsOut :=
    congrArg Prod.snd outputExact
  subst scaleOut
  subst factorsOut
  refine ⟨expectedCanonical, expectedFactorsCanonical, ?_, ?_⟩
  · rw [expectedFactorsExact, List.length_take, hfactorsLength]
    omega
  ·
    rw [dualWeightFoldLayer_structuredComponentWeights]
    funext fibre
    unfold structuredComponentWeights
    rw [expectedFactorsExact, structuredBasisWeightNat_take]
    rw [expectedScaleExact]
    simp only [tensorDualFactor, structuredPairWeights]
    ring

abbrev LinkedComponent :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

private theorem multilinearDispatchSuccessExposesHelper
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (componentOut : LinkedComponent)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Multilinear scale point) currentLog alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = ok (none, componentOut)) :
    ∃ scaleOut pointOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut) ∧
      componentOut = .Multilinear scaleOut pointOut := by
  simp only [
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
    at success
  generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
        scale point alpha alpha2 alpha3 = helperResult at success
  cases helperResult with
  | fail error => simp at success
  | div => simp at success
  | ok output =>
      rcases output with ⟨scaleOut, pointOut⟩
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      exact ⟨scaleOut, pointOut, rfl, success.2.symm⟩

private theorem tensorDispatchSuccessExposesHelper
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (currentLog : Std.U32) (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (componentOut : LinkedComponent)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Tensor scale factors) currentLog alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = ok (none, componentOut)) :
    ∃ scaleOut factorsOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut) ∧
      componentOut = .Tensor scaleOut factorsOut := by
  simp only [
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4]
    at success
  generalize helperRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
        scale factors alpha3 preparedAlpha preparedAlpha2 = helperResult at success
  cases helperResult with
  | fail error => simp at success
  | div => simp at success
  | ok output =>
      rcases output with ⟨scaleOut, factorsOut⟩
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at success
      exact ⟨scaleOut, factorsOut, rfl, success.2.symm⟩

private theorem preparedNewSuccessRepresents
    (value : RawQM31) (prepared :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (canonical : CanonicalQM31 value)
    (success :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
        value = ok prepared) :
    RepresentsPrepared prepared value := by
  obtain ⟨expected, expectedRun, represents⟩ :=
    generated_prepared_new_establishes value canonical
  rw [success] at expectedRun
  cases expectedRun
  exact represents

/-- The power/cache calls exposed by the complete accumulator fold have the
exact canonical field meaning required by both structured helper proofs. -/
private theorem acceptedFoldPowerRunsExact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier)
    (halpha : CanonicalQM31 alpha)
    (squareRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha = ok alpha2)
    (prepareRun :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
        alpha = ok preparedAlpha)
    (prepare2Run :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
        alpha2 = ok preparedAlpha2)
    (alpha3Run :
      V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
        preparedAlpha alpha2 = ok alpha3) :
    CanonicalQM31 alpha2 ∧ CanonicalQM31 alpha3 ∧
      RepresentsPrepared preparedAlpha alpha ∧
      RepresentsPrepared preparedAlpha2 alpha2 ∧
      toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2 ∧
      toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3 := by
  have alpha2Data := generated_qm31_square_run_corresponds alpha alpha2
    halpha squareRun
  have halpha2 : CanonicalQM31 alpha2 := alpha2Data.1
  have alpha2Exact := congrArg
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained alpha2Data.2
  simp only [AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_toExact,
    pow_two,
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_mul] at alpha2Exact
  have alpha2ExactPow :
      toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2 := by
    simpa [pow_two] using alpha2Exact
  have hpreparedAlpha := preparedNewSuccessRepresents alpha preparedAlpha
    halpha prepareRun
  have hpreparedAlpha2 := preparedNewSuccessRepresents alpha2 preparedAlpha2
    halpha2 prepare2Run
  obtain ⟨expectedAlpha3, expectedAlpha3Run, expectedAlpha3Canonical,
      expectedAlpha3Exact⟩ := generated_prepared_mul_corresponds
    preparedAlpha alpha alpha2 hpreparedAlpha halpha halpha2
  rw [alpha3Run] at expectedAlpha3Run
  cases expectedAlpha3Run
  refine ⟨halpha2, expectedAlpha3Canonical, hpreparedAlpha,
    hpreparedAlpha2, alpha2ExactPow, ?_⟩
  rw [expectedAlpha3Exact, alpha2ExactPow]
  ring

/-- One multilinear cell in a successful complete-driver accumulator fold
has the exact maintained radix-four transport at the same list index. -/
theorem fullFoldMultilinearCellTransportsWeights
    (weights output : FullWeights) (alpha : RawQM31)
    (target : Nat) (targetBound : target < weights.components.val.length)
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (inputCell : componentToLinked weights.components.val[target]! =
      .Multilinear scale point)
    (rounds : Nat)
    (hpointLength : point.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : CanonicalQM31 scale)
    (hpoint : AspisV5RelationLinkedStructuredFold.CanonicalList point.val)
    (halpha : CanonicalQM31 alpha)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold weights alpha = ok output) :
    ∃ scaleOut pointOut,
      componentToLinked output.components.val[target]! =
        .Multilinear scaleOut pointOut ∧
      CanonicalQM31 scaleOut ∧
      AspisV5RelationLinkedStructuredFold.CanonicalList pointOut.val ∧
      pointOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
          (structuredComponentWeights .multilinear (rounds + 1) scale
            point.val) =
        structuredComponentWeights .multilinear rounds scaleOut
          pointOut.val := by
  have released :
      ReleasedComponent
        (componentToLinked weights.components.val[target]!) := by
    rw [inputCell]
    trivial
  obtain ⟨alpha2, alpha3, preparedAlpha, preparedAlpha2, componentOut,
      _folded, squareRun, prepareRun, prepare2Run, alpha3Run, dispatchRun,
      outputCell, _outputReleased⟩ :=
    fullFoldSuccessExposesLinkedComponent weights output alpha target
      targetBound released success
  have dispatchRun' :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Multilinear scale point) weights.log_len alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = ok (none, componentOut) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component weights.log_len alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2)
      inputCell).symm.trans dispatchRun
  obtain ⟨scaleOut, pointOut, helperRun, componentExact⟩ :=
    multilinearDispatchSuccessExposesHelper scale point weights.log_len alpha
      alpha2 alpha3 preparedAlpha preparedAlpha2 componentOut dispatchRun'
  obtain ⟨halpha2, halpha3, hpreparedAlpha, hpreparedAlpha2,
      halpha2Exact, halpha3Exact⟩ :=
    acceptedFoldPowerRunsExact alpha alpha2 alpha3 preparedAlpha
      preparedAlpha2 halpha squareRun prepareRun prepare2Run alpha3Run
  obtain ⟨hscaleOut, hpointOut, pointOutLength, weightsExact⟩ :=
    extracted_multilinear_fold_transports_weights scale point alpha alpha2
      alpha3 rounds hpointLength hrounds hscale hpoint halpha halpha2 halpha3
      halpha2Exact halpha3Exact scaleOut pointOut helperRun
  exact ⟨scaleOut, pointOut, outputCell.trans componentExact, hscaleOut,
    hpointOut, pointOutLength, weightsExact⟩

/-- One tensor cell in a successful complete-driver accumulator fold has the
exact maintained radix-four transport at the same list index. -/
theorem fullFoldTensorCellTransportsWeights
    (weights output : FullWeights) (alpha : RawQM31)
    (target : Nat) (targetBound : target < weights.components.val.length)
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (inputCell : componentToLinked weights.components.val[target]! =
      .Tensor scale factors)
    (rounds : Nat)
    (hfactorsLength : factors.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : CanonicalQM31 scale)
    (hfactors : AspisV5RelationLinkedTensorFold.CanonicalList factors.val)
    (halpha : CanonicalQM31 alpha)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold weights alpha = ok output) :
    ∃ scaleOut factorsOut,
      componentToLinked output.components.val[target]! =
        .Tensor scaleOut factorsOut ∧
      CanonicalQM31 scaleOut ∧
      AspisV5RelationLinkedTensorFold.CanonicalList factorsOut.val ∧
      factorsOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
          (structuredComponentWeights .tensor (rounds + 1) scale factors.val) =
        structuredComponentWeights .tensor rounds scaleOut factorsOut.val := by
  have released :
      ReleasedComponent
        (componentToLinked weights.components.val[target]!) := by
    rw [inputCell]
    trivial
  obtain ⟨alpha2, alpha3, preparedAlpha, preparedAlpha2, componentOut,
      _folded, squareRun, prepareRun, prepare2Run, alpha3Run, dispatchRun,
      outputCell, _outputReleased⟩ :=
    fullFoldSuccessExposesLinkedComponent weights output alpha target
      targetBound released success
  have dispatchRun' :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          (.Tensor scale factors) weights.log_len alpha alpha2 alpha3
            preparedAlpha preparedAlpha2 = ok (none, componentOut) := by
    exact (congrArg
      (fun component =>
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_component_arity4
          component weights.log_len alpha alpha2 alpha3 preparedAlpha
            preparedAlpha2)
      inputCell).symm.trans dispatchRun
  obtain ⟨scaleOut, factorsOut, helperRun, componentExact⟩ :=
    tensorDispatchSuccessExposesHelper scale factors weights.log_len alpha
      alpha2 alpha3 preparedAlpha preparedAlpha2 componentOut dispatchRun'
  obtain ⟨halpha2, halpha3, hpreparedAlpha, hpreparedAlpha2,
      halpha2Exact, halpha3Exact⟩ :=
    acceptedFoldPowerRunsExact alpha alpha2 alpha3 preparedAlpha
      preparedAlpha2 halpha squareRun prepareRun prepare2Run alpha3Run
  obtain ⟨hscaleOut, hfactorsOut, factorsOutLength, weightsExact⟩ :=
    extracted_tensor_fold_transports_weights scale factors alpha alpha2
      alpha3 preparedAlpha preparedAlpha2 rounds hfactorsLength hrounds hscale
      hfactors halpha halpha2 halpha3 hpreparedAlpha hpreparedAlpha2
      halpha2Exact halpha3Exact scaleOut factorsOut helperRun
  exact ⟨scaleOut, factorsOut, outputCell.trans componentExact, hscaleOut,
    hfactorsOut, factorsOutLength, weightsExact⟩

/-- Constructor selected by the common structured-cell wrapper. -/
def structuredLinkedComponent (kind : StructuredWeightKind)
    (scale : RawQM31) (values : alloc.vec.Vec RawQM31) : LinkedComponent :=
  match kind with
  | .multilinear => .Multilinear scale values
  | .tensor => .Tensor scale values

/-- One exact multilinear or tensor cell at a fixed accumulator index and
radix-four stage. -/
structure StructuredCellAt (kind : StructuredWeightKind)
    (weights : FullWeights) (target rounds : Nat) : Type where
  scale : RawQM31
  values : alloc.vec.Vec RawQM31
  cell : componentToLinked weights.components.val[target]! =
    structuredLinkedComponent kind scale values
  scaleCanonical : CanonicalQM31 scale
  valuesCanonical : ∀ value ∈ values.val, CanonicalQM31 value
  valuesLength : values.val.length = 2 * rounds

def StructuredCellAt.meaning
    {kind : StructuredWeightKind} {weights : FullWeights}
    {target rounds : Nat} (cell : StructuredCellAt kind weights target rounds) :
    Fin (radix4Size rounds) → ExactQM31 :=
  structuredComponentWeights kind rounds cell.scale cell.values.val

/-- Common accepted-driver step for either structured constructor. -/
theorem StructuredCellAt.fold
    {kind : StructuredWeightKind} {weights output : FullWeights}
    {target rounds : Nat}
    (cell : StructuredCellAt kind weights target (rounds + 1))
    (targetBound : target < weights.components.val.length)
    (alpha : RawQM31) (halpha : CanonicalQM31 alpha)
    (hrounds : rounds ≤ 4)
    (success :
      aspis_core.sumcheck.WeightAccumulator.fold weights alpha = ok output) :
    ∃ next : StructuredCellAt kind output target rounds,
      dualWeightFoldLayer (radix4Size rounds) (toMaintainedExact alpha)
          cell.meaning = next.meaning := by
  cases kind with
  | multilinear =>
      obtain ⟨scaleOut, valuesOut, outputCell, hscaleOut, hvaluesOut,
          valuesOutLength, weightsExact⟩ :=
        fullFoldMultilinearCellTransportsWeights weights output alpha target
          targetBound cell.scale cell.values (by simpa [structuredLinkedComponent]
            using cell.cell) rounds (by simpa using cell.valuesLength) hrounds
          cell.scaleCanonical cell.valuesCanonical halpha success
      let next : StructuredCellAt .multilinear output target rounds := {
        scale := scaleOut
        values := valuesOut
        cell := by simpa [structuredLinkedComponent] using outputCell
        scaleCanonical := hscaleOut
        valuesCanonical := hvaluesOut
        valuesLength := valuesOutLength }
      exact ⟨next, by simpa [StructuredCellAt.meaning, next] using weightsExact⟩
  | tensor =>
      obtain ⟨scaleOut, valuesOut, outputCell, hscaleOut, hvaluesOut,
          valuesOutLength, weightsExact⟩ :=
        fullFoldTensorCellTransportsWeights weights output alpha target
          targetBound cell.scale cell.values (by simpa [structuredLinkedComponent]
            using cell.cell) rounds (by simpa using cell.valuesLength) hrounds
          cell.scaleCanonical cell.valuesCanonical halpha success
      let next : StructuredCellAt .tensor output target rounds := {
        scale := scaleOut
        values := valuesOut
        cell := by simpa [structuredLinkedComponent] using outputCell
        scaleCanonical := hscaleOut
        valuesCanonical := hvaluesOut
        valuesLength := valuesOutLength }
      exact ⟨next, by simpa [StructuredCellAt.meaning, next] using weightsExact⟩

#print axioms dualWeightFoldLayer_structuredComponentWeights
#print axioms structuredBasisWeightNat_congr_prefix
#print axioms structuredBasisWeightNat_take
#print axioms extracted_multilinear_fold_transports_weights
#print axioms extracted_tensor_fold_transports_weights
#print axioms multilinearDispatchSuccessExposesHelper
#print axioms tensorDispatchSuccessExposesHelper
#print axioms acceptedFoldPowerRunsExact
#print axioms fullFoldMultilinearCellTransportsWeights
#print axioms fullFoldTensorCellTransportsWeights
#print axioms StructuredCellAt.fold

end AspisV5AcceptedStructuredWeightSemantics
