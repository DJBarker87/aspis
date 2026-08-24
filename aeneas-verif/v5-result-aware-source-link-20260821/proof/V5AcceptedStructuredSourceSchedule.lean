import V5AcceptedStructuredTerminalSchedule
import AspisFormal.V5RelationStressSourceBridge

/-!
# Source schedule for the accepted structured accumulator components

This module is separate from the production component-journey proof so the
source-level finite-sum algebra can be checked and cached independently.
-/

namespace AspisV5AcceptedStructuredTerminalSchedule

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedAccumulatorCanonicalSchedule
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedStructuredWeightSemantics
open AspisV5AcceptedStructuredWeightJourneys
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationCallerInitialComponents
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedStructuredFold
open AspisV5RelationPrepareCanonicalProof
open AspisV5RelationPreparedPointCanonical
open AspisV5RelationPreparedPointVectors
open AspisV5RelationTerminalDotCanonical
open AspisV5RelationStressSourceBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000


private theorem sourceCallerOneCanonical :
    AspisV5RelationLinkedFieldProjection.CanonicalQM31
      V5RelationFullGenerated.aspis_core.field.QM31.ONE := by
  norm_num [AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationFullGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem sourcePrepareVecToCallerCanonical
    (values : alloc.vec.Vec
      V5RelationPrepareGenerated.aspis_core.field.QM31)
    (canonical : PrepareCanonicalList values.val) :
    CanonicalList (prepareVecToCaller values).val := by
  intro value member
  change value ∈ values.val.map prepareToCallerQM31 at member
  obtain ⟨source, sourceMember, sourceExact⟩ := List.mem_map.mp member
  subst value
  obtain ⟨index, bound, indexExact⟩ :=
    List.mem_iff_getElem.mp sourceMember
  have bangExact : values.val[index]! = values.val[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  have sourceCanonical : PrepareCanonicalQM31 source := by
    rw [← indexExact, ← bangExact]
    exact canonical index bound
  have mappedCanonical :=
    (prepareToCaller_canonical_iff source).2 sourceCanonical
  simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31] using mappedCanonical

private theorem sourcePrepareToCallerCanonical
    (value : V5RelationPrepareGenerated.aspis_core.field.QM31)
    (canonical : PrepareCanonicalQM31 value) :
    AspisV5RelationLinkedFieldProjection.CanonicalQM31
      (prepareToCallerQM31 value) := by
  have mappedCanonical :=
    (prepareToCaller_canonical_iff value).2 canonical
  simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisV5RelationLinkedFieldProjection.CanonicalQM31,
    AspisV5RelationLinkedFieldProjection.CanonicalCM31] using mappedCanonical

/-- The terminal-dot ledger states canonicality by index, while the
structured-fold bridge consumes the equivalent membership formulation. -/
private theorem sourceTerminalCanonicalListToStructured
    (values : List RawQM31)
    (canonical :
      AspisV5RelationLinkedTerminalDotSemantics.CanonicalList values) :
    AspisV5RelationLinkedStructuredFold.CanonicalList values := by
  intro value member
  obtain ⟨index, bound, valueEq⟩ := List.mem_iff_getElem.mp member
  have bangEq : values[index]! = values[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  rw [← valueEq, ← bangEq]
  exact canonical index bound


/-- First prepared multilinear cell, viewed after the two round-zero tensor
appends and before the first fold. -/
private def sourceInitialMultilinear0
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 0 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  refine {
    scale := V5RelationFullGenerated.aspis_core.field.QM31.ONE
    values := prepareVecToCaller schedule.prepareTrace.pointVec0
    cell := ?_
    scaleCanonical := sourceCallerOneCanonical
    valuesCanonical := sourcePrepareVecToCallerCanonical
      schedule.prepareTrace.pointVec0 points.2.2.2.1
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent, prepareToCallerQM31,
      V5RelationPrepareGenerated.aspis_core.field.QM31.ONE,
      V5RelationFullGenerated.aspis_core.field.QM31.ONE]
  · simp [prepareVecToCaller, lengths.2.2.2.1]

/-- Second prepared multilinear cell before the first fold. -/
private def sourceInitialMultilinear1
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 1 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  refine {
    scale := kappa
    values := prepareVecToCaller schedule.prepareTrace.pointVec1
    cell := ?_
    scaleCanonical := hkappa
    valuesCanonical := sourcePrepareVecToCallerCanonical
      schedule.prepareTrace.pointVec1 points.2.2.2.2.1
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent, prepareToCaller_callerToPrepare]
  · simp [prepareVecToCaller, lengths.2.2.2.2.1]

/-- Third prepared multilinear cell before the first fold. -/
private def sourceInitialMultilinear2
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    StructuredCellAt .multilinear schedule.rounds.round0.weights2 2 5 := by
  have points := preparedPointVectorsCanonical schedule.prepareTrace
  have lengths := preparedPointVectorsExact schedule.prepareTrace
  have sourceKappaCanonical :
      PrepareCanonicalQM31 (callerToPrepareQM31 kappa) :=
    (callerToPrepare_canonical_iff kappa).2 (by
      simpa [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
        AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
        AspisV5RelationLinkedFieldProjection.CanonicalQM31,
        AspisV5RelationLinkedFieldProjection.CanonicalCM31] using hkappa)
  have kappa2Canonical := prepare_qm31_square_success_canonical
    (callerToPrepareQM31 kappa) schedule.prepareTrace.kappa2
    sourceKappaCanonical schedule.prepareTrace.kappa2Run
  refine {
    scale := prepareToCallerQM31 schedule.prepareTrace.kappa2
    values := prepareVecToCaller schedule.prepareTrace.pointVec2
    cell := ?_
    scaleCanonical := sourcePrepareToCallerCanonical schedule.prepareTrace.kappa2
      kappa2Canonical
    valuesCanonical := sourcePrepareVecToCallerCanonical
      schedule.prepareTrace.pointVec2 points.2.2.2.2.2
    valuesLength := ?_ }
  · rw [schedule.round0Schedule.secondShape, schedule.initialMapped,
      schedule.initialExact]
    simp [prepareComponentToCaller, componentToLinked,
      structuredLinkedComponent]
  · simp [prepareVecToCaller, lengths.2.2.2.2.2]


/-! ## The matching source-level weight schedule -/

/-- Pointwise sum of a finite list of covectors. -/
def functionSum {n : Nat}
    (weights : List (Fin n → ExactQM31)) : Fin n → ExactQM31 :=
  fun index => (weights.map (fun weight => weight index)).sum

/-- The maintained arity-four dual fold distributes over an arbitrary finite
sum of covectors. -/
theorem dualWeightFoldLayer_functionSum
    (n : Nat) (alpha : ExactQM31)
    (weights : List (Fin (4 * n) → ExactQM31)) :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer n alpha
        (functionSum weights) =
      functionSum (weights.map
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer n alpha)) := by
  induction weights with
  | nil =>
      funext index
      simp [functionSum,
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue]
  | cons head tail ih =>
      have sumExact : functionSum (head :: tail) =
          fun index => head index + functionSum tail index := by
        funext index
        simp [functionSum]
      rw [sumExact,
        AspisV5RelationStressSourceBridge.dualWeightFoldLayer_add, ih]
      funext index
      simp [functionSum]

private theorem callerOneExact :
    AspisV5RelationLinkedFieldProjection.toMaintainedExact
      V5RelationFullGenerated.aspis_core.field.QM31.ONE = 1 := by
  norm_num [AspisV5RelationLinkedFieldProjection.toMaintainedExact,
    V5RelationFullGenerated.aspis_core.field.QM31.ONE]
  change (⟨⟨1, 0⟩, ⟨0, 0⟩⟩ : ExactQM31) = ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
  rfl

/-- A source OOD functional is stored without its transcript mix.  Multiplying
that unit-scale tensor by the accepted mix gives exactly the tensor component
stored by production Rust. -/
theorem acceptedMix_times_unitTensor
    (rounds : Nat) (mix : RawQM31) (factors : List RawQM31) :
    (fun index =>
      AspisV5RelationLinkedFieldProjection.toMaintainedExact mix *
        structuredComponentWeights .tensor rounds
          V5RelationFullGenerated.aspis_core.field.QM31.ONE factors index) =
      structuredComponentWeights .tensor rounds mix factors := by
  funext index
  simp [structuredComponentWeights, callerOneExact]

/-- The three prepared multilinear covectors before any OOD tensor is added. -/
def acceptedPreparedInitial0
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    Fin 1024 → ExactQM31 :=
  structuredComponentWeights .multilinear 5
    V5RelationFullGenerated.aspis_core.field.QM31.ONE
    (prepareVecToCaller schedule.prepareTrace.pointVec0).val

def acceptedPreparedInitial1
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    Fin 1024 → ExactQM31 :=
  structuredComponentWeights .multilinear 5 kappa
    (prepareVecToCaller schedule.prepareTrace.pointVec1).val

def acceptedPreparedInitial2
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    Fin 1024 → ExactQM31 :=
  structuredComponentWeights .multilinear 5
    (prepareToCallerQM31 schedule.prepareTrace.kappa2)
    (prepareVecToCaller schedule.prepareTrace.pointVec2).val

def acceptedStructuredInitialFunctions
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 1024 → ExactQM31) :=
  [acceptedPreparedInitial0 schedule,
   acceptedPreparedInitial1 schedule,
   acceptedPreparedInitial2 schedule]

/-- Unit-scale tensor functional supplied to the source model. -/
def acceptedUnitTensor (rounds : Nat)
    (factors : alloc.vec.Vec RawQM31) : Fin (radix4Size rounds) → ExactQM31 :=
  structuredComponentWeights .tensor rounds
    V5RelationFullGenerated.aspis_core.field.QM31.ONE factors.val

/-- Actual scaled tensor retained in the production accumulator. -/
def acceptedScaledTensor (rounds : Nat) (mix : RawQM31)
    (factors : alloc.vec.Vec RawQM31) : Fin (radix4Size rounds) → ExactQM31 :=
  structuredComponentWeights .tensor rounds mix factors.val

abbrev acceptedUnitTensor5 (factors : alloc.vec.Vec RawQM31) :
    Fin 1024 → ExactQM31 := acceptedUnitTensor 5 factors
abbrev acceptedUnitTensor4 (factors : alloc.vec.Vec RawQM31) :
    Fin 256 → ExactQM31 := acceptedUnitTensor 4 factors
abbrev acceptedUnitTensor3 (factors : alloc.vec.Vec RawQM31) :
    Fin 64 → ExactQM31 := acceptedUnitTensor 3 factors
abbrev acceptedUnitTensor2 (factors : alloc.vec.Vec RawQM31) :
    Fin 16 → ExactQM31 := acceptedUnitTensor 2 factors

abbrev acceptedScaledTensor5 (mix : RawQM31)
    (factors : alloc.vec.Vec RawQM31) : Fin 1024 → ExactQM31 :=
  acceptedScaledTensor 5 mix factors
abbrev acceptedScaledTensor4 (mix : RawQM31)
    (factors : alloc.vec.Vec RawQM31) : Fin 256 → ExactQM31 :=
  acceptedScaledTensor 4 mix factors
abbrev acceptedScaledTensor3 (mix : RawQM31)
    (factors : alloc.vec.Vec RawQM31) : Fin 64 → ExactQM31 :=
  acceptedScaledTensor 3 mix factors
abbrev acceptedScaledTensor2 (mix : RawQM31)
    (factors : alloc.vec.Vec RawQM31) : Fin 16 → ExactQM31 :=
  acceptedScaledTensor 2 mix factors

/-- Fixed-size forms avoid asking elaboration to normalize the dependent
`radix4Size` index while assembling the released four-round schedule. -/
theorem acceptedMix_times_unitTensor5
    (mix : RawQM31) (factors : alloc.vec.Vec RawQM31) :
    (fun index : Fin 1024 => toMaintainedExact mix *
      acceptedUnitTensor5 factors index) = acceptedScaledTensor5 mix factors := by
  funext index
  simp [acceptedUnitTensor5, acceptedScaledTensor5, acceptedUnitTensor,
    acceptedScaledTensor, structuredComponentWeights, callerOneExact]

theorem acceptedMix_times_unitTensor4
    (mix : RawQM31) (factors : alloc.vec.Vec RawQM31) :
    (fun index : Fin 256 => toMaintainedExact mix *
      acceptedUnitTensor4 factors index) = acceptedScaledTensor4 mix factors := by
  funext index
  simp [acceptedUnitTensor4, acceptedScaledTensor4, acceptedUnitTensor,
    acceptedScaledTensor, structuredComponentWeights, callerOneExact]

theorem acceptedMix_times_unitTensor3
    (mix : RawQM31) (factors : alloc.vec.Vec RawQM31) :
    (fun index : Fin 64 => toMaintainedExact mix *
      acceptedUnitTensor3 factors index) = acceptedScaledTensor3 mix factors := by
  funext index
  simp [acceptedUnitTensor3, acceptedScaledTensor3, acceptedUnitTensor,
    acceptedScaledTensor, structuredComponentWeights, callerOneExact]

theorem acceptedMix_times_unitTensor2
    (mix : RawQM31) (factors : alloc.vec.Vec RawQM31) :
    (fun index : Fin 16 => toMaintainedExact mix *
      acceptedUnitTensor2 factors index) = acceptedScaledTensor2 mix factors := by
  funext index
  simp [acceptedUnitTensor2, acceptedScaledTensor2, acceptedUnitTensor,
    acceptedScaledTensor, structuredComponentWeights, callerOneExact]

/-- Exact maintained challenge tuple consumed by the accepted accumulator. -/
def acceptedAccumulatorChallenges
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (schedule : AcceptedFourRoundAccumulatorSchedule trace) :
    AspisV5RelationSumcheckSoundness.TwelveRelationChallenges ExactQM31 :=
  (((((AspisV5RelationLinkedFieldProjection.toMaintainedExact
          schedule.rounds.round0.sample0.mix,
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          schedule.rounds.round0.sample1.mix),
       AspisV5RelationLinkedFieldProjection.toMaintainedExact
         (acceptedAlphaAt alphas 0)),
      ((AspisV5RelationLinkedFieldProjection.toMaintainedExact
          schedule.rounds.round1.sample0.mix,
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          schedule.rounds.round1.sample1.mix),
       AspisV5RelationLinkedFieldProjection.toMaintainedExact
         (acceptedAlphaAt alphas 1))),
     ((AspisV5RelationLinkedFieldProjection.toMaintainedExact
         schedule.rounds.round2.sample0.mix,
       AspisV5RelationLinkedFieldProjection.toMaintainedExact
         schedule.rounds.round2.sample1.mix),
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))),
    ((AspisV5RelationLinkedFieldProjection.toMaintainedExact
        schedule.rounds.round3.sample0.mix,
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
        schedule.rounds.round3.sample1.mix),
     AspisV5RelationLinkedFieldProjection.toMaintainedExact
       (acceptedAlphaAt alphas 3)))

/-- The source schedule represented by the three prepared multilinears and
the eight production tensor appends.  The deferred inactive table is added
separately by `withInitial`, after its own source bridge is established. -/
def acceptedStructuredSourceSchedule
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    SourceMainWeightSchedule ExactQM31 where
  initial := functionSum (acceptedStructuredInitialFunctions schedule hkappa)
  round0First := acceptedUnitTensor5 schedule.round0Schedule.firstFactors
  round0Second := fun _ =>
    acceptedUnitTensor5 schedule.round0Schedule.secondFactors
  round1First := acceptedUnitTensor4 schedule.round1Schedule.firstFactors
  round1Second := fun _ =>
    acceptedUnitTensor4 schedule.round1Schedule.secondFactors
  round2First := acceptedUnitTensor3 schedule.round2Schedule.firstFactors
  round2Second := fun _ =>
    acceptedUnitTensor3 schedule.round2Schedule.secondFactors
  round3First := acceptedUnitTensor2 schedule.round3Schedule.firstFactors
  round3Second := fun _ =>
    acceptedUnitTensor2 schedule.round3Schedule.secondFactors

theorem mixedFunctionSumWithAcceptedTensors
    {n : Nat}
    (incoming : List (Fin (4 * n) → ExactQM31))
    (firstMix secondMix : RawQM31)
    (firstUnit secondUnit firstScaled secondScaled :
      Fin (4 * n) → ExactQM31)
    (firstExact : (fun index =>
      AspisV5RelationLinkedFieldProjection.toMaintainedExact firstMix *
        firstUnit index) = firstScaled)
    (secondExact : (fun index =>
      AspisV5RelationLinkedFieldProjection.toMaintainedExact secondMix *
        secondUnit index) = secondScaled) :
    AspisV5FriRelationCandidateBridge.mixedWeights
        (functionSum incoming)
        firstUnit (fun _ => secondUnit)
        (AspisV5RelationLinkedFieldProjection.toMaintainedExact firstMix)
        (AspisV5RelationLinkedFieldProjection.toMaintainedExact secondMix) =
      functionSum (incoming ++ [firstScaled, secondScaled]) := by
  funext index
  have firstAt := congrFun firstExact index
  have secondAt := congrFun secondExact index
  simp [functionSum, AspisV5FriRelationCandidateBridge.mixedWeights]
  rw [firstAt, secondAt, add_assoc]

/-- Functions present just before the first accepted fold. -/
def acceptedStructuredBefore0
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 1024 → ExactQM31) :=
  acceptedStructuredInitialFunctions schedule hkappa ++
    [acceptedScaledTensor5 schedule.rounds.round0.sample0.mix
       schedule.round0Schedule.firstFactors,
     acceptedScaledTensor5 schedule.rounds.round0.sample1.mix
       schedule.round0Schedule.secondFactors]

def acceptedStructuredAfter0
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 256 → ExactQM31) :=
  (acceptedStructuredBefore0 schedule hkappa).map
    (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0)))

def acceptedStructuredBefore1
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 256 → ExactQM31) :=
  acceptedStructuredAfter0 schedule hkappa ++
    [acceptedScaledTensor4 schedule.rounds.round1.sample0.mix
       schedule.round1Schedule.firstFactors,
     acceptedScaledTensor4 schedule.rounds.round1.sample1.mix
       schedule.round1Schedule.secondFactors]

def acceptedStructuredAfter1
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 64 → ExactQM31) :=
  (acceptedStructuredBefore1 schedule hkappa).map
    (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1)))

def acceptedStructuredBefore2
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 64 → ExactQM31) :=
  acceptedStructuredAfter1 schedule hkappa ++
    [acceptedScaledTensor3 schedule.rounds.round2.sample0.mix
       schedule.round2Schedule.firstFactors,
     acceptedScaledTensor3 schedule.rounds.round2.sample1.mix
       schedule.round2Schedule.secondFactors]

def acceptedStructuredAfter2
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 16 → ExactQM31) :=
  (acceptedStructuredBefore2 schedule hkappa).map
    (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2)))

def acceptedStructuredBefore3
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 16 → ExactQM31) :=
  acceptedStructuredAfter2 schedule hkappa ++
    [acceptedScaledTensor2 schedule.rounds.round3.sample0.mix
       schedule.round3Schedule.firstFactors,
     acceptedScaledTensor2 schedule.rounds.round3.sample1.mix
       schedule.round3Schedule.secondFactors]

def acceptedStructuredAfter3
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 4 → ExactQM31) :=
  (acceptedStructuredBefore3 schedule hkappa).map
    (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3)))

/-- The eleven source functions written directly as their complete remaining
fold journeys. -/
def acceptedStructuredJourneyFunctions
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    List (Fin 4 → ExactQM31) :=
  [foldFourMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (acceptedPreparedInitial0 schedule),
   foldFourMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (acceptedPreparedInitial1 schedule),
   foldFourMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (acceptedPreparedInitial2 schedule),
   foldFourMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 5
        schedule.rounds.round0.sample0.mix
        schedule.round0Schedule.firstFactors.val),
   foldFourMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 0))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 5
        schedule.rounds.round0.sample1.mix
        schedule.round0Schedule.secondFactors.val),
   foldThreeMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 4
        schedule.rounds.round1.sample0.mix
        schedule.round1Schedule.firstFactors.val),
   foldThreeMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 1))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 4
        schedule.rounds.round1.sample1.mix
        schedule.round1Schedule.secondFactors.val),
   foldTwoMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 3
        schedule.rounds.round2.sample0.mix
        schedule.round2Schedule.firstFactors.val),
   foldTwoMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 2))
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 3
        schedule.rounds.round2.sample1.mix
        schedule.round2Schedule.secondFactors.val),
   foldOneMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 2
        schedule.rounds.round3.sample0.mix
        schedule.round3Schedule.firstFactors.val),
   foldOneMeaning
      (AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (acceptedAlphaAt alphas 3))
      (structuredComponentWeights .tensor 2
        schedule.rounds.round3.sample1.mix
        schedule.round3Schedule.secondFactors.val)]

theorem acceptedStructuredAfter3_eq_journeys
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (schedule : AcceptedFourRoundAccumulatorSchedule trace)
    (hkappa : AspisV5RelationLinkedFieldProjection.CanonicalQM31 kappa) :
    acceptedStructuredAfter3 schedule hkappa =
      acceptedStructuredJourneyFunctions schedule hkappa := by
  rfl

#print axioms acceptedScheduleLogLengths
#print axioms sourceInitialMultilinear0
#print axioms sourceInitialMultilinear1
#print axioms sourceInitialMultilinear2
#print axioms acceptedStructuredTerminalSchedule_exists
#print axioms dualWeightFoldLayer_functionSum
#print axioms acceptedStructuredAfter3_eq_journeys

end AspisV5AcceptedStructuredTerminalSchedule
