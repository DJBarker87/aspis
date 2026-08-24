import V5AcceptedInactiveTerminalJourney
import V5RelationLinkedTerminalDotSemantics

/-!
# Exact terminal weights of the accepted main accumulator

The accepted main accumulator has exactly twelve terminal components: three
prepared multilinear cells, the deferred inactive-table cell, and eight OOD
tensor cells.  This file identifies every one of those cells with its exact
four-entry maintained-field covector.
-/

namespace AspisV5AcceptedTerminalAccumulatorWeights

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedInactiveTerminalJourney
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedStructuredTerminalSchedule
open AspisV5AcceptedStructuredWeightSemantics
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupedRows
open AspisV5RelationLinkedGroupedRowsSemantics
open AspisV5RelationLinkedGroupedRowsStaged
open AspisV5RelationLinkedStructuredFold
open AspisV5RelationLinkedTensorFold
open AspisV5RelationLinkedTerminalDotSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev LinkedComponent :=
  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent

/- The terminal-dot definitions and the traversal definitions each derive an
`Inhabited WeightComponent` instance.  Every lookup below is in bounds, but
using the terminal definition's exact instance keeps the `get!` terms
definitionally identical to the public terminal-accumulator function. -/
local instance terminalLinkedComponentInhabited : Inhabited LinkedComponent :=
  AspisV5RelationLinkedTerminalDotSemantics.instInhabitedWeightComponent_v5RelationLinkedTerminalDotSemantics

private theorem weightsToLinkedTerminalComponent
    (weights : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (index : Nat) (bound : index < weights.components.val.length) :
    (weightsToLinked weights).components.val[index]! =
      componentToLinked weights.components.val[index]! := by
  change (List.map componentToLinked weights.components.val)[index]! =
    componentToLinked weights.components.val[index]!
  have mapBound :
      index < (List.map componentToLinked weights.components.val).length := by
    simpa using bound
  have mapBang :
      (List.map componentToLinked weights.components.val)[index]! =
        (List.map componentToLinked weights.components.val)[index] := by
    apply List.getElem!_of_getElem?
    exact (List.getElem?_eq_some_getElem_iff mapBound).mpr trivial
  have sourceBang :
      weights.components.val[index]! = weights.components.val[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  have actualMap :
      (List.map componentToLinked weights.components.val)[index] =
        componentToLinked weights.components.val[index] := by
    rw [List.getElem_map]
  exact mapBang.trans (actualMap.trans
    (congrArg componentToLinked sourceBang.symm))

private theorem canonicalListAt
    (values : List RawQM31)
    (canonical : ∀ value ∈ values, CanonicalQM31 value) :
    AspisV5RelationLinkedTerminalDotSemantics.CanonicalList values := by
  intro index bound
  have bangEq : values[index]! = values[index] := by
    apply List.getElem!_of_getElem?
    simp [bound]
  exact (congrArg CanonicalQM31 bangEq).mpr
    (canonical values[index] (List.getElem_mem _))

/-- A one-digit structured terminal cell has exactly the direct four-entry
meaning used by the terminal dot implementation. -/
theorem structuredTerminalComponentWeights
    {kind : StructuredWeightKind}
    {weights : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator}
    {target : Nat}
    (cell : StructuredCellAt kind weights target 1) :
    terminalComponentWeights
        (componentToLinked weights.components.val[target]!) =
      cell.meaning := by
  have valuesLength : cell.values.val.length = 2 := by
    simpa using cell.valuesLength
  obtain ⟨high, low, valuesExact⟩ := List.length_eq_two.mp valuesLength
  rw [cell.cell]
  cases kind <;> funext coordinate <;> fin_cases coordinate <;>
    simp [terminalComponentWeights, StructuredCellAt.meaning, valuesExact,
      structuredLinkedComponent, structuredComponentWeights,
      structuredBasisWeightNat, structuredPairWeights,
      multilinearFibreWeights, tensorFibreWeights]
  all_goals ring

/-- Every one-digit structured terminal cell satisfies the exact shape,
length, and canonicality preconditions of the released terminal-dot proof. -/
theorem structuredTerminalComponentReleased
    {kind : StructuredWeightKind}
    {weights : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator}
    {target : Nat}
    (cell : StructuredCellAt kind weights target 1) :
    ReleasedTerminalComponent
      (componentToLinked weights.components.val[target]!) := by
  rw [cell.cell]
  cases kind with
  | multilinear =>
      exact ⟨cell.scaleCanonical, by simpa using cell.valuesLength,
        canonicalListAt cell.values.val cell.valuesCanonical⟩
  | tensor =>
      exact ⟨cell.scaleCanonical, by simpa using cell.valuesLength,
        canonicalListAt cell.values.val cell.valuesCanonical⟩

/-- The terminal deferred inactive cell denotes exactly its released
four-entry grouped covector. -/
theorem inactiveTerminalComponentWeights
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
    (inactive : AcceptedInactiveTerminal trace) :
    terminalComponentWeights
        (componentToLinked trace.weights4.components.val[3]!) =
      representedGroupedWeights releasedRowGroups4
        (releasedFourValues inactive.value0 inactive.value1 inactive.value2
          inactive.value3) := by
  rw [inactive.cell]
  funext coordinate
  fin_cases coordinate <;>
    simp [terminalComponentWeights, representedGroupedWeights,
      releasedRowGroups4, releasedFourValues]

/-- The released inactive four-value terminal cell satisfies the direct-dot
shape, routing, and canonicality preconditions. -/
theorem inactiveTerminalComponentReleased
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
    (inactive : AcceptedInactiveTerminal trace) :
    ReleasedTerminalComponent
      (componentToLinked trace.weights4.components.val[3]!) := by
  rw [inactive.cell]
  rcases inactive.canonical with ⟨h0, h1, h2, h3⟩
  refine ⟨by rfl, ?_, ?_⟩
  · intro index bound
    have indexBound : index < 4 := by
      simpa [releasedFourValues] using bound
    interval_cases index <;>
      simp [releasedFourValues, h0, h1, h2, h3]
  · intro row bound
    interval_cases row <;>
      simp [releasedRowGroups4, releasedFourValues]

/-- All twelve terminal components are in one of the exact released shapes
accepted by the terminal-dot proof. -/
theorem acceptedTerminalComponentsReleased
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
    {schedule : AcceptedFourRoundAccumulatorSchedule trace}
    {hkappa : CanonicalQM31 kappa}
    (terminal : AcceptedStructuredTerminalSchedule trace schedule hkappa)
    (inactive : AcceptedInactiveTerminal trace) :
    ∀ index, index < (weightsToLinked trace.weights4).components.val.length →
      ReleasedTerminalComponent
        (weightsToLinked trace.weights4).components.val[index]! := by
  intro index bound
  have fullBound : index < trace.weights4.components.val.length := by
    simpa [weightsToLinked] using bound
  have linkedCell := weightsToLinkedTerminalComponent trace.weights4 index
    fullBound
  rw [schedule.round3Length] at fullBound
  interval_cases index
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.initial0)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.initial1)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.initial2)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (inactiveTerminalComponentReleased inactive)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round0First)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round0Second)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round1First)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round1Second)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round2First)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round2Second)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round3First)
  · exact (congrArg ReleasedTerminalComponent linkedCell).mpr
      (structuredTerminalComponentReleased terminal.round3Second)

/-- The exact combined terminal covector is the sum of the eleven structured
component meanings and the deferred inactive-table meaning, each included
once at its actual production index. -/
theorem acceptedTerminalAccumulatorWeightsExact
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
    {schedule : AcceptedFourRoundAccumulatorSchedule trace}
    {hkappa : CanonicalQM31 kappa}
    (terminal : AcceptedStructuredTerminalSchedule trace schedule hkappa)
    (inactive : AcceptedInactiveTerminal trace) :
    terminalAccumulatorWeights (weightsToLinked trace.weights4) =
      functionSum [terminal.initial0.meaning, terminal.initial1.meaning,
        terminal.initial2.meaning,
        representedGroupedWeights releasedRowGroups4
          (releasedFourValues inactive.value0 inactive.value1 inactive.value2
            inactive.value3),
        terminal.round0First.meaning, terminal.round0Second.meaning,
        terminal.round1First.meaning, terminal.round1Second.meaning,
        terminal.round2First.meaning, terminal.round2Second.meaning,
        terminal.round3First.meaning, terminal.round3Second.meaning] := by
  have h0 := structuredTerminalComponentWeights terminal.initial0
  have h1 := structuredTerminalComponentWeights terminal.initial1
  have h2 := structuredTerminalComponentWeights terminal.initial2
  have h3 := inactiveTerminalComponentWeights inactive
  have h4 := structuredTerminalComponentWeights terminal.round0First
  have h5 := structuredTerminalComponentWeights terminal.round0Second
  have h6 := structuredTerminalComponentWeights terminal.round1First
  have h7 := structuredTerminalComponentWeights terminal.round1Second
  have h8 := structuredTerminalComponentWeights terminal.round2First
  have h9 := structuredTerminalComponentWeights terminal.round2Second
  have h10 := structuredTerminalComponentWeights terminal.round3First
  have h11 := structuredTerminalComponentWeights terminal.round3Second
  have linked0 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 0 (by
      rw [schedule.round3Length]; decide))).trans h0
  have linked1 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 1 (by
      rw [schedule.round3Length]; decide))).trans h1
  have linked2 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 2 (by
      rw [schedule.round3Length]; decide))).trans h2
  have linked3 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 3 (by
      rw [schedule.round3Length]; decide))).trans h3
  have linked4 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 4 (by
      rw [schedule.round3Length]; decide))).trans h4
  have linked5 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 5 (by
      rw [schedule.round3Length]; decide))).trans h5
  have linked6 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 6 (by
      rw [schedule.round3Length]; decide))).trans h6
  have linked7 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 7 (by
      rw [schedule.round3Length]; decide))).trans h7
  have linked8 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 8 (by
      rw [schedule.round3Length]; decide))).trans h8
  have linked9 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 9 (by
      rw [schedule.round3Length]; decide))).trans h9
  have linked10 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 10 (by
      rw [schedule.round3Length]; decide))).trans h10
  have linked11 := (congrArg terminalComponentWeights
    (weightsToLinkedTerminalComponent trace.weights4 11 (by
      rw [schedule.round3Length]; decide))).trans h11
  funext coordinate
  unfold terminalAccumulatorWeights
  have lengthExact :
      (weightsToLinked trace.weights4).components.val.length = 12 := by
    simpa [weightsToLinked] using schedule.round3Length
  rw [lengthExact]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [linked0, linked1, linked2, linked3, linked4, linked5, linked6,
    linked7, linked8, linked9, linked10, linked11]
  simp [functionSum, add_assoc]
  rfl

#print axioms structuredTerminalComponentWeights
#print axioms structuredTerminalComponentReleased
#print axioms inactiveTerminalComponentWeights
#print axioms inactiveTerminalComponentReleased
#print axioms acceptedTerminalComponentsReleased
#print axioms acceptedTerminalAccumulatorWeightsExact

end AspisV5AcceptedTerminalAccumulatorWeights
