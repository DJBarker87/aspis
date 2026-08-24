import V5AcceptedStructuredSourceAlgebra

/-!
# Exact combined terminal weights of the eleven structured components
-/

namespace AspisV5AcceptedStructuredTerminalSchedule

open Aeneas Aeneas.Std Result
open AspisV5AcceptedAccumulatorSchedule
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedStructuredWeightSemantics
open AspisV5AcceptedStructuredWeightJourneys
open AspisV5RelationAcceptanceSourceProof
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationStressSourceBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- The lightweight source definitions of the three prepared covectors are
definitionally the meanings used by the production journey theorem. -/
theorem acceptedStructuredAfter3_eq_terminalSum
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
    (terminal : AcceptedStructuredTerminalSchedule trace schedule hkappa) :
    functionSum (acceptedStructuredAfter3 schedule hkappa) =
      functionSum [terminal.initial0.meaning, terminal.initial1.meaning,
        terminal.initial2.meaning, terminal.round0First.meaning,
        terminal.round0Second.meaning, terminal.round1First.meaning,
        terminal.round1Second.meaning, terminal.round2First.meaning,
        terminal.round2Second.meaning, terminal.round3First.meaning,
        terminal.round3Second.meaning] := by
  rw [acceptedStructuredAfter3_eq_journeys]
  have initial0Exact :
      foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
          (toMaintainedExact (acceptedAlphaAt alphas 1))
          (toMaintainedExact (acceptedAlphaAt alphas 2))
          (toMaintainedExact (acceptedAlphaAt alphas 3))
          (acceptedPreparedInitial0 schedule) = terminal.initial0.meaning := by
    simpa [acceptedPreparedInitial0, acceptedInitialMultilinear0,
      StructuredCellAt.meaning] using
      terminal.initial0Exact
  have initial1Exact :
      foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
          (toMaintainedExact (acceptedAlphaAt alphas 1))
          (toMaintainedExact (acceptedAlphaAt alphas 2))
          (toMaintainedExact (acceptedAlphaAt alphas 3))
          (acceptedPreparedInitial1 schedule) = terminal.initial1.meaning := by
    simpa [acceptedPreparedInitial1, acceptedInitialMultilinear1,
      StructuredCellAt.meaning] using
      terminal.initial1Exact
  have initial2Exact :
      foldFourMeaning (toMaintainedExact (acceptedAlphaAt alphas 0))
          (toMaintainedExact (acceptedAlphaAt alphas 1))
          (toMaintainedExact (acceptedAlphaAt alphas 2))
          (toMaintainedExact (acceptedAlphaAt alphas 3))
          (acceptedPreparedInitial2 schedule) = terminal.initial2.meaning := by
    simpa [acceptedPreparedInitial2, acceptedInitialMultilinear2,
      StructuredCellAt.meaning] using
      terminal.initial2Exact
  unfold acceptedStructuredJourneyFunctions
  rw [initial0Exact, initial1Exact, initial2Exact,
    terminal.round0FirstExact, terminal.round0SecondExact,
    terminal.round1FirstExact, terminal.round1SecondExact,
    terminal.round2FirstExact, terminal.round2SecondExact,
    terminal.round3FirstExact, terminal.round3SecondExact]
  rfl

/-- The exact source output equals the sum of the eleven actual terminal
component meanings. -/
theorem acceptedStructuredSourceSchedule_terminalWeights
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
    (terminal : AcceptedStructuredTerminalSchedule trace schedule hkappa) :
    sourceMainFinalWeights (acceptedStructuredSourceSchedule schedule hkappa)
        (acceptedAccumulatorChallenges trace schedule) =
      functionSum [terminal.initial0.meaning, terminal.initial1.meaning,
        terminal.initial2.meaning, terminal.round0First.meaning,
        terminal.round0Second.meaning, terminal.round1First.meaning,
        terminal.round1Second.meaning, terminal.round2First.meaning,
        terminal.round2Second.meaning, terminal.round3First.meaning,
        terminal.round3Second.meaning] := by
  rw [acceptedStructuredSourceSchedule_finalWeights]
  exact acceptedStructuredAfter3_eq_terminalSum terminal

#print axioms acceptedStructuredAfter3_eq_terminalSum
#print axioms acceptedStructuredSourceSchedule_terminalWeights

end AspisV5AcceptedStructuredTerminalSchedule
