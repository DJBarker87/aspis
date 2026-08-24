import V5CompactCallerWrapperExact

/-!
# Exact compact terminal value of one accepted relation execution

This file composes the extracted compact constructor, the four reachable
fold calls, the final-weight scatter, and the four-term dot from one accepted
production relation trace.  The result is the maintained compact terminal
formula, with no separately supplied Rust-to-model equality.
-/

namespace AspisV5AcceptedCompactExecutionExact

open Aeneas Aeneas.Std Result
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5CompactCallerWrapperExact

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev K := AspisV5CompactCallerWrapperExact.K
abbrev Raw := AspisV5CompactCallerWrapperExact.CallerRaw

/-- An in-bounds fixed-array read cannot depend on the default value carried
by a generated module's local `Inhabited` instance.  Several independently
extracted helpers use distinct local instances for the same Rust record. -/
private theorem list_getBang_instance_independent
    {T : Type} (first second : Inhabited T)
    (values : List T) (index : Nat) (bound : index < values.length) :
    @getElem! (List T) Nat T (fun items position => position < items.length)
        List.instGetElem?NatLtLength first values index =
      @getElem! (List T) Nat T (fun items position => position < items.length)
        List.instGetElem?NatLtLength second values index := by
  have left :
      @getElem! (List T) Nat T
          (fun items position => position < items.length)
          List.instGetElem?NatLtLength first values index =
        values[index]'bound := by
    letI : Inhabited T := first
    exact getElem!_pos values index bound
  have right :
      @getElem! (List T) Nat T
          (fun items position => position < items.length)
          List.instGetElem?NatLtLength second values index =
        values[index]'bound := by
    letI : Inhabited T := second
    exact getElem!_pos values index bound
  exact left.trans right.symm

/-- Equality with the exact released initializer fixes all ten selectors.
The selector bytes are source data, not an additional semantic assumption. -/
theorem callerReleasedSelectors_of_project_eq_optimizedInit
    (state : CallerState) (point : Fin 10 → K) (scale : K)
    (exact : callerProjectState state =
      AspisV5CompactTerminalOptimized.optimizedInit point scale) :
    CallerReleasedSelectors state := by
  intro index
  have selectorExact := congrArg
    (fun projected => (projected.blocks index).selector) exact
  simpa [callerProjectState, callerProjectBlock,
    AspisV5CompactTerminalOptimized.optimizedInit] using selectorExact

/-- The fixed left-associated four-term source dot is the ordinary `Fin 4`
dot after replacing the returned raw weights by their exact field values. -/
theorem exactFourTermDot_eq_modelDot
    (weights : Array FinalRaw 4#usize) (values : Array Raw 4#usize)
    (modelWeights : Fin 4 → K)
    (weightsExact : (fun index : Fin 4 =>
      AspisV5CompactFinalFieldSemantics.toExact
        weights.val[index.val]!) = modelWeights) :
    AspisV5RelationCompactAdditiveDotExact.exactFourTermDot weights values =
      ∑ index : Fin 4, modelWeights index *
        callerToK values.val[index.val]! := by
  have w0 := congrFun weightsExact (0 : Fin 4)
  have w1 := congrFun weightsExact (1 : Fin 4)
  have w2 := congrFun weightsExact (2 : Fin 4)
  have w3 := congrFun weightsExact (3 : Fin 4)
  have w0' :
      AspisV5CompactFinalFieldSemantics.toExact weights.val[0]! =
        modelWeights 0 := by
    convert w0 using 1
    congr 1
  have w1' :
      AspisV5CompactFinalFieldSemantics.toExact weights.val[1]! =
        modelWeights 1 := by
    convert w1 using 1
    congr 1
  have w2' :
      AspisV5CompactFinalFieldSemantics.toExact weights.val[2]! =
        modelWeights 2 := by
    convert w2 using 1
    congr 1
  have w3' :
      AspisV5CompactFinalFieldSemantics.toExact weights.val[3]! =
        modelWeights 3 := by
    convert w3 using 1
    congr 1
  have v0 :
      callerToK values.val[0]! =
        callerToK values.val[(0 : Fin 4).val]! := by
    apply congrArg callerToK
    exact list_getBang_instance_independent _ _ values.val 0
      (by simpa [Array.length_eq])
  have v1 :
      callerToK values.val[1]! =
        callerToK values.val[(1 : Fin 4).val]! := by
    apply congrArg callerToK
    exact list_getBang_instance_independent _ _ values.val 1
      (by simpa [Array.length_eq])
  have v2 :
      callerToK values.val[2]! =
        callerToK values.val[(2 : Fin 4).val]! := by
    apply congrArg callerToK
    exact list_getBang_instance_independent _ _ values.val 2
      (by simpa [Array.length_eq])
  have v3 :
      callerToK values.val[3]! =
        callerToK values.val[(3 : Fin 4).val]! := by
    apply congrArg callerToK
    exact list_getBang_instance_independent _ _ values.val 3
      (by simpa [Array.length_eq])
  rw [Fin.sum_univ_four]
  simp only [AspisV5RelationCompactAdditiveDotExact.exactFourTermDot,
    AspisV5RelationCompactAdditiveDotExact.finalWeightAt,
    AspisV5RelationCompactAdditiveDotExact.finalValueAt]
  change
    (((AspisV5CompactFinalFieldSemantics.toExact weights.val[0]! *
        callerToK values.val[0]!) +
      AspisV5CompactFinalFieldSemantics.toExact weights.val[1]! *
        callerToK values.val[1]!) +
      AspisV5CompactFinalFieldSemantics.toExact weights.val[2]! *
        callerToK values.val[2]!) +
      AspisV5CompactFinalFieldSemantics.toExact weights.val[3]! *
        callerToK values.val[3]! = _
  rw [w0', w1', w2', w3', v0, v1, v2, v3]

/-- The four compact-fold results used by one accepted relation trace must be
the results of the corrected source-shaped caller wrapper.  The no-premise
bridge proves these equalities from the pinned caller and the normalized
corrected Aeneas extraction. -/
structure CompactFoldSourceEquality
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array Raw 4#usize}
    {alphas : Array Raw 4#usize}
    {kappa inactiveClaim : Raw}
    {roundChallenges : Array Raw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : Raw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) : Prop
    where
  fold0 : correctedCallerFold trace.calls.compact
      (acceptedAlphaAt alphas 0) = .ok trace.additive1
  fold1 : correctedCallerFold trace.additive1
      (acceptedAlphaAt alphas 1) = .ok trace.additive2
  fold2 : correctedCallerFold trace.additive2
      (acceptedAlphaAt alphas 2) = .ok trace.additive3
  fold3 : correctedCallerFold trace.additive3
      (acceptedAlphaAt alphas 3) = .ok trace.additive4

/-- A single accepted extracted relation execution computes exactly the
maintained optimized compact terminal value.  The hypotheses are only the
canonical raw-field facts for values decoded earlier in the same accepted
execution.  `foldSource` is the explicit remaining connection from the four
production caller results to the corrected compact-fold wrapper. -/
theorem accepted_trace_compact_terminal_exact
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array Raw 4#usize}
    {alphas : Array Raw 4#usize}
    {kappa inactiveClaim : Raw}
    {roundChallenges : Array Raw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : Raw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (foldSource : CompactFoldSourceEquality trace)
    (pointCanonical : ∀ index : Fin 10,
      CallerCanonical (callerPointAt roundChallenges index))
    (scaleCanonical : CallerCanonical trace.calls.denseScale)
    (alphaCanonical : ∀ index : Fin 4,
      CallerCanonical (acceptedAlphaAt alphas index))
    (valuesCanonical : ∀ index : Fin 4,
      CallerCanonical trace.finalCoefficients.val[index.val]!) :
    CallerCanonical trace.additiveDot ∧
      callerToK trace.additiveDot =
        AspisV5CompactTerminalOptimized.optimizedCompactFinalDot
          (fun index => callerToK (callerPointAt roundChallenges index))
          (callerToK trace.calls.denseScale)
          (fun index => callerToK (acceptedAlphaAt alphas index))
          (fun index => callerToK
            trace.finalCoefficients.val[index.val]!) := by
  have initialSem := caller_new_success_exact roundChallenges
    trace.calls.denseScale trace.calls.compact pointCanonical scaleCanonical
    trace.calls.compactSuccess
  have initialSelectors : CallerReleasedSelectors trace.calls.compact :=
    callerReleasedSelectors_of_project_eq_optimizedInit trace.calls.compact
      (fun index => callerToK (callerPointAt roundChallenges index))
      (callerToK trace.calls.denseScale) initialSem.2.2
  have initialFolds : trace.calls.compact.folds.val = 0 := by
    rw [initialSem.2.1]
    rfl
  have fold0Sem := caller_fold_success_exact trace.calls.compact
    trace.additive1 (acceptedAlphaAt alphas 0) initialSem.1
    initialSelectors (alphaCanonical 0) (by omega) foldSource.fold0
  have folds1 : trace.additive1.folds.val = 1 := by omega
  have fold1Sem := caller_fold_success_exact trace.additive1 trace.additive2
    (acceptedAlphaAt alphas 1) fold0Sem.1 fold0Sem.2.1
    (alphaCanonical 1) (by omega) foldSource.fold1
  have folds2 : trace.additive2.folds.val = 2 := by omega
  have fold2Sem := caller_fold_success_exact trace.additive2 trace.additive3
    (acceptedAlphaAt alphas 2) fold1Sem.1 fold1Sem.2.1
    (alphaCanonical 2) (by omega) foldSource.fold2
  have folds3 : trace.additive3.folds.val = 3 := by omega
  have fold3Sem := caller_fold_success_exact trace.additive3 trace.additive4
    (acceptedAlphaAt alphas 3) fold2Sem.1 fold2Sem.2.1
    (alphaCanonical 3) (by omega) foldSource.fold3
  have finalStateExact : callerProjectState trace.additive4 =
      AspisV5CompactTerminalOptimized.optimizedRun
        (fun index => callerToK (callerPointAt roundChallenges index))
        (callerToK trace.calls.denseScale)
        (fun index => callerToK (acceptedAlphaAt alphas index)) := by
    rw [fold3Sem.2.2.2, folds3]
    simp only [AspisV5CompactFoldProgramSemantics.optimizedFoldFor]
    rw [fold2Sem.2.2.2, folds2]
    simp only [AspisV5CompactFoldProgramSemantics.optimizedFoldFor]
    rw [fold1Sem.2.2.2, folds1]
    simp only [AspisV5CompactFoldProgramSemantics.optimizedFoldFor]
    rw [fold0Sem.2.2.2, initialFolds]
    simp only [AspisV5CompactFoldProgramSemantics.optimizedFoldFor]
    rw [initialSem.2.2]
    rfl
  obtain ⟨weights, weightsRun, dotRun⟩ := caller_dot_success_exposes_subcalls
    trace.additive4 trace.finalCoefficients trace.additiveDot
    trace.additiveDotSuccess
  have weightsSem := caller_final_weights_success_exact trace.additive4
    weights (callerCanonicalState_implies_canonicalScales trace.additive4
      fold3Sem.1) fold3Sem.2.1 weightsRun
  have dotWeightsCanonical :
      AspisV5RelationCompactAdditiveDotExact.CanonicalFinalWeights weights := by
    intro index
    simpa [AspisV5RelationCompactAdditiveDotExact.finalWeightAt,
      AspisV5CompactFinalFieldSemantics.Canonical,
      AspisV5CompactFinalFieldSemantics.toFull,
      AspisV5RelationCompactAdditiveDotExact.finalToRaw] using
        weightsSem.1 index
  have dotValuesCanonical :
      AspisV5RelationCompactAdditiveDotExact.CanonicalFinalValues
        trace.finalCoefficients := by
    intro index
    unfold AspisV5RelationCompactAdditiveDotExact.finalValueAt
    unfold CallerCanonical at valuesCanonical
    convert valuesCanonical index using 1
  have dotSem :=
    AspisV5RelationCompactAdditiveDotExact.fourTermDotProgram_success_exact
      weights trace.finalCoefficients trace.additiveDot
      dotWeightsCanonical dotValuesCanonical dotRun
  refine ⟨dotSem.1, ?_⟩
  change
    AspisV5RelationGeneratedFieldProjection.toMaintainedExact
        trace.additiveDot = _
  rw [dotSem.2]
  rw [exactFourTermDot_eq_modelDot weights trace.finalCoefficients
    (AspisV5CompactTerminalOptimized.optimizedFinalWeights
      (callerProjectState trace.additive4)) weightsSem.2]
  rw [finalStateExact]
  rfl

#print axioms callerReleasedSelectors_of_project_eq_optimizedInit
#print axioms exactFourTermDot_eq_modelDot
#print axioms CompactFoldSourceEquality
#print axioms accepted_trace_compact_terminal_exact

end AspisV5AcceptedCompactExecutionExact
