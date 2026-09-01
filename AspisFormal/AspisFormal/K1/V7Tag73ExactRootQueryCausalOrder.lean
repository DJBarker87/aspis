import AspisFormal.K1.V7Tag73ExactRootPriorQueryHistory
import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap

/-!
# Target-clean causal order of exact root queries

The exact root query lists are chronological source traces.  If a later
fresh answer is used as the literal 32-byte state prefix of another query,
that dependent query cannot already occur in the answer-producing query's
prefix outside the existing target event.  The proof identifies the source
request state and the target-clean certificate state at the same native
scheduler prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootQueryCausalOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalProgrammingFreshness
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootPriorQueryHistory
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Within the adversary root segment, the selected fresh answer is not the
literal state prefix of any earlier adversary query. -/
theorem exact_root_adversary_answer_avoids_prior_query_prefixes
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (producerInput : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        prior ++ (producerInput, answer) :: later) :
    ∀ query ∈ prior, ¬ HasLiteralStatePrefix answer query.1 := by
  obtain ⟨sourceState, priorHistory, sourceRequest⟩ :=
    exact_root_adversary_query_has_global_prior_history transitionRoom input
      prior producerInput answer later decomposition
  let priorRecords := projectedMachineFreshRecords .adversary prior
  let laterRecords :=
    projectedMachineFreshRecords .adversary later ++
      projectedMachineFreshRecords .verifier
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries ++
      (exactFixedComputedClientTailRun transitionFuel configuration sample
        input.package.root).trace
  have traceExact :
      exactCompilerUnifiedExposureTrace parameters transitionFuel
          (exactPlainRomCursor configuration sample.1) sample.2 =
        priorRecords ++
          .machineFresh .adversary producerInput answer :: laterRecords := by
    rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
      fullProjectedRootRecords priorRecords laterRecords
    rw [decomposition]
    simp only [projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append, List.append_assoc]
  have certificateTraceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2)) =
        priorRecords ++
          .machineFresh .adversary producerInput answer :: laterRecords := by
    change exactCompilerUnifiedExposureTrace parameters transitionFuel
      (exactPlainRomCursor configuration sample.1) sample.2 = _
    exact traceExact
  obtain ⟨certificateState, atPrefix⟩ :=
    certified_operational_machine_at_prefix_of_trace_decomposition
      input.package.root.wholeTraceClean.operationalCertificate priorRecords
      laterRecords .adversary producerInput answer certificateTraceExact
  have certificateRequest :=
    certified_machine_exposure_has_exact_native_request (rootExact := rfl)
      atPrefix
  have priorAnswers :
      priorRecords.map UnifiedExposureRecord.answer = prior.map Prod.snd := by
    exact projected_machine_fresh_record_answers .adversary prior
  rw [priorAnswers] at certificateRequest
  have stateExact : certificateState = sourceState :=
    exact_native_machine_request_state_unique certificateRequest sourceRequest
  intro query queryMember
  have recordAtSource := priorHistory query queryMember
  have recordAtCertificate :
      projectedFreshQueryRecord .adversary query ∈ certificateState.history := by
    rw [stateExact]
    exact recordAtSource
  exact certified_machine_exposure_at_prefix_avoids_history_literal_prefix
    atPrefix (projectedFreshQueryRecord .adversary query) recordAtCertificate

/-- At a verifier-root fresh query, the selected answer is not the literal
state prefix of any adversary query or any earlier verifier query.  This is
the exact cross-callback causal-order fact: the certificate state and the
source state are identified at the same global native scheduler prefix. -/
theorem exact_root_verifier_answer_avoids_prior_query_prefixes
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior : List (ShaInput × Digest256)) (producerInput : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        prior ++ (producerInput, answer) :: later) :
    (∀ query ∈
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries,
      ¬ HasLiteralStatePrefix answer query.1) ∧
    (∀ query ∈ prior, ¬ HasLiteralStatePrefix answer query.1) := by
  obtain ⟨sourceState, adversaryHistory, verifierHistory, sourceRequest⟩ :=
    exact_root_verifier_query_has_global_prior_history transitionRoom input
      prior producerInput answer later decomposition
  let adversaryQueries :=
    input.package.root.full.projection.rootPrefixes.adversary.freshQueries
  let priorRecords :=
    projectedMachineFreshRecords .adversary adversaryQueries ++
      projectedMachineFreshRecords .verifier prior
  let laterRecords :=
    projectedMachineFreshRecords .verifier later ++
      (exactFixedComputedClientTailRun transitionFuel configuration sample
        input.package.root).trace
  have traceExact :
      exactCompilerUnifiedExposureTrace parameters transitionFuel
          (exactPlainRomCursor configuration sample.1) sample.2 =
        priorRecords ++
          .machineFresh .verifier producerInput answer :: laterRecords := by
    rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
      fullProjectedRootRecords priorRecords laterRecords
    rw [decomposition]
    simp only [adversaryQueries, projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append, List.append_assoc]
  have certificateTraceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2)) =
        priorRecords ++
          .machineFresh .verifier producerInput answer :: laterRecords := by
    change exactCompilerUnifiedExposureTrace parameters transitionFuel
      (exactPlainRomCursor configuration sample.1) sample.2 = _
    exact traceExact
  obtain ⟨certificateState, atPrefix⟩ :=
    certified_operational_machine_at_prefix_of_trace_decomposition
      input.package.root.wholeTraceClean.operationalCertificate priorRecords
      laterRecords .verifier producerInput answer certificateTraceExact
  have certificateRequest :=
    certified_machine_exposure_has_exact_native_request (rootExact := rfl)
      atPrefix
  have priorAnswers :
      priorRecords.map UnifiedExposureRecord.answer =
        (adversaryQueries ++ prior).map Prod.snd := by
    unfold priorRecords
    simp only [List.map_append,
      projected_machine_fresh_record_answers]
  rw [priorAnswers] at certificateRequest
  have stateExact : certificateState = sourceState :=
    exact_native_machine_request_state_unique certificateRequest sourceRequest
  constructor
  · intro query queryMember
    have recordAtSource := adversaryHistory query queryMember
    have recordAtCertificate :
        projectedFreshQueryRecord .adversary query ∈
          certificateState.history := by
      rw [stateExact]
      exact recordAtSource
    exact certified_machine_exposure_at_prefix_avoids_history_literal_prefix
      atPrefix (projectedFreshQueryRecord .adversary query)
        recordAtCertificate
  · intro query queryMember
    have recordAtSource := verifierHistory query queryMember
    have recordAtCertificate :
        projectedFreshQueryRecord .verifier query ∈ certificateState.history := by
      rw [stateExact]
      exact recordAtSource
    exact certified_machine_exposure_at_prefix_avoids_history_literal_prefix
      atPrefix (projectedFreshQueryRecord .verifier query) recordAtCertificate

#print axioms exact_root_adversary_answer_avoids_prior_query_prefixes
#print axioms exact_root_verifier_answer_avoids_prior_query_prefixes

end

end AspisK1.V7Tag73ExactRootQueryCausalOrder
