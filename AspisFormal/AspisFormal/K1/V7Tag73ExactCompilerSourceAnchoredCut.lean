import AspisFormal.K1.V7Tag73SourceAnchoredSchedulerCut
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates

/-!
# Exact compiler source-anchored root cut

This file instantiates the neutral cursor-relative alignment invariant on the
two literal projected production machines.  It strengthens the old unordered
whole-trace occurrence fact: a final-table answer is routed chronologically to
the adversary suffix or, after the exact actor-change state, to the verifier
suffix.

The theorem deliberately stops at ordered source alignment.  It does not
classify a SHA coordinate by logical role and does not charge adversarial
prequery as a bad event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerSourceAnchoredCut

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73FullCursorClientLineageLift

noncomputable section

/-- The actual adversary and verifier projected prefixes form one joined
source-anchored cut.  Both cuts are constructed from executable prefix
certificates already carried by the exact operational input. -/
def exactCompilerRootSourceAnchoredCut
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    SourceAnchoredSequentialCut
      configuration.machine.adversaryLimits .adversary
      configuration.machine.verifierLimits .verifier
      prefixes.adversary.finalState prefixes.verifier.finalState
      prefixes.adversary.result prefixes.verifier.result := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  let first := SourceAnchoredMachineCut.ofProjectedPrefix
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    (freshAnswerTapeToList sample.2) prefixes.adversary
  let second := SourceAnchoredMachineCut.ofProjectedPrefix
    configuration.machine.verifierLimits .verifier
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.adversary.remaining prefixes.verifier
  exact SourceAnchoredSequentialCut.mk first second rfl

@[simp] theorem exact_compiler_root_source_anchored_cut_first_state
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactCompilerRootSourceAnchoredCut input).first.state = emptyOracle := by
  rfl

@[simp] theorem exact_compiler_root_source_anchored_cut_first_remaining
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactCompilerRootSourceAnchoredCut input).first.remainingFresh =
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries := by
  rfl

@[simp] theorem exact_compiler_root_source_anchored_cut_second_remaining
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactCompilerRootSourceAnchoredCut input).second.remainingFresh =
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries := by
  rfl

/-- Exact final-root lookup routing in chronological actor order.  Since the
root starts from the empty table, the cached-at-entry branch of the generic
sequential theorem is impossible: the original fresh exposure lies in exactly
one of the two ordered production prefix lists. -/
theorem exact_compiler_final_lookup_in_ordered_root_suffix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    (target, answer) ∈
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries \/
      (target, answer) ∈
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact : (exactK12Runtime input).verifierFinalOracle =
      prefixes.verifier.finalState := by
    have exact := congrArg
      (fun runtime => runtime.verifierFinalOracle) prefixes.runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using exact
  have finalFound :
      (lookupEntry prefixes.verifier.finalState target).map
          AspisK1.V7FsAokExperiment.TableEntry.output =
        some answer := by
    change tableLookup
        (fixedTableOfOracleState (exactK12Runtime input).verifierFinalOracle)
          target = some answer at found
    rw [fixed_table_lookup_eq_lookup_entry_output] at found
    change (lookupEntry (exactK12Runtime input).verifierFinalOracle target).map
        AspisK1.V7FsAokExperiment.TableEntry.output = some answer at found
    rwa [runtimeExact] at found
  have routed :=
    source_anchored_sequential_cut_lookup_or_ordered_future_fresh
      (exactCompilerRootSourceAnchoredCut input) target answer finalFound
  rcases routed with cached | adversaryFuture | verifierFuture
  · rcases cached with ⟨entry, selected, _outputExact⟩
    have selectedEmpty : lookupEntry emptyOracle target = some entry := by
      rw [← exact_compiler_root_source_anchored_cut_first_state input]
      exact selected
    simp [lookupEntry, emptyOracle] at selectedEmpty
  · exact Or.inl (by
      rw [← exact_compiler_root_source_anchored_cut_first_remaining input]
      exact adversaryFuture)
  · exact Or.inr (by
      rw [← exact_compiler_root_source_anchored_cut_second_remaining input]
      exact verifierFuture)

/-- Every coordinate actually consumed by the deployed variable-prefix gamma
decoder is source-routed to one of the two chronological root suffixes.  This
strictly strengthens the old unordered trace-occurrence endpoint while
preserving the adversary-first possibility. -/
theorem exact_compiler_consumed_gamma_coordinates_ordered_root
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ initialDigest outputs advances,
      GammaTableCoordinateChain (exactOperationalTable input) initialDigest
          outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      ∀ target answer,
        (target, answer) ∈
            gammaConsumedCoordinates initialDigest outputs advances ->
          (target, answer) ∈
              input.package.root.full.projection.rootPrefixes.adversary.freshQueries \/
            (target, answer) ∈
              input.package.root.full.projection.rootPrefixes.verifier.freshQueries := by
  obtain ⟨initialDigest, outputs, advances, coordinates, outputsLength,
      occurs⟩ := exact_compiler_consumed_gamma_coordinates_occur input
  refine ⟨initialDigest, outputs, advances, coordinates, outputsLength, ?_⟩
  intro target answer member
  have lookup := gamma_consumed_coordinate_lookup
    (exactOperationalTable input) initialDigest outputs advances coordinates
      target answer member
  exact exact_compiler_final_lookup_in_ordered_root_suffix input target answer
    lookup

/-- Any exact final-table coordinate is reachable by the executable scanner
from the literal production root.  The proof is sourced by the ordered
adversary/verifier suffix theorem, then erased to the existing full scheduler
trace; no caller supplies a replay equality. -/
theorem exact_compiler_final_lookup_has_full_target_pause
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result) target,
      exactCompilerFullTargetScan input target = .paused pause := by
  rcases exact_compiler_final_lookup_in_ordered_root_suffix input target answer
      found with adversaryFuture | verifierFuture
  · have rootMember :
        (.machineFresh .adversary target answer : UnifiedExposureRecord) ∈
          exactFixedRootRecords input.package.root := by
      unfold exactFixedRootRecords fullProjectedRootRecords
      exact List.mem_append_left _
        (machine_fresh_mem_projected_records .adversary _ target answer
          adversaryFuture)
    have fullMember :
        (.machineFresh .adversary target answer : UnifiedExposureRecord) ∈
          (runExactPlainRom transitionFuel configuration sample).trace := by
      rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
      exact List.mem_append_left _ rootMember
    exact exact_compiler_full_target_scan_paused_of_trace_mem input target
      .adversary answer fullMember
  · have rootMember :
        (.machineFresh .verifier target answer : UnifiedExposureRecord) ∈
          exactFixedRootRecords input.package.root := by
      unfold exactFixedRootRecords fullProjectedRootRecords
      exact List.mem_append_right _
        (machine_fresh_mem_projected_records .verifier _ target answer
          verifierFuture)
    have fullMember :
        (.machineFresh .verifier target answer : UnifiedExposureRecord) ∈
          (runExactPlainRom transitionFuel configuration sample).trace := by
      rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
      exact List.mem_append_left _ rootMember
    exact exact_compiler_full_target_scan_paused_of_trace_mem input target
      .verifier answer fullMember

#print axioms exact_compiler_final_lookup_in_ordered_root_suffix
#print axioms exact_compiler_consumed_gamma_coordinates_ordered_root
#print axioms exact_compiler_final_lookup_has_full_target_pause

end

end AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
