import AspisFormal.K1.V7Tag73K13PreQ16TargetSchedulerTree
import AspisFormal.K1.V7Tag73K12CollisionSchedulerTree
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

/-!
# Actual-run bridge for the pre-q16 Merkle target tree

This file connects a concrete late first-unresolved Merkle target in an
accepted Tag-73 trial to a later fresh record in the literal root scheduler.
It then embeds that record in the exact compiler master-tape trace, so the
causal target-tree probability theorem applies without a verifier-first or
independence assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16TargetActualBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K12CollisionSchedulerTree
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetInventory
open AspisK1.V7Tag73K13PreQ16TargetSchedulerTree
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleFirstUnresolvedBinding
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleQueryExtractor

noncomputable section

theorem preQ16FullMerkleTargets_append_left
    (records later : List UnifiedExposureRecord) :
    preQ16FullMerkleTargets records ⊆
      preQ16FullMerkleTargets (records ++ later) := by
  intro digest digestMem
  unfold preQ16FullMerkleTargets deployedPrefixTargetPreimage at digestMem ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at digestMem ⊢
  unfold prefixMerkleCandidateSet at digestMem ⊢
  obtain ⟨rawInput, rawInputMem, candidateMem⟩ :=
    Finset.mem_biUnion.mp digestMem
  apply Finset.mem_biUnion.mpr
  refine ⟨rawInput, ?_, candidateMem⟩
  rw [List.mem_toFinset] at rawInputMem ⊢
  simpa [exposurePrefixRawQueries, List.filterMap_append,
    List.map_append] using Or.inl rawInputMem

/-- A late target in the accepted trial is carried by a fresh root record
strictly after the trial prefix. Cached repetitions are routed to their first
fresh table entry; the `input ∉ prefixLog` clause excludes an earlier entry. -/
theorem exact_actual_late_target_has_post_prefix_root_record
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior pivotLater : List UnifiedExposureRecord)
    (pivot : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ pivot :: pivotLater)
    (lateHit : PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)) :
    ∃ target middle after actor queryInput answer,
      target ∈ prefixResolutionTargetSet (exactK12Truncate input)
        (exposurePrefixRawQueries prior) (exactK12Roots input)
        (exactK12Openings input) ∧
      exactFixedRootRecords input.package.root =
        prior ++ middle ++
          (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
            after ∧
      runtimeDigest256PrefixToMerkleDigest answer = target := by
  rcases lateHit with
    ⟨target, targetMem, rawInput, rawMember, rawNotPrefix, digestExact⟩
  obtain ⟨record, entry, recordMember, rawExact, found, inputExact,
      outputExact, truncateExact⟩ :=
    exact_k12_logged_raw_input_has_table_entry input rawInput rawMember
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact : (exactK12Runtime input).verifierFinalOracle =
      prefixes.verifier.finalState := by
    have exact := congrArg
      (fun runtime => runtime.verifierFinalOracle) prefixes.runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using exact
  have tableFound : tableLookup (exactOperationalTable input) record.input =
      some record.output := by
    unfold exactOperationalTable
    rw [fixed_table_lookup_eq_lookup_entry_output, runtimeExact, found]
    simp [outputExact]
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input record.input record.output
      tableFound
  have notPrior :
      (.machineFresh actor record.input record.output : UnifiedExposureRecord) ∉
        prior := by
    intro priorMember
    apply rawNotPrefix
    rw [rawExact]
    exact machineFresh_input_mem_exposurePrefixRawQueries prior actor
      record.input record.output priorMember
  have suffixMember :
      (.machineFresh actor record.input record.output : UnifiedExposureRecord) ∈
        pivot :: pivotLater := by
    rw [rootExact] at rootMember
    rcases List.mem_append.mp rootMember with earlier | later
    · exact False.elim (notPrior earlier)
    · exact later
  obtain ⟨middle, after, suffixExact⟩ :=
    (List.mem_iff_append).mp suffixMember
  refine ⟨target, middle, after, actor, record.input, record.output,
    targetMem, ?_, ?_⟩
  · calc
      exactFixedRootRecords input.package.root =
          prior ++ pivot :: pivotLater := rootExact
      _ = prior ++ (pivot :: pivotLater) := rfl
      _ = prior ++
          (middle ++
            (.machineFresh actor record.input record.output :
              UnifiedExposureRecord) :: after) := by rw [suffixExact]
      _ = prior ++ middle ++
          (.machineFresh actor record.input record.output :
            UnifiedExposureRecord) :: after := by simp [List.append_assoc]
  · calc
      runtimeDigest256PrefixToMerkleDigest record.output =
          runtimeDigest256PrefixToMerkleDigest entry.output := by
            rw [outputExact]
      _ = exactK12Truncate input rawInput := truncateExact.symm
      _ = target := digestExact

/-- The concrete post-prefix record is a hit in the causal scheduler tree on
the exact compiler's own master tape. -/
theorem exact_actual_late_target_implies_preQ16_scheduler_hit
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput) (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : trial.val = prior.length)
    (lateHit : PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exposurePrefixRawQueries prior) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)) :
    (preQ16MerkleTargetTree
      (globalFull256OracleCallCap parameters)
      (unifiedFull256ExposureCap parameters) transitionFuel
      (exactPlainRomCursor configuration sample.1).erase).everHits
        (preQ16MerkleTargetTapeFrom 0
          (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2))) := by
  obtain ⟨target, middle, after, actor, queryInput, answer, targetMem,
      rootHitExact, answerPrefix⟩ :=
    exact_actual_late_target_has_post_prefix_root_record input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact lateHit
  have targetFixed : target ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries prior) :=
    exact_actual_trial_prefixResolutionTargetSet_subset transitionRoom input
      trial actual prior later pivotActor pivotInput pivotAnswer rootExact
      trialExact targetMem
  have answerTarget : answer ∈ preQ16FullMerkleTargets prior :=
    answer_mem_preQ16FullMerkleTargets_of_prefix prior answer target targetFixed
      answerPrefix
  have answerTargetLater : answer ∈
      preQ16FullMerkleTargets (prior ++ middle) :=
    preQ16FullMerkleTargets_append_left prior middle answerTarget
  let hitRecord : UnifiedExposureRecord :=
    .machineFresh actor queryInput answer
  let clientTail :=
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace
  have traceExact :
      exactCompilerUnifiedExposureTrace parameters transitionFuel
          (exactPlainRomCursor configuration sample.1) sample.2 =
        (prior ++ middle) ++ hitRecord :: (after ++ clientTail) := by
    rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    rw [rootHitExact]
    simp only [hitRecord, clientTail, List.cons_append, List.append_assoc]
  apply later_record_target_implies_tree_hit transitionFuel
    (exactPlainRomCursor configuration sample.1).erase
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters sample.2))
    (prior ++ middle) hitRecord (after ++ clientTail)
  · exact traceExact
  · simpa only [hitRecord, UnifiedExposureRecord.answer] using answerTargetLater

#print axioms preQ16FullMerkleTargets_append_left
#print axioms exact_actual_late_target_has_post_prefix_root_record
#print axioms exact_actual_late_target_implies_preQ16_scheduler_hit

end

end AspisK1.V7Tag73K13PreQ16TargetActualBridge
