import AspisFormal.K1.V7Tag73K13PreQ16TargetProbability
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift

/-!
# Deployed-view agreement on the selected pre-q16 prefix

The pre-q16 extractor uses the chronological first answer in the selected
root prefix.  This file proves that the completed deployed oracle table
returns that same answer.  The proof uses the literal fresh-query table and
its noduplicated input list, not collision resistance or SHA injectivity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16ViewAgreement

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootFreshInputUniqueness
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A lookup in a duplicate-free first-creation pair table returns the
recorded answer of every member. -/
theorem pairTableLookup_of_mem
    (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256)
    (nodup : (queries.map Prod.fst).Nodup)
    (member : (input, answer) ∈ queries) :
    tableLookup (queries.map fun query =>
      ({ input := query.1, output := query.2 } :
        AspisK1.V7Tag73DeterministicRefinement.TableEntry)) input =
        some answer := by
  induction queries with
  | nil => simp at member
  | cons head tail ih =>
      rcases head with ⟨headInput, headAnswer⟩
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with headExact | tailMember
      · rcases headExact with ⟨rfl, rfl⟩
        simp [tableLookup]
      · have different : headInput ≠ input := by
          intro equal
          apply headFresh
          rw [List.mem_map]
          exact ⟨(input, answer), tailMember, by simpa [equal]⟩
        simpa [tableLookup, different] using ih tailNodup tailMember

/-- Every enumerated fresh coordinate is carried by a literal history record
with the same raw input. -/
theorem freshQueryEnumeration_raw_input_mem_history
    (records : List QueryRecord) (input : ShaInput) (answer : Digest256)
    (member : (input, answer) ∈ freshQueryEnumeration records) :
    runtimeInputToRawHashInput input ∈ records.map
      (fun record => runtimeInputToRawHashInput record.input) := by
  induction records with
  | nil => simp [freshQueryEnumeration] at member
  | cons record rest ih =>
      rcases record with ⟨recordInput, recordOutput, recordActor, origin⟩
      cases origin with
      | programmed =>
          simp only [List.map_cons, List.mem_cons]
          apply Or.inr
          exact ih (by simpa [freshQueryEnumeration] using member)
      | fresh =>
          simp only [freshQueryEnumeration, List.mem_cons, Prod.mk.injEq]
            at member
          simp only [List.map_cons, List.mem_cons]
          rcases member with ⟨inputExact, _outputExact⟩ | tailMember
          · exact Or.inl (congrArg runtimeInputToRawHashInput inputExact)
          · exact Or.inr (ih tailMember)
      | cached =>
          simp only [List.map_cons, List.mem_cons]
          apply Or.inr
          exact ih (by simpa [freshQueryEnumeration] using member)

/-- Every actor-tagged fresh root record has its exact answer in the final
deployed oracle table. -/
theorem exact_root_machineFresh_has_operational_lookup
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
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (member : (.machineFresh actor queryInput answer : UnifiedExposureRecord) ∈
      exactFixedRootRecords input.package.root) :
    tableLookup (exactOperationalTable input) queryInput = some answer := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have mappedMember : some (queryInput, answer) ∈
      (exactFixedRootRecords input.package.root).map machineFreshPair? := by
    exact List.mem_map.mpr ⟨_, member, rfl⟩
  rw [exact_root_records_map_pair input] at mappedMember
  have pairMember : (queryInput, answer) ∈ exactRootFreshQueries input := by
    simpa using mappedMember
  have inputNodup := exact_root_fresh_query_inputs_nodup input
  have adversaryTable := projected_machine_prefix_table_eq_fresh_coordinates
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    (freshAnswerTapeToList sample.2) prefixes.adversary
  have verifierTable := projected_machine_prefix_table_eq_fresh_coordinates
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
  have runtimeExact : (exactK12Runtime input).verifierFinalOracle =
      prefixes.verifier.finalState := by
    have exact := congrArg
      (fun runtime => runtime.verifierFinalOracle) prefixes.runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using exact
  unfold exactOperationalTable
  unfold AspisK1.V7Tag73CoupledReplayAlignment.fixedTableOfOracleState
  rw [runtimeExact, verifierTable, adversaryTable]
  simp only [emptyOracle, List.nil_append, List.map_append, List.map_map,
    Function.comp_def]
  have lookup := pairTableLookup_of_mem (exactRootFreshQueries input)
    queryInput answer inputNodup pairMember
  unfold exactRootFreshQueries at lookup
  simpa using lookup

/-- A prefix lookup identifies a literal machine-fresh record in that prefix. -/
theorem exposurePrefixLookup_has_machineFresh_record :
    ∀ (records : List UnifiedExposureRecord),
      OnlyMachineFreshRecords records →
      ∀ (queryInput : ShaInput) (answer : Digest256),
        exposurePrefixLookup records queryInput = some answer →
        ∃ actor,
          (.machineFresh actor queryInput answer : UnifiedExposureRecord) ∈
            records := by
  intro records onlyFresh
  induction records with
  | nil => simp [exposurePrefixLookup]
  | cons record tail ih =>
      intro queryInput answer found
      obtain ⟨actor, headInput, headAnswer, recordExact⟩ :=
        onlyFresh record (by simp)
      subst record
      by_cases same : headInput = queryInput
      · subst queryInput
        have answerExact : headAnswer = answer := by
          simpa only [exposurePrefixLookup, causalInput?,
            UnifiedExposureRecord.answer, Option.some.injEq, if_pos] using found
        subst answer
        exact ⟨actor, by simp⟩
      · have headMiss : causalInput?
            (.machineFresh actor headInput headAnswer : UnifiedExposureRecord) ≠
          some queryInput := by
            intro equal
            exact same (Option.some.inj equal)
        have tailFound : exposurePrefixLookup tail queryInput = some answer := by
          simpa [exposurePrefixLookup, headMiss] using found
        have tailOnly : OnlyMachineFreshRecords tail := by
          intro selected selectedMem
          exact onlyFresh selected (by simp [selectedMem])
        obtain ⟨tailActor, tailMember⟩ :=
          ih tailOnly queryInput answer tailFound
        exact ⟨tailActor, by simp [tailMember]⟩

/-- The deployed truncation agrees with the first chronological answer on
every raw input advertised by the selected exact root prefix. -/
theorem exactK12Truncate_agrees_on_root_prefix
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
    (prior later : List UnifiedExposureRecord) (pivot : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ pivot :: later) :
    ∀ rawInput digest,
      exposurePrefixLookup prior (rawHashInputToRuntimeInput rawInput) =
          some digest →
        exactK12Truncate input rawInput =
          runtimeDigest256PrefixToMerkleDigest digest := by
  intro rawInput digest found
  have priorOnly : OnlyMachineFreshRecords prior := by
    intro record recordMember
    apply exact_root_records_only_machine_fresh input record
    rw [rootExact]
    exact List.mem_append_left _ recordMember
  obtain ⟨actor, priorMember⟩ :=
    exposurePrefixLookup_has_machineFresh_record prior priorOnly
      (rawHashInputToRuntimeInput rawInput) digest found
  have rootMember :
      (.machineFresh actor (rawHashInputToRuntimeInput rawInput) digest :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    rw [rootExact]
    exact List.mem_append_left _ priorMember
  have tableFound := exact_root_machineFresh_has_operational_lookup input actor
    (rawHashInputToRuntimeInput rawInput) digest rootMember
  unfold exactOperationalTable at tableFound
  rw [fixed_table_lookup_eq_lookup_entry_output] at tableFound
  cases selected : lookupEntry (exactK12Runtime input).verifierFinalOracle
      (rawHashInputToRuntimeInput rawInput) with
  | none => simp [selected] at tableFound
  | some entry =>
      have outputExact : entry.output = digest := by
        simpa [selected] using tableFound
      simp [exactK12Truncate, selected, outputExact]

#print axioms pairTableLookup_of_mem
#print axioms freshQueryEnumeration_raw_input_mem_history
#print axioms exact_root_machineFresh_has_operational_lookup
#print axioms exposurePrefixLookup_has_machineFresh_record
#print axioms exactK12Truncate_agrees_on_root_prefix

end

end AspisK1.V7Tag73K13PreQ16ViewAgreement
