import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree
import AspisFormal.K1.V7Tag73ExactFixedK12FailureReduction

/-!
# Exact Tag-73 K1.2 truncated-collision scheduler tree

This module lifts the ordinary 208-bit birthday event to the real 256-bit
compiler tape.  Each prior 208-bit prefix contributes its exact `2^48`
full-output fibre, so a duplicate prefix in the executable root history is
charged with the ordinary birthday coefficient over `2^208`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K12CollisionSchedulerTree

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK12FailureReduction
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

noncomputable section

def projectedPrefixCollisionCapsFrom : Nat → Nat → List Nat
  | _, 0 => []
  | step, remaining + 1 =>
      step * 2 ^ 48 :: projectedPrefixCollisionCapsFrom (step + 1) remaining

@[simp] theorem projected_prefix_collision_caps_from_length
    (step remaining : Nat) :
    (projectedPrefixCollisionCapsFrom step remaining).length = remaining := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      simp [projectedPrefixCollisionCapsFrom, inductionHypothesis]

theorem projected_prefix_collision_caps_from_sum
    (step remaining : Nat) :
    (projectedPrefixCollisionCapsFrom step remaining).sum =
      (List.range' step remaining).sum * 2 ^ 48 := by
  induction remaining generalizing step with
  | zero => simp [projectedPrefixCollisionCapsFrom]
  | succ remaining inductionHypothesis =>
      simp only [projectedPrefixCollisionCapsFrom, List.sum_cons,
        List.range'_succ]
      rw [inductionHypothesis]
      omega

def projectedPrefixCollisionTreeFrom
    (step remaining : Nat) (seen : Finset MerkleDigest208)
    (seenCardLe : seen.card ≤ step) :
    CausalTargetTree Digest256
      (projectedPrefixCollisionCapsFrom step remaining) := by
  induction remaining generalizing step seen with
  | zero => exact .done
  | succ remaining inductionHypothesis =>
      exact .step (deployedPrefixTargetPreimage seen)
        (deployed_prefix_target_preimage_card_le seen seenCardLe)
        fun output =>
          inductionHypothesis (step + 1)
            (insert (runtimeDigest256PrefixToMerkleDigest output) seen)
            ((Finset.card_insert_le _ _).trans
              (Nat.add_le_add_right seenCardLe 1))

def projectedPrefixCollisionTree (freshExposures : Nat) :
    CausalTargetTree Digest256
      (projectedPrefixCollisionCapsFrom 0 freshExposures) :=
  projectedPrefixCollisionTreeFrom 0 freshExposures ∅ (by simp)

def projectedPrefixCollisionTapeFrom {Output : Type} (step : Nat) :
    ∀ {remaining : Nat}, FreshAnswerTape Output remaining →
      FreshAnswerTape Output
        (projectedPrefixCollisionCapsFrom step remaining).length
  | 0, tape => tape
  | _remaining + 1, tape =>
      (tape.1, projectedPrefixCollisionTapeFrom (step + 1) tape.2)

def projectedPrefixCollisionTape {Output : Type} {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    FreshAnswerTape Output
      (projectedPrefixCollisionCapsFrom 0 remaining).length :=
  projectedPrefixCollisionTapeFrom 0 tape

@[simp] theorem projected_prefix_collision_tape_from_to_list
    {Output : Type} {remaining : Nat}
    (step : Nat) (tape : FreshAnswerTape Output remaining) :
    freshAnswerTapeToList (projectedPrefixCollisionTapeFrom step tape) =
      freshAnswerTapeToList tape := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      change tape.1 ::
          freshAnswerTapeToList
            (projectedPrefixCollisionTapeFrom (step + 1) tape.2) =
        tape.1 :: freshAnswerTapeToList tape.2
      rw [inductionHypothesis (step + 1)]

@[simp] theorem projected_prefix_collision_tape_to_list
    {Output : Type} {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    freshAnswerTapeToList (projectedPrefixCollisionTape tape) =
      freshAnswerTapeToList tape := by
  exact projected_prefix_collision_tape_from_to_list 0 tape

def ProjectedPrefixBad (seen : Finset MerkleDigest208)
    (outputs : List Digest256) : Prop :=
  (∃ output ∈ outputs,
      runtimeDigest256PrefixToMerkleDigest output ∈ seen) ∨
    ¬ (outputs.map runtimeDigest256PrefixToMerkleDigest).Nodup

theorem projected_prefix_bad_implies_tree_hit :
    ∀ (step remaining : Nat) (seen : Finset MerkleDigest208)
      (seenCardLe : seen.card ≤ step)
      (tape : FreshAnswerTape Digest256 remaining),
      ProjectedPrefixBad seen (freshAnswerTapeToList tape) →
        ((projectedPrefixCollisionTreeFrom step remaining seen
          seenCardLe).everHits
            (projectedPrefixCollisionTapeFrom step tape)) := by
  intro step remaining
  induction remaining generalizing step with
  | zero =>
      intro seen seenCardLe tape bad
      rcases bad with ⟨output, member, _hit⟩ | duplicate
      · simp [freshAnswerTapeToList] at member
      · exact duplicate (by simp [freshAnswerTapeToList])
  | succ remaining inductionHypothesis =>
      intro seen seenCardLe tape bad
      let head := tape.1
      let tail := tape.2
      by_cases headSeen :
          runtimeDigest256PrefixToMerkleDigest head ∈ seen
      · apply Or.inl
        change tape.1 ∈ deployedPrefixTargetPreimage seen
        simpa [head, deployedPrefixTargetPreimage] using headSeen
      · apply Or.inr
        apply inductionHypothesis (step + 1)
          (insert (runtimeDigest256PrefixToMerkleDigest head) seen)
          ((Finset.card_insert_le _ _).trans
            (Nat.add_le_add_right seenCardLe 1)) tail
        rcases bad with earlier | duplicate
        · rcases earlier with ⟨output, member, outputSeen⟩
          simp only [freshAnswerTapeToList, List.mem_cons] at member
          rcases member with headExact | tailMember
          · subst output
            exact False.elim (headSeen outputSeen)
          · exact Or.inl ⟨output, tailMember,
              Finset.mem_insert_of_mem outputSeen⟩
        · have duplicate' : ¬
              (runtimeDigest256PrefixToMerkleDigest head ::
                (freshAnswerTapeToList tail).map
                  runtimeDigest256PrefixToMerkleDigest).Nodup := by
            simpa [freshAnswerTapeToList, head, tail] using duplicate
          by_cases headLater : runtimeDigest256PrefixToMerkleDigest head ∈
              (freshAnswerTapeToList tail).map
                runtimeDigest256PrefixToMerkleDigest
          · obtain ⟨output, outputMember, outputPrefix⟩ :=
              List.mem_map.mp headLater
            exact Or.inl ⟨output, outputMember, by
              rw [outputPrefix]
              exact Finset.mem_insert_self _ _⟩
          · exact Or.inr (fun tailNodup =>
              duplicate' (List.nodup_cons.mpr ⟨headLater, tailNodup⟩))

theorem projected_prefix_duplicate_implies_collision_tree_hit
    {freshExposures : Nat}
    (tape : FreshAnswerTape Digest256 freshExposures)
    (duplicate : ¬ ((freshAnswerTapeToList tape).map
      runtimeDigest256PrefixToMerkleDigest).Nodup) :
    (projectedPrefixCollisionTree freshExposures).everHits
      (projectedPrefixCollisionTape tape) := by
  apply projected_prefix_bad_implies_tree_hit 0 freshExposures ∅ (by simp)
  exact Or.inr duplicate

theorem projected_prefix_collision_caps_sum_exact (freshExposures : Nat) :
    (projectedPrefixCollisionCapsFrom 0 freshExposures).sum =
      freshExposures.choose 2 * 2 ^ 48 := by
  rw [projected_prefix_collision_caps_from_sum,
    List.sum_range', Nat.choose_two_right]
  simp

theorem projected_prefix_collision_tree_probability_le_exact_count
    (freshExposures : Nat) :
    (uniformDigestFreshTape
        (projectedPrefixCollisionCapsFrom 0 freshExposures).length).toOuterMeasure
        (causalHitEvent
          (projectedPrefixCollisionTree freshExposures)) ≤
      (((freshExposures.choose 2 * 2 ^ 48) *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  have bound := uniform_digest_causal_hit_probability_le_exact_count
    (projectedPrefixCollisionTree freshExposures)
  simpa only [projected_prefix_collision_caps_sum_exact,
    projected_prefix_collision_caps_from_length] using bound

/-! ## Actual root-table collision inclusion -/

theorem nodup_map_forces_equal_of_members
    {α β : Type} {values : List α} {mapValue : α → β}
    (nodup : (values.map mapValue).Nodup)
    {left right : α} (leftMember : left ∈ values)
    (rightMember : right ∈ values)
    (mappedEqual : mapValue left = mapValue right) :
    left = right := by
  induction values with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      have headNotTail : mapValue head ∉ tail.map mapValue :=
        (List.nodup_cons.mp nodup).1
      have tailNodup : (tail.map mapValue).Nodup :=
        (List.nodup_cons.mp nodup).2
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftTail <;>
        rcases rightMember with rfl | rightTail
      · rfl
      · exact False.elim (headNotTail
          (List.mem_map.mpr ⟨right, rightTail, mappedEqual.symm⟩))
      · exact False.elim (headNotTail
          (List.mem_map.mpr ⟨left, leftTail, mappedEqual⟩))
      · exact inductionHypothesis tailNodup leftTail rightTail

theorem fresh_table_entry_prefixes_eq_fresh_answer_prefixes
    (records : List QueryRecord) :
    ((records.filter fun record => record.origin = .fresh).map
        freshTableEntryOfRecord).map
          (fun entry => runtimeDigest256PrefixToMerkleDigest entry.output) =
      (freshAnswerEnumeration records).map
        runtimeDigest256PrefixToMerkleDigest := by
  induction records with
  | nil => rfl
  | cons record records inductionHypothesis =>
      cases originExact : record.origin <;>
        simp [freshTableEntryOfRecord, freshAnswerEnumeration, originExact,
          inductionHypothesis]

theorem exact_k12_final_history_record_lookup
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
    (record : QueryRecord)
    (recordMember : record ∈
      input.package.root.full.projection.rootPrefixes.verifier.finalState.history) :
    (lookupEntry
      input.package.root.full.projection.rootPrefixes.verifier.finalState
      record.input).map TableEntry.output = some record.output := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  obtain ⟨appended, historyExact, _answersExact⟩ :=
    projected_fresh_returned_trace_preserves_suffix
      configuration.machine.verifierLimits .verifier
      prefixes.adversary.finalState.history []
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.verifier.freshQueries prefixes.verifier.result
      prefixes.verifier.finalState prefixes.verifier.steps
      (projected_fresh_suffix_initial prefixes.adversary.finalState)
      prefixes.verifier.trace
  rw [historyExact] at recordMember
  rcases List.mem_append.mp recordMember with inherited | appendedMember
  · have adversaryMember : record ∈ historySince emptyOracle
        prefixes.adversary.finalState := by
      simpa [historySince, emptyOracle] using inherited
    have before := projected_machine_prefix_lookup_retains_segment_answer
      configuration.machine.adversaryLimits .adversary
      configuration.machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.adversaryFuel
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)))
      (freshAnswerTapeToList sample.2) prefixes.adversary record adversaryMember
    obtain ⟨tableSuffix, tableExtension⟩ :=
      projected_machine_prefix_table_extension
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
    cases beforeLookup : lookupEntry prefixes.adversary.finalState record.input with
    | none => simp [beforeLookup] at before
    | some entry =>
        have beforeOutput : entry.output = record.output := by
          simpa [beforeLookup] using before
        have afterLookup := lookupEntry_preserved_by_table_extension
          prefixes.adversary.finalState prefixes.verifier.finalState tableSuffix
          tableExtension record.input entry beforeLookup
        change (lookupEntry prefixes.verifier.finalState record.input).map
          TableEntry.output = some record.output
        rw [afterLookup]
        exact congrArg some beforeOutput
  · have segmentMember : record ∈ historySince
        prefixes.adversary.finalState prefixes.verifier.finalState := by
      unfold historySince
      rw [historyExact]
      simpa using appendedMember
    exact projected_machine_prefix_lookup_retains_segment_answer
      configuration.machine.verifierLimits .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.adversary.remaining prefixes.verifier record segmentMember

theorem exact_k12_logged_raw_input_has_table_entry
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
    (rawInput : RawHashInput) (rawMember : rawInput ∈ exactK12OrderedQueries input) :
    ∃ record entry,
      record ∈ input.package.root.full.projection.rootPrefixes.verifier.finalState.history ∧
      rawInput = runtimeInputToRawHashInput record.input ∧
      lookupEntry input.package.root.full.projection.rootPrefixes.verifier.finalState
          record.input = some entry ∧
      entry.input = record.input ∧ entry.output = record.output ∧
      exactK12Truncate input rawInput =
        runtimeDigest256PrefixToMerkleDigest entry.output := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact : exactK12Runtime input =
      operationalRootRuntime
        (configuration.machine.tapeIdentity sample.1)
        prefixes.adversaryValue prefixes.adversary.finalState
        prefixes.verifier.finalState prefixes.verifierFinalStateValue := by
    simpa [exactK12Runtime, prefixes] using prefixes.runtimeExact
  have rawMember' : rawInput ∈ prefixes.verifier.finalState.history.map
      (fun record : QueryRecord => runtimeInputToRawHashInput record.input) := by
    simpa [exactK12OrderedQueries, runtimeExact, operationalRootRuntime] using
      rawMember
  obtain ⟨record, recordMember, rawExact⟩ := List.mem_map.mp rawMember'
  have retained := exact_k12_final_history_record_lookup input record recordMember
  change (lookupEntry prefixes.verifier.finalState record.input).map
      TableEntry.output = some record.output at retained
  cases found : lookupEntry prefixes.verifier.finalState record.input with
  | none => simp [found] at retained
  | some entry =>
      have outputExact : entry.output = record.output := by
        simpa [found] using retained
      have inputExact : entry.input = record.input := by
        unfold lookupEntry at found
        exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
      refine ⟨record, entry, recordMember, rawExact.symm, found, inputExact,
        outputExact, ?_⟩
      unfold exactK12Truncate
      rw [runtimeExact]
      change (match lookupEntry prefixes.verifier.finalState
          (rawHashInputToRuntimeInput rawInput) with
        | some selected => runtimeDigest256PrefixToMerkleDigest selected.output
        | none => zeroMerkleDigest) =
          runtimeDigest256PrefixToMerkleDigest entry.output
      rw [← rawExact, rawHashInputToRuntimeInput_roundtrip, found]

theorem verifier_fresh_table_prefixes_eq_fresh_answer_prefixes
    (before after : OracleState) :
    (verifierFreshTableEntries before after).map
        (fun entry => runtimeDigest256PrefixToMerkleDigest entry.output) =
      (freshAnswerEnumeration (historySince before after)).map
        runtimeDigest256PrefixToMerkleDigest := by
  unfold verifierFreshTableEntries verifierFreshRecords
  exact fresh_table_entry_prefixes_eq_fresh_answer_prefixes _

theorem exact_k12_final_table_prefixes_eq_root_fresh_prefixes
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
    prefixes.verifier.finalState.table.map
        (fun entry => runtimeDigest256PrefixToMerkleDigest entry.output) =
      (prefixes.adversary.freshQueries.map Prod.snd ++
        prefixes.verifier.freshQueries.map Prod.snd).map
          runtimeDigest256PrefixToMerkleDigest := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  dsimp only
  let proverController := controllerFromProjectedFreshAnswers
    emptyOracle.history (prefixes.adversary.freshQueries.map Prod.snd)
  have proverRun := projected_machine_prefix_returned_run_exact
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    (freshAnswerTapeToList sample.2) prefixes.adversary
    empty_oracle_history_total_coherent
  have proverExtension :=
    (run_machine_exact_fresh_extension proverController
      configuration.machine.adversaryLimits .adversary
      configuration.machine.adversaryFuel emptyOracle
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.adversaryFuel
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)))).1
  rw [proverRun] at proverExtension
  change prefixes.adversary.finalState.table = emptyOracle.table ++
      verifierFreshTableEntries emptyOracle
        prefixes.adversary.finalState at proverExtension
  let verifierController := controllerFromProjectedFreshAnswers
    prefixes.adversary.finalState.history
    (prefixes.verifier.freshQueries.map Prod.snd)
  have verifierRun := projected_machine_prefix_returned_run_exact
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
    prefixes.adversary.finalCoherent
  have verifierExtension :=
    (run_machine_exact_fresh_extension verifierController
      configuration.machine.verifierLimits .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))).1
  rw [verifierRun] at verifierExtension
  change prefixes.verifier.finalState.table =
      prefixes.adversary.finalState.table ++
        verifierFreshTableEntries prefixes.adversary.finalState
          prefixes.verifier.finalState at verifierExtension
  have proverAnswers := projected_machine_prefix_fresh_answers_are_history_suffix
    configuration.machine.adversaryLimits .adversary
    configuration.machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.adversaryFuel
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)))
    (freshAnswerTapeToList sample.2) prefixes.adversary
  have verifierAnswers := projected_machine_prefix_fresh_answers_are_history_suffix
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
  rw [verifierExtension, proverExtension]
  have emptyTable : emptyOracle.table = [] := rfl
  rw [emptyTable, List.nil_append]
  simp only [List.map_append]
  rw [verifier_fresh_table_prefixes_eq_fresh_answer_prefixes,
    verifier_fresh_table_prefixes_eq_fresh_answer_prefixes,
    proverAnswers, verifierAnswers]

theorem exact_k12_raw_collision_implies_final_table_prefix_duplicate
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
    (collision : RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input)) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    ¬ (prefixes.verifier.finalState.table.map
      (fun entry => runtimeDigest256PrefixToMerkleDigest entry.output)).Nodup := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  dsimp only
  rcases collision with
    ⟨left, leftMember, right, rightMember, rawDistinct, truncatedEqual⟩
  rcases exact_k12_logged_raw_input_has_table_entry input left leftMember with
    ⟨leftRecord, leftEntry, leftRecordMember, leftRaw, leftFound,
      leftInput, leftOutput, leftTruncate⟩
  rcases exact_k12_logged_raw_input_has_table_entry input right rightMember with
    ⟨rightRecord, rightEntry, rightRecordMember, rightRaw, rightFound,
      rightInput, rightOutput, rightTruncate⟩
  have leftEntryMember : leftEntry ∈ prefixes.verifier.finalState.table := by
    unfold lookupEntry at leftFound
    exact List.mem_of_find?_eq_some leftFound
  have rightEntryMember : rightEntry ∈ prefixes.verifier.finalState.table := by
    unfold lookupEntry at rightFound
    exact List.mem_of_find?_eq_some rightFound
  have entryDistinct : leftEntry ≠ rightEntry := by
    intro entriesEqual
    apply rawDistinct
    rw [leftRaw, rightRaw, ← leftInput, ← rightInput, entriesEqual]
  have outputPrefixEqual :
      runtimeDigest256PrefixToMerkleDigest leftEntry.output =
        runtimeDigest256PrefixToMerkleDigest rightEntry.output :=
    leftTruncate.symm.trans (truncatedEqual.trans rightTruncate)
  intro tableNodup
  exact entryDistinct (nodup_map_forces_equal_of_members tableNodup
    leftEntryMember rightEntryMember outputPrefixEqual)

theorem exact_k12_raw_collision_implies_master_prefix_duplicate
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
    (collision : RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input)) :
    ¬ ((freshAnswerTapeToList sample.2).map
      runtimeDigest256PrefixToMerkleDigest).Nodup := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have tableDuplicate :=
    exact_k12_raw_collision_implies_final_table_prefix_duplicate input collision
  have tableExact := exact_k12_final_table_prefixes_eq_root_fresh_prefixes input
  have masterExact : freshAnswerTapeToList sample.2 =
      (prefixes.adversary.freshQueries.map Prod.snd ++
        prefixes.verifier.freshQueries.map Prod.snd) ++
          prefixes.verifier.remaining := by
    calc
      freshAnswerTapeToList sample.2 =
          prefixes.adversary.freshQueries.map Prod.snd ++
            prefixes.adversary.remaining :=
        prefixes.adversary.availableExact
      _ = prefixes.adversary.freshQueries.map Prod.snd ++
          (prefixes.verifier.freshQueries.map Prod.snd ++
            prefixes.verifier.remaining) :=
        congrArg
          (fun remaining =>
            prefixes.adversary.freshQueries.map Prod.snd ++ remaining)
          prefixes.verifier.availableExact
      _ = _ := by rw [List.append_assoc]
  intro masterNodup
  rw [masterExact, List.map_append] at masterNodup
  have rootNodup := (List.nodup_append.mp masterNodup).1
  apply tableDuplicate
  rw [tableExact]
  exact rootNodup

theorem exact_k12_raw_collision_implies_collision_scheduler_hit
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
    (collision : RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input)) :
    (projectedPrefixCollisionTree
      (exactCompilerTargetCaps parameters).length).everHits
        (projectedPrefixCollisionTape sample.2) := by
  exact projected_prefix_duplicate_implies_collision_tree_hit sample.2
    (exact_k12_raw_collision_implies_master_prefix_duplicate input collision)

/-- The executable K1.2 classifier's two remaining ROM failures are now both
events on the same exact compiler master tape: unresolved targets use the
budgeted verifier tree, and truncated collisions use the birthday tree. -/
theorem exact_prefix_k12_error_implies_counted_scheduler_events
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (transitionRoom : 2 ≤ transitionFuel)
    (openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input))
    (suppliedCovered : ExactPrefixK12SuppliedCoverage input)
    (error : ExactPrefixK12Error input) :
    ((exactK12BudgetedSchedulerTree configuration transitionFuel
        sample.1).toCausal).everHits (k12RuntimeTape sample.2) ∨
      (projectedPrefixCollisionTree
        (exactCompilerTargetCaps parameters).length).everHits
          (projectedPrefixCollisionTape sample.2) := by
  rcases exact_prefix_k12_error_yields_counted_rom_event openingsAccepted
      suppliedCovered error with lateHit | collision
  · exact Or.inl
      (exact_k12_late_target_hit_implies_budgeted_scheduler_hit
        transitionRoom input lateHit)
  · exact Or.inr
      (exact_k12_raw_collision_implies_collision_scheduler_hit input collision)

#print axioms projected_prefix_bad_implies_tree_hit
#print axioms projected_prefix_duplicate_implies_collision_tree_hit
#print axioms projected_prefix_collision_tree_probability_le_exact_count
#print axioms exact_k12_final_history_record_lookup
#print axioms exact_k12_logged_raw_input_has_table_entry
#print axioms exact_k12_final_table_prefixes_eq_root_fresh_prefixes
#print axioms exact_k12_raw_collision_implies_master_prefix_duplicate
#print axioms exact_k12_raw_collision_implies_collision_scheduler_hit
#print axioms exact_prefix_k12_error_implies_counted_scheduler_events

end

end AspisK1.V7Tag73K12CollisionSchedulerTree
