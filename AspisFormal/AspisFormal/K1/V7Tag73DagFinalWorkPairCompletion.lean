import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion

/-!
# Final-work pair completion for the causal-DAG controller

The older branch controller already proves the exact accepted final-work/q16
base pair.  Its branch cell is intentionally not reused for q16 routing: an
adversary may pipeline an advance before the sibling output.  This file proves
that the old controller and the causal-DAG controller nevertheless have the
same small final-work core at every literal record prefix.  The accepted pair
can therefore be reused solely to establish the anchor, work flag, and q16
base, while all q16 producer routing remains native to the causal DAG.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73DagFinalWorkPairCompletion

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The common state needed before q16 classification.  Branch tracking and
the DAG producer inventory are deliberately erased. -/
inductive FinalWorkQ16Core where
  | inactive
  | tracked (key : RawFinalWorkKey) (workSeen : Bool)
      (q16Base : Option Digest256)
  deriving DecidableEq

def candidateMemoryCore : FinalWorkQ16CandidateMemory → FinalWorkQ16Core
  | .inactive => .inactive
  | .tracked key workSeen q16Base _branches =>
      .tracked key workSeen q16Base

def dagMemoryCore (memory : FinalWorkQ16DagMemory) : FinalWorkQ16Core :=
  match memory.anchor with
  | .inactive => .inactive
  | .tracked key workSeen => .tracked key workSeen memory.q16Base

/-- One answer preserves equality of the two erased cores when both indexed
states share the literal pre-answer cursor and exposure ordinal. -/
theorem candidate_dag_after_core_eq
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (candidateState : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory)
    (dagState : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256)
    (exposureExact : candidateState.exposureIndex = dagState.exposureIndex)
    (cursorExact : candidateState.cursor = dagState.cursor)
    (coreExact : candidateMemoryCore candidateState.memory =
      dagMemoryCore dagState.memory) :
    candidateMemoryCore
        (candidateAfterMemory transitionFuel anchor candidateState answer) =
      dagMemoryCore
        (dagCandidateAfterMemory transitionFuel anchor dagState answer) := by
  rcases candidateState with ⟨candidateIndex, candidateCursor,
    candidateMemory⟩
  rcases dagState with ⟨dagIndex, dagCursor, dagMemory⟩
  simp only at exposureExact cursorExact
  subst dagIndex
  subst dagCursor
  rcases dagMemory with ⟨dagAnchor, dagBase, dagProducers, dagUsed⟩
  unfold candidateAfterMemory dagCandidateAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel candidateCursor with
  | none =>
      simpa [inputExact, dagMemoryCore] using coreExact
  | some input =>
      simp only [inputExact]
      cases candidateMemory with
      | inactive =>
          cases dagAnchor with
          | inactive =>
              by_cases atAnchor : candidateIndex = anchor
              · simp only [candidateMemoryCore, dagMemoryCore,
                  dagMemoryAfterInput, dagCoreMemoryAfterInput, atAnchor,
                  if_pos]
                cases work : rawFinalWorkKeyOfWorkInput? input with
                | some key => simp [work, candidateMemoryCore, dagMemoryCore]
                | none =>
                    cases absorb : rawFinalWorkKeyOfAbsorbInput? input with
                    | some key =>
                        simp [work, absorb, candidateMemoryCore, dagMemoryCore]
                    | none =>
                        simp [work, absorb, candidateMemoryCore, dagMemoryCore]
              · simp [candidateMemoryCore, dagMemoryCore,
                  dagMemoryAfterInput, dagCoreMemoryAfterInput, atAnchor]
          | tracked key workSeen =>
              simp [candidateMemoryCore, dagMemoryCore] at coreExact
      | tracked key workSeen base branches =>
          cases dagAnchor with
          | inactive =>
              simp [candidateMemoryCore, dagMemoryCore] at coreExact
          | tracked dagKey dagWorkSeen =>
              simp only [candidateMemoryCore, dagMemoryCore] at coreExact
              injection coreExact with keyExact workExact baseExact
              subst dagKey
              subst dagWorkSeen
              subst dagBase
              cases base with
              | none =>
                  by_cases absorb : input = key.absorbInput <;>
                    simp [candidateMemoryCore, dagMemoryCore,
                      dagMemoryAfterInput, dagCoreMemoryAfterInput, absorb]
              | some base =>
                  simp [candidateMemoryCore, dagMemoryCore,
                    dagMemoryAfterInput, dagCoreMemoryAfterInput]

/-- The two controllers retain equal final-work cores over any common literal
answer list. -/
theorem candidate_dag_replay_core_eq
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (candidateState : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory)
      (dagState : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      candidateState.exposureIndex = dagState.exposureIndex →
      candidateState.cursor = dagState.cursor →
      candidateMemoryCore candidateState.memory =
        dagMemoryCore dagState.memory →
      candidateMemoryCore
          (indexedStateAfterRecords transitionFuel
            (finalWorkQ16CandidateController globalOracleCalls transitionFuel
              anchor) records candidateState).memory =
        dagMemoryCore
          (indexedStateAfterRecords transitionFuel
            (finalWorkQ16DagController globalOracleCalls transitionFuel anchor)
            records dagState).memory := by
  intro records
  induction records with
  | nil =>
      intro candidateState dagState _exposureExact _cursorExact coreExact
      simpa only [indexed_state_after_records_nil] using coreExact
  | cons record records ih =>
      intro candidateState dagState exposureExact cursorExact coreExact
      let candidateController := finalWorkQ16CandidateController
        globalOracleCalls transitionFuel anchor
      let dagController := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchor
      let nextCandidate := candidateController.afterAnswer transitionFuel
        candidateState record.answer
      let nextDag := dagController.afterAnswer transitionFuel dagState
        record.answer
      have nextExposure : nextCandidate.exposureIndex = nextDag.exposureIndex := by
        simp [nextCandidate, nextDag, candidateController, dagController,
          IndexedUnifiedExposureController.afterAnswer, exposureExact]
      have nextCursor : nextCandidate.cursor = nextDag.cursor := by
        simp [nextCandidate, nextDag, candidateController, dagController,
          IndexedUnifiedExposureController.afterAnswer, cursorExact]
      have nextCore : candidateMemoryCore nextCandidate.memory =
          dagMemoryCore nextDag.memory := by
        simpa [nextCandidate, nextDag, candidateController, dagController,
          finalWorkQ16CandidateController, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          candidate_dag_after_core_eq transitionFuel anchor candidateState
            dagState record.answer exposureExact cursorExact coreExact
      rw [indexed_state_after_records_cons,
        indexed_state_after_records_cons]
      exact ih nextCandidate nextDag nextExposure nextCursor nextCore

/-- The canonical initial states agree in cursor, ordinal, and erased core. -/
theorem exact_pair_and_dag_initial_core_agree
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
    (exactPairControllerInitialState input).exposureIndex =
        (exactDagCandidateInitialState input).exposureIndex ∧
      (exactPairControllerInitialState input).cursor =
        (exactDagCandidateInitialState input).cursor ∧
      candidateMemoryCore (exactPairControllerInitialState input).memory =
        dagMemoryCore (exactDagCandidateInitialState input).memory := by
  simp [exactPairControllerInitialState, exactDagCandidateInitialState,
    inactiveCandidateMemory, inactiveDagMemory, candidateMemoryCore,
    dagMemoryCore]

/-- Accepted final work reaches a concrete causal-DAG state with the exact
deployed q16 base.  No branch-cell conclusion from the sequential controller
is imported. -/
theorem exact_compiler_accepted_final_work_dag_pair_completes
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
    ∃ (digest workAnswer q16Base : Digest256)
        (trial : ExactCompilerExposureTrial parameters)
        (completedPrefix remaining : List UnifiedExposureRecord),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      exactFixedRootRecords input.package.root =
        completedPrefix ++ remaining ∧
      trial.val < completedPrefix.length ∧
      let reached := indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) completedPrefix
        (exactDagCandidateInitialState input)
      reached.memory.anchor =
          .tracked
            (literalFinalWorkKey digest
              (exactOperationalTape input).messages.finalGrinding.selected)
            true ∧
        reached.memory.q16Base = some q16Base := by
  obtain ⟨digest, workAnswer, q16Base, trial, completedPrefix, remaining,
    branches, workAccepted, q16BaseExact, rootSplit, trialBeforeEnd,
    candidateMemoryExact⟩ :=
      exact_compiler_accepted_final_work_pair_controller_completes input
  have initialAgree := exact_pair_and_dag_initial_core_agree input
  have replayCore := candidate_dag_replay_core_eq transitionFuel trial.val
    completedPrefix (exactPairControllerInitialState input)
      (exactDagCandidateInitialState input) initialAgree.1 initialAgree.2.1
      initialAgree.2.2
  rw [candidateMemoryExact] at replayCore
  simp only [candidateMemoryCore] at replayCore
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) completedPrefix
    (exactDagCandidateInitialState input)
  have dagCoreExact : dagMemoryCore reached.memory =
      .tracked
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected)
        true (some q16Base) := by
    simpa only [reached, exactDagTrialController] using replayCore.symm
  rcases reachedMemoryExact : reached.memory with
    ⟨anchor, base, producers, usedSlots⟩
  cases anchor with
  | inactive =>
      simp [dagMemoryCore, reachedMemoryExact] at dagCoreExact
  | tracked key workSeen =>
      simp only [dagMemoryCore, reachedMemoryExact,
        FinalWorkQ16Core.tracked.injEq] at dagCoreExact
      rcases dagCoreExact with ⟨keyExact, workSeenExact, baseExact⟩
      refine ⟨digest, workAnswer, q16Base, trial, completedPrefix, remaining,
        workAccepted, q16BaseExact, rootSplit, trialBeforeEnd, ?_⟩
      dsimp only
      constructor
      · simpa [reached, reachedMemoryExact] using
          And.intro keyExact workSeenExact
      · simpa [reached, reachedMemoryExact] using baseExact

#print axioms candidate_dag_after_core_eq
#print axioms candidate_dag_replay_core_eq
#print axioms exact_pair_and_dag_initial_core_agree
#print axioms exact_compiler_accepted_final_work_dag_pair_completes

end

end AspisK1.V7Tag73DagFinalWorkPairCompletion
