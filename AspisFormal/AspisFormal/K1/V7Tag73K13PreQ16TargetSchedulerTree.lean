import AspisFormal.K1.V7Tag73K13PreQ16TargetInventory

/-!
# Causal scheduler tree for pre-q16 Merkle targets

This tree follows the literal unified Tag-73 exposure cursor.  Before each
fresh 256-bit answer it derives at most four 208-bit Merkle candidates from
each earlier SHA input, then lifts that inventory to complete SHA outputs.
The current answer and all future answers are structurally unavailable when
the target set is chosen.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16TargetSchedulerTree

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetInventory
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def preQ16MerkleTargetCapsFrom : Nat → Nat → List Nat
  | _, 0 => []
  | step, remaining + 1 =>
      (step * 4) * 2 ^ 48 ::
        preQ16MerkleTargetCapsFrom (step + 1) remaining

@[simp] theorem pre_q16_merkle_target_caps_from_length
    (step remaining : Nat) :
    (preQ16MerkleTargetCapsFrom step remaining).length = remaining := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining ih =>
      simp [preQ16MerkleTargetCapsFrom, ih]

theorem pre_q16_merkle_target_caps_from_sum
    (step remaining : Nat) :
    (preQ16MerkleTargetCapsFrom step remaining).sum =
      (List.range' step remaining).sum * 4 * 2 ^ 48 := by
  induction remaining generalizing step with
  | zero => simp [preQ16MerkleTargetCapsFrom]
  | succ remaining ih =>
      simp only [preQ16MerkleTargetCapsFrom, List.sum_cons,
        List.range'_succ]
      rw [ih]
      ring

def preQ16FullMerkleTargets (records : List UnifiedExposureRecord) :
    Finset Digest256 :=
  deployedPrefixTargetPreimage
    (prefixMerkleCandidateSet (exposurePrefixRawQueries records))

theorem preQ16FullMerkleTargets_card_le
    (records : List UnifiedExposureRecord) :
    (preQ16FullMerkleTargets records).card ≤
      (records.length * 4) * 2 ^ 48 := by
  unfold preQ16FullMerkleTargets
  refine (prefixMerkleCandidatePreimage_card_le
    (exposurePrefixRawQueries records)).trans ?_
  have rawLength :
      (exposurePrefixRawQueries records).length ≤ records.length := by
    unfold exposurePrefixRawQueries
    rw [List.length_map]
    exact List.length_filterMap_le _ _
  exact Nat.mul_le_mul_right (2 ^ 48) (Nat.mul_le_mul_right 4 rawLength)

theorem preQ16FullMerkleTargets_card_le_step
    (step : Nat) (records : List UnifiedExposureRecord)
    (recordsBound : records.length ≤ step) :
    (preQ16FullMerkleTargets records).card ≤ (step * 4) * 2 ^ 48 := by
  exact (preQ16FullMerkleTargets_card_le records).trans
    (Nat.mul_le_mul_right (2 ^ 48)
      (Nat.mul_le_mul_right 4 recordsBound))

/-- One literal step of the same exposure transition used by the trace and
the causal target tree. -/
def nextUnifiedExposure
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) (answer : Digest256) :
    UnifiedExposureRecord × UnifiedExposureCursor globalOracleCalls :=
  match seekUnifiedExposure transitionFuel cursor with
  | .halted | .transitionLimit =>
      (.padding answer, .halted)
  | .machineFresh limits limitBound actor state input nextProgram
      remainingFuel coherent _totalRoom _freshRoom _missing onReturned =>
      (.machineFresh actor input answer,
        .machine limits limitBound actor
          (freshQueryState actor state input answer) (nextProgram answer)
          remainingFuel
          (fresh_query_state_preserves_history_total_coherent actor state input
            answer coherent)
          onReturned)
  | .forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      (.forkOutput frozenHistory outputInput advanceInput template answer,
        .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          answer next)
  | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
      forkOutput next =>
      let scheduled : ScheduledForkCoins :=
        { frozenHistory := frozenHistory
          outputInput := outputInput
          advanceInput := advanceInput
          template := template
          forkOutput := forkOutput
          forkAdvance := answer }
      (.forkAdvance scheduled, next scheduled.configuration)

@[simp] theorem nextUnifiedExposure_record_answer
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) (answer : Digest256) :
    (nextUnifiedExposure transitionFuel cursor answer).1.answer = answer := by
  unfold nextUnifiedExposure
  cases request : seekUnifiedExposure transitionFuel cursor <;> rfl

theorem run_unified_exposure_trace_succ_eq_next
    {globalOracleCalls remaining : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 (remaining + 1)) :
    runUnifiedExposureTrace transitionFuel (remaining + 1) cursor tape =
      let next := nextUnifiedExposure transitionFuel cursor tape.1
      next.1 :: runUnifiedExposureTrace transitionFuel remaining next.2
        tape.2 := by
  unfold nextUnifiedExposure
  simp only [runUnifiedExposureTrace]
  cases request : seekUnifiedExposure transitionFuel cursor <;> rfl

/-- The causal tree mirrors `runUnifiedExposureTrace`.  Its explicit record
prefix is extended only after the current answer has been supplied. -/
noncomputable def preQ16MerkleTargetTreeFrom
    (globalOracleCalls transitionFuel : Nat) :
    (step remaining : Nat) →
      (records : List UnifiedExposureRecord) → records.length ≤ step →
      UnifiedExposureCursor globalOracleCalls →
      CausalTargetTree Digest256
        (preQ16MerkleTargetCapsFrom step remaining)
  | _step, 0, _records, _recordsBound, _cursor => .done
  | step, remaining + 1, records, recordsBound, cursor =>
      .step (preQ16FullMerkleTargets records)
        (preQ16FullMerkleTargets_card_le_step step records recordsBound)
        fun answer =>
          let next := nextUnifiedExposure transitionFuel cursor answer
          preQ16MerkleTargetTreeFrom globalOracleCalls transitionFuel
            (step + 1) remaining (records ++ [next.1])
            (by simpa using Nat.succ_le_succ recordsBound) next.2

noncomputable def preQ16MerkleTargetTree
    (globalOracleCalls exposures transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    CausalTargetTree Digest256
      (preQ16MerkleTargetCapsFrom 0 exposures) :=
  preQ16MerkleTargetTreeFrom globalOracleCalls transitionFuel 0 exposures []
    (by simp) cursor

def preQ16MerkleTargetTapeFrom {Output : Type} (step : Nat) :
    ∀ {remaining : Nat}, FreshAnswerTape Output remaining →
      FreshAnswerTape Output
        (preQ16MerkleTargetCapsFrom step remaining).length
  | 0, tape => tape
  | remaining + 1, tape =>
      (tape.1, preQ16MerkleTargetTapeFrom (step + 1) tape.2)

@[simp] theorem pre_q16_merkle_target_tape_from_to_list
    {Output : Type} (step : Nat) {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    freshAnswerTapeToList (preQ16MerkleTargetTapeFrom step tape) =
      freshAnswerTapeToList tape := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining ih =>
      change tape.1 :: freshAnswerTapeToList
          (preQ16MerkleTargetTapeFrom (step + 1) tape.2) =
        tape.1 :: freshAnswerTapeToList tape.2
      rw [ih]

/-- A later trace record whose answer hits the inventory derived from all
earlier records is an actual hit in the causal tree on the same master tape. -/
theorem later_record_target_implies_tree_hit_from
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    ∀ (step remaining : Nat) (records : List UnifiedExposureRecord)
      (recordsBound : records.length ≤ step)
      (cursor : UnifiedExposureCursor globalOracleCalls)
      (tape : FreshAnswerTape Digest256 remaining)
      (before : List UnifiedExposureRecord) (hit : UnifiedExposureRecord)
      (after : List UnifiedExposureRecord),
      runUnifiedExposureTrace transitionFuel remaining cursor tape =
          before ++ hit :: after →
      hit.answer ∈ preQ16FullMerkleTargets (records ++ before) →
      (preQ16MerkleTargetTreeFrom globalOracleCalls transitionFuel step
        remaining records recordsBound cursor).everHits
          (preQ16MerkleTargetTapeFrom step tape) := by
  intro step remaining
  induction remaining generalizing step with
  | zero =>
      intro records recordsBound cursor tape before hit after traceExact
        hitTarget
      simp [runUnifiedExposureTrace] at traceExact
  | succ remaining ih =>
      intro records recordsBound cursor tape before hit after traceExact
        hitTarget
      rw [run_unified_exposure_trace_succ_eq_next] at traceExact
      let next := nextUnifiedExposure transitionFuel cursor tape.1
      change tape.1 ∈ preQ16FullMerkleTargets records ∨
        (preQ16MerkleTargetTreeFrom globalOracleCalls transitionFuel
          (step + 1) remaining (records ++ [next.1])
          (by simpa using Nat.succ_le_succ recordsBound) next.2).everHits
            (preQ16MerkleTargetTapeFrom (step + 1) tape.2)
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at traceExact
          have recordExact : next.1 = hit := traceExact.1
          apply Or.inl
          subst hit
          simpa [next, nextUnifiedExposure_record_answer] using hitTarget
      | cons first rest =>
          simp only [List.cons_append, List.cons.injEq] at traceExact
          have recordExact : next.1 = first := traceExact.1
          have tailExact := traceExact.2
          subst first
          apply Or.inr
          apply ih (step + 1) (records ++ [next.1])
            (by simpa using Nat.succ_le_succ recordsBound) next.2 tape.2 rest
            hit after tailExact
          simpa [List.append_assoc] using hitTarget

theorem later_record_target_implies_tree_hit
    {globalOracleCalls exposures : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 exposures)
    (before : List UnifiedExposureRecord) (hit : UnifiedExposureRecord)
    (after : List UnifiedExposureRecord)
    (traceExact : runUnifiedExposureTrace transitionFuel exposures cursor tape =
      before ++ hit :: after)
    (hitTarget : hit.answer ∈ preQ16FullMerkleTargets before) :
    (preQ16MerkleTargetTree globalOracleCalls exposures transitionFuel cursor).everHits
      (preQ16MerkleTargetTapeFrom 0 tape) := by
  exact later_record_target_implies_tree_hit_from transitionFuel 0 exposures []
    (by simp) cursor tape before hit after traceExact (by simpa using hitTarget)

theorem answer_mem_preQ16FullMerkleTargets_of_prefix
    (records : List UnifiedExposureRecord) (answer : Digest256)
    (target : AspisPool.V7MerkleQueryGrammar.Digest208)
    (targetMem : target ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (answerPrefix : runtimeDigest256PrefixToMerkleDigest answer = target) :
    answer ∈ preQ16FullMerkleTargets records := by
  unfold preQ16FullMerkleTargets deployedPrefixTargetPreimage
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simpa [answerPrefix] using targetMem⟩

theorem pre_q16_merkle_target_tree_uniform_probability_le
    (globalOracleCalls exposures transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    (uniformDigestFreshTape
        (preQ16MerkleTargetCapsFrom 0 exposures).length).toOuterMeasure
      (causalHitEvent
        (preQ16MerkleTargetTree globalOracleCalls exposures transitionFuel
          cursor)) ≤
      ((((preQ16MerkleTargetCapsFrom 0 exposures).sum) *
          (2 ^ 256) ^ (exposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ exposures) := by
  simpa only [pre_q16_merkle_target_caps_from_length] using
    uniform_digest_causal_hit_probability_le_exact_count
      (preQ16MerkleTargetTree globalOracleCalls exposures transitionFuel cursor)

#print axioms pre_q16_merkle_target_caps_from_length
#print axioms pre_q16_merkle_target_caps_from_sum
#print axioms preQ16FullMerkleTargets_card_le
#print axioms preQ16FullMerkleTargets_card_le_step
#print axioms pre_q16_merkle_target_tape_from_to_list
#print axioms later_record_target_implies_tree_hit_from
#print axioms later_record_target_implies_tree_hit
#print axioms answer_mem_preQ16FullMerkleTargets_of_prefix
#print axioms pre_q16_merkle_target_tree_uniform_probability_le

end

end AspisK1.V7Tag73K13PreQ16TargetSchedulerTree
