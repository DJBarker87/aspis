import AspisFormal.K1.V7Tag73FoldOuterSourceSeparation
import AspisFormal.K1.V7Tag73ExactFinal256DigestRootOrigin
import AspisFormal.K1.V7Tag73ExactFinalWorkEarliestExposure
import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff

/-!
# Exact separation of the fold-work and final-work source coordinates

The two deployed grinding inputs have the same 41-byte grammar, so raw input
shape cannot distinguish them.  Their state prefixes are nevertheless outputs
of two different accepted transcript absorptions: relation round zero before
fold work, and `final256` before final work.  The inputs to those absorptions
have different literal lengths.  Exact root target cleanliness makes the list
of non-padding outputs injective, hence their output digests -- and therefore
the two grinding inputs -- are distinct.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73FoldFinalWorkSourceSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFinalWorkEarliestExposure
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldOuterSourceSeparation
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Accepted post-C2 events ending immediately before the relation-round-zero
absorption that produces the fold-work state digest. -/
def prefixAfterC2BeforeFoldDigest (messages : Messages) : List MachineEvent :=
  [.absorb .constraintRegistry,
   .absorb .helperSum,
   challengeEvent messages .theta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    challengeEvent messages (.zerocheckPoint coordinate)) ++
  [challengeEvent messages .mu,
   .absorb (.initialMaskClaim messages.initialClaim),
   challengeEvent messages .eta] ++
  semanticEvents messages ++
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected),
   challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages

theorem prefix_before_fold_work_relation_split (messages : Messages) :
    prefixAfterC2BeforeFoldWork messages =
      prefixAfterC2BeforeFoldDigest messages ++
        [.absorb (.relationRound 0 (messages.relationSent 0))] := by
  simp [prefixAfterC2BeforeFoldWork, prefixAfterC2BeforeFoldDigest]

private theorem run_machine_events_append_iff
    (table : FixedOracleTable) (first second : List MachineEvent)
    (state final : EvalState) :
    runMachineEvents table (first ++ second) state = some final ↔
      ∃ middle,
        runMachineEvents table first state = some middle ∧
        runMachineEvents table second middle = some final := by
  induction first generalizing state with
  | nil => simp [runMachineEvents]
  | cons event rest ih =>
      simp only [List.cons_append, runMachineEvents]
      constructor
      · intro run
        obtain ⟨next, eventRun, tailRun⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨middle, prefixRun, suffixRun⟩ := (ih next).mp tailRun
        exact ⟨middle, Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, prefixRun⟩, suffixRun⟩
      · rintro ⟨middle, prefixRun, suffixRun⟩
        obtain ⟨next, eventRun, tailRun⟩ :=
          Option.bind_eq_some_iff.mp prefixRun
        exact Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, (ih next).mpr ⟨middle, tailRun, suffixRun⟩⟩

/-- The accepted fold-work state digest is literally the answer of the
preceding relation-round-zero absorption. -/
theorem exact_operational_relation_zero_and_fold_work_lookups
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
    ∃ (beforeRelation : EvalState)
        (foldDigest workAnswer boundaryAnswer : Digest256),
      tableLookup (exactOperationalTable input)
          (bytes beforeRelation.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
                ((exactOperationalTape input).messages.relationSent 0)).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).data) =
        some foldDigest ∧
      tableLookup (exactOperationalTable input)
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        some workAnswer ∧
      FoldWork31Accepted workAnswer ∧
      tableLookup (exactOperationalTable input)
          (bytes foldDigest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        some boundaryAnswer := by
  have strict := input.package.root.fixedRoot.base.strictRefinement
  have refined := (checked_refinement_is_well_formed
    (exactOperationalTable input) exactDeterministicDecoders
    (exactOperationalTape input) (exactOperationalRawTrace input) strict).1
  rw [refine] at refined
  obtain ⟨prefixState, prefixRun, _refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  rw [runPrefix] at prefixRun
  obtain ⟨beforeC1, _beforeC1Run, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c1Pair, _c1SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c1Pair with ⟨_c1Salt, _withC1SaltQuery⟩
  obtain ⟨afterC1, _c1AbsorbRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨afterPhaseChallenges, _phaseRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c2Pair, _c2SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c2Pair with ⟨_c2Salt, _withC2SaltQuery⟩
  obtain ⟨afterC2, _c2AbsorbRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rw [prefix_after_c2_fold_work_split] at remainingRun
  obtain ⟨beforeFoldWork, beforeFoldRun, suffixRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFoldWork (exactOperationalTape input).messages)
      (prefixAfterC2FromFoldWork (exactOperationalTape input).messages)
      afterC2 prefixState).mp remainingRun
  rw [prefix_before_fold_work_relation_split] at beforeFoldRun
  obtain ⟨beforeRelation, beforeRelationRun, relationRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFoldDigest (exactOperationalTape input).messages)
      [.absorb (.relationRound 0
        ((exactOperationalTape input).messages.relationSent 0))]
      afterC2 beforeFoldWork).mp beforeFoldRun
  simp only [runMachineEvents] at relationRun
  obtain ⟨afterRelation, absorbRun, relationDone⟩ :=
    Option.bind_eq_some_iff.mp relationRun
  have afterRelationExact : afterRelation = beforeFoldWork := by
    simpa [runMachineEvents] using Option.some.inj relationDone
  subst afterRelation
  have relationLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) beforeRelation beforeFoldWork
      (.relationRound 0 ((exactOperationalTape input).messages.relationSent 0))
      absorbRun
  simp only [prefixAfterC2FromFoldWork, runMachineEvents] at suffixRun
  obtain ⟨afterFoldGrind, foldGrindRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterFoldCheck, foldCheckRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterFoldCheckExact : afterFoldCheck = afterFoldGrind := by
    simpa [runMachineEvent] using (Option.some.inj foldCheckRun).symm
  subst afterFoldCheck
  obtain ⟨afterFoldNonce, foldNonceRun, _suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨workAnswer, workLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFoldWork afterFoldGrind .fold
      (exactOperationalTape input).messages.foldGrinding foldGrindRun
  have stableDigest : afterFoldGrind.digest = beforeFoldWork.digest :=
    grinding_choice_does_not_advance (exactOperationalTable input)
      beforeFoldWork afterFoldGrind .fold
      (exactOperationalTape input).messages.foldGrinding foldGrindRun
  have boundaryLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) afterFoldGrind afterFoldNonce
    (.foldNonce
      (exactOperationalTape input).messages.foldGrinding.selected) foldNonceRun
  rw [stableDigest] at boundaryLookup
  exact ⟨beforeRelation, beforeFoldWork.digest, workAnswer,
    afterFoldNonce.digest, relationLookup, workLookup, workAccepted, by
      simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
        AspisK1.V7Tag73TranscriptSchedule.Payload.data] using boundaryLookup⟩

@[simp] theorem relation_zero_absorb_input_length
    (digest : Digest256) (relation : Fin 6 → Qm31Bytes) :
    (bytes digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
          relation).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
        relation).data).length = 131 := by
  simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data, bytes_length,
    encodeBlocks_length]

@[simp] theorem final256_absorb_input_length
    (digest : Digest256) (values : Fin 256 → Qm31Bytes) :
    (bytes digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256 values).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256 values).data).length =
        4130 := by
  simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data, bytes_length,
    encodeBlocks_length]

/-- Exact target cleanliness separates the state output of relation round zero
from the later state output of `final256`. -/
theorem exact_fold_digest_ne_final_digest
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
    ∃ foldDigest finalDigest foldAnswer finalAnswer : Digest256,
      tableLookup (exactOperationalTable input)
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        some foldAnswer ∧
      FoldWork31Accepted foldAnswer ∧
      tableLookup (exactOperationalTable input)
          (bytes finalDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        some finalAnswer ∧
      FinalWork34Accepted finalAnswer ∧
      foldDigest ≠ finalDigest := by
  obtain ⟨beforeRelation, foldDigest, foldAnswer, _boundaryAnswer,
      relationLookup, foldLookup, foldAccepted, _boundaryLookup⟩ :=
    exact_operational_relation_zero_and_fold_work_lookups input
  obtain ⟨beforeFinal256, finalDigest, finalAnswer, _q16Base, final256Lookup,
      finalLookup, finalAccepted, _absorbLookup, _baseExact, _prefixRun⟩ :=
    exact_operational_final256_and_work_lookups input
  refine ⟨foldDigest, finalDigest, foldAnswer, finalAnswer, foldLookup,
    foldAccepted, finalLookup, finalAccepted, ?_⟩
  intro digestEqual
  obtain ⟨relationActor, relationMember⟩ :=
    exact_final_table_lookup_has_root_record input _ foldDigest relationLookup
  obtain ⟨final256Actor, final256Member⟩ :=
    exact_final_table_lookup_has_root_record input _ finalDigest final256Lookup
  have recordExact :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      relationMember final256Member digestEqual
  have inputExact :
      bytes beforeRelation.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)).data =
        bytes beforeFinal256.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape input).messages.finalValues).data := by
    injection recordExact
  have lengthExact := congrArg List.length inputExact
  have impossible : (131 : Nat) = 4130 := by
    simpa only [relation_zero_absorb_input_length,
      final256_absorb_input_length] using lengthExact
  omega

/-- Consequently the two selected deployed grinding inputs are distinct even
though both use the same 41-byte grammar. -/
theorem exact_fold_work_input_ne_final_work_input
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
    ∃ foldDigest finalDigest foldAnswer finalAnswer : Digest256,
      tableLookup (exactOperationalTable input)
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        some foldAnswer ∧
      FoldWork31Accepted foldAnswer ∧
      tableLookup (exactOperationalTable input)
          (bytes finalDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        some finalAnswer ∧
      FinalWork34Accepted finalAnswer ∧
      bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected ≠
        bytes finalDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected := by
  obtain ⟨foldDigest, finalDigest, foldAnswer, finalAnswer, foldLookup,
      foldAccepted, finalLookup, finalAccepted, digestDifferent⟩ :=
    exact_fold_digest_ne_final_digest input
  refine ⟨foldDigest, finalDigest, foldAnswer, finalAnswer, foldLookup,
    foldAccepted, finalLookup, finalAccepted, ?_⟩
  intro inputEqual
  apply digestDifferent
  have prefixEqual := congrArg (List.take 32) inputEqual
  have foldTake : List.take 32
      (bytes foldDigest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      bytes foldDigest := by
    simpa [bytes_length] using
      (List.take_append_length
        (l₁ := bytes foldDigest)
        (l₂ := [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected))
  have finalTake : List.take 32
      (bytes finalDigest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      bytes finalDigest := by
    simpa [bytes_length] using
      (List.take_append_length
        (l₁ := bytes finalDigest)
        (l₂ := [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected))
  have bytesEqual : bytes foldDigest = bytes finalDigest := by
    rw [foldTake, finalTake] at prefixEqual
    exact prefixEqual
  exact List.ofFn_injective bytesEqual

/-- The accepted execution supplies one fold trial and the exact earliest
final-work/q16 trial at different exposure indices.  This is the source-level
separation required by the complete 518-slot controller. -/
theorem exact_fold_and_final_have_distinct_exposure_trials
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
    ∃ (foldDigest finalDigest foldAnswer finalAnswer q16Base : Digest256)
        (foldTrial finalTrial : ExactCompilerExposureTrial parameters),
      FoldWork31Accepted foldAnswer ∧
      FinalWork34Accepted finalAnswer ∧
      foldTrial.val ≠ finalTrial.val ∧
      EarliestExactFinalWorkPairOccurrence
        (literalFinalWorkKey finalDigest
          (exactOperationalTape input).messages.finalGrinding.selected)
        finalAnswer q16Base
        (runExactPlainRom transitionFuel configuration sample).trace
        finalTrial.val := by
  obtain ⟨beforeRelation, foldDigest, foldAnswer, _boundaryAnswer,
      relationLookup, foldLookup, foldAccepted, _boundaryLookup⟩ :=
    exact_operational_relation_zero_and_fold_work_lookups input
  obtain ⟨beforeFinal256, finalDigest, finalAnswer, q16Base, final256Lookup,
      finalLookup, finalAccepted, absorbLookup, _baseExact, _prefixRun⟩ :=
    exact_operational_final256_and_work_lookups input
  obtain ⟨relationActor, relationMember⟩ :=
    exact_final_table_lookup_has_root_record input _ foldDigest relationLookup
  obtain ⟨final256Actor, final256Member⟩ :=
    exact_final_table_lookup_has_root_record input _ finalDigest final256Lookup
  have digestDifferent : foldDigest ≠ finalDigest := by
    intro digestEqual
    have recordExact :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
        relationMember final256Member digestEqual
    have inputExact :
        bytes beforeRelation.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
                ((exactOperationalTape input).messages.relationSent 0)).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).data =
          bytes beforeFinal256.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape input).messages.finalValues).data := by
      injection recordExact
    have lengthExact := congrArg List.length inputExact
    have impossible : (131 : Nat) = 4130 := by
      simpa only [relation_zero_absorb_input_length,
        final256_absorb_input_length] using lengthExact
    omega
  have workInputsDifferent :
      bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected ≠
        bytes finalDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected := by
    intro equal
    apply digestDifferent
    have prefixEqual := congrArg (List.take 32) equal
    have foldTake : List.take 32
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        bytes foldDigest := by
      simpa [bytes_length] using
        (List.take_append_length
          (l₁ := bytes foldDigest)
          (l₂ := [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected))
    have finalTake : List.take 32
        (bytes finalDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        bytes finalDigest := by
      simpa [bytes_length] using
        (List.take_append_length
          (l₁ := bytes finalDigest)
          (l₂ := [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected))
    rw [foldTake, finalTake] at prefixEqual
    exact List.ofFn_injective prefixEqual
  obtain ⟨foldActor, foldMember⟩ :=
    exact_final_table_lookup_has_root_record input _ foldAnswer foldLookup
  obtain ⟨foldPrior, foldLater, foldDecomposition⟩ :=
    (List.mem_iff_append).mp foldMember
  have foldPriorLtRoot : foldPrior.length <
      (exactFixedRootRecords input.package.root).length := by
    rw [foldDecomposition]
    simp
  have rootLengthLeFull :
      (exactFixedRootRecords input.package.root).length ≤
        (runExactPlainRom transitionFuel configuration sample).trace.length := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp
  have foldPriorLtCap : foldPrior.length <
      unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    exact foldPriorLtRoot.trans_le rootLengthLeFull
  let foldTrial : ExactCompilerExposureTrial parameters :=
    ⟨foldPrior.length, foldPriorLtCap⟩
  let key := literalFinalWorkKey finalDigest
    (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨finalActor, finalRootMember⟩ :=
    exact_final_table_lookup_has_root_record input key.workInput finalAnswer
      (by simpa [key] using finalLookup)
  have finalFullMember :
      (.machineFresh finalActor key.workInput finalAnswer :
          UnifiedExposureRecord) ∈
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    exact List.mem_append_left _ finalRootMember
  obtain ⟨finalIndex, finalEarliest⟩ :=
    earliest_exact_pair_exists_of_member key finalAnswer q16Base
      (runExactPlainRom transitionFuel configuration sample).trace
      (.machineFresh finalActor key.workInput finalAnswer) finalFullMember
      (Or.inl ⟨rfl, rfl⟩)
  have finalIndexLtCap : finalIndex < unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    exact earliest_exact_pair_index_lt_length finalEarliest
  let finalTrial : ExactCompilerExposureTrial parameters :=
    ⟨finalIndex, finalIndexLtCap⟩
  refine ⟨foldDigest, finalDigest, foldAnswer, finalAnswer, q16Base,
    foldTrial, finalTrial, foldAccepted, finalAccepted, ?_, finalEarliest⟩
  obtain ⟨finalPrior, selected, finalLater, fullFinalDecomposition,
      finalPriorLength, selectedPair⟩ :=
    earliest_exact_pair_trace_decomposition finalEarliest
  have fullFoldDecomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        foldPrior ++
          (.machineFresh foldActor
            (bytes foldDigest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected)
            foldAnswer : UnifiedExposureRecord) ::
          (foldLater ++
            (exactFixedComputedClientTailRun transitionFuel configuration sample
              input.package.root).trace) := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    rw [foldDecomposition]
    simp only [List.cons_append, List.append_assoc]
  intro trialEqual
  have prefixLengthEqual : foldPrior.length = finalPrior.length := by
    change foldPrior.length = finalIndex at trialEqual
    exact trialEqual.trans finalPriorLength.symm
  have selectedExact := selected_record_eq_of_equal_prefix_length
    fullFoldDecomposition fullFinalDecomposition prefixLengthEqual
  obtain ⟨selectedActor, selectedWork | selectedAbsorb⟩ :=
    exact_final_work_pair_record_cases key finalAnswer q16Base selected
      selectedPair
  · rw [selectedWork] at selectedExact
    have inputExact :
        bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          key.workInput := by
      injection selectedExact
    exact workInputsDifferent (by simpa [key] using inputExact)
  · rw [selectedAbsorb] at selectedExact
    have inputExact :
        bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          key.absorbInput := by
      injection selectedExact
    have lengthExact := congrArg List.length inputExact
    simp [key, RawFinalWorkKey.absorbInput, literalFinalWorkKey,
      bytes_length] at lengthExact

/-- The relation-round-produced fold state differs from any digest carrying
the exact accepted `final256` origin predicate. -/
theorem exact_relation_fold_digest_ne_operational_prefinal
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
    (beforeRelation : EvalState) (foldDigest finalDigest : Digest256)
    (relationLookup :
      tableLookup (exactOperationalTable input)
          (bytes beforeRelation.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
                ((exactOperationalTape input).messages.relationSent 0)).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).data) =
        some foldDigest)
    (prefinal : ExactOperationalPrefinalDigest input finalDigest) :
    foldDigest ≠ finalDigest := by
  obtain ⟨beforeFinal256, final256Lookup⟩ := prefinal
  obtain ⟨relationActor, relationMember⟩ :=
    exact_final_table_lookup_has_root_record input _ foldDigest relationLookup
  obtain ⟨final256Actor, final256Member⟩ :=
    exact_final_table_lookup_has_root_record input _ finalDigest final256Lookup
  intro digestEqual
  have recordExact :=
    List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      relationMember final256Member digestEqual
  have inputExact :
      bytes beforeRelation.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)).data =
        bytes beforeFinal256.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape input).messages.finalValues).data := by
    injection recordExact
  have lengthExact := congrArg List.length inputExact
  have impossible : (131 : Nat) = 4130 := by
    simpa only [relation_zero_absorb_input_length,
      final256_absorb_input_length] using lengthExact
  omega

/-- Every proof-relevant actual K1.3 final-work trial has a separately
positioned accepted fold-work trial in the same clean root. -/
theorem exact_actual_k13_trial_has_distinct_fold_trial
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input finalTrial) :
    ∃ (foldTrial : ExactCompilerExposureTrial parameters)
        (foldAnswer : Digest256),
      FoldWork31Accepted foldAnswer ∧ foldTrial.val ≠ finalTrial.val := by
  let finalDigest := Classical.choose actual
  let afterDigest := Classical.choose_spec actual
  let finalAnswer := Classical.choose afterDigest
  let afterAnswer := Classical.choose_spec afterDigest
  let base := Classical.choose afterAnswer
  let afterBase := Classical.choose_spec afterAnswer
  have prefinal : ExactOperationalPrefinalDigest input finalDigest :=
    afterBase.2.1
  let pairLabeled := afterBase.2.2.2.1
  obtain ⟨beforeRelation, foldDigest, foldAnswer, _boundaryAnswer,
      relationLookup, foldLookup, foldAccepted, _boundaryLookup⟩ :=
    exact_operational_relation_zero_and_fold_work_lookups input
  have digestDifferent : foldDigest ≠ finalDigest :=
    exact_relation_fold_digest_ne_operational_prefinal input beforeRelation
      foldDigest finalDigest relationLookup prefinal
  have workInputsDifferent :
      bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected ≠
        (literalFinalWorkKey finalDigest
          (exactOperationalTape input).messages.finalGrinding.selected).workInput := by
    intro equal
    apply digestDifferent
    have prefixEqual := congrArg (List.take 32) equal
    have foldTake : List.take 32
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        bytes foldDigest := by
      simpa [bytes_length] using
        (List.take_append_length
          (l₁ := bytes foldDigest)
          (l₂ := [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected))
    have finalTake : List.take 32
        (literalFinalWorkKey finalDigest
          (exactOperationalTape input).messages.finalGrinding.selected).workInput =
        bytes finalDigest := by
      simp [RawFinalWorkKey.workInput, literalFinalWorkKey, bytes_length]
    rw [foldTake, finalTake] at prefixEqual
    exact List.ofFn_injective prefixEqual
  obtain ⟨foldActor, foldMember⟩ :=
    exact_final_table_lookup_has_root_record input _ foldAnswer foldLookup
  obtain ⟨foldPrior, foldLater, foldDecomposition⟩ :=
    (List.mem_iff_append).mp foldMember
  have foldPriorLtRoot : foldPrior.length <
      (exactFixedRootRecords input.package.root).length := by
    rw [foldDecomposition]
    simp
  have foldPriorLtCap : foldPrior.length <
      unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    apply foldPriorLtRoot.trans_le
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp
  let foldTrial : ExactCompilerExposureTrial parameters :=
    ⟨foldPrior.length, foldPriorLtCap⟩
  refine ⟨foldTrial, foldAnswer, foldAccepted, ?_⟩
  intro trialEqual
  rcases pairLabeled with
      ⟨finalPrior, middle, later, workActor, absorbActor, recordsExact,
        finalTrialExact⟩ |
      ⟨finalPrior, middle, later, workActor, absorbActor, recordsExact,
        finalTrialExact⟩
  · have prefixLengthEqual : foldPrior.length = finalPrior.length := by
      change foldPrior.length = finalTrial.val at trialEqual
      exact trialEqual.trans finalTrialExact
    have firstDecomposition :
        exactFixedRootRecords input.package.root =
          finalPrior ++
            (.machineFresh workActor
              (literalFinalWorkKey finalDigest
                (exactOperationalTape input).messages.finalGrinding.selected).workInput
              finalAnswer : UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh absorbActor
                (literalFinalWorkKey finalDigest
                  (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
                base : UnifiedExposureRecord) :: later) := by
      simpa only [List.cons_append, List.append_assoc] using recordsExact
    have recordExact := selected_record_eq_of_equal_prefix_length
      foldDecomposition firstDecomposition prefixLengthEqual
    have inputExact :
        bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          (literalFinalWorkKey finalDigest
            (exactOperationalTape input).messages.finalGrinding.selected).workInput := by
      injection recordExact
    exact workInputsDifferent inputExact
  · have prefixLengthEqual : foldPrior.length = finalPrior.length := by
      change foldPrior.length = finalTrial.val at trialEqual
      exact trialEqual.trans finalTrialExact
    have firstDecomposition :
        exactFixedRootRecords input.package.root =
          finalPrior ++
            (.machineFresh absorbActor
              (literalFinalWorkKey finalDigest
                (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
              base : UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh workActor
                (literalFinalWorkKey finalDigest
                  (exactOperationalTape input).messages.finalGrinding.selected).workInput
                finalAnswer : UnifiedExposureRecord) :: later) := by
      simpa only [List.cons_append, List.append_assoc] using recordsExact
    have recordExact := selected_record_eq_of_equal_prefix_length
      foldDecomposition firstDecomposition prefixLengthEqual
    have inputExact :
        bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          (literalFinalWorkKey finalDigest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput := by
      injection recordExact
    have lengthExact := congrArg List.length inputExact
    have impossible : (41 : Nat) = 42 := by
      simpa [RawFinalWorkKey.absorbInput, literalFinalWorkKey, bytes_length]
        using lengthExact
    omega

#print axioms exact_operational_relation_zero_and_fold_work_lookups
#print axioms exact_fold_digest_ne_final_digest
#print axioms exact_fold_work_input_ne_final_work_input
#print axioms exact_fold_and_final_have_distinct_exposure_trials
#print axioms exact_relation_fold_digest_ne_operational_prefinal
#print axioms exact_actual_k13_trial_has_distinct_fold_trial

end

end AspisK1.V7Tag73FoldFinalWorkSourceSeparation
