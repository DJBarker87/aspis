import AspisFormal.K1.V7Tag73FoldOuterSourceSeparation
import AspisFormal.K1.V7Tag73ExactFinal256DigestRootOrigin

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
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldOuterSourceSeparation
open AspisK1.V7Tag73FinalWorkDigestProbability
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
    ∃ (beforeRelation : EvalState) (foldDigest workAnswer : Digest256),
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
      FoldWork31Accepted workAnswer := by
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
  obtain ⟨afterFoldGrind, foldGrindRun, _suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨workAnswer, workLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFoldWork afterFoldGrind .fold
      (exactOperationalTape input).messages.foldGrinding foldGrindRun
  exact ⟨beforeRelation, beforeFoldWork.digest, workAnswer,
    relationLookup, workLookup, workAccepted⟩

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
  obtain ⟨beforeRelation, foldDigest, foldAnswer, relationLookup, foldLookup,
      foldAccepted⟩ := exact_operational_relation_zero_and_fold_work_lookups input
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

#print axioms exact_operational_relation_zero_and_fold_work_lookups
#print axioms exact_fold_digest_ne_final_digest
#print axioms exact_fold_work_input_ne_final_work_input

end

end AspisK1.V7Tag73FoldFinalWorkSourceSeparation
