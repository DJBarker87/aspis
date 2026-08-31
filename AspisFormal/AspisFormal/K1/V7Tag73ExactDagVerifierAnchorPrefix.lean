import AspisFormal.K1.V7Tag73ExactDagPreAnchorResidualPrefix
import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier

/-!
# Verifier-owned q16 anchors retain the completed prover prefix

The deployed root is chronological: the adversary's complete fresh-query
segment precedes the verifier's fresh-query segment.  A selected final-work or
nonce-absorb coordinate whose first fresh owner is the verifier therefore has
the whole completed prover prefix strictly before it.  Combined with the
residual-coordinate router, this gives the precise source fact available
without making any claim about an adversary-first anchor.

The adversary-first case remains deliberately outside this lemma.  It needs a
cache-aware counterfactual/restart argument, not a false freshness assertion.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagVerifierAnchorPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagPreAnchorResidualPrefix
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Actor-tagged projected fresh records reflect membership of their literal
source pair.  The forward direction is used to recover a verifier-prefix
decomposition from a selected verifier-owned root record. -/
theorem machine_fresh_mem_projected_records_iff
    (actor : QueryActor) (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256) :
    (.machineFresh actor input answer : UnifiedExposureRecord) ∈
        projectedMachineFreshRecords actor queries ↔
      (input, answer) ∈ queries := by
  induction queries with
  | nil => simp [projectedMachineFreshRecords]
  | cons query rest ih =>
      rcases query with ⟨headInput, headAnswer⟩
      simp [projectedMachineFreshRecords, ih]

/-- A verifier-owned root coordinate has a literal prefix consisting of the
entire completed adversary segment followed by a strict verifier segment. -/
theorem exact_dag_verifier_root_record_has_completed_prover_prefix
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
    (prior later : List UnifiedExposureRecord)
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later) :
    ∃ verifierPrior verifierLater,
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ (target, answer) :: verifierLater ∧
      prior =
        projectedMachineFreshRecords .adversary
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier verifierPrior := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  let selected : UnifiedExposureRecord := .machineFresh .verifier target answer
  have selectedMember : selected ∈ exactFixedRootRecords input.package.root := by
    rw [rootExact]
    simp [selected]
  have selectedVerifier : selected ∈
      projectedMachineFreshRecords .verifier prefixes.verifier.freshQueries := by
    unfold exactFixedRootRecords fullProjectedRootRecords at selectedMember
    rw [List.mem_append] at selectedMember
    rcases selectedMember with adversary | verifier
    · obtain ⟨sourceInput, sourceAnswer, recordExact⟩ :=
        only_machine_fresh_actor_projected_records .adversary
          prefixes.adversary.freshQueries selected adversary
      simp [selected] at recordExact
    · exact verifier
  have selectedSource : (target, answer) ∈ prefixes.verifier.freshQueries := by
    simpa [selected] using
      (machine_fresh_mem_projected_records_iff .verifier
        prefixes.verifier.freshQueries target answer).mp selectedVerifier
  obtain ⟨verifierPrior, verifierLater, verifierExact⟩ :=
    (List.mem_iff_append).mp selectedSource
  have verifierExact' :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ (target, answer) :: verifierLater := by
    simpa [prefixes] using verifierExact
  have canonicalRoot : exactFixedRootRecords input.package.root =
      (projectedMachineFreshRecords .adversary
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier verifierPrior) ++
        selected :: projectedMachineFreshRecords .verifier verifierLater := by
    unfold exactFixedRootRecords fullProjectedRootRecords
    rw [verifierExact', projected_machine_fresh_records_append]
    simp [selected, projectedMachineFreshRecords, List.append_assoc]
  have prefixExact := mapped_nodup_selected_prefix_eq causalInput?
    (exactFixedRootRecords input.package.root)
    (projectedMachineFreshRecords .adversary
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
      projectedMachineFreshRecords .verifier verifierPrior)
    (projectedMachineFreshRecords .verifier verifierLater)
    prior later selected selected (exact_root_record_causal_inputs_nodup input)
    canonicalRoot rootExact rfl
  exact ⟨verifierPrior, verifierLater, verifierExact, prefixExact.symm⟩

/-- On a verifier-owned selected final-work/q16 anchor, equal residual
coordinates force a replay tape to preserve the full completed-prover answer
prefix.  This is intentionally only a tape-prefix result: turning it into an
accepted counterfactual source execution still requires the cache-aware
adversary causality bridge. -/
theorem exact_dag_residual_coordinate_forces_completed_prover_tape_prefix
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    ∃ verifierPrior verifierLater rightRemaining,
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ (target, answer) :: verifierLater ∧
      freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right)) =
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries.map
          Prod.snd ++ verifierPrior.map Prod.snd ++ rightRemaining := by
  obtain ⟨verifierPrior, verifierLater, verifierExact, priorExact⟩ :=
    exact_dag_verifier_root_record_has_completed_prover_prefix input prior later
      target answer rootExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix input trial
      prior ((.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later) (by simpa only [List.cons_append] using rootExact) trialExact
        programmedCover right coordinateExact
  have priorAnswers : prior.map UnifiedExposureRecord.answer =
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries.map
          Prod.snd ++ verifierPrior.map Prod.snd := by
    rw [priorExact, List.map_append,
      projected_machine_fresh_record_answers,
      projected_machine_fresh_record_answers]
  refine ⟨verifierPrior, verifierLater, rightRemaining, verifierExact, ?_⟩
  rw [priorAnswers] at rightPrefix
  exact rightPrefix

/-- The verifier-owned case already gives an executable replay of the exact
completed prover on every equal-residual tape.  This says only that rerunning
the deterministic prover from the retained answer prefix returns the original
raw adversary value and final oracle; it does not yet identify that rerun with
an independently accepted counterfactual full source execution. -/
theorem exact_dag_residual_coordinate_replays_completed_prover_at_verifier_anchor
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    k12ProverRunFromAnswerPrefix configuration.machine sample.1
        (freshAnswerTapeToList
          (finalWorkQ16NamedSlotInputTape
            (exactCompilerFinalWorkQ16InputTape parameters right))) =
      { halt := .returned
          input.package.root.full.projection.rootPrefixes.adversaryValue
        oracle := input.package.root.full.projection.rootPrefixes.adversary.finalState
        steps := input.package.root.full.projection.rootPrefixes.adversary.steps } := by
  obtain ⟨verifierPrior, _verifierLater, rightRemaining, _verifierExact,
      rightPrefix⟩ :=
    exact_dag_residual_coordinate_forces_completed_prover_tape_prefix input
      trial prior later target answer rootExact trialExact programmedCover right
        coordinateExact
  have replay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine sample.1 (freshAnswerTapeToList sample.2)
    input.package.root.fixedRoot.base.runtime
    input.package.root.full.projection.rootPrefixes
    (verifierPrior.map Prod.snd ++ rightRemaining)
  rw [rightPrefix]
  simpa only [List.append_assoc] using replay

/-- If the right-hand tape is itself a genuine exact source input with the
same hidden prover tape, the verifier-owned residual-prefix replay identifies
its prover result and prover-final oracle with the left source input.  It
does not identify the later verifier-final table: q16 answers after the
anchor may legitimately differ. -/
theorem exact_dag_residual_coordinate_preserves_prover_runtime_at_verifier_anchor
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (sample.1, right))
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    (exactK12Runtime rightInput).adversaryValue =
        (exactK12Runtime input).adversaryValue ∧
      (exactK12Runtime rightInput).proverFinalOracle =
        (exactK12Runtime input).proverFinalOracle := by
  have leftReplay :=
    exact_dag_residual_coordinate_replays_completed_prover_at_verifier_anchor
      input trial prior later target answer rootExact trialExact programmedCover
        right coordinateExact
  rw [final_work_q16_named_slot_tape_preserves_master_list] at leftReplay
  let rightPrefixes :=
    rightInput.package.root.full.projection.rootPrefixes
  have rightReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine sample.1 (freshAnswerTapeToList right)
    rightInput.package.root.fixedRoot.base.runtime rightPrefixes
    rightPrefixes.adversary.remaining
  have rightAvailable : freshAnswerTapeToList right =
      rightPrefixes.adversary.freshQueries.map Prod.snd ++
        rightPrefixes.adversary.remaining := by
    simpa [rightPrefixes] using rightPrefixes.adversary.availableExact
  rw [← rightAvailable] at rightReplay
  have rawRunExact := leftReplay.symm.trans rightReplay
  have adversaryExact :
      input.package.root.full.projection.rootPrefixes.adversaryValue =
        rightPrefixes.adversaryValue := by
    have haltExact := congrArg (fun run => run.halt) rawRunExact
    simpa only [MachineHalt.returned.injEq] using haltExact
  have proverExact :
      input.package.root.full.projection.rootPrefixes.adversary.finalState =
        rightPrefixes.adversary.finalState := by
    exact congrArg (fun run => run.oracle) rawRunExact
  have leftAdversaryRuntime : (exactK12Runtime input).adversaryValue =
      input.package.root.full.projection.rootPrefixes.adversaryValue := by
    have runtimeExact := congrArg (fun runtime => runtime.adversaryValue)
      input.package.root.full.projection.rootPrefixes.runtimeExact
    simpa [exactK12Runtime, operationalRootRuntime] using runtimeExact
  have rightAdversaryRuntime : (exactK12Runtime rightInput).adversaryValue =
      rightPrefixes.adversaryValue := by
    have runtimeExact := congrArg (fun runtime => runtime.adversaryValue)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      runtimeExact
  have leftProverRuntime : (exactK12Runtime input).proverFinalOracle =
      input.package.root.full.projection.rootPrefixes.adversary.finalState := by
    have runtimeExact := congrArg (fun runtime => runtime.proverFinalOracle)
      input.package.root.full.projection.rootPrefixes.runtimeExact
    simpa [exactK12Runtime, operationalRootRuntime] using runtimeExact
  have rightProverRuntime : (exactK12Runtime rightInput).proverFinalOracle =
      rightPrefixes.adversary.finalState := by
    have runtimeExact := congrArg (fun runtime => runtime.proverFinalOracle)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      runtimeExact
  constructor
  · exact rightAdversaryRuntime.trans adversaryExact.symm |>.trans
      leftAdversaryRuntime.symm
  · exact rightProverRuntime.trans proverExact.symm |>.trans
      leftProverRuntime.symm

/-- The parsed proof is a direct projection of the completed prover return,
so the verifier-owned residual prefix also fixes the complete parsed proof
without assumptions about the later verifier table. -/
theorem exact_dag_residual_coordinate_preserves_parsed_proof_at_verifier_anchor
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (sample.1, right))
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    exactK13ParsedProof rightInput = exactK13ParsedProof input := by
  obtain ⟨adversaryExact, _proverExact⟩ :=
    exact_dag_residual_coordinate_preserves_prover_runtime_at_verifier_anchor
      input trial prior later target answer rootExact trialExact programmedCover
        right rightInput coordinateExact
  simpa only [exactK13ParsedProof] using congrArg
    (fun value => value.1.publicProof.proof.rawProof) adversaryExact

#print axioms machine_fresh_mem_projected_records_iff
#print axioms exact_dag_verifier_root_record_has_completed_prover_prefix
#print axioms exact_dag_residual_coordinate_forces_completed_prover_tape_prefix
#print axioms exact_dag_residual_coordinate_replays_completed_prover_at_verifier_anchor
#print axioms exact_dag_residual_coordinate_preserves_prover_runtime_at_verifier_anchor
#print axioms exact_dag_residual_coordinate_preserves_parsed_proof_at_verifier_anchor

end

end AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
