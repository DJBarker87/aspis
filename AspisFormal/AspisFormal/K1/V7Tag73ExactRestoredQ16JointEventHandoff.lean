import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Events

/-!
# Exact restored K1.3 query event to the joint final-work/q16 trial

The restored root classifier now obtains its fixed-field view and selected q16
ledger from the checked source execution.  The causal DAG router separately
constructs one concrete final-work/q16 trial from that same accepted execution.
This file proves the deterministic handoff between those two results.

The conclusion is deliberately pointwise.  It identifies the exact successful
joint coordinate and its intrinsic bad set, but does not yet claim that this bad
set factors through the residual (non-final-work, non-q16) coordinates.  That
residual-invariance statement is the remaining probability-facing endpoint.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredQ16JointEventHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-- Transporting a selected-ledger certificate across equal environment
indices cannot change its non-dependent selected schedule. -/
theorem selected_q16_ledger_cast_environment_selected_schedule
    {environmentBefore environmentAfter : FutureFreeEnvironment}
    {snapshot : FutureFreeSnapshot}
    (environmentExact : environmentBefore = environmentAfter)
    (certificate :
      SelectedQ16LedgerCertificate environmentBefore snapshot) :
    (cast (show
        SelectedQ16LedgerCertificate environmentBefore snapshot =
          SelectedQ16LedgerCertificate environmentAfter snapshot by
          rw [environmentExact]) certificate
      ).selectedSchedule =
      certificate.selectedSchedule := by
  subst environmentAfter
  rfl

/-- Transporting a selected-ledger certificate across equal snapshot indices
cannot change its non-dependent selected schedule. -/
theorem selected_q16_ledger_cast_snapshot_selected_schedule
    {environment : FutureFreeEnvironment}
    {snapshotBefore snapshotAfter : FutureFreeSnapshot}
    (snapshotExact : snapshotBefore = snapshotAfter)
    (certificate :
      SelectedQ16LedgerCertificate environment snapshotBefore) :
    (cast (show
        SelectedQ16LedgerCertificate environment snapshotBefore =
          SelectedQ16LedgerCertificate environment snapshotAfter by
          rw [snapshotExact]) certificate
      ).selectedSchedule =
      certificate.selectedSchedule := by
  subst snapshotAfter
  rfl

/-- Any admissible restored K1.3 data witness on the literal root selects the
same q16 schedule as the checked operational tape.  This removes the last
`Classical.choice` ambiguity before the joint causal event handoff. -/
theorem exact_root_k13_data_selected_schedule_eq_operational
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
    (data : RestoredOperationalK13Data configuration.machine.environment
      input.package.root.fixedRoot.base.runtime.node) :
    data.selectedSchedule =
      (exactOperationalTape input).search.selectedSchedule := by
  have selectedUnique := selected_q16_ledger_certificate_selected_unique
    data.selectedLedgerCertificate
    (exact_fixed_package_root_selected_q16_ledger input.package)
  have packageSchedule :
      (exact_fixed_package_root_selected_q16_ledger
        input.package).selectedSchedule =
        (exactOperationalTape input).search.selectedSchedule := by
    let root := input.package.root.fixedRoot.base
    let construction := root.canonical.construction
    have finalStateExact : construction.complete.final =
        root.runtime.verifierFinalState :=
      root.actualPathAlignment.finalStateExact.symm.trans
        root.projected.finalStateExact
    have finalSnapshotExact : construction.complete.final.current =
        root.runtime.verifierFinalState.current :=
      congrArg (fun state => state.current) finalStateExact
    let environmentCertificate : SelectedQ16LedgerCertificate
        configuration.machine.environment construction.complete.final.current :=
      cast (congrArg (fun environment => SelectedQ16LedgerCertificate
        environment construction.complete.final.current)
        root.environmentExact) construction.selectedQ16
    let finalCertificate : SelectedQ16LedgerCertificate
        configuration.machine.environment
          root.runtime.verifierFinalState.current :=
      cast (congrArg (fun snapshot => SelectedQ16LedgerCertificate
        configuration.machine.environment snapshot) finalSnapshotExact)
        environmentCertificate
    have environmentSchedule :=
      selected_q16_ledger_cast_environment_selected_schedule
        root.environmentExact construction.selectedQ16
    have snapshotSchedule :=
      selected_q16_ledger_cast_snapshot_selected_schedule finalSnapshotExact
        environmentCertificate
    have castSchedule : finalCertificate.selectedSchedule =
        construction.selectedQ16.selectedSchedule :=
      snapshotSchedule.trans environmentSchedule
    dsimp only [finalCertificate, environmentCertificate] at castSchedule
    have rootSchedule : root.selectedQ16Ledger.selectedSchedule =
        construction.selectedQ16.selectedSchedule := by
      change finalCertificate.selectedSchedule =
        construction.selectedQ16.selectedSchedule
      exact castSchedule
    exact rootSchedule.trans construction.selectedQ16ScheduleExact
  exact selectedUnique.2.trans packageSchedule

/-- A restored-root K1.3 query failure, the selected final-work digest and the
entire q16 forest are realized by one concrete exposure trial.  In particular,
the exact 513-coordinate factor lies in the successful joint bad event for the
intrinsic consistency set exposed by the root classifier. -/
theorem exact_restored_root_query_failure_has_joint_trial_coordinate
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (member : sample ∈
      exactTag73RestoredOperationalRootK13QueryEvent transitionFuel
        configuration projection fixedInstance decoder) :
    ∃ (input : ExactK12OperationalInput transitionFuel configuration
          projection fixedInstance sample)
        (words : ExtractedWords)
        (bad : Finset (Fin 262144))
        (trial : ExactCompilerExposureTrial parameters),
      bad = restoredOperationalK13ConsistencySet decoder words
          ((exact_restored_operational_k13_provider input).data
            input.package.root.fixedRoot.base.runtime.node
            (exact_restoration_accumulator_contains_root input)
            (exact_restoration_accumulator_root_is_done input)) ∧
      bad.card ≤ 9557 ∧
      let router := exactCompilerExposureTrialDagRouter parameters
        transitionFuel trial
          (exactPlainRomCursor configuration sample.1).erase
      let coordinates := exactCompilerCausalFinalWorkQ16Coordinates parameters
        router sample.2
      coordinates ∈
        dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
          (fun _residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
            finalWorkQ16SuccessfulBadEvent bad) := by
  obtain ⟨input, words, intrinsicBad⟩ :=
    exact_restored_operational_root_query_event_exposes_intrinsic_bad_set
      member
  let node := input.package.root.fixedRoot.base.runtime.node
  let rootMember : node ∈ (exactRestorationAccumulator input).nodes :=
    exact_restoration_accumulator_contains_root input
  let rootDone : node.verifierFinalState.current.control = .done :=
    exact_restoration_accumulator_root_is_done input
  let data := (exact_restored_operational_k13_provider input).data node
    rootMember rootDone
  let bad := restoredOperationalK13ConsistencySet decoder words data
  have badFacts : bad.card ≤ 9557 ∧
      AllInBad bad data.selectedSchedule.positions := by
    simpa [bad] using intrinsicBad data
  have selectedScheduleExact : data.selectedSchedule =
      (exactOperationalTape input).search.selectedSchedule :=
    exact_root_k13_data_selected_schedule_eq_operational input data
  have allBad : AllInBad bad
      (semanticScheduleOfOperational
        (exactOperationalTape input).search.selectedSchedule) := by
    change AllInBad bad
      (exactOperationalTape input).search.selectedSchedule.positions
    rw [← selectedScheduleExact]
    exact badFacts.2
  obtain ⟨_digest, _workAnswer, _base, trial, workAccepted, _baseExact,
      _workLabeled, workCoordinate, realized⟩ :=
    exact_compiler_accepted_dag_q16_operational_realization transitionRoom
      programmedCover input (frontierExact input)
  refine ⟨input, words, bad, trial, rfl, badFacts.1, ?_⟩
  let router := exactCompilerExposureTrialDagRouter parameters transitionFuel
    trial (exactPlainRomCursor configuration sample.1).erase
  let coordinates := exactCompilerCausalFinalWorkQ16Coordinates parameters
    router sample.2
  have q16Success : q16DigestForestSucceeds coordinates.2.2 :=
    operational_realization_implies_q16_digest_forest_succeeds realized
  have q16Bad : successfulQ16DigestForestEquiv
        ⟨coordinates.2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad :=
    operational_all_in_bad_implies_successful_coordinate_bad realized bad
      allBad
  refine ⟨q16Success, ?_⟩
  change FinalWork34Accepted coordinates.2.1 ∧
    successfulQ16DigestForestEquiv ⟨coordinates.2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad
  exact ⟨workCoordinate ▸ workAccepted, q16Bad⟩

#print axioms exact_root_k13_data_selected_schedule_eq_operational
#print axioms exact_restored_root_query_failure_has_joint_trial_coordinate

end

end AspisK1.V7Tag73ExactRestoredQ16JointEventHandoff
