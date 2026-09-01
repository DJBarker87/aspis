import AspisFormal.K1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
import AspisFormal.K1.V7Tag73FinalWorkEarliestExposure

/-!
# Exact fold-work exposure trial

The literal accepted fold-work lookup is turned into its actor-tagged root
decomposition and therefore into a concrete `Fin F` compiler trial.  The
trial index is exactly the number of root exposures preceding that first
creation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldWorkExposureTrial

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem exact_compiler_accepted_fold_work_has_exposure_trial
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
    ∃ (digest workAnswer : Digest256)
        (trial : ExactCompilerExposureTrial parameters)
        (before later : List UnifiedExposureRecord) (actor : QueryActor),
      FoldWork31Accepted workAnswer ∧
      exactFixedRootRecords input.package.root =
        before ++
          (.machineFresh actor
            (bytes digest ++ [domGrind] ++
              bytes
                (exactOperationalTape input).messages.foldGrinding.selected)
            workAnswer : UnifiedExposureRecord) :: later ∧
      trial.val = before.length := by
  obtain ⟨digest, workAnswer, workLookup, accepted⟩ :=
    exact_operational_fold_work_lookup input
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input _ workAnswer workLookup
  obtain ⟨before, later, decomposition⟩ :=
    (List.mem_iff_append).mp rootMember
  have beforeRoot : before.length <
      (exactFixedRootRecords input.package.root).length := by
    rw [decomposition]
    simp
  have rootFull : (exactFixedRootRecords input.package.root).length ≤
      (runExactPlainRom transitionFuel configuration sample).trace.length := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp
  have beforeCap : before.length < unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    exact beforeRoot.trans_le rootFull
  let trial : ExactCompilerExposureTrial parameters :=
    ⟨before.length, beforeCap⟩
  exact ⟨digest, workAnswer, trial, before, later, actor, accepted,
    decomposition, rfl⟩

end


#print axioms exact_compiler_accepted_fold_work_has_exposure_trial

end AspisK1.V7Tag73ExactFoldWorkExposureTrial
