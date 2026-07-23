import ComponentBDeterministicPipelineCapstone
import GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone
import RuntimeWeightAccumulatorFoldLevel3
import RuntimeReleasedTraceFamiliesCurrentJoin
import Tag67WorkVerifierClosure

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace FormalClosureStream1

open AspisCircleRectangularMasking
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness
open AspisV5NonceWorkAuthentication

/-- The maintained wire byte, kept local so the Tag-67 premise can retain its
source statement `(3 : Byte) :: List.ofFn (nonceLEBytes nonce)` verbatim. -/
abbrev Byte := AspisFormal.V5ExactRuntimeWireRepair.Byte

/-- The accepted source-extracted Component-A matrix execution and the
maintained concrete GoodA endpoint, stated together without an encoder-model
premise. -/
def ComponentAActualMatchesMaintained : Prop :=
  (∃ finalA finalB,
    v5_cu_probe.good_gate_probe.good_matrices
        GoodMatricesCurrent.ProbeGeneratedConcrete.kernel
        GoodMatricesCurrent.ProbeGeneratedConcrete.point =
      .ok (finalA, finalB) ∧
    GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput.aMatrixToExact finalA =
      printedTerminalMatrixFin) ∧
  ConcreteProbeTerminalMatrixEquality ∧
  GoodA concreteSchedule

theorem component_a_actual_matches_maintained :
    ComponentAActualMatchesMaintained := by
  exact GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone.generated_and_maintained_goodA_capstone

/-- The executable part of the current deterministic Component-B theorem:
the sampled mask reaches the generated evaluator and C2 layout, while the
returned terminal is exactly the maintained ten-round relation terminal. -/
def ComponentBActualMatchesMaintained
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (componentB : ComponentBRelationClaimsLayoutInstantiation.Lane)
    (hcopy componentC :
      alloc.vec.Vec ComponentBGenerated.aspis_core.field.QM31) : Prop :=
  ∃ mixed terminal covector copied assembled,
    ComponentBGenerated.v5_sumcheck_mask.v5_sumcheck_mask_mixing_evaluate_correspondence
          mask (ComponentBMaintainedTerminalBridge.roundUsize selectedRound)
          totalClaim eta real point = .ok (.some mixed, terminal) ∧
    ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
        mixed = .ok totalClaim ∧
    ComponentBRealEvaluatorProof.generatedQm31ToExact terminal =
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (AspisV5SumcheckCommitment.tenRoundTerminal
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationPoint point)) ∧
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
        point = .ok covector ∧
    ComponentBC2SlotGenerated.component_b_message_values componentB =
      .ok copied ∧
    ComponentBC2SlotGenerated.assemble_v5_c2_messages
        hcopy copied componentC = .ok assembled ∧
    assembled = Array.make 3#usize [hcopy, copied, componentC]

theorem component_b_actual_matches_maintained
    {S : Type} (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource))
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real)
    (pads : Array ComponentBGenerated.aspis_core.field.QM31 255#usize)
    (pivotPad : ComponentBGenerated.aspis_core.field.QM31)
    (componentB : ComponentBRelationClaimsLayoutInstantiation.Lane)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = .ok (.Ok componentB))
    (hcopy componentC :
      alloc.vec.Vec ComponentBGenerated.aspis_core.field.QM31) :
    ComponentBActualMatchesMaintained mask selectedRound totalClaim eta real
      point componentB hcopy componentC := by
  obtain ⟨mixed, terminal, covector, copied, assembled,
      helperRun, boundary, _terminalCanonical, terminalRelation,
      covectorRun, copiedRun, assembledRun, assembledExact, _⟩ :=
    ComponentBDeterministicPipelineCapstone.sampled_mask_to_c2_relation_and_tenRoundTerminal
        sourceInst nextWordTotal source finalSource mask sampleRun selectedRound
        totalClaim eta real point hpoint htotal heta hreal pads pivotPad
        componentB encodeRun hcopy componentC
  exact ⟨mixed, terminal, covector, copied, assembled, helperRun, boundary,
    terminalRelation, covectorRun, copiedRun, assembledRun, assembledExact⟩

namespace Tag67

open AspisTag67WorkVerifierClosure

/-- The exact conclusion of the accepted Tag-67 wire/verifier closure.  The
only abstract correspondence input to the theorem below is the concrete
transcript hash-application equality; parser, projection, digest-predicate,
and six-step correspondence assumptions do not appear. -/
def ActualWireAndVerifierClosure
    {State Challenge : Type*}
    (shape : AspisFormal.V5ExactRuntimeWireRepair.RuntimeShape)
    (wire : AspisFormal.V5ExactRuntimeWireRepair.RuntimeExactWire shape)
    (hfit : AspisFormal.V5ExactRuntimeWireRepair.runtimeRepairedProofBytes
      shape ≤ Std.Usize.max)
    (fold0 fold1 fold2 fold3 batch final : Std.U64) (selected : Std.U8)
    (actualTranscriptGrindingDigest :
      State → Nonce64 → AspisTag67WorkVerifierClosure.GrindingDigest)
    (rustHash : State → List Byte →
      AspisTag67WorkVerifierClosure.GrindingDigest)
    (absorb : State → Nat → List Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State) : Prop :=
  ∃ view : WorkWireView,
    view = AspisTag67WorkWireMaintained.decodedWorkWireView
      fold0 fold1 fold2 fold3 batch final ∧
    AspisV5NonceWorkAuthentication.projectWorkWire shape wire =
      AspisV5NonceWorkAuthentication.canonicalWorkWire view ∧
    aspis_verifier.v5_cu_probe.project_v5_work_wire
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit) =
        ok {
          fold_nonces := Array.make 4#usize [fold0, fold1, fold2, fold3]
          batch_nonce := batch
          final_nonce := final
          query_selector := selected
        } ∧
    ExactRustWorkVerifierCorrespondence
      (AspisTag67WorkVerifierClosure.extractedSixStepAcceptance
        actualTranscriptGrindingDigest stateBefore view)
      rustHash AspisTag67WorkVerifierClosure.digestHasLeadingZeroBitsNat
      (AspisTag67WorkVerifierClosure.actualWorkFunctions
        actualTranscriptGrindingDigest absorb executeNext)
      (AspisTag67SixActualSteps.positionedInputsFromActualOperations
        (AspisTag67WorkVerifierClosure.actualWorkFunctions
          actualTranscriptGrindingDigest absorb executeNext)
        stateBefore view.nonces)

theorem actual_wire_and_verifier_closure
    {State Challenge : Type*}
    (shape : AspisFormal.V5ExactRuntimeWireRepair.RuntimeShape)
    (wire : AspisFormal.V5ExactRuntimeWireRepair.RuntimeExactWire shape)
    (hfit : AspisFormal.V5ExactRuntimeWireRepair.runtimeRepairedProofBytes
      shape ≤ Std.Usize.max)
    (fold0 fold1 fold2 fold3 batch final : Std.U64) (selected : Std.U8)
    (hmagic : aspis_verifier.v5_cu_probe.v5_work_wire_magic_is_valid
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit) =
        ok true)
    (hfold0 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11048#usize = ok fold0)
    (hfold1 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11056#usize = ok fold1)
    (hfold2 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11064#usize = ok fold2)
    (hfold3 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11072#usize = ok fold3)
    (hbatch : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11080#usize = ok batch)
    (hfinal : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19127#usize = ok final)
    (hselector : Slice.index_usize
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19135#usize = ok selected)
    (hzero : aspis_verifier.v5_cu_probe.v5_relation_final_zero_tail_is_valid
      (AspisTag67WorkWireMaintained.serializedRelationFinalSlice
        shape wire hfit) = ok true)
    (actualTranscriptGrindingDigest :
      State → Nonce64 → AspisTag67WorkVerifierClosure.GrindingDigest)
    (rustHash : State → List Byte →
      AspisTag67WorkVerifierClosure.GrindingDigest)
    (absorb : State → Nat → List Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State)
    (hHashApplication : ∀ state nonce,
      actualTranscriptGrindingDigest state nonce =
        rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))) :
    ActualWireAndVerifierClosure shape wire hfit fold0 fold1 fold2 fold3 batch
      final selected actualTranscriptGrindingDigest rustHash absorb executeNext
      stateBefore := by
  apply AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure
    shape wire hfit fold0 fold1 fold2 fold3 batch final selected hmagic hfold0
    hfold1 hfold2 hfold3 hbatch hfinal hselector hzero
    actualTranscriptGrindingDigest rustHash absorb executeNext stateBefore
  simpa [grindingHashPayload] using hHashApplication

end Tag67

namespace OperationalFold

open ComponentCRuntimeCanonicalGenerated
open ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorFoldLevel3

local instance : Inhabited RawQM31 :=
  ⟨ComponentCRuntimeCanonicalGenerated.aspis_core.field.QM31.ZERO⟩

/-- Exact operational statement proved for the current five-component
relation accumulator.  It records source component order, alpha forwarding,
prepared-cache construction, primitive dispatch, and the `log_len - 2`
transition.  It deliberately does not claim the still-missing
`weight_at = capturedFoldAt` semantic equation. -/
def RealFiveComponentFoldExact : Prop :=
  ∀ (currentLogLen : Std.U32)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared)
    (scale0 scale1 scale2 scale0Out scale1Out scale2Out : RawQM31)
    (point0 point1 point2 point0Out point1Out point2Out :
      alloc.vec.Vec RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupMasks groupMasksOut : alloc.vec.Vec Std.U16)
    (firstAlpha firstAlphaOut : Option RawQM31)
    (groupValues groupValuesOut dense denseOut : alloc.vec.Vec RawQM31),
    ComponentCRuntimeCanonicalGenerated.aspis_core.field.QM31.square alpha =
        ok alpha2 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.field.PreparedQm31Multiplier.new
        alpha = ok preparedAlpha →
    ComponentCRuntimeCanonicalGenerated.aspis_core.field.PreparedQm31Multiplier.new
        alpha2 = ok preparedAlpha2 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.field.PreparedQm31Multiplier.mul
        preparedAlpha alpha2 = ok alpha3 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
        scale0 point0 alpha alpha2 alpha3 = ok (scale0Out, point0Out) →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
        scale1 point1 alpha alpha2 alpha3 = ok (scale1Out, point1Out) →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
        scale2 point2 alpha alpha2 alpha3 = ok (scale2Out, point2Out) →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_grouped64_binary_deferred_arity4
        rowGroups groupMasks firstAlpha groupValues currentLogLen alpha alpha2
          alpha3 =
      ok (rowGroups, groupMasksOut, firstAlphaOut, groupValuesOut) →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
        dense alpha alpha2 alpha3 = ok denseOut →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        { log_len := currentLogLen
          components := realRelationComponents
            (.Multilinear scale0 point0)
            (.Multilinear scale1 point1)
            (.Multilinear scale2 point2)
            (.Grouped64x16BinaryDeferred rowGroups groupMasks firstAlpha
              groupValues)
            (.Dense dense) }
        alpha =
      ok {
        log_len := Std.U32.wrapping_sub currentLogLen 2#u32
        components := realRelationComponents
          (.Multilinear scale0Out point0Out)
          (.Multilinear scale1Out point1Out)
          (.Multilinear scale2Out point2Out)
          (.Grouped64x16BinaryDeferred rowGroups groupMasksOut firstAlphaOut
            groupValuesOut)
          (.Dense denseOut) }

theorem real_five_component_fold_exact : RealFiveComponentFoldExact := by
  intro currentLogLen alpha alpha2 alpha3 preparedAlpha preparedAlpha2
    scale0 scale1 scale2 scale0Out scale1Out scale2Out point0 point1 point2
    point0Out point1Out point2Out rowGroups groupMasks groupMasksOut firstAlpha
    firstAlphaOut groupValues groupValuesOut dense denseOut hsquare
    hprepareAlpha hprepareAlpha2 halpha3 hml0 hml1 hml2 hgrouped hdense
  exact generated_real_five_component_fold_exact currentLogLen alpha alpha2
    alpha3 preparedAlpha preparedAlpha2 scale0 scale1 scale2 scale0Out
    scale1Out scale2Out point0 point1 point2 point0Out point1Out point2Out
    rowGroups groupMasks groupMasksOut firstAlpha firstAlphaOut groupValues
    groupValuesOut dense denseOut hsquare hprepareAlpha hprepareAlpha2 halpha3
    hml0 hml1 hml2 hgrouped hdense

/-- Four consecutive successful actual fold calls retain their precise
10/8/6/4/2 log-length trace and exact error-free call witnesses. -/
def FourRoundDeferredFoldExact : Prop :=
  ∀ (initial after1 after2 after3 final : Accumulator)
    (alphas : Array RawQM31 4#usize),
    initial.log_len = 10#u32 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        initial alphas.val[0]! = ok after1 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        after1 alphas.val[1]! = ok after2 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        after2 alphas.val[2]! = ok after3 →
    ComponentCRuntimeCanonicalGenerated.aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
        after3 alphas.val[3]! = ok final →
    Nonempty (GeneratedFourRoundDeferredFold initial alphas final)

theorem four_round_deferred_fold_exact : FourRoundDeferredFoldExact := by
  intro initial after1 after2 after3 final alphas hinitial hrun0 hrun1 hrun2
    hrun3
  exact generated_four_round_deferred_fold_exact initial after1 after2 after3
    final alphas hinitial hrun0 hrun1 hrun2 hrun3

def ComponentCActualFoldOperational : Prop :=
  RealFiveComponentFoldExact ∧ FourRoundDeferredFoldExact

theorem component_c_actual_fold_operational :
    ComponentCActualFoldOperational :=
  ⟨real_five_component_fold_exact, four_round_deferred_fold_exact⟩

end OperationalFold

namespace PublicOutput

open aspis_prover.ComponentCRuntimeReleasedTraceFamilies

/-- Every packaged authentic successful public Component-C run returns the
maintained `deployedEvaluate` vector, including its exact public length. -/
def ComponentCActualPublicOutputClosure : Prop :=
  ∀ run : GeneratedPublicRun, GeneratedPublicOutputMatchesDeployed run

theorem component_c_actual_public_output_closure :
    ComponentCActualPublicOutputClosure := by
  intro run
  exact generated_public_run_output_matches_deployed run

end PublicOutput

/-- Current-source A/B plus actual-current Component-C fold and public-output
composition.  Its
only randomness-side premise is totality of the supplied Component-B word
source; all remaining hypotheses are concrete successful executions or
canonical-input obligations. -/
theorem current_source_ab_capstone
    {S : Type}
    (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource))
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real)
    (pads : Array ComponentBGenerated.aspis_core.field.QM31 255#usize)
    (pivotPad : ComponentBGenerated.aspis_core.field.QM31)
    (componentB : ComponentBRelationClaimsLayoutInstantiation.Lane)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = .ok (.Ok componentB))
    (hcopy componentC :
      alloc.vec.Vec ComponentBGenerated.aspis_core.field.QM31) :
    ComponentAActualMatchesMaintained ∧
      ComponentBActualMatchesMaintained mask selectedRound totalClaim eta real
        point componentB hcopy componentC ∧
      OperationalFold.ComponentCActualFoldOperational ∧
      PublicOutput.ComponentCActualPublicOutputClosure := by
  exact ⟨component_a_actual_matches_maintained,
    component_b_actual_matches_maintained sourceInst nextWordTotal source
      finalSource mask sampleRun selectedRound totalClaim eta real point hpoint
      htotal heta hreal pads pivotPad componentB encodeRun hcopy componentC,
    OperationalFold.component_c_actual_fold_operational,
    PublicOutput.component_c_actual_public_output_closure⟩

/-- Strongest combined current-source closure.  Beyond Component-B source
totality, its sole abstract implementation/model correspondence premise is
the transcript grinding hash application on the exact Tag-67 payload. -/
theorem current_source_combined_capstone
    {S State Challenge : Type}
    (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource))
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real)
    (pads : Array ComponentBGenerated.aspis_core.field.QM31 255#usize)
    (pivotPad : ComponentBGenerated.aspis_core.field.QM31)
    (componentB : ComponentBRelationClaimsLayoutInstantiation.Lane)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = .ok (.Ok componentB))
    (hcopy componentC :
      alloc.vec.Vec ComponentBGenerated.aspis_core.field.QM31)
    (shape : AspisFormal.V5ExactRuntimeWireRepair.RuntimeShape)
    (wire : AspisFormal.V5ExactRuntimeWireRepair.RuntimeExactWire shape)
    (hfit : AspisFormal.V5ExactRuntimeWireRepair.runtimeRepairedProofBytes
      shape ≤ Std.Usize.max)
    (fold0 fold1 fold2 fold3 batch final : Std.U64) (selected : Std.U8)
    (hmagic : aspis_verifier.v5_cu_probe.v5_work_wire_magic_is_valid
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit) =
        ok true)
    (hfold0 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11048#usize = ok fold0)
    (hfold1 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11056#usize = ok fold1)
    (hfold2 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11064#usize = ok fold2)
    (hfold3 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11072#usize = ok fold3)
    (hbatch : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11080#usize = ok batch)
    (hfinal : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19127#usize = ok final)
    (hselector : Slice.index_usize
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19135#usize = ok selected)
    (hzero : aspis_verifier.v5_cu_probe.v5_relation_final_zero_tail_is_valid
      (AspisTag67WorkWireMaintained.serializedRelationFinalSlice
        shape wire hfit) = ok true)
    (actualTranscriptGrindingDigest :
      State → Nonce64 → AspisTag67WorkVerifierClosure.GrindingDigest)
    (rustHash : State → List Byte →
      AspisTag67WorkVerifierClosure.GrindingDigest)
    (absorb : State → Nat → List Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State)
    (hHashApplication : ∀ state nonce,
      actualTranscriptGrindingDigest state nonce =
        rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))) :
    ComponentAActualMatchesMaintained ∧
      ComponentBActualMatchesMaintained mask selectedRound totalClaim eta real
        point componentB hcopy componentC ∧
      OperationalFold.ComponentCActualFoldOperational ∧
      PublicOutput.ComponentCActualPublicOutputClosure ∧
      Tag67.ActualWireAndVerifierClosure shape wire hfit fold0 fold1 fold2
        fold3 batch final selected actualTranscriptGrindingDigest rustHash
        absorb executeNext stateBefore := by
  exact ⟨component_a_actual_matches_maintained,
    component_b_actual_matches_maintained sourceInst nextWordTotal source
      finalSource mask sampleRun selectedRound totalClaim eta real point hpoint
      htotal heta hreal pads pivotPad componentB encodeRun hcopy componentC,
    OperationalFold.component_c_actual_fold_operational,
    PublicOutput.component_c_actual_public_output_closure,
    Tag67.actual_wire_and_verifier_closure shape wire hfit fold0 fold1 fold2
      fold3 batch final selected hmagic hfold0 hfold1 hfold2 hfold3 hbatch
      hfinal hselector hzero actualTranscriptGrindingDigest rustHash absorb
      executeNext stateBefore hHashApplication⟩

#print axioms component_a_actual_matches_maintained
#print axioms component_b_actual_matches_maintained
#print axioms OperationalFold.component_c_actual_fold_operational
#print axioms PublicOutput.component_c_actual_public_output_closure
#print axioms Tag67.actual_wire_and_verifier_closure
#print axioms current_source_ab_capstone
#print axioms current_source_combined_capstone

end FormalClosureStream1
