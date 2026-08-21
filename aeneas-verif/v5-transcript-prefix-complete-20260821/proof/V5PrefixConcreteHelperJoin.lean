import V5PrefixProgramHelpersProof
import V5PrefixMaskHelperProof
import V5ZeroUnchangedProof
import V5SemanticUnchangedProof
import V5PrefixByteEncodingProof
import AspisFormal.V5TranscriptPrefixExtractionBridge

/-!
# Concrete unchanged-source evidence for the V5 transcript prefix

This file runs the six separately extracted Rust helpers at the arguments used
by an accepted prefix.  It projects the event logs returned by those generated
functions into the maintained transcript event type.  The proof therefore
depends on all six unchanged-source helper theorems; no caller may supply an
arbitrary `PrefixHelperEvents` value.

The accepted initial claim crosses one explicit representation boundary: its
16 generated little-endian bytes must equal the 16 bytes parsed from the wire.
The outer successful-call list crosses the separate pinned-file checker
boundary described at the end of the file.
-/

namespace AspisV5PrefixConcreteHelperJoin

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open AspisV5TranscriptPrefixNormalizedGenerated
open AspisV5TranscriptPrefixExtractionBridge
open AspisV5PrefixByteEncodingProof
open AspisV5PrefixNonceEncodingProof

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev ExactFieldValue := V5PrefixMaskHelperProof.QM31Bytes

def modelArray16 (value : FixedBytes 16) : Array Std.U8 16#usize :=
  ⟨(bytes value).map byteToGenerated, by simp⟩

def modelArray32 (value : FixedBytes 32) : Array Std.U8 32#usize :=
  ⟨(bytes value).map byteToGenerated, by simp⟩

def modelArray448 (value : FixedBytes 448) : Array Std.U8 448#usize :=
  ⟨(bytes value).map byteToGenerated, by simp⟩

@[simp] theorem generatedToByte_modelArray16
    (value : FixedBytes 16) :
    (modelArray16 value).val.map generatedToByte = bytes value := by
  exact generated_byte_list_roundtrip (bytes value)

@[simp] theorem generatedToByte_modelArray32
    (value : FixedBytes 32) :
    (modelArray32 value).val.map generatedToByte = bytes value := by
  exact generated_byte_list_roundtrip (bytes value)

@[simp] theorem generatedToByte_modelArray448
    (value : FixedBytes 448) :
    (modelArray448 value).val.map generatedToByte = bytes value := by
  exact generated_byte_list_roundtrip (bytes value)

def projectProgramAbsorb (slot : AbsorbSlot) :
    V5PrefixProgramHelpersGenerated.ProgramTranscriptEvent → TranscriptEvent
  | .absorb label payload =>
      .absorb slot (generatedToByte label) (payload.map generatedToByte)

def emptyProgramTranscript : V5PrefixProgramHelpersProof.Transcript where
  events := []
  workValid := fun _ _ => false

def roundRootTrace (input : V5TranscriptInputs) : List TranscriptEvent :=
  match
      V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_round_root
        emptyProgramTranscript 0#usize
        (modelArray32 (input.circleRoot 0))
        (modelArray32 (input.publicSalt 0)) with
  | .ok transcript =>
      transcript.events.map (projectProgramAbsorb (.circleRoot 0))
  | _ => []

def c2RootTrace (input : V5TranscriptInputs) : List TranscriptEvent :=
  match
      V5PrefixProgramHelpersGenerated.v5_cu_probe.absorb_real_v5_c2_root
        emptyProgramTranscript (modelArray32 input.c2Root)
        (modelArray32 (input.publicSalt 1)) with
  | .ok transcript => transcript.events.map (projectProgramAbsorb .c2Root)
  | _ => []

def zeroSqueezeTrace : List TranscriptEvent :=
  [sourceSqueeze .theta] ++
    List.ofFn (fun coordinate : Fin 10 =>
      sourceSqueeze (.zerocheckPoint coordinate)) ++
    [sourceSqueeze .mu]

/-! `projectZeroEvents` keeps the two generated absorb labels and payloads.
It accepts the squeeze tail only when all twelve generated sampler calls are
present in the exact order proved for the unchanged helper. -/
def projectZeroEvents :
    List V5ZeroUnchangedGenerated.ZeroTranscriptEvent → List TranscriptEvent
  | .absorb labelRegistry payloadRegistry ::
      .absorb labelHelper payloadHelper :: squeezes =>
      if squeezes = List.replicate 12 .squeeze then
        [.absorb .constraintRegistry (generatedToByte labelRegistry)
            (payloadRegistry.map generatedToByte),
          .absorb .helperSum (generatedToByte labelHelper)
            (payloadHelper.map generatedToByte)] ++ zeroSqueezeTrace
      else []
  | _ => []

def zerocheckTrace : List TranscriptEvent :=
  match
      V5ZeroUnchangedGenerated.extract_begin_state_only_zerocheck
        { events := [] } with
  | .ok (.Ok _, transcript) => projectZeroEvents transcript.events
  | _ => []

def projectMaskEvent :
    V5PrefixMaskHelperGenerated.MaskTranscriptEvent → TranscriptEvent
  | .absorb label payload =>
      .absorb .maskClaim (generatedToByte label) (payload.map generatedToByte)
  | .squeezeNonzero => .squeeze .eta

def maskedSumcheckTrace
    (initialClaim eta : ExactFieldValue) : List TranscriptEvent :=
  match
      V5PrefixMaskHelperGenerated.extract_begin_state_only_masked_sumcheck
        { events := [], next := some eta } initialClaim with
  | .ok (.Ok _, transcript) => transcript.events.map projectMaskEvent
  | _ => []

def semanticChunks (input : V5TranscriptInputs) :
    List (Array Std.U8 448#usize) :=
  List.ofFn (fun round : Fin 10 => modelArray448 (input.semanticSumcheck round))

@[simp] theorem semanticChunks_length (input : V5TranscriptInputs) :
    (semanticChunks input).length = 10 := by
  simp [semanticChunks]

theorem semanticChunks_are_exact_wire (input : V5TranscriptInputs) :
    (V5SemanticUnchangedProof.joinedRoundSlice
        (semanticChunks input) (semanticChunks_length input)).val.map
        generatedToByte = semanticSumcheckWire input := by
  simp [V5SemanticUnchangedProof.joinedRoundSlice, semanticChunks,
    semanticSumcheckWire, List.map_flatMap]

def generatedSemanticEvents (input : V5TranscriptInputs) :
    List V5SemanticUnchangedGenerated.SemanticTranscriptEvent :=
  V5SemanticUnchangedProof.semanticRoundSequence 0#usize
    (semanticChunks input)

def projectedSemanticEvents (input : V5TranscriptInputs) :
    List TranscriptEvent :=
  (List.ofFn fun round : Fin 10 =>
    [.absorb (.semanticSumcheck round) (generatedToByte 29#u8)
      (generatedToByte (byteToGenerated (roundByte round)) ::
        (modelArray448 (input.semanticSumcheck round)).val.map generatedToByte),
      .squeeze (.relationChallenge round)]).flatten

/-! The event equality test is over the full generated list, including every
round byte, 448-byte payload, and squeeze.  Only that exact generated trace is
assigned the round-indexed maintained slots. -/
def projectSemanticEvents (input : V5TranscriptInputs)
    (events : List V5SemanticUnchangedGenerated.SemanticTranscriptEvent) :
    List TranscriptEvent :=
  if events = generatedSemanticEvents input then projectedSemanticEvents input
  else []

def semanticSumcheckTrace (input : V5TranscriptInputs) : List TranscriptEvent :=
  match
      V5SemanticUnchangedGenerated.extract_verify_state_only_sumcheck_streaming
        { events := [] }
        (V5SemanticUnchangedProof.joinedRoundSlice
          (semanticChunks input) (semanticChunks_length input)) () with
  | .ok (.Ok _, transcript) => projectSemanticEvents input transcript.events
  | _ => []

def batchTrace
    (workValid : Std.U64 → Std.U8 → Bool)
    (nonce : Nonce64) : List TranscriptEvent :=
  match
      V5PrefixProgramHelpersGenerated.v5_cu_probe.check_and_absorb_real_v5_batch_nonce
        ({ events := [], workValid := workValid } :
          V5PrefixProgramHelpersProof.Transcript) (modelNonce nonce) with
  | .ok (.Ok (), resultTranscript) =>
      [.verifyWork .batch 37 (List.ofFn (nonceLEBytes nonce))] ++
        resultTranscript.events.map (projectProgramAbsorb .batchNonce)
  | _ => []

/-! This is the concrete observer.  Every field executes a generated helper;
none returns a maintained source event by definition.  The root and semantic
fields are scoped to the one accepted call made by the checked outer path. -/
def generatedPrefixHelpers
    (input : V5TranscriptInputs)
    (workValid : Std.U64 → Std.U8 → Bool) :
    PrefixHelperEvents ExactFieldValue where
  absorbRoundRoot _ _ _ := roundRootTrace input
  absorbC2Root _ _ := c2RootTrace input
  beginZerocheck _ _ _ := zerocheckTrace
  beginMaskedSumcheck initialClaim eta :=
    maskedSumcheckTrace initialClaim eta
  verifySemanticSumcheck _ _ _ _ := semanticSumcheckTrace input
  checkAndAbsorbBatchNonce nonce := batchTrace workValid nonce

/-- Exact representation premise for the value parsed before the masked
sumcheck helper.  It is a byte equality, not a cryptographic assumption. -/
structure ExactAcceptedInitialClaimEncoding
    (input : V5TranscriptInputs)
    (values : PrefixSuccessfulValues ExactFieldValue) : Prop where
  initialClaim : values.initialClaim.val.map generatedToByte =
    bytes input.initialClaim

theorem projected_semantic_events_eq_source
    (input : V5TranscriptInputs) :
    projectedSemanticEvents input =
      (List.ofFn (sourceSemanticRound input)).flatten := by
  simp [projectedSemanticEvents, sourceSemanticRound, sourceAbsorb,
    sourceSqueeze, absorbPayload, semanticSumcheckPayload,
    AbsorbSlot.label]

theorem generated_round_root_trace_exact (input : V5TranscriptInputs) :
    roundRootTrace input = [sourceAbsorb input (.circleRoot 0)] := by
  unfold roundRootTrace
  rw [V5PrefixProgramHelpersProof.generated_absorb_round_zero_root_exact]
  simp [emptyProgramTranscript, projectProgramAbsorb, sourceAbsorb,
    absorbPayload, roundRootPayload, circleSaltIndex, foldByte,
    AbsorbSlot.label]

theorem generated_c2_root_trace_exact (input : V5TranscriptInputs) :
    c2RootTrace input = [sourceAbsorb input .c2Root] := by
  unfold c2RootTrace
  rw [V5PrefixProgramHelpersProof.generated_absorb_c2_root_exact]
  simp [emptyProgramTranscript, projectProgramAbsorb, sourceAbsorb,
    absorbPayload, c2RootPayload, AbsorbSlot.label]

theorem generated_zerocheck_trace_exact (input : V5TranscriptInputs) :
    zerocheckTrace =
      [sourceAbsorb input .constraintRegistry,
        sourceAbsorb input .helperSum,
        sourceSqueeze .theta] ++
      List.ofFn (fun coordinate : Fin 10 =>
        sourceSqueeze (.zerocheckPoint coordinate)) ++
      [sourceSqueeze .mu] := by
  unfold zerocheckTrace
  rw [V5ZeroUnchangedProof.extracted_zerocheck_success_exact]
  simp [projectZeroEvents, V5ZeroUnchangedProof.zerocheckEvents,
    V5ZeroUnchangedProof.registryBytes, zeroSqueezeTrace, sourceAbsorb,
    sourceSqueeze, absorbPayload, stateOnlyConstraintRegistry, zeroBytes,
    AbsorbSlot.label, generatedToByte]

theorem generated_masked_sumcheck_trace_exact
    (input : V5TranscriptInputs) (initialClaim eta : ExactFieldValue)
    (hclaim : initialClaim.val.map generatedToByte = bytes input.initialClaim) :
    maskedSumcheckTrace initialClaim eta =
      [sourceAbsorb input .maskClaim, sourceSqueeze .eta] := by
  unfold maskedSumcheckTrace
  rw [V5PrefixMaskHelperProof.extracted_masked_sumcheck_success_exact
    { events := [], next := some eta } initialClaim eta rfl]
  simp [projectMaskEvent, sourceAbsorb, sourceSqueeze, absorbPayload,
    maskClaimPayload, AbsorbSlot.label, hclaim]

theorem generated_semantic_sumcheck_trace_exact (input : V5TranscriptInputs) :
    semanticSumcheckTrace input =
      (List.ofFn (sourceSemanticRound input)).flatten := by
  unfold semanticSumcheckTrace
  rw [V5SemanticUnchangedProof.extracted_semantic_sumcheck_success_exact]
  simp [projectSemanticEvents, generatedSemanticEvents,
    projected_semantic_events_eq_source]

theorem generated_batch_trace_exact
    (input : V5TranscriptInputs)
    (workValid : Std.U64 → Std.U8 → Bool)
    (hwork : workValid (modelNonce input.batchNonce) 37#u8 = true) :
    batchTrace workValid input.batchNonce =
      sourceCheckAndAbsorb input .batch := by
  unfold batchTrace
  rw [V5PrefixProgramHelpersProof.generated_batch_work_success_exact
    { events := [], workValid := workValid } (modelNonce input.batchNonce)
    hwork]
  change
    [.verifyWork .batch 37 (List.ofFn (nonceLEBytes input.batchNonce)),
      .absorb .batchNonce (generatedToByte 28#u8)
        ((core.num.U64.to_le_bytes (modelNonce input.batchNonce)).val.map
          generatedToByte)] = sourceCheckAndAbsorb input .batch
  rw [generated_nonce_bytes_are_exact]
  simp [projectProgramAbsorb, sourceCheckAndAbsorb, sourceAbsorb,
    absorbPayload, workAbsorbSlot, workAbsorbPayload,
    WorkKind.difficulty, V5TranscriptInputs.nonce, AbsorbSlot.label]

/-! All six fields are proved from their corresponding generated helper
execution.  Removing any one of those helper theorems leaves its constructor
case unsolved. -/
theorem generated_prefix_helpers_are_exact
    {PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues ExactFieldValue PointValue)
    (values : PrefixSuccessfulValues ExactFieldValue)
    (workValid : Std.U64 → Std.U8 → Bool)
    (hwork : workValid (modelNonce input.batchNonce) 37#u8 = true)
    (hclaim : ExactAcceptedInitialClaimEncoding input values) :
    ExactSuccessfulPrefixHelperEvents
      (generatedPrefixHelpers input workValid) input derived values := by
  constructor
  · exact generated_round_root_trace_exact input
  · exact generated_c2_root_trace_exact input
  · exact generated_zerocheck_trace_exact input
  · exact generated_masked_sumcheck_trace_exact input
      values.initialClaim derived.eta hclaim.initialClaim
  · exact generated_semantic_sumcheck_trace_exact input
  · exact generated_batch_trace_exact input workValid hwork

/-! The pinned checker supplies only this equality for the outer generated
file.  It is kept visibly separate because a file-reading Python check is not
a Lean-kernel theorem. -/
structure PinnedOuterSuccessfulPathBoundary
    {PointValue : Type*}
    (outerCalls : List (PrefixExternalCall ExactFieldValue))
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues ExactFieldValue PointValue)
    (values : PrefixSuccessfulValues ExactFieldValue) : Prop where
  exactCalls : outerCalls = generatedSuccessfulPrefixCalls input derived values

theorem checked_outer_prefix_trace_eq_source
    {PointValue : Type*}
    (outerCalls : List (PrefixExternalCall ExactFieldValue))
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues ExactFieldValue PointValue)
    (values : PrefixSuccessfulValues ExactFieldValue)
    (workValid : Std.U64 → Std.U8 → Bool)
    (hwork : workValid (modelNonce input.batchNonce) 37#u8 = true)
    (hclaim : ExactAcceptedInitialClaimEncoding input values)
    (outer : PinnedOuterSuccessfulPathBoundary
      outerCalls input derived values) :
    runPrefixCalls
      (eventObserver (generatedPrefixHelpers input workValid)) [] outerCalls =
      sourcePrefix input := by
  rw [outer.exactCalls]
  exact normalized_generated_successful_prefix_trace_eq_sourcePrefix
    (generatedPrefixHelpers input workValid) input derived values
    (generated_prefix_helpers_are_exact input derived values workValid hwork
      hclaim)

#print axioms semanticChunks_are_exact_wire
#print axioms generated_prefix_helpers_are_exact
#print axioms checked_outer_prefix_trace_eq_source

end AspisV5PrefixConcreteHelperJoin
