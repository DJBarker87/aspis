import AspisFormal.K1.V7Tag73CausalSlotRouterRealization
import AspisFormal.K1.V7Tag73SchedulerCausalQ16Router
import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73SamplerDecoder
import AspisFormal.K1.V7Tag73SecureCircleMap

/-!
# Scheduler-native pre-answer routing for the semantic ordinary challenges

The root verifier samples `theta`, ten zerocheck coordinates, `mu`, and ten
semantic sumcheck challenges with the ordinary Tag-73 sampler.  The ten
zerocheck coordinates and `mu` have no absorb marker between them, so their
labels cannot be recovered by looking only at the current oracle input.  This
file reconstructs the literal sequential sampler state from the completed
root-verifier history.

The reconstructed phase contains every output already consumed by the current
sampler.  Hence it applies the production decoder after the matching advance
call and moves to the next challenge precisely when the production sampler
would stop.  The label for the next missing answer is computed before that
answer is available.

This is a coordinate router, not a probability assertion.  It deliberately
does not claim that a cached verifier query allocates a new master-tape
coordinate; that source-alignment issue is stated separately by the exact
compiler trace semantics.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K15SemanticSequentialRouter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Literal input recognizers -/

/-- A deployed duplex-output input has exactly the digest and squeeze domain. -/
def isSemanticSqueezeInput (input : ShaInput) : Bool :=
  input.length = 33 && input[32]? = some domSqueeze

/-- A deployed duplex-advance input has exactly the digest and advance domain. -/
def isSemanticAdvanceInput (input : ShaInput) : Bool :=
  input.length = 33 && input[32]? = some domAdvance

/-- The payload label of a literal deployed absorb input.  The digest itself
is intentionally opaque; only the fixed input layout is inspected. -/
def semanticAbsorbLabelOfInput? (input : ShaInput) : Option UInt8 :=
  match input[32]?, input[33]? with
  | some domain, some label =>
      if domain = domAbsorb then some label else none
  | _, _ => none

/-- Semantic-round marker, including the literal round byte. -/
def semanticRoundOfInput? (input : ShaInput) : Option (Fin 10) :=
  if semanticAbsorbLabelOfInput? input = some semanticRoundLabel then
    match input[34]? with
    | some round =>
        if bounded : round.toNat < 10 then some ⟨round.toNat, bounded⟩
        else none
    | none => none
  else none

@[simp] theorem literal_semantic_absorb_label
    (digest : Digest256) (label : UInt8) (data : ByteString) :
    semanticAbsorbLabelOfInput?
        (bytes digest ++ [domAbsorb, label] ++ data) = some label := by
  have at32 :
      (bytes digest ++ [domAbsorb, label] ++ data)[32]? = some domAbsorb := by
    rw [List.getElem?_append_left (by simp)]
    rw [List.getElem?_append_right (by simp)]
    simp
  have at33 :
      (bytes digest ++ [domAbsorb, label] ++ data)[33]? = some label := by
    rw [List.getElem?_append_left (by simp)]
    rw [List.getElem?_append_right (by simp)]
    simp
  unfold semanticAbsorbLabelOfInput?
  rw [at32, at33]
  simp

@[simp] theorem literal_semantic_squeeze_input
    (digest : Digest256) :
    isSemanticSqueezeInput (bytes digest ++ [domSqueeze]) = true := by
  simp [isSemanticSqueezeInput]

@[simp] theorem literal_semantic_advance_input
    (digest : Digest256) :
    isSemanticAdvanceInput (bytes digest ++ [domAdvance]) = true := by
  simp [isSemanticAdvanceInput]

@[simp] theorem literal_helper_sum_absorb_label
    (digest : Digest256) :
    semanticAbsorbLabelOfInput?
        (bytes digest ++ [domAbsorb, helperSumLabel] ++
          List.replicate 16 0) = some helperSumLabel := by
  simp [semanticAbsorbLabelOfInput?]

@[simp] theorem literal_semantic_round_of_input
    (digest : Digest256) (round : Fin 10)
    (sent : Fin 27 → Qm31Bytes) :
    semanticRoundOfInput?
        (bytes digest ++ [domAbsorb, semanticRoundLabel] ++
          ([UInt8.ofNat round.val] ++ encodeBlocks sent)) = some round := by
  have roundLt256 : round.val < 256 := lt_trans round.isLt (by omega)
  have roundMod : round.val % 256 = round.val := Nat.mod_eq_of_lt roundLt256
  simp [semanticRoundOfInput?, semanticAbsorbLabelOfInput?, roundMod,
    round.isLt]

/-! ## Sequential semantic sampler automaton -/

/-- The 22 ordinary challenges used by the fixed semantic event. -/
inductive SemanticOrdinaryPosition where
  | theta
  | zerocheckPoint (coordinate : Fin 10)
  | mu
  | sumcheck (round : Fin 10)
  deriving DecidableEq, Fintype, Repr

def SemanticOrdinaryPosition.challengeId :
    SemanticOrdinaryPosition → ChallengeId
  | .theta => .theta
  | .zerocheckPoint coordinate => .zerocheckPoint coordinate
  | .mu => .mu
  | .sumcheck round => .semantic round

/-- After completing `theta`, the production verifier immediately samples the
ten zerocheck coordinates and then `mu`.  Semantic sumcheck challenges are
separately restarted by their literal absorb markers. -/
def SemanticOrdinaryPosition.next? :
    SemanticOrdinaryPosition → Option SemanticOrdinaryPosition
  | .theta => some (.zerocheckPoint 0)
  | .zerocheckPoint coordinate =>
      if bounded : coordinate.val + 1 < 10 then
        some (.zerocheckPoint ⟨coordinate.val + 1, bounded⟩)
      else
        some .mu
  | .mu | .sumcheck _ => none

/-- Reconstructed state immediately before the next root-verifier call. -/
inductive SemanticHistoryPhase where
  | inactive
  | output (position : SemanticOrdinaryPosition)
      (priorOutputs : List Digest256)
  | advance (position : SemanticOrdinaryPosition)
      (priorOutputs : List Digest256) (currentOutput : Digest256)
  deriving DecidableEq, Repr

def semanticMarkerOfInput? (input : ShaInput) :
    Option SemanticOrdinaryPosition :=
  if semanticAbsorbLabelOfInput? input = some helperSumLabel then
    some .theta
  else
    (semanticRoundOfInput? input).map SemanticOrdinaryPosition.sumcheck

@[simp] theorem semantic_marker_of_literal_helper_sum
    (digest : Digest256) :
    semanticMarkerOfInput?
        (bytes digest ++ domAbsorb :: helperSumLabel :: List.replicate 16 0) =
      some .theta := by
  have label : semanticAbsorbLabelOfInput?
      (bytes digest ++ domAbsorb :: helperSumLabel :: List.replicate 16 0) =
      some helperSumLabel := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_absorb_label digest helperSumLabel
        (List.replicate 16 0)
  unfold semanticMarkerOfInput?
  rw [label]
  rfl

@[simp] theorem semantic_marker_of_literal_round
    (digest : Digest256) (round : Fin 10)
    (sent : Fin 27 → Qm31Bytes) :
    semanticMarkerOfInput?
        (bytes digest ++ domAbsorb :: semanticRoundLabel ::
          UInt8.ofNat round.val :: encodeBlocks sent) =
      some (.sumcheck round) := by
  have label : semanticAbsorbLabelOfInput?
      (bytes digest ++ domAbsorb :: semanticRoundLabel ::
        UInt8.ofNat round.val :: encodeBlocks sent) =
      some semanticRoundLabel := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_absorb_label digest semanticRoundLabel
        (UInt8.ofNat round.val :: encodeBlocks sent)
  have decoded : semanticRoundOfInput?
      (bytes digest ++ domAbsorb :: semanticRoundLabel ::
        UInt8.ofNat round.val :: encodeBlocks sent) = some round := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_round_of_input digest round sent
  unfold semanticMarkerOfInput?
  rw [label]
  norm_num [helperSumLabel, semanticRoundLabel]
  exact congrArg (Option.map SemanticOrdinaryPosition.sumcheck) decoded

/-- State after one completed initial-verifier call.  A successful decode is
tested only after the matching advance call, exactly when the next transcript
digest becomes available. -/
def SemanticHistoryPhase.afterVerifierRecord
    (phase : SemanticHistoryPhase) (record : QueryRecord) :
    SemanticHistoryPhase :=
  match semanticMarkerOfInput? record.input with
  | some position => .output position []
  | none =>
      match phase with
      | .inactive => .inactive
      | .output position priorOutputs =>
          if isSemanticSqueezeInput record.input then
            .advance position priorOutputs record.output
          else
            .inactive
      | .advance position priorOutputs currentOutput =>
          if isSemanticAdvanceInput record.input then
            let outputs := priorOutputs ++ [currentOutput]
            match decodeChallengeParameter exactSecureCircleParameterMap
                position.challengeId outputs with
            | some _ =>
                match position.next? with
                | some next => .output next []
                | none => .inactive
            | none => .output position outputs
          else
            .inactive

theorem SemanticHistoryPhase.afterVerifierRecord_of_marker
    (phase : SemanticHistoryPhase) (record : QueryRecord)
    (position : SemanticOrdinaryPosition)
    (marker : semanticMarkerOfInput? record.input = some position) :
    phase.afterVerifierRecord record = .output position [] := by
  simp [SemanticHistoryPhase.afterVerifierRecord, marker]

/-- Scan all completed calls while ignoring non-root actors. -/
def semanticHistoryPhase (history : List QueryRecord) : SemanticHistoryPhase :=
  history.foldl (fun phase record =>
    if record.actor = .verifier then
      phase.afterVerifierRecord record
    else
      phase) .inactive

@[simp] theorem semantic_history_phase_append_verifier
    (history : List QueryRecord) (record : QueryRecord)
    (actor : record.actor = .verifier) :
    semanticHistoryPhase (history ++ [record]) =
      (semanticHistoryPhase history).afterVerifierRecord record := by
  simp [semanticHistoryPhase, actor]

@[simp] theorem semantic_history_phase_append_nonverifier
    (history : List QueryRecord) (record : QueryRecord)
    (actor : record.actor ≠ .verifier) :
    semanticHistoryPhase (history ++ [record]) =
      semanticHistoryPhase history := by
  simp [semanticHistoryPhase, actor]

@[simp] theorem phase_after_literal_helper_sum
    (phase : SemanticHistoryPhase) (digest : Digest256) (output : Digest256)
    (origin : AnswerOrigin) :
    phase.afterVerifierRecord
        { input := bytes digest ++ [domAbsorb, helperSumLabel] ++
            List.replicate 16 0
          output := output
          actor := .verifier
          origin := origin } =
      .output .theta [] := by
  apply SemanticHistoryPhase.afterVerifierRecord_of_marker
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    semantic_marker_of_literal_helper_sum digest

@[simp] theorem phase_after_literal_semantic_round
    (phase : SemanticHistoryPhase) (digest output : Digest256)
    (round : Fin 10) (sent : Fin 27 → Qm31Bytes) (origin : AnswerOrigin) :
    phase.afterVerifierRecord
        { input := bytes digest ++ [domAbsorb, semanticRoundLabel] ++
            ([UInt8.ofNat round.val] ++ encodeBlocks sent)
          output := output
          actor := .verifier
          origin := origin } =
      .output (.sumcheck round) [] := by
  apply SemanticHistoryPhase.afterVerifierRecord_of_marker
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    semantic_marker_of_literal_round digest round sent

@[simp] theorem output_phase_after_literal_squeeze
    (position : SemanticOrdinaryPosition) (prior : List Digest256)
    (digest output : Digest256) (origin : AnswerOrigin) :
    (SemanticHistoryPhase.output position prior).afterVerifierRecord
        { input := bytes digest ++ [domSqueeze]
          output := output
          actor := .verifier
          origin := origin } =
      .advance position prior output := by
  simp [SemanticHistoryPhase.afterVerifierRecord, semanticMarkerOfInput?,
    semanticRoundOfInput?, semanticAbsorbLabelOfInput?]

/-- Each complete ordinary attempt has four output and four advance answers. -/
abbrev SemanticDuplexSlot :=
  SemanticOrdinaryPosition × Fin 4 × Fin 2

theorem semantic_ordinary_position_card :
    Fintype.card SemanticOrdinaryPosition = 22 := by
  decide

theorem semantic_duplex_slot_card : Fintype.card SemanticDuplexSlot = 176 := by
  simp [SemanticDuplexSlot, semantic_ordinary_position_card]

/-- Pre-answer slot selected by the already-completed verifier history.  Both
the output and advance halves are retained because advance digests belong to
the complete causal nuisance skeleton. -/
def semanticPreferredSlotFromHistory
    (history : List QueryRecord) (input : ShaInput) : Option SemanticDuplexSlot :=
  match semanticHistoryPhase history with
  | .output position priorOutputs =>
      if isSemanticSqueezeInput input then
        if bounded : priorOutputs.length < 4 then
          some (position, ⟨priorOutputs.length, bounded⟩, 0)
        else none
      else none
  | .advance position priorOutputs _ =>
      if isSemanticAdvanceInput input then
        if bounded : priorOutputs.length < 4 then
          some (position, ⟨priorOutputs.length, bounded⟩, 1)
        else none
      else none
  | .inactive => none

theorem semantic_preferred_output_of_phase
    (history : List QueryRecord) (position : SemanticOrdinaryPosition)
    (prior : List Digest256) (phase : semanticHistoryPhase history =
      .output position prior) (bounded : prior.length < 4)
    (digest : Digest256) :
    semanticPreferredSlotFromHistory history
        (bytes digest ++ [domSqueeze]) =
      some (position, ⟨prior.length, bounded⟩, 0) := by
  simp [semanticPreferredSlotFromHistory, phase, bounded]

theorem semantic_preferred_advance_of_phase
    (history : List QueryRecord) (position : SemanticOrdinaryPosition)
    (prior : List Digest256) (current : Digest256)
    (phase : semanticHistoryPhase history = .advance position prior current)
    (bounded : prior.length < 4) (digest : Digest256) :
    semanticPreferredSlotFromHistory history
        (bytes digest ++ [domAdvance]) =
      some (position, ⟨prior.length, bounded⟩, 1) := by
  simp [semanticPreferredSlotFromHistory, phase, bounded]

/-! ## Exact compiler scheduler specialization -/

/-- Literal scheduler label, computed from the selected request's pre-answer
oracle state and input. -/
def schedulerSemanticSequentialLabel
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    UnifiedExposureCursor globalOracleCalls → Option SemanticDuplexSlot :=
  fun cursor =>
    match seekUnifiedExposure transitionFuel cursor with
    | .machineFresh _limits _limitBound actor state input _nextProgram
        _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
        if actor = .verifier then
          semanticPreferredSlotFromHistory state.history input
        else none
    | .halted | .transitionLimit | .forkOutput .. | .forkAdvance .. => none

def semanticSequentialSlotMachine
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    PreAnswerSlotMachine Digest256 SemanticDuplexSlot
      (UnifiedExposureCursor globalOracleCalls) where
  preferredSlot := schedulerSemanticSequentialLabel transitionFuel
  afterAnswer := unifiedCursorAfterAnswer transitionFuel

def semanticRouterResidual (parameters : ExactCompilerResourceParameters) : Nat :=
  (exactCompilerTargetCaps parameters).length -
    Fintype.card SemanticDuplexSlot

theorem semantic_slots_fit_exact_compiler
    (parameters : ExactCompilerResourceParameters) :
    Fintype.card SemanticDuplexSlot ≤
      (exactCompilerTargetCaps parameters).length := by
  rw [semantic_duplex_slot_card,
    exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

theorem semantic_slots_add_residual
    (parameters : ExactCompilerResourceParameters) :
    Fintype.card SemanticDuplexSlot + semanticRouterResidual parameters =
      (exactCompilerTargetCaps parameters).length := by
  unfold semanticRouterResidual
  have fit := semantic_slots_fit_exact_compiler parameters
  omega

/-- Total causal router on the production plain-ROM cursor.  All 176 named
answers are isolated without a caller-supplied provider. -/
def exactPlainRomSemanticSequentialRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  (semanticSequentialSlotMachine transitionFuel).fullRouter
    (semanticRouterResidual parameters)
    (exactPlainRomExposureCursor configuration hidden)

/-- Exact master-tape equivalence induced by the concrete scheduler/history
automaton.  The first factor is the whole pre-fixed semantic response family. -/
def exactPlainRomSemanticSequentialCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      (SemanticDuplexSlot → Digest256) ×
        FreshAnswerTape Digest256 (semanticRouterResidual parameters) :=
  (castFreshAnswerTape (semantic_slots_add_residual parameters).symm).trans
    ((semanticSequentialSlotMachine transitionFuel).fullCoordinateEquiv
      (semanticRouterResidual parameters)
      (exactPlainRomExposureCursor configuration hidden))

#print axioms semanticAbsorbLabelOfInput?
#print axioms semanticRoundOfInput?
#print axioms SemanticHistoryPhase.afterVerifierRecord
#print axioms semanticHistoryPhase
#print axioms semanticPreferredSlotFromHistory
#print axioms schedulerSemanticSequentialLabel
#print axioms exactPlainRomSemanticSequentialRouter
#print axioms exactPlainRomSemanticSequentialCoordinates

end

end AspisK1.V7Tag73K15SemanticSequentialRouter
