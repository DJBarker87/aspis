import AspisFormal.K1.V7Tag73IndexedExposureCausalRouter
import AspisFormal.K1.V7Tag73SchedulerHistoryQ16Router
import AspisFormal.K1.V7Tag73AdaptiveQ16TrialAccounting

/-!
# Raw first-exposure controller for one final-work/q16 candidate

A future protocol role cannot be recovered from a raw SHA input after its
answer has already been exposed.  The source cover therefore indexes one
controller by a chronological full-256 exposure.  At that exposure the
controller recognizes either side of the literal final-work pair:

* `digest || domGrind || nonce`, whose answer is the 34-bit work digest; or
* `digest || domAbsorb || finalWorkNonceLabel || nonce`, whose answer is the
  post-final-nonce q16 base.

The two inputs carry the same digest/nonce key.  Whichever is exposed first
anchors the trial; the other can occur later in either order.  Once the
post-final-nonce answer is known, the controller follows every literal q16
candidate absorb and duplex output/advance chain using only earlier answers.

This module constructs the executable pre-answer controller.  It does not yet
assert that every accepting source execution is covered: that theorem must
exclude the already-accounted forward-reference/collision event and connect
the raw first exposures to the production caller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FinalWorkQ16CandidateController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-! ## Literal raw key grammar -/

/-- The shared pre-final digest and selected nonce as raw byte strings.  The
parsers below enforce their deployed 32-byte and 8-byte widths. -/
structure RawFinalWorkKey where
  digest : ByteString
  nonce : ByteString
  deriving DecidableEq, Repr

def RawFinalWorkKey.workInput (key : RawFinalWorkKey) : ShaInput :=
  key.digest ++ [domGrind] ++ key.nonce

def RawFinalWorkKey.absorbInput (key : RawFinalWorkKey) : ShaInput :=
  key.digest ++ [domAbsorb, finalWorkNonceLabel] ++ key.nonce

theorem RawFinalWorkKey.absorbInput_ne_workInput (key : RawFinalWorkKey) :
    key.absorbInput ≠ key.workInput := by
  intro equal
  have lengths := congrArg List.length equal
  simp [RawFinalWorkKey.absorbInput, RawFinalWorkKey.workInput] at lengths

def rawFinalWorkKeyOfWorkInput? (input : ShaInput) : Option RawFinalWorkKey :=
  if _lengthExact : input.length = 41 then
    if _domainExact : input[32]? = some domGrind then
      some { digest := input.take 32, nonce := input.drop 33 }
    else none
  else none

def rawFinalWorkKeyOfAbsorbInput? (input : ShaInput) : Option RawFinalWorkKey :=
  if _lengthExact : input.length = 42 then
    if _domainExact : input[32]? = some domAbsorb then
      if _labelExact : input[33]? = some finalWorkNonceLabel then
        some { digest := input.take 32, nonce := input.drop 34 }
      else none
    else none
  else none

def literalFinalWorkKey (digest : Digest256)
    (nonce : NonceBytes) : RawFinalWorkKey :=
  { digest := bytes digest, nonce := bytes nonce }

@[simp] theorem literal_final_work_key_work_input
    (digest : Digest256) (nonce : NonceBytes) :
    (literalFinalWorkKey digest nonce).workInput =
      bytes digest ++ [domGrind] ++ bytes nonce := by
  rfl

@[simp] theorem literal_final_work_key_absorb_input
    (digest : Digest256) (nonce : NonceBytes) :
    (literalFinalWorkKey digest nonce).absorbInput =
      bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce := by
  rfl

@[simp] theorem parse_literal_final_work_input
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfWorkInput?
        (bytes digest ++ [domGrind] ++ bytes nonce) =
      some (literalFinalWorkKey digest nonce) := by
  have dropExact :
      List.drop 33 (bytes digest ++ domGrind :: bytes nonce) = bytes nonce := by
    simpa using
      (List.drop_length_add_append (l₁ := bytes digest)
        (l₂ := domGrind :: bytes nonce) 1)
  simp [rawFinalWorkKeyOfWorkInput?, literalFinalWorkKey, dropExact]

@[simp] theorem parse_literal_final_nonce_absorb_input
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfAbsorbInput?
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) =
      some (literalFinalWorkKey digest nonce) := by
  have dropExact :
      List.drop 34
          (bytes digest ++ domAbsorb :: finalWorkNonceLabel :: bytes nonce) =
        bytes nonce := by
    simpa using
      (List.drop_length_add_append (l₁ := bytes digest)
        (l₂ := domAbsorb :: finalWorkNonceLabel :: bytes nonce) 2)
  simp [rawFinalWorkKeyOfAbsorbInput?, literalFinalWorkKey, dropExact]

@[simp] theorem work_parser_rejects_literal_final_nonce_absorb
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfWorkInput?
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) =
      none := by
  simp [rawFinalWorkKeyOfWorkInput?]

@[simp] theorem absorb_parser_rejects_literal_final_work
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfAbsorbInput?
        (bytes digest ++ [domGrind] ++ bytes nonce) = none := by
  simp [rawFinalWorkKeyOfAbsorbInput?]

@[simp] theorem parse_literal_final_work_input_cons
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfWorkInput?
        (bytes digest ++ domGrind :: bytes nonce) =
      some (literalFinalWorkKey digest nonce) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    parse_literal_final_work_input digest nonce

@[simp] theorem parse_literal_final_nonce_absorb_input_cons
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfAbsorbInput?
        (bytes digest ++ domAbsorb :: finalWorkNonceLabel :: bytes nonce) =
      some (literalFinalWorkKey digest nonce) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    parse_literal_final_nonce_absorb_input digest nonce

@[simp] theorem work_parser_rejects_literal_final_nonce_absorb_cons
    (digest : Digest256) (nonce : NonceBytes) :
    rawFinalWorkKeyOfWorkInput?
        (bytes digest ++ domAbsorb :: finalWorkNonceLabel :: bytes nonce) =
      none := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    work_parser_rejects_literal_final_nonce_absorb digest nonce

/-! ## Current full-256 request -/

/-- The literal SHA input waiting at the current unified-scheduler exposure.
The answer is intentionally absent. -/
def unifiedInputBeforeAnswer?
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Option ShaInput :=
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound _actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      some input
  | .forkOutput _history _room outputInput _advanceInput _template _next =>
      some outputInput
  | .forkAdvance _history _room _outputInput advanceInput _template
      _forkOutput _next => some advanceInput
  | .halted | .transitionLimit => none

/-! ## Q16 raw chain tracker -/

inductive RawQ16BranchPhase where
  | unseen
  /-- Both sibling inputs are determined by `digest`. `outputSeen` records
  whether the named q16 output coordinate has already been exposed;
  `advanceAnswer` retains an advance sibling exposed first. -/
  | pending (digest : Digest256) (block : Nat)
      (outputSeen : Bool) (advanceAnswer : Option Digest256)
  | finished
  deriving DecidableEq, Repr

def emptyRawQ16Branches : Fin 64 → RawQ16BranchPhase :=
  fun _ => .unseen

def q16CandidateOfBaseInput? (base : Digest256)
    (input : ShaInput) : Option (Fin 64) :=
  match q16CandidateCounterOfInput? input with
  | some counter =>
      if _prefixExact : input.take 32 = bytes base then some counter else none
  | none => none

@[simp] theorem q16_candidate_of_literal_base_input
    (base : Digest256) (counter : Fin 64) :
    q16CandidateOfBaseInput? base
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) = some counter := by
  simp [q16CandidateOfBaseInput?]

def RawQ16BranchPhase.preferredSlot
    (counter : Fin 64) (phase : RawQ16BranchPhase)
    (input : ShaInput) : Option Q16DigestSlot :=
  match phase with
  | .pending digest block outputSeen _advanceAnswer =>
      if _notSeen : outputSeen = false then
        if _inputExact : input = bytes digest ++ [domSqueeze] then
          if bounded : block < 8 then some (counter, ⟨block, bounded⟩) else none
        else none
      else none
  | .unseen | .finished => none

def firstRawQ16PreferredSlot
    (branches : Fin 64 → RawQ16BranchPhase) (input : ShaInput) :
    Option Q16DigestSlot :=
  (List.ofFn fun counter =>
      (branches counter).preferredSlot counter input).foldl
    (fun found candidate => found.orElse fun _ => candidate) none

/-- Complete a block once both sibling exposures are available. -/
def nextRawQ16BranchPhase (block : Nat) (nextDigest : Digest256) :
    RawQ16BranchPhase :=
  if _bounded : block + 1 < 8 then
    .pending nextDigest (block + 1) false none
  else
    .finished

/-- Consume output and advance siblings in either chronological order. -/
def RawQ16BranchPhase.afterInput
    (phase : RawQ16BranchPhase) (input : ShaInput) (answer : Digest256) :
    RawQ16BranchPhase :=
  match phase with
  | .pending digest block outputSeen advanceAnswer =>
      if input = bytes digest ++ [domSqueeze] then
        match advanceAnswer with
        | some nextDigest => nextRawQ16BranchPhase block nextDigest
        | none => .pending digest block true none
      else if input = bytes digest ++ [domAdvance] then
        if outputSeen = true then nextRawQ16BranchPhase block answer
        else .pending digest block false (some answer)
      else phase
  | .unseen | .finished => phase

def updateRawQ16Branches
    (base : Digest256) (branches : Fin 64 → RawQ16BranchPhase)
    (input : ShaInput) (answer : Digest256) :
    Fin 64 → RawQ16BranchPhase := fun counter =>
  if _candidate : q16CandidateOfBaseInput? base input = some counter then
    .pending answer 0 false none
  else
    (branches counter).afterInput input answer

/-! ## One exposure-indexed final-work/q16 controller -/

inductive FinalWorkQ16CandidateMemory where
  | inactive
  | tracked
      (key : RawFinalWorkKey)
      (workSeen : Bool)
      (q16Base : Option Digest256)
      (branches : Fin 64 → RawQ16BranchPhase)

def inactiveCandidateMemory : FinalWorkQ16CandidateMemory := .inactive

def candidatePreferredSlot
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory) : Option FinalWorkQ16DigestSlot :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => none
  | some input =>
      match state.memory with
      | .inactive =>
          if state.exposureIndex = anchor then
            match rawFinalWorkKeyOfWorkInput? input with
            | some _ => some none
            | none => none
          else none
      | .tracked key workSeen _base branches =>
          if workSeen = false ∧ input = key.workInput then
            some none
          else
            (firstRawQ16PreferredSlot branches input).map some

def candidateAfterMemory
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory)
    (answer : Digest256) : FinalWorkQ16CandidateMemory :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input =>
      match state.memory with
      | .inactive =>
          if state.exposureIndex = anchor then
            match rawFinalWorkKeyOfWorkInput? input with
            | some key => .tracked key true none emptyRawQ16Branches
            | none =>
                match rawFinalWorkKeyOfAbsorbInput? input with
                | some key =>
                    .tracked key false (some answer) emptyRawQ16Branches
                | none => .inactive
          else .inactive
      | .tracked key workSeen q16Base branches =>
          let nextWorkSeen := workSeen || decide (input = key.workInput)
          match q16Base with
          | some base =>
              .tracked key nextWorkSeen (some base)
                (updateRawQ16Branches base branches input answer)
          | none =>
              if input = key.absorbInput then
                .tracked key nextWorkSeen (some answer) branches
              else
                .tracked key nextWorkSeen none branches

def finalWorkQ16CandidateController
    (globalOracleCalls transitionFuel anchor : Nat) :
    IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot FinalWorkQ16CandidateMemory where
  preferredSlot := candidatePreferredSlot transitionFuel anchor
  afterMemory := candidateAfterMemory transitionFuel anchor

/-- The concrete exposure-indexed controller compiled into the exact
fixed-length compiler router. -/
def exactCompilerFinalWorkQ16CandidateRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel anchor : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFinalWorkQ16Router parameters :=
  exactCompilerIndexedFinalWorkQ16Router parameters transitionFuel
    (finalWorkQ16CandidateController
      (globalFull256OracleCallCap parameters) transitionFuel anchor)
    inactiveCandidateMemory cursor

/-- Hence every chronological anchor supplies the lossless joint
final-work/q16 coordinates used by the product theorem. -/
def exactCompilerFinalWorkQ16CandidateCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel anchor : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerIndexedFinalWorkQ16Coordinates parameters transitionFuel
    (finalWorkQ16CandidateController
      (globalFull256OracleCallCap parameters) transitionFuel anchor)
    inactiveCandidateMemory cursor

/-- Production-facing specialization: exactly one controller for each
chronological master-tape exposure in the conservative finite inventory. -/
def exactCompilerExposureTrialFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (trial : AspisK1.V7Tag73AdaptiveQ16TrialAccounting.ExactCompilerExposureTrial
      parameters)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFinalWorkQ16Router parameters :=
  exactCompilerFinalWorkQ16CandidateRouter parameters transitionFuel trial.val
    cursor

def exactCompilerExposureTrialFinalWorkQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (trial : AspisK1.V7Tag73AdaptiveQ16TrialAccounting.ExactCompilerExposureTrial
      parameters)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerFinalWorkQ16CandidateCoordinates parameters transitionFuel
    trial.val cursor

/-! ## Exact local transition facts -/

theorem inactive_anchor_work_labels_final_work
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (digest : Digest256) (nonce : NonceBytes)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel cursor =
      some (bytes digest ++ [domGrind] ++ bytes nonce)) :
    candidatePreferredSlot transitionFuel anchor
        { exposureIndex := anchor
          cursor := cursor
          memory := inactiveCandidateMemory } =
      some none := by
  simp [candidatePreferredSlot, inactiveCandidateMemory, inputExact]

theorem inactive_anchor_absorb_stores_q16_base
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (digest answer : Digest256) (nonce : NonceBytes)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel cursor =
      some (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce)) :
    candidateAfterMemory transitionFuel anchor
        { exposureIndex := anchor
          cursor := cursor
          memory := inactiveCandidateMemory } answer =
      .tracked (literalFinalWorkKey digest nonce) false (some answer)
        emptyRawQ16Branches := by
  simp [candidateAfterMemory, inactiveCandidateMemory, inputExact]

theorem inactive_anchor_work_stores_key
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (digest answer : Digest256) (nonce : NonceBytes)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel cursor =
      some (bytes digest ++ [domGrind] ++ bytes nonce)) :
    candidateAfterMemory transitionFuel anchor
        { exposureIndex := anchor
          cursor := cursor
          memory := inactiveCandidateMemory } answer =
      .tracked (literalFinalWorkKey digest nonce) true none
        emptyRawQ16Branches := by
  simp [candidateAfterMemory, inactiveCandidateMemory, inputExact]

theorem tracked_unseen_work_labels_final_work
    {globalOracleCalls : Nat}
    (transitionFuel anchor exposureIndex : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (key : RawFinalWorkKey) (base : Option Digest256)
    (branches : Fin 64 → RawQ16BranchPhase)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel cursor =
      some key.workInput) :
    candidatePreferredSlot transitionFuel anchor
        { exposureIndex := exposureIndex
          cursor := cursor
          memory := .tracked key false base branches } =
      some none := by
  simp [candidatePreferredSlot, inputExact]

theorem tracked_absorb_stores_q16_base
    {globalOracleCalls : Nat}
    (transitionFuel anchor exposureIndex : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (key : RawFinalWorkKey) (workSeen : Bool)
    (branches : Fin 64 → RawQ16BranchPhase) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel cursor =
      some key.absorbInput) :
    candidateAfterMemory transitionFuel anchor
        { exposureIndex := exposureIndex
          cursor := cursor
          memory := .tracked key workSeen none branches } answer =
      .tracked key workSeen (some answer) branches := by
  simp [candidateAfterMemory, inputExact,
    RawFinalWorkKey.absorbInput_ne_workInput]

theorem literal_candidate_absorb_starts_block_zero
    (base answer : Digest256) (counter : Fin 64) :
    updateRawQ16Branches base emptyRawQ16Branches
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) answer counter =
      .pending answer 0 false none := by
  simp [updateRawQ16Branches]

theorem literal_output_phase_labels_exact_slot
    (digest : Digest256) (counter : Fin 64) (block : Nat)
    (advanceAnswer : Option Digest256)
    (bounded : block < 8) :
    (RawQ16BranchPhase.pending digest block false advanceAnswer).preferredSlot
        counter
        (bytes digest ++ [domSqueeze]) =
      some (counter, ⟨block, bounded⟩) := by
  simp [RawQ16BranchPhase.preferredSlot, bounded]

theorem literal_output_then_waits_for_advance
    (digest outputAnswer : Digest256) (block : Nat) :
    (RawQ16BranchPhase.pending digest block false none).afterInput
        (bytes digest ++ [domSqueeze]) outputAnswer =
      .pending digest block true none := by
  simp [RawQ16BranchPhase.afterInput]

theorem literal_advance_then_waits_for_output
    (digest advanceAnswer : Digest256) (block : Nat) :
    (RawQ16BranchPhase.pending digest block false none).afterInput
        (bytes digest ++ [domAdvance]) advanceAnswer =
      .pending digest block false (some advanceAnswer) := by
  have different :
      bytes digest ++ [domAdvance] ≠ bytes digest ++ [domSqueeze] :=
    (squeeze_output_and_advance_inputs_are_distinct digest).symm
  simp [RawQ16BranchPhase.afterInput, different]

theorem literal_output_after_advance_starts_next
    (digest outputAnswer advanceAnswer : Digest256) (block : Nat)
    (bounded : block + 1 < 8) :
    (RawQ16BranchPhase.pending digest block false
        (some advanceAnswer)).afterInput
        (bytes digest ++ [domSqueeze]) outputAnswer =
      .pending advanceAnswer (block + 1) false none := by
  simp [RawQ16BranchPhase.afterInput, nextRawQ16BranchPhase, bounded]

theorem literal_advance_after_output_starts_next
    (digest advanceAnswer : Digest256) (block : Nat)
    (bounded : block + 1 < 8) :
    (RawQ16BranchPhase.pending digest block true none).afterInput
        (bytes digest ++ [domAdvance]) advanceAnswer =
      .pending advanceAnswer (block + 1) false none := by
  have different :
      bytes digest ++ [domAdvance] ≠ bytes digest ++ [domSqueeze] :=
    (squeeze_output_and_advance_inputs_are_distinct digest).symm
  simp [RawQ16BranchPhase.afterInput, nextRawQ16BranchPhase, bounded,
    different]

theorem literal_output_after_final_advance_finishes
    (digest outputAnswer advanceAnswer : Digest256) :
    (RawQ16BranchPhase.pending digest 7 false
        (some advanceAnswer)).afterInput
        (bytes digest ++ [domSqueeze]) outputAnswer =
      .finished := by
  simp [RawQ16BranchPhase.afterInput, nextRawQ16BranchPhase]

theorem literal_final_advance_after_output_finishes
    (digest advanceAnswer : Digest256) :
    (RawQ16BranchPhase.pending digest 7 true none).afterInput
        (bytes digest ++ [domAdvance]) advanceAnswer =
      .finished := by
  have different :
      bytes digest ++ [domAdvance] ≠ bytes digest ++ [domSqueeze] :=
    (squeeze_output_and_advance_inputs_are_distinct digest).symm
  simp [RawQ16BranchPhase.afterInput, nextRawQ16BranchPhase, different]

#print axioms parse_literal_final_work_input
#print axioms parse_literal_final_nonce_absorb_input
#print axioms RawFinalWorkKey.absorbInput_ne_workInput
#print axioms q16_candidate_of_literal_base_input
#print axioms inactive_anchor_work_labels_final_work
#print axioms inactive_anchor_absorb_stores_q16_base
#print axioms inactive_anchor_work_stores_key
#print axioms tracked_unseen_work_labels_final_work
#print axioms tracked_absorb_stores_q16_base
#print axioms literal_candidate_absorb_starts_block_zero
#print axioms literal_output_phase_labels_exact_slot
#print axioms literal_output_then_waits_for_advance
#print axioms literal_advance_then_waits_for_output
#print axioms literal_output_after_advance_starts_next
#print axioms literal_advance_after_output_starts_next
#print axioms literal_output_after_final_advance_finishes
#print axioms literal_final_advance_after_output_finishes
#print axioms finalWorkQ16CandidateController
#print axioms exactCompilerFinalWorkQ16CandidateRouter
#print axioms exactCompilerFinalWorkQ16CandidateCoordinates
#print axioms exactCompilerExposureTrialFinalWorkQ16Router
#print axioms exactCompilerExposureTrialFinalWorkQ16Coordinates

end

end AspisK1.V7Tag73FinalWorkQ16CandidateController
