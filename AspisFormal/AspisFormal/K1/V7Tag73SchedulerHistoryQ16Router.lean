import AspisFormal.K1.V7Tag73SchedulerCausalQ16Router
import AspisFormal.K1.V7Tag73ExactPlainRomRun

/-!
# A concrete q16 router from the literal scheduler history

The root Tag-73 verifier writes every oracle call to the shared chronological
`OracleState.history`.  Candidate absorbs have a unique deployed 35-byte
shape, and each candidate block is the following squeeze/advance pair.  This
file turns that already-existing pre-query history into the pre-answer label
consumed by the causal q16 router.

Only records whose actor is the initial `.verifier` participate.  Adversary,
simulator, and extractor-replay records cannot spoof or advance the root q16
scan.  The current fresh answer is not an argument of any definition below.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerHistoryQ16Router

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router

noncomputable section

/-! ## Exact deployed input classifiers -/

/-- Decode only the literal Tag-73 q16 candidate-absorb input:
`digest[32] || domAbsorb || queryCandidateLabel || counter` with
`counter < 64`. -/
def q16CandidateCounterOfInput? (input : ShaInput) : Option (Fin 64) :=
  if lengthExact : input.length = 35 then
    match input[32]?, input[33]?, input[34]? with
    | some domain, some label, some counter =>
        if tagsExact : domain = domAbsorb ∧ label = queryCandidateLabel then
          if counterBound : counter.toNat < 64 then
            some ⟨counter.toNat, counterBound⟩
          else
            none
        else
          none
    | _, _, _ => none
  else
    none

/-- A deployed duplex output query is exactly 32 digest bytes followed by
`domSqueeze`. -/
def isTag73SqueezeInput (input : ShaInput) : Bool :=
  input.length = 33 && input[32]? = some domSqueeze

/-- A deployed duplex advance query is exactly 32 digest bytes followed by
`domAdvance`. -/
def isTag73AdvanceInput (input : ShaInput) : Bool :=
  input.length = 33 && input[32]? = some domAdvance

@[simp] theorem q16_candidate_counter_of_literal_input
    (digest : Digest256) (counter : Fin 64) :
    q16CandidateCounterOfInput?
        (bytes digest ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) =
      some counter := by
  have counterLt256 : counter.val < 256 := lt_trans counter.isLt (by omega)
  have counterMod : counter.val % 256 = counter.val :=
    Nat.mod_eq_of_lt counterLt256
  simp [q16CandidateCounterOfInput?, counterMod, counter.isLt]

@[simp] theorem literal_squeeze_input_is_tag73_squeeze
    (digest : Digest256) :
    isTag73SqueezeInput (bytes digest ++ [domSqueeze]) = true := by
  simp [isTag73SqueezeInput]

@[simp] theorem literal_advance_input_is_tag73_advance
    (digest : Digest256) :
    isTag73AdvanceInput (bytes digest ++ [domAdvance]) = true := by
  simp [isTag73AdvanceInput]

/-! ## Root-verifier history automaton -/

/-- State reconstructed from the completed root-verifier query history.
`ready counter block` means that the next q16 output query, if it is exposed,
belongs to this literal candidate/block coordinate.  `advance` means the
output half has already completed and the following advance half carries no
q16 digest coordinate. -/
inductive RootQ16HistoryPhase where
  | inactive
  | ready (counter : Fin 64) (block : Nat)
  | advance (counter : Fin 64) (block : Nat)
  deriving DecidableEq, Repr

/-- Consume one completed initial-verifier oracle call.  Any non-q16 input
ends the current candidate phase. -/
def RootQ16HistoryPhase.afterVerifierInput
    (phase : RootQ16HistoryPhase) (input : ShaInput) : RootQ16HistoryPhase :=
  match q16CandidateCounterOfInput? input with
  | some counter => .ready counter 0
  | none =>
      match phase with
      | .ready counter block =>
          if isTag73SqueezeInput input then .advance counter block
          else .inactive
      | .advance counter block =>
          if isTag73AdvanceInput input then .ready counter (block + 1)
          else .inactive
      | .inactive => .inactive

/-- Scan the shared history, ignoring every actor except the initial verifier.
This is a left-to-right fold over calls that have already completed. -/
def rootQ16HistoryPhase (history : List QueryRecord) : RootQ16HistoryPhase :=
  history.foldl (fun phase record =>
    if record.actor = .verifier then
      phase.afterVerifierInput record.input
    else
      phase) .inactive

@[simp] theorem root_q16_history_phase_append_verifier
    (history : List QueryRecord) (input : ShaInput) (output : ShaOutput)
    (origin : AnswerOrigin) :
    rootQ16HistoryPhase
        (history ++ [{ input := input
                       output := output
                       actor := .verifier
                       origin := origin }]) =
      (rootQ16HistoryPhase history).afterVerifierInput input := by
  simp [rootQ16HistoryPhase]

@[simp] theorem root_q16_history_phase_append_nonverifier
    (history : List QueryRecord) (input : ShaInput) (output : ShaOutput)
    (actor : QueryActor) (origin : AnswerOrigin)
    (notVerifier : actor ≠ .verifier) :
    rootQ16HistoryPhase
        (history ++ [{ input := input
                       output := output
                       actor := actor
                       origin := origin }]) =
      rootQ16HistoryPhase history := by
  simp [rootQ16HistoryPhase, notVerifier]

@[simp] theorem phase_after_literal_candidate_absorb
    (phase : RootQ16HistoryPhase) (digest : Digest256)
    (counter : Fin 64) :
    phase.afterVerifierInput
        (bytes digest ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) =
      .ready counter 0 := by
  simp [RootQ16HistoryPhase.afterVerifierInput]

@[simp] theorem ready_phase_after_literal_squeeze
    (digest : Digest256) (counter : Fin 64) (block : Nat) :
    (RootQ16HistoryPhase.ready counter block).afterVerifierInput
        (bytes digest ++ [domSqueeze]) =
      .advance counter block := by
  simp [RootQ16HistoryPhase.afterVerifierInput, isTag73SqueezeInput,
    q16CandidateCounterOfInput?]

@[simp] theorem advance_phase_after_literal_advance
    (digest : Digest256) (counter : Fin 64) (block : Nat) :
    (RootQ16HistoryPhase.advance counter block).afterVerifierInput
        (bytes digest ++ [domAdvance]) =
      .ready counter (block + 1) := by
  simp [RootQ16HistoryPhase.afterVerifierInput, isTag73AdvanceInput,
    q16CandidateCounterOfInput?]

/-- Label the next fresh request using only the completed history and current
input.  The current output is deliberately absent. -/
def rootQ16PreferredSlotFromHistory
    (history : List QueryRecord) (input : ShaInput) : Option Q16DigestSlot :=
  match rootQ16HistoryPhase history with
  | .ready counter block =>
      if squeeze : isTag73SqueezeInput input then
        if bounded : block < 8 then some (counter, ⟨block, bounded⟩)
        else none
      else none
  | .inactive | .advance _ _ => none

theorem root_q16_preferred_slot_of_ready_phase
    (history : List QueryRecord) (counter : Fin 64) (block : Nat)
    (digest : Digest256)
    (phaseExact : rootQ16HistoryPhase history = .ready counter block)
    (bounded : block < 8) :
    rootQ16PreferredSlotFromHistory history
        (bytes digest ++ [domSqueeze]) =
      some (counter, ⟨block, bounded⟩) := by
  simp [rootQ16PreferredSlotFromHistory, phaseExact,
    isTag73SqueezeInput, bounded]

/-! ## Literal unified-scheduler specialization -/

/-- Pre-answer q16 label for the exact unified scheduler.  Normalization may
pass cached calls and completed machine stages, but the selected label is
computed from the resulting pre-query state before its missing answer is
read. -/
def schedulerHistoryQ16Label
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    UnifiedQ16PreAnswerLabel globalOracleCalls := fun cursor =>
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound actor state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      if actor = .verifier then
        rootQ16PreferredSlotFromHistory state.history input
      else
        none
  | .forkOutput frozenHistory _pairRoom outputInput _advanceInput _template
      _next =>
      rootQ16PreferredSlotFromHistory frozenHistory outputInput
  | .halted | .transitionLimit | .forkAdvance .. => none

/-- A restoration-programmed output half is labelled from the exact frozen
pre-fork history and concrete output input. Both are fixed before the fresh
fork answer is exposed. This is essential for q16 calls that were cached in
the root verifier and become fresh only in a state-restoration branch. -/
theorem scheduler_history_q16_label_at_fork_output
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      UnifiedExposureCursor globalOracleCalls) :
    schedulerHistoryQ16Label (transitionFuel + 1)
        (.forkPair frozenHistory pairRoom outputInput advanceInput template
          next) =
      rootQ16PreferredSlotFromHistory frozenHistory outputInput := by
  rfl

/-- Concrete adaptive q16 router for the exact deployed plain-ROM cursor.
There is no caller-supplied labelling function in this specialization. -/
def exactPlainRomHistoryQ16Router
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    ExactCompilerCausalQ16Router parameters :=
  exactCompilerSchedulerQ16Router parameters transitionFuel
    (schedulerHistoryQ16Label transitionFuel)
    (exactPlainRomExposureCursor configuration hidden)

/-- The concrete router supplies the exact residual/forest coordinate
equivalence used by the semantic q16 probability theorem. -/
def exactPlainRomHistoryQ16Coordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerQ16Residual parameters × Q16CandidateDigestForest :=
  exactCompilerSchedulerQ16Coordinates parameters transitionFuel
    (schedulerHistoryQ16Label transitionFuel)
    (exactPlainRomExposureCursor configuration hidden)

#print axioms q16CandidateCounterOfInput?
#print axioms RootQ16HistoryPhase.afterVerifierInput
#print axioms rootQ16HistoryPhase
#print axioms rootQ16PreferredSlotFromHistory
#print axioms schedulerHistoryQ16Label
#print axioms scheduler_history_q16_label_at_fork_output
#print axioms exactPlainRomHistoryQ16Router
#print axioms exactPlainRomHistoryQ16Coordinates

end

end AspisK1.V7Tag73SchedulerHistoryQ16Router
