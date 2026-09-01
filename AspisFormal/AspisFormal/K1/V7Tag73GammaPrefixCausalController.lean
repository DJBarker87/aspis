import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Pre-answer causal controller for the gamma duplex prefix

The root verifier's gamma sampler starts immediately after the first verifier
batch-nonce absorption. The controller recognizes that exact grammar before
the boundary answer is exposed, installs the returned digest as block zero's
producer afterwards, and labels every later output/advance sibling from its
already-known producer digest. No label depends on the answer it names.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73GammaPrefixCausalController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- Only literal fresh verifier calls can arm or extend the root gamma chain.
Adversary and restoration actors, explicit fork coordinates, and padding are
not assigned a verifier-stage role. -/
def unifiedVerifierInputBeforeAnswer?
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Option ShaInput :=
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      if actor = .verifier then some input else none
  | .forkOutput .. | .forkAdvance .. | .halted | .transitionLimit => none

/-- Exact root boundary grammar: 32-byte previous digest, absorb domain,
batch-nonce label, and the deployed eight-byte nonce. -/
def isGammaPrefixBoundaryInput (input : ShaInput) : Bool :=
  input.length = 42 &&
    input[32]? = some domAbsorb &&
    input[33]? = some batchWorkNonceLabel

@[simp] theorem literal_batch_nonce_is_gamma_prefix_boundary
    (digest : Digest256) (nonce : NonceBytes) :
    isGammaPrefixBoundaryInput
        (bytes digest ++ [domAbsorb, batchWorkNonceLabel] ++ bytes nonce) =
      true := by
  simp [isGammaPrefixBoundaryInput]

structure GammaPrefixProducer where
  digest : Digest256
  block : Fin 12
  sourceInput : ShaInput
  deriving DecidableEq, Repr

structure GammaPrefixControllerMemory where
  boundarySeen : Bool
  producers : List GammaPrefixProducer
  usedSlots : Finset GammaPrefixDigestSlot
  deriving DecidableEq

def inactiveGammaPrefixMemory : GammaPrefixControllerMemory :=
  { boundarySeen := false, producers := [], usedSlots := ∅ }

def gammaPrefixOutputSlot? (producers : List GammaPrefixProducer)
    (input : ShaInput) : Option GammaPrefixDigestSlot :=
  (producers.find? fun producer ↦
    decide (input = bytes producer.digest ++ [domSqueeze])).map
      (fun producer ↦ (producer.block, false))

def gammaPrefixAdvanceSlot? (producers : List GammaPrefixProducer)
    (input : ShaInput) : Option GammaPrefixDigestSlot :=
  (producers.find? fun producer ↦
    decide (input = bytes producer.digest ++ [domAdvance])).map
      (fun producer ↦ (producer.block, true))

def gammaPrefixPreferredSlot
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) : Option GammaPrefixDigestSlot :=
  match unifiedVerifierInputBeforeAnswer? transitionFuel state.cursor with
  | none => none
  | some input =>
      let candidate := (gammaPrefixOutputSlot? state.memory.producers input).or
        (gammaPrefixAdvanceSlot? state.memory.producers input)
      match candidate with
      | none => none
      | some slot =>
          if slot ∈ state.memory.usedSlots then none else some slot

/-- An advance answer becomes the producer of the next block, if the next
block remains inside the twelve-block deployed cap. -/
def extendGammaPrefixProducers (producers : List GammaPrefixProducer)
    (input : ShaInput) (answer : Digest256) : List GammaPrefixProducer :=
  match producers.find? fun producer ↦
      decide (input = bytes producer.digest ++ [domAdvance]) with
  | none => producers
  | some producer =>
      if bounded : producer.block.val + 1 < 12 then
        producers ++ [GammaPrefixProducer.mk answer
          ⟨producer.block.val + 1, bounded⟩ input]
      else
        producers

def gammaPrefixAfterMemory
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory)
    (answer : Digest256) : GammaPrefixControllerMemory :=
  match unifiedVerifierInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input =>
      let nextUsed :=
        match gammaPrefixPreferredSlot transitionFuel state with
        | none => state.memory.usedSlots
        | some slot => insert slot state.memory.usedSlots
      if !state.memory.boundarySeen && isGammaPrefixBoundaryInput input then
        { boundarySeen := true
          producers := [{ digest := answer, block := 0, sourceInput := input }]
          usedSlots := nextUsed }
      else
        { boundarySeen := state.memory.boundarySeen
          producers := extendGammaPrefixProducers state.memory.producers
            input answer
          usedSlots := nextUsed }

def gammaPrefixCausalController
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      GammaPrefixDigestSlot GammaPrefixControllerMemory where
  preferredSlot := gammaPrefixPreferredSlot transitionFuel
  afterMemory := gammaPrefixAfterMemory transitionFuel

/-- Exact compiler router obtained from the root-verifier gamma controller. -/
def exactCompilerGammaPrefixRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalGammaPrefixRouter parameters :=
  exactCompilerIndexedGammaPrefixRouter parameters transitionFuel
    (gammaPrefixCausalController transitionFuel) inactiveGammaPrefixMemory
    cursor

/-- Concrete residual/gamma coordinates for the literal unified scheduler. -/
def exactCompilerGammaPrefixCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerCausalGammaPrefixCoordinates parameters
    (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)

@[simp] theorem gamma_prefix_controller_preferred
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) :
    (gammaPrefixCausalController transitionFuel).preferredSlot state =
      gammaPrefixPreferredSlot transitionFuel state := by
  rfl

@[simp] theorem gamma_prefix_controller_after_memory
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) (answer : Digest256) :
    (gammaPrefixCausalController transitionFuel).afterMemory state answer =
      gammaPrefixAfterMemory transitionFuel state answer := by
  rfl

/-- At the first verifier batch-nonce boundary the returned digest is the
unique initial producer, and the controller cannot have selected a gamma slot
at that boundary from its empty initial inventory. -/
theorem gamma_prefix_after_initial_boundary
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedVerifierInputBeforeAnswer? transitionFuel
      state.cursor = some input)
    (unseen : state.memory.boundarySeen = false)
    (empty : state.memory.producers = [])
    (boundary : isGammaPrefixBoundaryInput input = true) :
    gammaPrefixAfterMemory transitionFuel state answer =
      { boundarySeen := true
        producers := [{ digest := answer, block := 0, sourceInput := input }]
        usedSlots := state.memory.usedSlots } := by
  simp [gammaPrefixAfterMemory, inputExact, unseen, empty,
    gammaPrefixPreferredSlot, boundary, gammaPrefixOutputSlot?,
    gammaPrefixAdvanceSlot?]

#print axioms unifiedVerifierInputBeforeAnswer?
#print axioms literal_batch_nonce_is_gamma_prefix_boundary
#print axioms gammaPrefixPreferredSlot
#print axioms gammaPrefixAfterMemory
#print axioms gammaPrefixCausalController
#print axioms exactCompilerGammaPrefixRouter
#print axioms exactCompilerGammaPrefixCoordinates
#print axioms gamma_prefix_after_initial_boundary

end

end AspisK1.V7Tag73GammaPrefixCausalController
