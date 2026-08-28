import AspisFormal.K1.V7Tag73OperationalNodeCertificate

/-!
# Pre-answer roles retained by restoration preparation

The executable restoration preparer selects an actual future-free verifier
transition before either fork answer is sampled.  A selected squeeze
transition already contains its `SqueezeOwner` and block number.  This file
projects that data into a ghost descriptor and proves that every executable
`.ready` preparation has such a descriptor.

The descriptor erases to exactly the input pair and fork header already used
by `dispatchPreparedRestoration`.  No scheduler constructor is changed here;
in particular, the theorem also makes precise that the current `forkPair`
constructor retains the erasure but not the role.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreparedRestorationRoles

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73OperationalNodeCertificate

noncomputable section

universe u

/-- Data available at preparation time for both halves of one restored
squeeze.  The two `RawQueryRole`s are computed fields, not propositions. -/
structure PreparedRestorationPairRole where
  owner : SqueezeOwner
  block : Nat
  outputInput : ShaInput
  advanceInput : ShaInput
  deriving Repr

def PreparedRestorationPairRole.outputRole
    (role : PreparedRestorationPairRole) : RawQueryRole :=
  .squeezeOutput role.owner role.block

def PreparedRestorationPairRole.advanceRole
    (role : PreparedRestorationPairRole) : RawQueryRole :=
  .squeezeAdvance role.owner role.block

def PreparedRestorationPairRole.inputs
    (role : PreparedRestorationPairRole) : ShaInput × ShaInput :=
  (role.outputInput, role.advanceInput)

/-- Read the role from the selected transition itself.  Malformed manually
constructed preparations remain total and return `none`. -/
def preparedRestorationPairRole?
    {Statement Proof Payload : Type*}
    (prepared : PreparedConcreteRestoration Statement Proof Payload) :
    Option PreparedRestorationPairRole :=
  match prepared.transition.event with
  | .verifier (.squeezePair owner block) _reply =>
      some
        { owner := owner
          block := block
          outputInput := prepared.outputInput
          advanceInput := prepared.advanceInput }
  | _ => none

@[simp] theorem prepared_pair_role_inputs
    {Statement Proof Payload : Type*}
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (projected : preparedRestorationPairRole? prepared = some role) :
    role.inputs = (prepared.outputInput, prepared.advanceInput) := by
  unfold preparedRestorationPairRole? at projected
  cases eventExact : prepared.transition.event <;>
    simp [eventExact] at projected
  next action reply =>
    cases action <;> simp at projected
    next owner block =>
      cases projected
      rfl

/-- Successful executable preparation cannot take the `none` branch of the
role projection.  This follows from the preparer's existing exact pair-input
theorem, not from an added well-formedness field. -/
theorem ready_preparation_has_pair_role
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    ∃ role : PreparedRestorationPairRole,
      preparedRestorationPairRole? prepared = some role ∧
      role.inputs = (prepared.outputInput, prepared.advanceInput) ∧
      role.outputInput =
        bytes prepared.transition.before.core.digest ++ [domSqueeze] ∧
      role.advanceInput =
        bytes prepared.transition.before.core.digest ++ [domAdvance] := by
  have pairExact := prepare_from_start_ready_pair_inputs_exact startProgram
    configuration accumulator request prepared ready
  unfold squeezePairInputsOfTransition at pairExact
  cases eventExact : prepared.transition.event <;>
    simp [eventExact] at pairExact
  next action reply =>
    cases action <;> simp at pairExact
    next owner block =>
      have outputExact := pairExact.1
      have advanceExact := pairExact.2
      let role : PreparedRestorationPairRole :=
        { owner := owner
          block := block
          outputInput := prepared.outputInput
          advanceInput := prepared.advanceInput }
      refine ⟨role, ?_, rfl, ?_, ?_⟩
      · simp [preparedRestorationPairRole?, eventExact, role]
      · simpa [role] using outputExact.symm
      · simpa [role] using advanceExact.symm

/-- The header of the current scheduler fork, separated from its answer-
dependent continuation. -/
structure PreparedForkHeader where
  frozenHistory : List QueryRecord
  outputInput : ShaInput
  advanceInput : ShaInput
  template : AtomicPairReplayConfiguration

def preparedForkHeader
    {Statement Proof Payload : Type*}
    (configuration : ConcreteRestorationConfiguration)
    (prepared : PreparedConcreteRestoration Statement Proof Payload) :
    PreparedForkHeader :=
  { frozenHistory := prepared.programmingBase.history
    outputInput := prepared.outputInput
    advanceInput := prepared.advanceInput
    template := canonicalForkTemplate configuration }

/-- Observe only the role-erased header of an emitted fork. -/
def schedulerNativeForkHeader?
    {globalOracleCalls : Nat} {Result : Type*}
    (cursor : SchedulerNativeCursor globalOracleCalls Result) :
    Option PreparedForkHeader :=
  match cursor with
  | .forkPair frozenHistory _pairRoom outputInput advanceInput template _next =>
      some { frozenHistory, outputInput, advanceInput, template }
  | .forkAdvance frozenHistory _pairRoom outputInput advanceInput template
      _forkOutput _next =>
      some { frozenHistory, outputInput, advanceInput, template }
  | .machine .. | .returned .. | .failed .. => none

/-- Erasing the ghost owner/block yields the exact input fields of the fork
header used by the current dispatcher. -/
theorem prepared_pair_role_erases_to_fork_header
    {Statement Proof Payload : Type*}
    (configuration : ConcreteRestorationConfiguration)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (projected : preparedRestorationPairRole? prepared = some role) :
    role.inputs =
      ((preparedForkHeader configuration prepared).outputInput,
        (preparedForkHeader configuration prepared).advanceInput) := by
  exact prepared_pair_role_inputs prepared role projected

/-- Under the three literal dispatcher guards, the current implementation
emits exactly the role-erased fork header.  The observer deliberately erases
the existing answer-dependent continuation closed over `prepared`. -/
theorem dispatch_prepared_restoration_emits_role_erased_fork
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (prefixCoherent : HistoryTotalCoherent prepared.programmingBase)
    (globalLimit : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    schedulerNativeForkHeader?
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume) =
      some (preparedForkHeader configuration prepared) := by
  unfold dispatchPreparedRestoration
  rw [dif_pos prefixCoherent, dif_pos globalLimit, dif_pos pairRoom]
  rfl

#print axioms preparedRestorationPairRole?
#print axioms prepared_pair_role_inputs
#print axioms ready_preparation_has_pair_role
#print axioms prepared_pair_role_erases_to_fork_header
#print axioms dispatch_prepared_restoration_emits_role_erased_fork

end

end AspisK1.V7Tag73PreparedRestorationRoles
