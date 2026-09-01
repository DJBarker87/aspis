import AspisFormal.K1.V7Tag73ExactFixedOperationalNodeExecution
import AspisFormal.K1.V7Tag73ExactCompilerTargetClean
import AspisFormal.K1.V7Tag73PreparedRestorationRoles

/-!
# Exact programmed coordinates of operational restoration nodes

The concrete restoration client samples each nonroot fork as two adjacent
master-tape coordinates and installs those values into the child's prover
entry oracle.  This file exports that fact from the literal operational-node
execution certificate.  It is the source endpoint needed by cache-aware
challenge replay: a later cached gamma call must resolve to an already sampled
fork coordinate, not to independently chosen randomness.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedOperationalNodeProgramming

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactCompilerTargetClean

universe u

/-- A literal successful operational node installs exactly the output and
advance answers carried by its adjacent scheduled fork pair. -/
theorem projected_restoration_node_installs_scheduled_pair
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final)
      startProgram environment configuration fullTrace accumulator child) :
    ConcretePairInstalledExactly execution.prepared.programmingBase
      child.proverEntryOracle execution.prepared.outputInput
      execution.prepared.advanceInput execution.scheduled.forkOutput
      execution.scheduled.forkAdvance := by
  have ready :
      programConcretePair configuration.oracleLimits
          configuration.pairProgrammingOrder
          execution.prepared.programmingBase execution.prepared.outputInput
          execution.prepared.advanceInput execution.scheduled.forkOutput
          execution.scheduled.forkAdvance =
        .ready child.proverEntryOracle := by
    simpa [ScheduledForkCoins.configuration, scheduledForkConfiguration]
      using execution.programmingExact
  exact program_concrete_pair_ready_installs_exact_coordinates
    configuration.oracleLimits configuration.pairProgrammingOrder
      execution.prepared.programmingBase child.proverEntryOracle
        execution.prepared.outputInput execution.prepared.advanceInput
          execution.scheduled.forkOutput execution.scheduled.forkAdvance
            ready

/-- The programmed output input resolves to the literal output coordinate of
the node's scheduled master-tape pair. -/
theorem projected_restoration_node_output_lookup_exact
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final)
      startProgram environment configuration fullTrace accumulator child) :
    (lookupEntry child.proverEntryOracle execution.prepared.outputInput).map
        TableEntry.output = some execution.scheduled.forkOutput := by
  exact (projected_restoration_node_installs_scheduled_pair execution).outputInstalled

/-- The programmed advance input resolves to the literal advance coordinate
of the same adjacent scheduled master-tape pair. -/
theorem projected_restoration_node_advance_lookup_exact
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final)
      startProgram environment configuration fullTrace accumulator child) :
    (lookupEntry child.proverEntryOracle execution.prepared.advanceInput).map
        TableEntry.output = some execution.scheduled.forkAdvance := by
  exact (projected_restoration_node_installs_scheduled_pair execution).advanceInstalled

/-- Every operational child has a source-derived pre-answer squeeze role, and
the scheduled pair uses exactly that role's two grammar inputs.  Keeping the
owner and block in the witness is essential for the later gamma-lineage
induction; no role is inferred from a post-answer value. -/
theorem projected_restoration_node_has_exact_fork_role
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final)
      startProgram environment configuration fullTrace accumulator child) :
    exists role : PreparedRestorationPairRole,
      preparedRestorationPairRole? execution.prepared = some role ∧
      execution.scheduled.outputInput = role.outputInput ∧
      execution.scheduled.advanceInput = role.advanceInput ∧
      role.outputInput =
        bytes execution.prepared.transition.before.core.digest ++ [domSqueeze] ∧
      role.advanceInput =
        bytes execution.prepared.transition.before.core.digest ++ [domAdvance] := by
  obtain ⟨role, roleExact, inputsExact, outputExact, advanceExact⟩ :=
    ready_preparation_has_pair_role startProgram configuration accumulator
      execution.prepared.request execution.prepared execution.preparationExact
  have roleInputs :
      role.outputInput = execution.prepared.outputInput ∧
        role.advanceInput = execution.prepared.advanceInput := by
    simpa [PreparedRestorationPairRole.inputs] using congrArg id inputsExact
  exact ⟨role, roleExact,
    execution.scheduledOutputInputExact.trans roleInputs.1.symm,
    execution.scheduledAdvanceInputExact.trans roleInputs.2.symm,
    outputExact, advanceExact⟩

#print axioms projected_restoration_node_installs_scheduled_pair
#print axioms projected_restoration_node_output_lookup_exact
#print axioms projected_restoration_node_advance_lookup_exact
#print axioms projected_restoration_node_has_exact_fork_role

end AspisK1.V7Tag73ExactFixedOperationalNodeProgramming
