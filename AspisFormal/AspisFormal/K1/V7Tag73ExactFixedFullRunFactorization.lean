import AspisFormal.K1.V7Tag73ExactFixedOperationalRootPackage
import AspisFormal.K1.V7Tag73FullCursorClientLineageLift

/-!
# Fixed-instance full-run factorization for exact Tag-73

A member of the fixed clean source event already constructs the deployed root,
forces completion of the result-carrying scheduler, and supplies the actual
projected root prefixes.  This leaf turns those constructed objects into the
literal chronological factorization needed by the restoration-client
induction:

* the two root machine traces occur first;
* the concrete client starts on the untouched suffix of the same master tape;
* its transition fuel is the exact continuation fuel computed by the two
  projected root prefixes; and
* the client's ordinary terminal is the client run returned by the full
  scheduler.

The public instance and hidden-tape identity are retained from the same
operational package.  No trace equation, restoration function, witness,
extraction result, or compiler conclusion is supplied by a caller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedFullRunFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerResultMapSemantics
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedOperationalRootPackage
open AspisK1.V7Tag73FullCursorClientLineageLift

noncomputable section

/-! ## Canonical data read from the constructed package -/

/-- The literal adversary then verifier records emitted before the client. -/
def exactFixedRootRecords
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanCompletedRootPackage transitionFuel configuration
      projection fixedInstance sample) : List UnifiedExposureRecord :=
  fullProjectedRootRecords package.full.projection.rootPrefixes

/-- The exact scheduler transition fuel after both projected root machines. -/
def exactFixedClientContinuationFuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (package : ExactFixedCleanCompletedRootPackage transitionFuel configuration
      projection fixedInstance sample) : Nat :=
  fullProjectedRootClientTransitionFuel transitionFuel
    package.full.projection.rootPrefixes

/-- The literal unmapped concrete-client tail on the untouched answer suffix. -/
def exactFixedComputedClientTailRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanCompletedRootPackage transitionFuel configuration
      projection fixedInstance sample) :
    SchedulerNativeRun
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  fullProjectedConcreteClientTailRun transitionFuel configuration sample
    package.fixedRoot.base.runtime package.full.projection.rootPrefixes

/-! ## Proof-relevant exact factorization -/

/-- Exact chronological facts derived from one already constructed completed
root package.  All data in the statements is canonical: only proofs are stored
in this certificate. -/
structure ExactFixedFullRunFactorization
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanCompletedRootPackage transitionFuel configuration
      projection fixedInstance sample) : Prop where
  fullRunExact :
    runSchedulerNativeListRunFrom transitionFuel transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) =
      let tail := exactFixedComputedClientTailRun transitionFuel configuration
        sample package
      { terminal := mapSchedulerNativeTerminalResult
          (fun clientResult => SchedulerNativePlainRomResult.completed
            package.fixedRoot.base.runtime clientResult)
          tail.terminal
        trace := exactFixedRootRecords package ++ tail.trace }
  computedClientTerminalExact :
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      package).terminal = .returned package.full.clientRun
  computedClientListTerminalExact :
    runSchedulerNativeListTerminalFrom transitionFuel
        (exactFixedClientContinuationFuel transitionFuel package)
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment package.fixedRoot.base.runtime.node
          configuration.restorationConfiguration configuration.restorationFuel
          configuration.client)
        package.full.projection.rootPrefixes.verifier.remaining =
      .returned package.full.clientRun
  sameHiddenTapeIdentity :
    package.fixedRoot.base.runtime.tapeIdentity =
      configuration.machine.tapeIdentity sample.1
  fixedInstanceExact :
    package.fixedRoot.base.runtime.adversaryValue.1.publicProof.publicInstance =
      fixedInstance

/-- The factorization is constructed solely from the completed root package
and the static three-transition scheduler reserve. -/
theorem exact_fixed_completed_root_has_full_run_factorization
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (transitionRoom : 3 ≤ transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (package : ExactFixedCleanCompletedRootPackage transitionFuel configuration
      projection fixedInstance sample) :
    ExactFixedFullRunFactorization transitionFuel configuration projection
      fixedInstance sample package := by
  refine
    { fullRunExact := ?_
      computedClientTerminalExact := ?_
      computedClientListTerminalExact := ?_
      sameHiddenTapeIdentity := completed_root_package_same_hidden_tape package
      fixedInstanceExact :=
        completed_root_package_preserves_fixed_instance package }
  · simpa [exactFixedComputedClientTailRun, exactFixedRootRecords] using
      completed_root_and_full_projection_factor_full_run transitionFuel
        transitionRoom configuration sample package.fixedRoot.base.runtime
          package.fixedRoot.base.clientRun package.full.clientRun
          package.fixedRoot.base.rootCompleted package.full.projection
  · exact completed_full_projection_computed_client_terminal_exact
      transitionFuel transitionRoom configuration sample
        package.fixedRoot.base.runtime package.fixedRoot.base.clientRun
        package.full.clientRun package.fixedRoot.base.rootCompleted
        package.full.fullCompleted package.full.projection
  · change runSchedulerNativeListTerminalFrom transitionFuel
        (fullProjectedRootClientTransitionFuel transitionFuel
          package.full.projection.rootPrefixes)
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment package.fixedRoot.base.runtime.node
          configuration.restorationConfiguration configuration.restorationFuel
          configuration.client)
        package.full.projection.rootPrefixes.verifier.remaining =
          .returned package.full.clientRun
    exact completed_full_projection_computed_client_list_terminal_exact
      transitionFuel transitionRoom configuration sample
        package.fixedRoot.base.runtime package.fixedRoot.base.clientRun
        package.full.clientRun package.fixedRoot.base.rootCompleted
        package.full.fullCompleted package.full.projection

/-! ## Direct construction from the literal fixed clean event -/

/-- Operational input precursor for K1.2--K1.5: the actual clean completed root
together with its proved full/root/client factorization. -/
structure ExactFixedCleanFullRunFactorizationPackage
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) : Type where
  root : ExactFixedCleanCompletedRootPackage transitionFuel configuration
    projection fixedInstance sample
  factorization : ExactFixedFullRunFactorization transitionFuel configuration
    projection fixedInstance sample root

/-- Every literal fixed clean-event member inhabits the exact full-run
factorization package.  Transition and driver bounds are static operational
adequacy hypotheses, not success or compiler-cover assumptions. -/
theorem fixed_legal_member_has_full_run_factorization_package
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance) :
    Nonempty (ExactFixedCleanFullRunFactorizationPackage transitionFuel
      configuration projection fixedInstance sample) := by
  let root := fixed_legal_member_completed_root_package transitionFuel
    configuration projection fixedInstance transitionRoom driverCoversProtocol
      sample member
  exact ⟨
    { root := root
      factorization := exact_fixed_completed_root_has_full_run_factorization
        transitionFuel transitionRoom configuration projection fixedInstance
          sample root }⟩

/-- Canonical proof-relevant package selected from the proved inhabitedness
theorem above. -/
noncomputable def fixed_legal_member_full_run_factorization_package
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance) :
    ExactFixedCleanFullRunFactorizationPackage transitionFuel configuration
      projection fixedInstance sample :=
  Classical.choice
    (fixed_legal_member_has_full_run_factorization_package transitionFuel
      configuration projection fixedInstance transitionRoom
        driverCoversProtocol sample member)

#print axioms exact_fixed_completed_root_has_full_run_factorization
#print axioms fixed_legal_member_has_full_run_factorization_package
#print axioms fixed_legal_member_full_run_factorization_package

end

end AspisK1.V7Tag73ExactFixedFullRunFactorization
