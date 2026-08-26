import AspisFormal.K1.V7Tag73RootSuccessForcesFullCompletion
import AspisFormal.K1.V7Tag73CompletedFullRunProjection

/-!
# Root-forced full Tag-73 operational projection

This thin composition exposes the exact API consumed by the resource and
legal-execution layers: a successful initial-only run forces a literal full
completed terminal, and that terminal is immediately inverted into its two
projected root prefixes, same-tape runtime, actual residual client equation,
and append-only node-store invariant.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RootForcedFullProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73RootSuccessForcesFullCompletion

noncomputable section

/-- The complete operational object forced by a successful source root.  The
terminal equation is retained alongside its structured inversion so clients
never need to rediscover which returned value was observed. -/
structure RootForcedCompletedFullProjection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload) : Type where
  clientRun : ConcreteRestorationClientRun Statement Proof Payload Result
  fullCompleted :
    (runExactPlainRom transitionFuel configuration sample).terminal =
      .returned (.completed rootRuntime clientRun)
  projection : CompletedExactPlainRomRootAndStoreProjection transitionFuel
    configuration sample rootRuntime clientRun

/-- Experiment-facing constructor with no full-terminal premise. -/
theorem completed_root_forces_full_projection_nonempty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (transitionRoom : 3 ≤ transitionFuel)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed rootRuntime rootClientRun)) :
    Nonempty (RootForcedCompletedFullProjection transitionFuel configuration
      sample rootRuntime) := by
  obtain ⟨clientRun, fullCompleted⟩ :=
    completed_exact_plain_rom_root_forces_full_completion transitionFuel
      configuration sample rootRuntime rootClientRun transitionRoom
        rootCompleted
  exact ⟨
    { clientRun := clientRun
      fullCompleted := fullCompleted
      projection :=
        completed_exact_plain_rom_gives_root_and_store_projection transitionFuel
          (by omega) configuration sample rootRuntime clientRun fullCompleted }⟩

/-- Chosen proof-relevant terminal projection, backed by the proved nonempty
package above. -/
noncomputable def completed_root_forces_full_projection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (rootRuntime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Proof Payload)
    (rootClientRun : ConcreteRestorationClientRun Statement Proof Payload
      PUnit)
    (transitionRoom : 3 ≤ transitionFuel)
    (rootCompleted :
      (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed rootRuntime rootClientRun)) :
    RootForcedCompletedFullProjection transitionFuel configuration sample
      rootRuntime :=
  Classical.choice
    (completed_root_forces_full_projection_nonempty transitionFuel configuration
      sample rootRuntime rootClientRun transitionRoom rootCompleted)

#print axioms completed_root_forces_full_projection

end

end AspisK1.V7Tag73RootForcedFullProjection
