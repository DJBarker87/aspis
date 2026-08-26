import AspisFormal.K1.V7Tag73ExactLegalSameTapeEvent

/-!
# Fixed-instance source and clean events for exact Tag-73 K1.6

The plain classical-ROM theorem is a fixed-instance statement.  Internal
agreement between a returned proof and its own context is not enough: the
program, release, statement digest, attempt/proof-account identifier, and the
opaque statement must already be fixed before the adversary receives oracle
access.

This leaf intersects the executable source-refinement event with the literal
public instance returned by the actual initial-only scheduler.  It then forms
the clean event by subtracting the same operational causal target event used
by the full result-carrying scheduler.  No caller supplies a trace cover or an
acceptance implication.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedInstanceEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73ExactLegalSameTapeEvent

noncomputable section

/-! ## The literal fixed public instance -/

/-- Public instance returned by the actual initial-only scheduler, when its
two totalized machine stages completed. -/
def exactPlainRomRootPublicInstance?
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Option (PublicInstance Statement) :=
  match (runExactPlainRomRoot transitionFuel configuration sample).terminal with
  | .returned (.completed runtime _clientRun) =>
      some runtime.adversaryValue.1.publicProof.publicInstance
  | .returned (.initialFailure _) | .failed _ => none

/-- Executable strict source acceptance restricted to one public instance
fixed before the hidden adversary tape and master oracle tape are sampled. -/
def exactFixedSourceRefinementEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactSourceRefinementEvent transitionFuel configuration projection ∩
    {sample |
      exactPlainRomRootPublicInstance? transitionFuel configuration sample =
        some fixedInstance}

/-- The fixed-instance clean event is the fixed source event minus the exact
adaptive target event of the same full scheduler cursor. -/
def exactFixedPlainRomLegalSameTapeEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactFixedSourceRefinementEvent transitionFuel configuration projection
      fixedInstance \
    exactPlainRomTargetEvent transitionFuel configuration

theorem mem_exact_fixed_source_refinement_event_iff
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactFixedSourceRefinementEvent transitionFuel configuration
        projection fixedInstance ↔
      sample ∈ exactSourceRefinementEvent transitionFuel configuration
          projection ∧
        exactPlainRomRootPublicInstance? transitionFuel configuration sample =
          some fixedInstance := by
  rfl

theorem exact_fixed_source_subset_legal_union_target
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement) :
    exactFixedSourceRefinementEvent transitionFuel configuration projection
        fixedInstance ⊆
      exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance ∪
        exactPlainRomTargetEvent transitionFuel configuration := by
  intro sample accepted
  by_cases hit : sample ∈ exactPlainRomTargetEvent transitionFuel
      configuration
  · exact Or.inr hit
  · exact Or.inl ⟨accepted, hit⟩

/-! ## Constructed fixed root certificate -/

/-- The clean root certificate together with equality to the public instance
fixed before the experiment. -/
structure ExactFixedCleanSourceRootProjection
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) where
  base : ExactCleanSourceRootProjection transitionFuel configuration projection
    sample
  fixedInstanceExact :
    base.runtime.adversaryValue.1.publicProof.publicInstance = fixedInstance

/-- Every member of the fixed clean event inhabits an exact root certificate
whose complete public instance is the one fixed before sampling. -/
theorem fixed_legal_event_has_exact_clean_root
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (driverCoversProtocol :
      AspisK1.V7Tag73CanonicalFutureFreeFuel.tag73CanonicalDriverFuelCap ≤
        configuration.machine.driverFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance) :
    Nonempty (ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) := by
  rcases member with ⟨⟨sourceMember, fixedExact⟩, targetMiss⟩
  have base := legal_same_tape_event_constructs_exact_clean_root transitionFuel
    positive configuration projection driverCoversProtocol sample
      ⟨sourceMember, targetMiss⟩
  refine ⟨⟨base, ?_⟩⟩
  change exactPlainRomRootPublicInstance? transitionFuel configuration sample =
    some fixedInstance at fixedExact
  unfold exactPlainRomRootPublicInstance? at fixedExact
  rw [base.rootCompleted] at fixedExact
  simpa using fixedExact

/-- Canonical proof-only fixed-instance certificate selected from the proved
inhabited operational projection. -/
noncomputable def fixed_legal_event_constructs_exact_clean_root
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (driverCoversProtocol :
      AspisK1.V7Tag73CanonicalFutureFreeFuel.tag73CanonicalDriverFuelCap ≤
        configuration.machine.driverFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance) :
    ExactFixedCleanSourceRootProjection transitionFuel configuration projection
      fixedInstance sample :=
  Classical.choice
    (fixed_legal_event_has_exact_clean_root transitionFuel positive
      configuration projection fixedInstance driverCoversProtocol sample member)

/-- The checked raw context, all four deployed binding fields, and the opaque
statement are literally those of the fixed public instance. -/
theorem fixed_clean_root_preserves_complete_instance
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) :
    fixed.base.runtime.adversaryValue.rawMessages.context =
        fixedInstance.context ∧
      fixed.base.runtime.adversaryValue.1.publicProof.publicInstance.statement =
        fixedInstance.statement := by
  have contextExact :
      fixed.base.runtime.adversaryValue.rawMessages.context =
        fixed.base.runtime.adversaryValue.1.publicProof.publicInstance.context := by
    simpa [CheckedRawTag73AdversaryReturnedValue.rawMessages] using
      (checked_raw_return_context_is_exact
        fixed.base.runtime.adversaryValue)
  have publicContextExact := congrArg
    (fun publicInstance : PublicInstance Statement => publicInstance.context)
    fixed.fixedInstanceExact
  have publicStatementExact := congrArg
    (fun publicInstance : PublicInstance Statement => publicInstance.statement)
    fixed.fixedInstanceExact
  exact ⟨contextExact.trans publicContextExact, publicStatementExact⟩

/-- Expanded byte-level binding statement.  In deployed Tag-73 the proof
account identifier is exactly the attempt identifier, so both equal the fixed
32-byte context field. -/
theorem fixed_clean_root_binding_fields_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) :
    let bindings := FixedBindings.ofContext
      fixed.base.runtime.adversaryValue.rawMessages.context
    bindings.programId = fixedInstance.context.programId ∧
      bindings.releaseBinding = fixedInstance.context.releaseBinding ∧
      bindings.statementDigest = fixedInstance.context.statementDigest ∧
      bindings.attemptId = fixedInstance.context.attemptId ∧
      bindings.proofAccountId = fixedInstance.context.attemptId := by
  have contextExact :=
    (fixed_clean_root_preserves_complete_instance fixed).1
  rw [contextExact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms mem_exact_fixed_source_refinement_event_iff
#print axioms exact_fixed_source_subset_legal_union_target
#print axioms fixed_legal_event_has_exact_clean_root
#print axioms fixed_legal_event_constructs_exact_clean_root
#print axioms fixed_clean_root_preserves_complete_instance
#print axioms fixed_clean_root_binding_fields_exact

end

end AspisK1.V7Tag73ExactFixedInstanceEvent
