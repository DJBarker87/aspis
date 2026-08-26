import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition

/-!
# Fixed-instance client extraction event for exact Tag-73 K1.6

The restoration client is run by the same result-carrying scheduler as the
compiler coupling.  A successful extraction for a fixed-instance argument of
knowledge must return a witness for the public instance fixed before oracle
access; a witness for a different root instance is not counted.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedClientExtraction

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactClientKnowledgeComposition

noncomputable section

/-- Actual completed-client event returning a valid witness for the one fixed
public instance.  Both the root and the witness come from the scheduler
terminal; there is no caller-supplied result map. -/
def exactFixedPlainRomValidClientExtractionEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ root clientRun witness,
    exactPlainRomCompleted? transitionFuel configuration sample =
        some (root, clientRun) ∧
      root.adversaryValue.1.publicProof.publicInstance = fixedInstance ∧
      clientRun.halt = .returned (some witness) ∧
      relation fixedInstance witness}

theorem mem_exact_fixed_plain_rom_valid_client_extraction_event_iff
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactFixedPlainRomValidClientExtractionEvent transitionFuel
        configuration fixedInstance relation ↔
      ∃ root clientRun witness,
        exactPlainRomCompleted? transitionFuel configuration sample =
            some (root, clientRun) ∧
          root.adversaryValue.1.publicProof.publicInstance = fixedInstance ∧
          clientRun.halt = .returned (some witness) ∧
          relation fixedInstance witness := by
  rfl

def exactFixedPlainRomValidClientExtractionProbability
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop) : ENNReal :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
    (exactFixedPlainRomValidClientExtractionEvent transitionFuel configuration
      fixedInstance relation)

/-- Forgetting the fixed-instance equality and rewriting the relation along
that equality embeds fixed extraction into the older root-indexed event. -/
theorem exact_fixed_valid_extraction_subset_root_indexed
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop) :
    exactFixedPlainRomValidClientExtractionEvent transitionFuel configuration
        fixedInstance relation ⊆
      exactPlainRomValidClientExtractionEvent transitionFuel configuration
        relation := by
  intro sample member
  rcases member with
    ⟨root, clientRun, witness, completed, fixedRoot, returned, valid⟩
  refine ⟨root, clientRun, witness, completed, returned, ?_⟩
  rw [fixedRoot]
  exact valid

#print axioms mem_exact_fixed_plain_rom_valid_client_extraction_event_iff
#print axioms exact_fixed_valid_extraction_subset_root_indexed

end

end AspisK1.V7Tag73ExactFixedClientExtraction
