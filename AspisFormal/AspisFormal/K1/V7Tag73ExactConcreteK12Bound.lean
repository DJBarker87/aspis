import AspisFormal.K1.V7Tag73ExactConcreteStageAssembly
import AspisFormal.K1.V7Tag73K12ExactFailureProbability

/-!
# Concrete K1.2 bound for the assembled Tag-73 stages

The executable stage package classifies K1.2 with the literal prefix/shared-
log Merkle extractor.  Production acceptance has two deterministic source
obligations: the paired openings authenticate, and all supplied path calls
occur in the prover-prefix trace.  Under precisely those two field-level
facts, every assembled K1.2 error is one of the already counted adaptive
208-bit ROM events.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactConcreteK12Bound

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73K12ExactFailureProbability
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The two deterministic source facts needed by the exact prefix K1.2
failure reduction.  These are ordinary successful-caller properties, not a
Merkle security assumption or a probability bound. -/
structure ExactTag73K12SourceObligations
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop where
  openingsAccepted :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      accepted_two_tree_openings (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input)
  suppliedCovered :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      ExactPrefixK12SuppliedCoverage input

/-- Exact numerical K1.2 term: adaptive first-unresolved targets plus all
distinct-input collisions in the 208-bit SHA prefix. -/
def exactTag73K12ErrorBound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters) :
    ENNReal :=
  ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
      (2 ^ 256) ^ ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
      ENNReal) /
      (((2 : ENNReal) ^ 256) ^
        (exactCompilerTargetCaps parameters).length) +
    ((((exactCompilerTargetCaps parameters).length.choose 2 * 2 ^ 48) *
      (2 ^ 256) ^ ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
      ENNReal) /
      (((2 : ENNReal) ^ 256) ^
        (exactCompilerTargetCaps parameters).length)

/-- The K1.2 error event of the actual assembled stages is contained in the
already-counted exact classifier event. -/
theorem assembled_k12_error_subset_exact_classified_event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance) :
    k12TwoTreeMerkle208ErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance relation decoder decoderBinding k15) ⊆
      exactPrefixK12ClassifiedErrorEvent transitionFuel configuration projection
        fixedInstance := by
  intro sample member
  rcases member with ⟨input, error⟩
  exact ⟨input, source.openingsAccepted sample input,
    source.suppliedCovered sample input, error⟩

/-- Fully constructed K1.2 measure bound for the concrete stage package.  No
caller-supplied K1.2 numerical inequality remains. -/
theorem exact_tag73_assembled_k12_error_measure_bound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel) :
    K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw
      (exactTag73ProofRelevantStages transitionFuel configuration projection
        fixedInstance relation decoder decoderBinding k15)
      (exactTag73K12ErrorBound configuration) := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (k12TwoTreeMerkle208ErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15)) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPrefixK12ClassifiedErrorEvent transitionFuel configuration
          projection fixedInstance) :=
      measure_mono
        (assembled_k12_error_subset_exact_classified_event transitionFuel
          configuration projection fixedInstance relation decoder
          decoderBinding k15 source)
    _ ≤ exactTag73K12ErrorBound configuration := by
      exact exact_prefix_k12_classified_error_probability_le hiddenLaw
        transitionFuel configuration projection fixedInstance transitionRoom

#print axioms assembled_k12_error_subset_exact_classified_event
#print axioms exact_tag73_assembled_k12_error_measure_bound

end

end AspisK1.V7Tag73ExactConcreteK12Bound
