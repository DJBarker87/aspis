import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Events
import AspisFormal.K1.V7Tag73ExactFixedK16Closure

/-!
# Correct restoration-wide Tag-73 K1.2--K1.6 assembly

The older file named `ExactRestoredConcreteK16Assembly` changes only K1.5;
its stage package is still `exactTag73ProofRelevantStages`, whose K1.2--K1.4
classifiers inspect the fixed accepted root.  This module assembles the actual
restoration-wide package `exactTag73RestoredOperationalStages` instead.

K1.2 is administrative and has no separate error event: authentication and
complete-tree extraction are performed for every candidate inside the
restoration-wide K1.3 classifier.  Consequently the K1.3 numerical term is
the complete restored K1.2/K1.3 term.  K1.4 is bounded by the exact width-29
event on the node selected by K1.3, and K1.5 is the literal error event of the
supplied restored-node client classifier.

This file changes no cryptographic bound.  It prevents a root-only stage
package from being presented as restoration-wide and gives the final source
proof three exact event endpoints to discharge.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK16Assembly

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredOperationalStages
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Error ledger for the corrected stage dependency order.  K1.2 is zero
because its authentication/extraction failures are classified by K1.3. -/
def exactRestoredOperationalUpstreamTerms
    (k13 k14 k15 : ENNReal) : ConcreteUpstreamErrorTerms where
  k12TwoTreeMerkle208 := 0
  k13CircleListDecoding := k13
  k14CoherentChainSelection := k14
  k15SpendWitnessRecovery := k15

/-- The administrative K1.2 stage of the restoration-wide package cannot
return an error. -/
theorem exact_restored_operational_stages_k12_error_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (k15 : ExactRestoredOperationalK15Classifier transitionFuel configuration
      projection fixedInstance relation decoder binding) :
    k12TwoTreeMerkle208ErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) = ∅ := by
  ext sample
  constructor
  · rintro ⟨input, failure⟩
    rcases failure with ⟨failure⟩
    exact failure.elim
  · simp

/-- Final K1.6 assembly over the actual restoration-wide K1.2--K1.5 stages.
The only upstream premises are the three literal events exposed by those
stages; there is no fixed-root K1.3/K1.4 alias in this theorem. -/
theorem exact_tag73_restored_operational_k16_aok_raw
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
    (binding : InitialProjectionBinding decoder)
    (k15 : ExactRestoredOperationalK15Classifier transitionFuel configuration
      projection fixedInstance relation decoder binding)
    (k13Error k14Error k15Error : ENNReal)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredOperationalK13FailureEvent transitionFuel
            configuration projection fixedInstance decoder) ≤ k13Error)
    (k14Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredOperationalK14Width29Event transitionFuel
            configuration projection fixedInstance decoder) ≤ k14Error)
    (k15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73RestoredOperationalK15FailureEvent k15) ≤ k15Error) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError
          (exactRestoredOperationalUpstreamTerms k13Error k14Error k15Error)
          parameters := by
  let stages := exactTag73RestoredOperationalStages transitionFuel configuration
    projection fixedInstance relation decoder binding k15
  have k12Measure : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages 0 := by
    unfold K12TwoTreeMerkle208ErrorMeasureBound
    rw [exact_restored_operational_stages_k12_error_event_eq_empty k15]
    simp
  have k13Measure : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      k13Error := by
    unfold K13CircleListDecodeErrorMeasureBound
    rw [exact_restored_stages_k13_error_event_eq k15]
    exact k13Bound
  have k14Measure : K14CoherentChainErrorMeasureBound hiddenLaw stages
      k14Error := by
    unfold K14CoherentChainErrorMeasureBound
    exact le_trans
      (measure_mono (exact_restored_stages_k14_error_subset_width29 k15))
      k14Bound
  have k15Measure : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      k15Error := by
    unfold K15SpendWitnessErrorMeasureBound
    rw [exact_restored_stages_k15_error_event_eq k15]
    exact k15Bound
  exact exact_fixed_tag73_k16_classical_rom_aok_raw hiddenLaw transitionFuel
    configuration projection fixedInstance relation transitionRoom
    driverCoversProtocol runtimeReserves cutoffBeyondCap stages
    (exactRestoredOperationalUpstreamTerms k13Error k14Error k15Error)
    k12Measure k13Measure k14Measure k15Measure

#print axioms exact_restored_operational_stages_k12_error_event_eq_empty
#print axioms exact_tag73_restored_operational_k16_aok_raw

end

end AspisK1.V7Tag73ExactRestoredOperationalK16Assembly
