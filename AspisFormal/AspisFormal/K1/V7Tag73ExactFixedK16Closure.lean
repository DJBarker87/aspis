import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface
import AspisFormal.K1.V7Tag73SeededTargetArithmetic

/-!
# Exact fixed-instance classical-ROM K1.6 closure for Tag-73

The compiler side is fully constructed here.  A fixed clean source sample
produces the literal completed root/client factorization, the exact
failure-inclusive restoration-state map, and the exact operational resource
certificate.  Four explicitly typed K1.2--K1.5 classifiers consume that
sample-indexed object.  The only numerical upstream premises are four
separately named error-event bounds.

The ROM loss is not imported from BCS.  It is the exact seeded causal-target
tree bound for the actual scheduler:

`F + F.choose 2 + F * G`, divided by `2^256`,

where `F` counts every full-256 exposure and `G` counts every actor oracle
call.  This theorem is ordinary fixed-instance classical-ROM AoK; it does not
claim simulation extractability after observed programmed proofs.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactFixedK16Closure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73SeededTargetArithmetic
open AspisK1.V7Tag73CanonicalFutureFreeFuel

noncomputable section

/-! ## Exact sample-indexed K1.2--K1.5 input -/

/-- The concrete upstream input is the actual scheduler package, state map,
and resource certificate constructed in the preceding leaf. -/
abbrev ExactFixedSchedulerK12ToK15Input
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters) : Type :=
  ExactFixedOperationalStateRestorationInput transitionFuel configuration
    projection fixedInstance sample

/-- Deterministic compiler cover: membership in the literal fixed clean event
constructs the exact proof-relevant operational input. -/
theorem exact_fixed_legal_subset_operational_input
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance ⊆
      proofRelevantOperationalInputEvent
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance) := by
  intro sample member
  exact fixed_legal_member_has_operational_state_restoration_input
    transitionFuel configuration projection fixedInstance transitionRoom
      driverCoversProtocol runtimeReserves cutoffBeyondCap sample member

/-! ## Clean-event composition with the four upstream stages -/

/-- Before replacing the four event probabilities by numerical bounds, the
literal clean event is bounded by actual extraction plus their exact union
sum. -/
theorem exact_fixed_clean_probability_le_extraction_plus_stage_events
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantUpstreamRawError hiddenLaw stages := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantOperationalInputEvent
          (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
            projection fixedInstance)) :=
      measure_mono
        (exact_fixed_legal_subset_operational_input transitionFuel configuration
          projection fixedInstance transitionRoom driverCoversProtocol
            runtimeReserves cutoffBeyondCap)
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantUpstreamRawError hiddenLaw stages :=
      proof_relevant_operational_input_probability_le_extraction_plus_raw_error
        hiddenLaw transitionFuel configuration fixedInstance relation
          (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
            projection fixedInstance) stages

/-- Numerical clean-event theorem with four separately supplied K1.2--K1.5
error bounds. -/
theorem exact_fixed_clean_probability_le_extraction_plus_four_terms
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (proofRelevantOperationalInputEvent
          (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
            projection fixedInstance)) :=
      measure_mono
        (exact_fixed_legal_subset_operational_input transitionFuel configuration
          projection fixedInstance transitionRoom driverCoversProtocol
            runtimeReserves cutoffBeyondCap)
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms :=
      proof_relevant_operational_input_probability_le_four_upstream_terms
        hiddenLaw transitionFuel configuration fixedInstance relation
          (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
            projection fixedInstance) stages terms k12Bound k13Bound k14Bound
              k15Bound

/-- Exact clean-event composition with stage bounds restricted to the same
literal compiler-clean event.  This is the operationally minimal form: K1.6
already pays the causal target event separately, so none of K1.2--K1.5 needs
to bound its behaviour on target-hit executions. -/
theorem exact_fixed_clean_probability_le_extraction_plus_four_restricted_terms
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k12TwoTreeMerkle208ErrorEvent stages) ≤
        terms.k12TwoTreeMerkle208)
    (k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k13CircleListDecodeErrorEvent stages) ≤
        terms.k13CircleListDecoding)
    (k14Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k14CoherentChainErrorEvent stages) ≤
        terms.k14CoherentChainSelection)
    (k15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k15SpendWitnessErrorEvent stages) ≤
        terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms := by
  have restricted :=
    clean_probability_le_extraction_plus_restricted_upstream_raw_error
      hiddenLaw transitionFuel configuration fixedInstance relation
      (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
        projection fixedInstance) stages
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)
      (exact_fixed_legal_subset_operational_input transitionFuel configuration
        projection fixedInstance transitionRoom driverCoversProtocol
          runtimeReserves cutoffBeyondCap)
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        proofRelevantRestrictedUpstreamRawError hiddenLaw
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance) stages := restricted
    _ ≤ exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms := by
      apply add_le_add (le_refl _)
      unfold proofRelevantRestrictedUpstreamRawError concreteUpstreamRawError
      exact add_le_add
        (add_le_add (add_le_add k12Bound k13Bound) k14Bound) k15Bound

/-! ## Exact compiler error and final AoK inequalities -/

def exactFixedClosedK16ExactCountError
    (terms : ConcreteUpstreamErrorTerms)
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  concreteUpstreamRawError terms + exactCompilerExactCountError parameters

def exactFixedClosedK16RawError
    (terms : ConcreteUpstreamErrorTerms)
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  concreteUpstreamRawError terms +
    exactCompilerPositiveExposureError parameters

/-- Kernel-visible raw error.  The 35-, 31-, and 34-bit grinding stages are
not divisors and are not merged into an independent nonce; all their oracle
calls are included in `G` through the actual resource certificate. -/
theorem exact_fixed_closed_k16_raw_error_expanded
    (terms : ConcreteUpstreamErrorTerms)
    (parameters : ExactCompilerResourceParameters) :
    exactFixedClosedK16RawError terms parameters =
      terms.k12TwoTreeMerkle208 + terms.k13CircleListDecoding +
        terms.k14CoherentChainSelection + terms.k15SpendWitnessRecovery +
        (unifiedFull256ExposureCap parameters +
          (unifiedFull256ExposureCap parameters).choose 2 +
          unifiedFull256ExposureCap parameters *
            globalFull256OracleCallCap parameters : ENNReal) /
          ((2 : ENNReal) ^ 256) := by
  unfold exactFixedClosedK16RawError concreteUpstreamRawError
    exactCompilerPositiveExposureError exactCompilerTargetCoefficient
    seededTargetCoefficient
  push_cast
  ac_rfl

/-- Exact finite-count fixed-instance classical-ROM argument-of-knowledge
inequality. -/
theorem exact_fixed_tag73_k16_classical_rom_aok_exact_count
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16ExactCountError terms parameters := by
  have cleanBound :=
    exact_fixed_clean_probability_le_extraction_plus_four_terms hiddenLaw
      transitionFuel configuration projection fixedInstance relation
        transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap
          stages terms k12Bound k13Bound k14Bound k15Bound
  have targetBound := exact_plain_rom_target_probability_le_exact_count
    hiddenLaw transitionFuel configuration
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∪
          exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_mono (exact_fixed_source_subset_legal_union_target transitionFuel
        configuration projection fixedInstance)
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_union_le _ _
    _ ≤
      (exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms) +
          exactCompilerExactCountError parameters :=
      add_le_add cleanBound targetBound
    _ = exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16ExactCountError terms parameters := by
      unfold exactFixedClosedK16ExactCountError
      ac_rfl

/-- Raw positive-exposure form with the exact Tag-73 coefficient proved from
the actual lazy-oracle target tree. -/
theorem exact_fixed_tag73_k16_classical_rom_aok_raw
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError terms parameters := by
  have cleanBound :=
    exact_fixed_clean_probability_le_extraction_plus_four_terms hiddenLaw
      transitionFuel configuration projection fixedInstance relation
        transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap
          stages terms k12Bound k13Bound k14Bound k15Bound
  have targetBound := exact_plain_rom_target_probability_le_raw_error hiddenLaw
    transitionFuel configuration
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∪
          exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_mono (exact_fixed_source_subset_legal_union_target transitionFuel
        configuration projection fixedInstance)
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_union_le _ _
    _ ≤
      (exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms) +
          exactCompilerPositiveExposureError parameters :=
      add_le_add cleanBound targetBound
    _ = exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError terms parameters := by
      unfold exactFixedClosedK16RawError
      ac_rfl

/-- Raw K1.6 closure from the minimal clean-restricted K1.2--K1.5 bounds.
The exact compiler target coefficient is unchanged and appears once. -/
theorem exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k12TwoTreeMerkle208ErrorEvent stages) ≤
        terms.k12TwoTreeMerkle208)
    (k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k13CircleListDecodeErrorEvent stages) ≤
        terms.k13CircleListDecoding)
    (k14Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k14CoherentChainErrorEvent stages) ≤
        terms.k14CoherentChainSelection)
    (k15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k15SpendWitnessErrorEvent stages) ≤
        terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError terms parameters := by
  have cleanBound :=
    exact_fixed_clean_probability_le_extraction_plus_four_restricted_terms
      hiddenLaw transitionFuel configuration projection fixedInstance relation
        transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap
          stages terms k12Bound k13Bound k14Bound k15Bound
  have targetBound := exact_plain_rom_target_probability_le_raw_error hiddenLaw
    transitionFuel configuration
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∪
          exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_mono (exact_fixed_source_subset_legal_union_target transitionFuel
        configuration projection fixedInstance)
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance) +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_union_le _ _
    _ ≤
      (exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        concreteUpstreamRawError terms) +
          exactCompilerPositiveExposureError parameters :=
      add_le_add cleanBound targetBound
    _ = exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError terms parameters := by
      unfold exactFixedClosedK16RawError
      ac_rfl

/-- Loss-one normalized extraction statement.  No soundness term and no
grinding work factor is divided out. -/
theorem exact_fixed_tag73_k16_classical_rom_aok_normalized
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedSourceRefinementEvent transitionFuel configuration
            projection fixedInstance) -
        exactFixedClosedK16RawError terms parameters ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
        transitionFuel configuration fixedInstance relation := by
  rw [tsub_le_iff_right]
  exact exact_fixed_tag73_k16_classical_rom_aok_raw hiddenLaw transitionFuel
    configuration projection fixedInstance relation transitionRoom
      driverCoversProtocol runtimeReserves cutoffBeyondCap stages terms k12Bound
        k13Bound k14Bound k15Bound

#print axioms exact_fixed_legal_subset_operational_input
#print axioms exact_fixed_clean_probability_le_extraction_plus_stage_events
#print axioms exact_fixed_clean_probability_le_extraction_plus_four_terms
#print axioms
  exact_fixed_clean_probability_le_extraction_plus_four_restricted_terms
#print axioms exact_fixed_closed_k16_raw_error_expanded
#print axioms exact_fixed_tag73_k16_classical_rom_aok_exact_count
#print axioms exact_fixed_tag73_k16_classical_rom_aok_raw
#print axioms exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages
#print axioms exact_fixed_tag73_k16_classical_rom_aok_normalized

end

end AspisK1.V7Tag73ExactFixedK16Closure
