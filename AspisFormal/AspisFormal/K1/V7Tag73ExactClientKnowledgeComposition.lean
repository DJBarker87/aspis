import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion

/-!
# Upstream K1.2--K1.5 arithmetic for the actual Tag-73 client result

This leaf replaces the outcome-map extraction event used by the older
observed-proof interface with an event computed from `runExactPlainRom`.
The restoration client's result is a fixed extractor program.  A valid
extraction sample must reach the actual scheduler terminal, apply that program
to the literal terminal replay accumulator, recover `some witness`, and
satisfy the relation for the public instance in the actual root prover result.

The left-hand `legalSameTapeEvent` remains an explicit argument because its
operational construction belongs to the compiler-coupling lane.  This file
does not assume or state any Fiat--Shamir acceptance inclusion.  Its only
premise is the explicitly typed K1.2--K1.5 knowledge inequality on that event.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactClientKnowledgeComposition

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun

noncomputable section

/-! ## The result-native valid-extraction event -/

/-- A fixed extractor program returned by the restoration client.  It is
chosen independently of the hidden tape and is evaluated on the literal
terminal accumulator produced by that client run. -/
abbrev ExactPlainRomWitnessExtractor
    (Statement Proof Payload Witness : Type) :=
  ConcreteRestorationAccumulator Statement Proof Payload → Option Witness

/-- The exact plain-ROM configuration whose restoration client returns an
extractor program.  Applying it to the actual terminal accumulator lets a
real extractor inspect the replay nodes it requested without admitting a
caller-selected per-sample witness map. -/
abbrev ExactPlainRomWitnessConfiguration
    (HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type)
    (parameters : ExactCompilerResourceParameters) :=
  ExactPlainRomConfiguration HiddenTape TapeIdentity Observation Statement
    Proof Payload
      (ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
      parameters

/-- A valid extraction is read directly from the actual scheduler/client
result.  The relation consumes the literal public instance returned at the
root and the literal witness returned by the client. -/
def exactPlainRomValidClientExtractionEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ root clientRun extractor witness,
    exactPlainRomCompleted? transitionFuel configuration sample =
        some (root, clientRun) ∧
      clientRun.halt = .returned extractor ∧
      extractor clientRun.accumulator = some witness ∧
      relation root.adversaryValue.1.publicProof.publicInstance witness}

/-- Kernel-visible expansion showing that membership uses no outcome/world
map and no caller-selected proof. -/
theorem exact_plain_rom_valid_client_extraction_event_iff
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ exactPlainRomValidClientExtractionEvent transitionFuel
        configuration relation ↔
      ∃ root clientRun extractor witness,
        exactPlainRomCompleted? transitionFuel configuration sample =
            some (root, clientRun) ∧
          clientRun.halt = .returned extractor ∧
          extractor clientRun.accumulator = some witness ∧
          relation root.adversaryValue.1.publicProof.publicInstance witness := by
  rfl

/-- Probability of the actual client-result event under the same finite joint
law that runs the exact scheduler. -/
def exactPlainRomValidClientExtractionProbability
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop) : ENNReal :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
    (exactPlainRomValidClientExtractionEvent transitionFuel configuration
      relation)

/-! ## The sole upstream K1.2--K1.5 premise -/

/-- K1.2--K1.5 may supply this inequality for the forthcoming concrete legal
same-tape event.  Its right side is the actual client-result event above.
There is no compiler cover, acceptance bit, restoration function, or outcome
map in this type. -/
def UpstreamExactPlainRomClientKnowledgeInequality
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms) : Prop :=
  (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      legalSameTapeEvent ≤
    polynomialLoss *
        exactPlainRomValidClientExtractionProbability hiddenLaw transitionFuel
          configuration relation +
      concreteUpstreamRawError terms

/-- Expanded four-term form of the upstream premise. -/
theorem upstream_exact_plain_rom_client_knowledge_expanded
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms)
    (upstream : UpstreamExactPlainRomClientKnowledgeInequality hiddenLaw
      transitionFuel configuration relation legalSameTapeEvent polynomialLoss
      terms) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        legalSameTapeEvent ≤
      polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        terms.k12TwoTreeMerkle208 + terms.k13CircleListDecoding +
        terms.k14CoherentChainSelection + terms.k15SpendWitnessRecovery := by
  simpa [UpstreamExactPlainRomClientKnowledgeInequality,
    concreteUpstreamRawError, add_assoc] using upstream

/-- Normalized upstream-only form. -/
theorem upstream_exact_plain_rom_client_knowledge_normalized
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms)
    (lossNonzero : polynomialLoss ≠ 0) (lossFinite : polynomialLoss ≠ ⊤)
    (upstream : UpstreamExactPlainRomClientKnowledgeInequality hiddenLaw
      transitionFuel configuration relation legalSameTapeEvent polynomialLoss
      terms) :
    ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          legalSameTapeEvent - concreteUpstreamRawError terms) /
        polynomialLoss ≤
      exactPlainRomValidClientExtractionProbability hiddenLaw transitionFuel
        configuration relation := by
  rw [ENNReal.div_le_iff' lossNonzero lossFinite, tsub_le_iff_right]
  exact upstream

/-! ## Composition with the actual scheduler target event -/

def exactClientCompositionExactCountError
    (terms : ConcreteUpstreamErrorTerms)
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  concreteUpstreamRawError terms + exactCompilerExactCountError parameters

def exactClientCompositionRawError
    (terms : ConcreteUpstreamErrorTerms)
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  concreteUpstreamRawError terms +
    exactCompilerPositiveExposureError parameters

/-- Exact finite-count union arithmetic.  The compiler-side event is the
literal target event of the same result-carrying cursor. -/
theorem exact_plain_rom_legal_union_target_exact_count_le
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms)
    (upstream : UpstreamExactPlainRomClientKnowledgeInequality hiddenLaw
      transitionFuel configuration relation legalSameTapeEvent polynomialLoss
      terms) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (legalSameTapeEvent ∪
          exactPlainRomTargetEvent transitionFuel configuration) ≤
      polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        exactClientCompositionExactCountError terms parameters := by
  have targetBound := exact_plain_rom_target_probability_le_exact_count
    hiddenLaw transitionFuel configuration
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (legalSameTapeEvent ∪
          exactPlainRomTargetEvent transitionFuel configuration) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          legalSameTapeEvent +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_union_le _ _
    _ ≤
      (polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        concreteUpstreamRawError terms) +
          exactCompilerExactCountError parameters :=
      add_le_add upstream targetBound
    _ = polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        exactClientCompositionExactCountError terms parameters := by
      unfold exactClientCompositionExactCountError
      ac_rfl

/-- Positive-exposure form with the exact
`(F + F.choose 2 + F * G) / 2^256` scheduler term.  The leading `F` is the
public dummy-initial-digest seed, not an imported generic ROM loss. -/
theorem exact_plain_rom_legal_union_target_raw_le
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms)
    (upstream : UpstreamExactPlainRomClientKnowledgeInequality hiddenLaw
      transitionFuel configuration relation legalSameTapeEvent polynomialLoss
      terms) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (legalSameTapeEvent ∪
          exactPlainRomTargetEvent transitionFuel configuration) ≤
      polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        exactClientCompositionRawError terms parameters := by
  have targetBound := exact_plain_rom_target_probability_le_raw_error
    hiddenLaw transitionFuel configuration
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (legalSameTapeEvent ∪
          exactPlainRomTargetEvent transitionFuel configuration) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          legalSameTapeEvent +
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPlainRomTargetEvent transitionFuel configuration) :=
      measure_union_le _ _
    _ ≤
      (polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        concreteUpstreamRawError terms) +
          exactCompilerPositiveExposureError parameters :=
      add_le_add upstream targetBound
    _ = polynomialLoss *
          exactPlainRomValidClientExtractionProbability hiddenLaw
            transitionFuel configuration relation +
        exactClientCompositionRawError terms parameters := by
      unfold exactClientCompositionRawError
      ac_rfl

/-- Normalized composition form.  It remains a theorem about the explicit
legal/target union; no acceptance event is silently substituted. -/
theorem exact_plain_rom_legal_union_target_normalized
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (relation : PublicInstance Statement → Witness → Prop)
    (legalSameTapeEvent : Set (ExactCompilerSample HiddenTape parameters))
    (polynomialLoss : ENNReal) (terms : ConcreteUpstreamErrorTerms)
    (lossNonzero : polynomialLoss ≠ 0) (lossFinite : polynomialLoss ≠ ⊤)
    (upstream : UpstreamExactPlainRomClientKnowledgeInequality hiddenLaw
      transitionFuel configuration relation legalSameTapeEvent polynomialLoss
      terms) :
    ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (legalSameTapeEvent ∪
            exactPlainRomTargetEvent transitionFuel configuration) -
        exactClientCompositionRawError terms parameters) / polynomialLoss ≤
      exactPlainRomValidClientExtractionProbability hiddenLaw transitionFuel
        configuration relation := by
  rw [ENNReal.div_le_iff' lossNonzero lossFinite, tsub_le_iff_right]
  exact exact_plain_rom_legal_union_target_raw_le hiddenLaw transitionFuel
    configuration relation legalSameTapeEvent polynomialLoss terms upstream

#print axioms exact_plain_rom_valid_client_extraction_event_iff
#print axioms upstream_exact_plain_rom_client_knowledge_expanded
#print axioms upstream_exact_plain_rom_client_knowledge_normalized
#print axioms exact_plain_rom_legal_union_target_exact_count_le
#print axioms exact_plain_rom_legal_union_target_raw_le
#print axioms exact_plain_rom_legal_union_target_normalized

end

end AspisK1.V7Tag73ExactClientKnowledgeComposition
