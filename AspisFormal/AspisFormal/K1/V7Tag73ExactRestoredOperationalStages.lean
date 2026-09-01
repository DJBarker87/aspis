import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Classifier
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface
import AspisFormal.K1.V7Tag73ExactFixedK16Closure

/-!
# Source-closed restoration-wide K1.2--K1.5 stage assembly

The older concrete stage assembly classifies only the fixed root proof before
asking K1.5 to search restored branches.  The state-restoration extractor must
instead be allowed to choose any literal completed node whose own two-tree
openings and verifier-derived K1.3 view succeed.

This module installs that corrected dependency order in the generic K1.6
stage interface.  K1.2 is an administrative unit stage because the
restoration-wide K1.3 classifier authenticates each candidate node's own
two-tree openings internally.  Its error therefore already includes exact
K1.2 authentication/extraction failures.  K1.4 is run on the same selected
node and view.  Only the final spend-witness/client handoff remains an
explicit typed classifier input.

No probability bound, acceptance premise, source oracle, or witness appears
in the installed K1.2--K1.4 classifiers.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalStages

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- K1.4 certificate for the exact node selected by restoration-wide K1.3. -/
structure ExactRestoredOperationalK14Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactRestoredOperationalK13Certificate decoder input) where
  classified : ParsedK14Certificate decoder binding
    k13.classified.k12.words (restoredOperationalK13View k13.data)

/-- Exact K1.4 error on that same selected restored node. -/
structure ExactRestoredOperationalK14Error
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactRestoredOperationalK13Certificate decoder input) where
  classified : ParsedK14Error decoder k13.classified.k12.words
    (restoredOperationalK13View k13.data)

/-- Total coherent-chain classifier for the node already selected by K1.3. -/
noncomputable def classifyExactRestoredOperationalK14
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactRestoredOperationalK13Certificate decoder input) :
    ExactRestoredOperationalK14Certificate decoder binding input k13 ⊕
      ExactRestoredOperationalK14Error decoder input k13 :=
  match classifyParsedK14 decoder binding k13.classified.k12.words
      (restoredOperationalK13View k13.data) k13.classified.k13 with
  | .inl certificate => .inl ⟨certificate⟩
  | .inr error => .inr ⟨error⟩

/-- The sole remaining stage input: convert the selected restored coherent
chain into the literal client extractor's valid spend witness, or return its
typed K1.5 error. -/
structure ExactRestoredOperationalK15Classifier
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder) where
  error :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample) →
      (k13 : ExactRestoredOperationalK13Certificate decoder input) →
      ExactRestoredOperationalK14Certificate decoder binding input k13 → Type
  classify :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactRestoredOperationalK13Certificate decoder input)
      (k14 : ExactRestoredOperationalK14Certificate decoder binding input k13),
      ExactFixedClientExtractionCertificate transitionFuel configuration
          fixedInstance relation sample ⊕
        error sample input k13 k14

/-- Correct restoration-wide stage package consumed by the generic K1.6
compiler theorem.  Authentication is internal to the selected-node K1.3
classifier, so the administrative K1.2 stage cannot silently select a
different proof or accumulator. -/
noncomputable def exactTag73RestoredOperationalStages
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
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
      projection fixedInstance relation decoder binding) :
    ProofRelevantK12ToK15Stages transitionFuel configuration fixedInstance
      relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance) where
  k12TwoTreeMerkle208Certificate := fun _sample _input => Unit
  k12TwoTreeMerkle208Error := fun _sample _input => Empty
  classifyK12TwoTreeMerkle208 := fun _sample _input => .inl ()
  k13CircleListDecodeCertificate := fun _sample input _unit =>
    ExactRestoredOperationalK13Certificate decoder input
  k13CircleListDecodeError := fun _sample input _unit =>
    ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input)
  classifyK13CircleListDecode := fun _sample input _unit =>
    classifyExactRestoredOperationalK13Checked decoder input
  k14CoherentChainCertificate := fun _sample input _unit k13 =>
    ExactRestoredOperationalK14Certificate decoder binding input k13
  k14CoherentChainError := fun _sample input _unit k13 =>
    ExactRestoredOperationalK14Error decoder input k13
  classifyK14CoherentChain := fun _sample input _unit k13 =>
    classifyExactRestoredOperationalK14 decoder binding input k13
  k15SpendWitnessError := fun sample input _unit k13 k14 =>
    k15.error sample input k13 k14
  classifyK15SpendWitness := fun sample input _unit k13 k14 =>
    k15.classify sample input k13 k14

@[simp] theorem exact_restored_stages_classify_k12
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
      projection fixedInstance relation decoder binding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactTag73RestoredOperationalStages transitionFuel configuration projection
      fixedInstance relation decoder binding k15
      |>.classifyK12TwoTreeMerkle208 sample input) = .inl () := by
  rfl

@[simp] theorem exact_restored_stages_classify_k13
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
      projection fixedInstance relation decoder binding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactTag73RestoredOperationalStages transitionFuel configuration projection
      fixedInstance relation decoder binding k15
      |>.classifyK13CircleListDecode sample input ()) =
        classifyExactRestoredOperationalK13Checked decoder input := by
  rfl

@[simp] theorem exact_restored_stages_classify_k14
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
      projection fixedInstance relation decoder binding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactRestoredOperationalK13Certificate decoder input) :
    (exactTag73RestoredOperationalStages transitionFuel configuration projection
      fixedInstance relation decoder binding k15
      |>.classifyK14CoherentChain sample input () k13) =
        classifyExactRestoredOperationalK14 decoder binding input k13 := by
  rfl

/-- The generic K1.6 error event for the restored stage package is exactly the
source-closed restoration-wide K1.3 event.  In particular, the administrative
`Unit` K1.2 value cannot change which operational input or restored accumulator
is measured. -/
theorem exact_restored_stages_k13_error_event_eq
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
    k13CircleListDecodeErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73RestoredOperationalK13FailureEvent transitionFuel configuration
        projection fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, k12, failure⟩
    cases k12
    exact ⟨input, failure⟩
  · rintro ⟨input, failure⟩
    exact ⟨input, (), failure⟩

/-- Literal sample event for failure of K1.4 on the node and K1.3
certificate selected by the restoration-wide classifier. -/
def exactTag73RestoredOperationalK14FailureEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactRestoredOperationalK13Certificate decoder input),
    Nonempty (ExactRestoredOperationalK14Error decoder input k13)}

/-- The generic K1.4 event is definitionally the literal restored-node K1.4
event; no root-only certificate or alternate parser view is involved. -/
theorem exact_restored_stages_k14_error_event_eq
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
    k14CoherentChainErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73RestoredOperationalK14FailureEvent transitionFuel configuration
        projection fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, k12, k13, failure⟩
    cases k12
    exact ⟨input, k13, failure⟩
  · rintro ⟨input, k13, failure⟩
    exact ⟨input, (), k13, failure⟩

/-- The literal restoration-wide width-29 failure event. -/
def exactTag73RestoredOperationalK14Width29Event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactRestoredOperationalK13Certificate decoder input),
    Width29DecompositionFailure decoder k13.classified.k12.words
      (restoredOperationalK13View k13.data).gamma
      (restoredOperationalK13View k13.data).disclosedFinal
      (restoredOperationalK13View k13.data).schedule}

/-- The sole restored K1.4 error constructor is exactly the width-29 event on
the same selected node and verifier-derived transcript view. -/
theorem exact_restored_operational_k14_failure_subset_width29
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact} :
    exactTag73RestoredOperationalK14FailureEvent transitionFuel configuration
        projection fixedInstance decoder ⊆
      exactTag73RestoredOperationalK14Width29Event transitionFuel configuration
        projection fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, k13, ⟨failure⟩⟩
  cases failure.classified with
  | width29 widthFailure => exact ⟨input, k13, widthFailure⟩

/-- Direct generic-stage form of the restored width-29 cover. -/
theorem exact_restored_stages_k14_error_subset_width29
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
    k14CoherentChainErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) ⊆
      exactTag73RestoredOperationalK14Width29Event transitionFuel configuration
        projection fixedInstance decoder := by
  rw [exact_restored_stages_k14_error_event_eq k15]
  exact exact_restored_operational_k14_failure_subset_width29

/-- Literal sample event for failure of the supplied restored-node K1.5
classifier after the exact K1.3 and K1.4 certificates have been fixed. -/
def exactTag73RestoredOperationalK15FailureEvent
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
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactRestoredOperationalK13Certificate decoder input)
      (k14 : ExactRestoredOperationalK14Certificate decoder binding input k13),
    Nonempty (k15.error sample input k13 k14)}

/-- The generic K1.5 event for the corrected stage package is exactly the
literal classifier event above. -/
theorem exact_restored_stages_k15_error_event_eq
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
    k15SpendWitnessErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) =
      exactTag73RestoredOperationalK15FailureEvent k15 := by
  ext sample
  constructor
  · rintro ⟨input, k12, k13, k14, failure⟩
    cases k12
    exact ⟨input, k13, k14, failure⟩
  · rintro ⟨input, k13, k14, failure⟩
    exact ⟨input, (), k13, k14, failure⟩

#print axioms classifyExactRestoredOperationalK14
#print axioms exactTag73RestoredOperationalStages
#print axioms exact_restored_stages_classify_k12
#print axioms exact_restored_stages_classify_k13
#print axioms exact_restored_stages_classify_k14
#print axioms exact_restored_stages_k13_error_event_eq
#print axioms exact_restored_stages_k14_error_event_eq
#print axioms exact_restored_operational_k14_failure_subset_width29
#print axioms exact_restored_stages_k14_error_subset_width29
#print axioms exact_restored_stages_k15_error_event_eq

end

end AspisK1.V7Tag73ExactRestoredOperationalStages
