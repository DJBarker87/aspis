import AspisFormal.K1.V7Tag73ExactFixedK16Closure
import AspisFormal.K1.V7Tag73ExactFixedK12PrefixClassifier
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier

/-!
# Concrete K1.2--K1.5 stage assembly for exact Tag-73

K1.6 consumes one dependent `ProofRelevantK12ToK15Stages` value.  This module
fills its K1.2, K1.3 and K1.4 slots with the actual executable classifiers on
the literal fixed scheduler input.  Only K1.5 remains as an explicit typed
classifier because that last step must additionally connect the decoded spend
witness to the extractor returned by the restoration client.

There is no acceptance or probability premise here.  Every right branch of
K1.2--K1.4 is the concrete error type already reduced to the counted Merkle,
q16 and published circle-code events by the corresponding failure modules.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactConcreteStageAssembly

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The sole remaining classifier input after installing the three concrete
upstream stages.  Its error family is proof relevant and indexed by the exact
K1.2--K1.4 values that reached it. -/
structure ExactTag73K15Classifier
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder) where
  error :
    (sample : ExactCompilerSample HiddenTape parameters) →
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample) →
      (k12 : ExactPrefixK12Certificate input) →
      (k13 : ExactK13Certificate decoder input k12) →
      ExactK14Certificate decoder decoderBinding input k12 → Type
  classify :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (k13 : ExactK13Certificate decoder input k12)
      (k14 : ExactK14Certificate decoder decoderBinding input k12),
      ExactFixedClientExtractionCertificate transitionFuel configuration
          fixedInstance relation sample ⊕
        error sample input k12 k13 k14

/-- The actual dependent stage package consumed by the fixed K1.6 theorem.
K1.2 is the prefix/shared-log Merkle classifier; K1.3 is the exact algorithmic
circle/list classifier; and K1.4 is the coherent-chain classifier using the
fixed decoder projection binding. -/
noncomputable def exactTag73ProofRelevantStages
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
      fixedInstance relation decoder decoderBinding) :
    ProofRelevantK12ToK15Stages transitionFuel configuration fixedInstance
      relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel configuration
          projection fixedInstance) where
  k12TwoTreeMerkle208Certificate := fun _sample input =>
    ExactPrefixK12Certificate input
  k12TwoTreeMerkle208Error := fun _sample input =>
    ExactPrefixK12Error input
  classifyK12TwoTreeMerkle208 := fun _sample input =>
    classifyExactPrefixK12 input
  k13CircleListDecodeCertificate := fun _sample input k12 =>
    ExactK13Certificate decoder input k12
  k13CircleListDecodeError := fun _sample input k12 =>
    ExactK13Error decoder input k12
  classifyK13CircleListDecode := fun _sample input k12 =>
    classifyExactK13 decoder input k12
  k14CoherentChainCertificate := fun _sample input k12 _k13 =>
    ExactK14Certificate decoder decoderBinding input k12
  k14CoherentChainError := fun _sample input k12 _k13 =>
    ExactK14Error decoder input k12
  classifyK14CoherentChain := fun _sample input k12 k13 =>
    classifyExactK14 decoder decoderBinding input k12 k13
  k15SpendWitnessError := fun sample input k12 k13 k14 =>
    k15.error sample input k12 k13 k14
  classifyK15SpendWitness := fun sample input k12 k13 k14 =>
    k15.classify sample input k12 k13 k14

@[simp] theorem exactTag73Stages_classifyK12
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15
      |>.classifyK12TwoTreeMerkle208 sample input) =
        classifyExactPrefixK12 input := by
  rfl

@[simp] theorem exactTag73Stages_classifyK13
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15
      |>.classifyK13CircleListDecode sample input k12) =
        classifyExactK13 decoder input k12 := by
  rfl

@[simp] theorem exactTag73Stages_classifyK14
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12) :
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15
      |>.classifyK14CoherentChain sample input k12 k13) =
        classifyExactK14 decoder decoderBinding input k12 k13 := by
  rfl

@[simp] theorem exactTag73Stages_classifyK15
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12)
    (k14 : ExactK14Certificate decoder decoderBinding input k12) :
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15
      |>.classifyK15SpendWitness sample input k12 k13 k14) =
        k15.classify sample input k12 k13 k14 := by
  rfl

#print axioms exactTag73ProofRelevantStages
#print axioms exactTag73Stages_classifyK12
#print axioms exactTag73Stages_classifyK13
#print axioms exactTag73Stages_classifyK14
#print axioms exactTag73Stages_classifyK15

end

end AspisK1.V7Tag73ExactConcreteStageAssembly
