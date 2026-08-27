import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface

/-!
# Operational input to the literal client-extraction certificate

The fixed K1.2--K1.5 input already contains the actual completed root, actual
restoration-client run, and their full scheduler factorization.  This module
shows that constructing the final extraction certificate needs only the two
implementation-specific facts which a concrete extractor must prove:

* the fixed client returned the named extractor; and
* that extractor returns the named witness on the actual accumulator.

The completed-run and fixed-public-instance equations are derived here from
the operational package, rather than being repeated in a handoff premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalClientExtractionBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ProofRelevantUpstreamInterface

noncomputable section

/-- Package a concrete extractor result using only the literal terminal run
already stored in the exact operational input. -/
def exactFixedClientExtractionCertificateOfOperationalInput
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactFixedOperationalStateRestorationInput transitionFuel
      configuration projection fixedInstance sample)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (witness : Witness)
    (clientReturned : input.package.root.full.clientRun.halt =
      .returned extractor)
    (extractorReturned : extractor
      input.package.root.full.clientRun.accumulator = some witness)
    (relationValid : relation fixedInstance witness) :
    ExactFixedClientExtractionCertificate transitionFuel configuration
      fixedInstance relation sample where
  root := input.package.root.fixedRoot.base.runtime
  clientRun := input.package.root.full.clientRun
  extractor := extractor
  witness := witness
  completed := by
    simp only [exactPlainRomCompleted?,
      input.package.root.full.fullCompleted]
  fixedInstanceExact := input.package.factorization.fixedInstanceExact
  clientReturned := clientReturned
  extractorReturned := extractorReturned
  relationValid := relationValid

#print axioms exactFixedClientExtractionCertificateOfOperationalInput

end

end AspisK1.V7Tag73OperationalClientExtractionBridge
