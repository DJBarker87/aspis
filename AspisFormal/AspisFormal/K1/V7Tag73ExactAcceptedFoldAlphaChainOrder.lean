import AspisFormal.K1.V7Tag73ExactAcceptedFoldTrialPackage
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder

/-!
# Exact root order of the deployed post-fold alpha chain

The accepted fold package retains the literal alpha duplex chain produced by
the same strict source suffix as the selected fold-work record.  This leaf
converts that source chain once into the strict root-order certificate used by
the causal alpha controller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactAcceptedFoldAlphaChainOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The alpha blocks consumed immediately after the selected fold nonce have
their exact producer lookup and strict root chronology.  No independently
chosen alpha witness or transcript-injectivity premise is used. -/
theorem exact_accepted_fold_alpha_chain_has_root_order
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    ExactRootOrderedQ16Chain input
      (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      fold.boundaryAnswer fold.alphaOutputs fold.alphaAdvances := by
  exact gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
    (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.boundaryAnswer fold.boundaryLookup fold.alphaCoordinates

#print axioms exact_accepted_fold_alpha_chain_has_root_order

end

end AspisK1.V7Tag73ExactAcceptedFoldAlphaChainOrder
