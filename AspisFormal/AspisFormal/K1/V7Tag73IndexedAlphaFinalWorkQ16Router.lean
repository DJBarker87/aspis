import AspisFormal.K1.V7Tag73CausalAlphaFinalWorkQ16Probability

/-!
# Counted scheduler routing for alpha-zero, final work, and q16

The corrected K1.3 factorization exposes four alpha-zero output blocks before
the existing final-work/q16 coordinates.  This module compiles any literal
pre-answer controller for those 517 named slots through the same exact unified
scheduler used by the 513-slot construction.

The controller chooses each destination before seeing the current answer.
Consequently this is only an operational coordinate constructor: the source
layer must still prove that its alpha, final-work, and q16 labels match the
accepted Tag-73 execution.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73IndexedAlphaFinalWorkQ16Router

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- Compile one exact counted unified-scheduler controller into the corrected
517-slot causal router.  Early halt and unused named slots use the generic
total padding equivalence, exactly as in the existing 513-slot router. -/
def exactCompilerIndexedAlphaFinalWorkQ16Router
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalAlphaFinalWorkQ16Router parameters :=
  (controller.machine transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 517)
    { exposureIndex := 0, cursor := cursor, memory := initialMemory }

/-- Exact master-tape coordinates induced by the counted 517-slot controller.
The four alpha blocks are part of the residual conditioning context; final
work and the q16 forest retain the checked product shape. -/
def exactCompilerIndexedAlphaFinalWorkQ16Coordinates
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerAlphaFinalWorkQ16Context parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerCausalAlphaFinalWorkQ16Coordinates parameters
    (exactCompilerIndexedAlphaFinalWorkQ16Router parameters transitionFuel
      controller initialMemory cursor)

#print axioms exactCompilerIndexedAlphaFinalWorkQ16Router
#print axioms exactCompilerIndexedAlphaFinalWorkQ16Coordinates

end

end AspisK1.V7Tag73IndexedAlphaFinalWorkQ16Router
