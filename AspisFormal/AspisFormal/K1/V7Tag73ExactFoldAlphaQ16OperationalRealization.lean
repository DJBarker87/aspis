import AspisFormal.K1.V7Tag73ExactAcceptedFoldTrialPackage
import AspisFormal.K1.V7Tag73CausalFinalWorkQ16UsedForest

/-!
# Exact 518-slot operational coordinates

These lemmas connect recursive lookups in the complete fold/alpha/final/q16
router to the three deployed coordinate components used by K1.3.  They are
pure consequences of the selected product/reindexing equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem exact_compiler_fold_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (answer : Digest256)
    (routed : causalRoutedAnswer? none router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.1 = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨none, Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    none (Finset.mem_univ _) answer routed

theorem exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (answer : Digest256)
    (routed : causalRoutedAnswer? (some (Sum.inr none)) router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.1 = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨some (Sum.inr none), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    (some (Sum.inr none)) (Finset.mem_univ _) answer routed

theorem exact_compiler_fold_q16_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (counter : Fin 64) (block : Fin 8) (answer : Digest256)
    (routed : causalRoutedAnswer?
      (some (Sum.inr (some (counter, block)))) router
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.2 counter block = answer := by
  change
    (router.coordinateEquiv
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))).1
        ⟨some (Sum.inr (some (counter, block))), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape))
    (some (Sum.inr (some (counter, block)))) (Finset.mem_univ _) answer routed

/-- The production decoder only consumes the prefix through its selected
counter, so routed equations for that prefix suffice for exact realization. -/
theorem exact_compiler_fold_q16_operational_realization_of_used_lookups
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (candidateBlocks : Fin 64 → List Digest256)
    (candidateLengthCap : ∀ counter,
      counter.val ≤ search.selectedCounter.val →
      (candidateBlocks counter).length ≤ 8)
    (routed : ∀ counter
      (beforeSelected : counter.val ≤ search.selectedCounter.val),
      ∀ index (inBlocks : index < (candidateBlocks counter).length),
        causalRoutedAnswer?
            (some (Sum.inr (some (counter,
              ⟨index, Nat.lt_of_lt_of_le inBlocks
                (candidateLengthCap counter beforeSelected)⟩))))
            router
            (foldAlphaFinalWorkQ16NamedSlotInputTape
              (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters tape)) =
          some ((candidateBlocks counter)[index]))
    (outcomeDecoded : ∀ counter,
      counter.val ≤ search.selectedCounter.val →
      decodeCandidateOutcome counter (candidateBlocks counter) =
        some (search.outcome counter))
    (frontierExact : ∀ counter schedule,
      counter.val ≤ search.selectedCounter.val →
      search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        frontierNodes schedule) :
    OperationalQ16ForestRealization frontierNodes search
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        tape).2.2.2 := by
  apply operationalQ16ForestRealizationOfDigestPointwise
  refine
    { candidateBlocks := candidateBlocks
      candidateLengthCap := candidateLengthCap
      candidateBlockExact := ?_
      outcomeDecoded := outcomeDecoded
      frontierExact := frontierExact }
  intro counter beforeSelected index inBlocks
  symm
  exact exact_compiler_fold_q16_coordinate_eq_of_routed_lookup parameters
    router tape counter
      ⟨index, Nat.lt_of_lt_of_le inBlocks
        (candidateLengthCap counter beforeSelected)⟩
      ((candidateBlocks counter)[index])
      (routed counter beforeSelected index inBlocks)

#print axioms exact_compiler_fold_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_final_work_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_q16_coordinate_eq_of_routed_lookup
#print axioms exact_compiler_fold_q16_operational_realization_of_used_lookups

end

end AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
