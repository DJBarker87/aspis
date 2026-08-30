import AspisFormal.K1.V7Tag73CausalQ16FinalWorkProbability
import AspisFormal.K1.V7Tag73CausalSlotRouterLookup
import AspisFormal.K1.V7Tag73OperationalQ16ForestHandoff

/-!
# Used-prefix realization for the joint final-work/q16 router

The production q16 decoder consumes only the blocks through the selected
counter.  The unused suffix of a completed `64 × 8` coordinate forest is
therefore irrelevant.  This file connects exact routed lookups for those
consumed blocks directly to `OperationalQ16ForestRealization`; it does not
require equality with an independently zero-padded whole forest.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalFinalWorkQ16UsedForest

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The exact compiler tape aligned to the `513 + residual` factorization
used by the joint final-work/q16 router. -/
def exactCompilerFinalWorkQ16InputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (513 + ((exactCompilerTargetCaps parameters).length - 513)) :=
  castFreshAnswerTape (by
    have enough := exact_compiler_tape_has_final_work_q16_capacity parameters
    omega) tape

/-- Align the public `513` constant with the finite cardinality of the joint
slot type before exposing the generic router lookup. -/
def finalWorkQ16NamedSlotInputTape
    {residual : Nat}
    (tape : FreshAnswerTape Digest256 (513 + residual)) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset FinalWorkQ16DigestSlot).card + residual) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, finalWorkQ16DigestSlot_card]) tape

/-- One q16 forest coordinate returned by the joint exact-compiler
factorization is the corresponding named-slot coordinate of the underlying
causal router. -/
theorem exact_compiler_final_work_q16_forest_apply_eq_named_slot_coordinate
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (counter : Fin 64) (block : Fin 8) :
    (exactCompilerCausalFinalWorkQ16Coordinates parameters router tape).2.2
        counter block =
      (router.coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters tape))).1
        ⟨some (counter, block), Finset.mem_univ _⟩ := by
  rfl

/-- A recursive routed-lookup equation for one q16 slot fixes that exact
forest coordinate, even though the joint router also carries the selected
final-work digest and an arbitrary residual tape. -/
theorem exact_compiler_final_work_q16_forest_coordinate_eq_of_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (counter : Fin 64) (block : Fin 8) (answer : Digest256)
    (routed :
      causalRoutedAnswer? (some (counter, block)) router
          (finalWorkQ16NamedSlotInputTape
            (exactCompilerFinalWorkQ16InputTape parameters tape)) =
        some answer) :
    (exactCompilerCausalFinalWorkQ16Coordinates parameters router tape).2.2
        counter block = answer := by
  rw [exact_compiler_final_work_q16_forest_apply_eq_named_slot_coordinate]
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (finalWorkQ16NamedSlotInputTape
      (exactCompilerFinalWorkQ16InputTape parameters tape))
    (some (counter, block)) (Finset.mem_univ _) answer routed

/-- Final used-prefix handoff.  Source chronology only has to prove routed
lookup equations for blocks the accepted decoder actually consumed.  No
condition is imposed on unused counters or unused suffix blocks. -/
theorem exact_compiler_final_work_q16_operational_realization_of_used_lookups
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters)
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
            (some (counter,
              ⟨index, Nat.lt_of_lt_of_le inBlocks
                (candidateLengthCap counter beforeSelected)⟩))
            router
            (finalWorkQ16NamedSlotInputTape
              (exactCompilerFinalWorkQ16InputTape parameters tape)) =
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
      (exactCompilerCausalFinalWorkQ16Coordinates parameters router tape).2.2 := by
  apply operationalQ16ForestRealizationOfDigestPointwise
  refine
    { candidateBlocks := candidateBlocks
      candidateLengthCap := candidateLengthCap
      candidateBlockExact := ?_
      outcomeDecoded := outcomeDecoded
      frontierExact := frontierExact }
  intro counter beforeSelected index inBlocks
  symm
  exact exact_compiler_final_work_q16_forest_coordinate_eq_of_routed_lookup
    parameters router tape counter
      ⟨index, Nat.lt_of_lt_of_le inBlocks
        (candidateLengthCap counter beforeSelected)⟩
      ((candidateBlocks counter)[index])
      (routed counter beforeSelected index inBlocks)

#print axioms
  exact_compiler_final_work_q16_forest_apply_eq_named_slot_coordinate
#print axioms
  exact_compiler_final_work_q16_forest_coordinate_eq_of_routed_lookup
#print axioms
  exact_compiler_final_work_q16_operational_realization_of_used_lookups

end

end AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
