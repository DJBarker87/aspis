import AspisFormal.K1.V7Tag73CausalQ16ProbabilityBridge
import AspisFormal.K1.V7Tag73CausalSlotRouterLookup

/-!
# Whole-forest realization of causal q16 coordinates

The causal router first exposes its 512 named slots as a function and then
reindexes that function as the deployed `64 × 8` digest forest.  These small
lemmas let an operational trace prove equality one candidate/block at a time
and obtain the exact forest equality consumed by the probability bridge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalQ16ForestRealization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16CompilerTapeCoordinates
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The exact tape presented to the underlying named-slot router after the
`512 = |Fin 64 × Fin 8|` reindexing. -/
def q16NamedSlotInputTape
    {residual : Nat}
    (tape : FreshAnswerTape Digest256 (512 + residual)) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset Q16DigestSlot).card + residual) :=
  castFreshAnswerTape (by simp [Q16DigestSlot]) tape

/-- Looking up one candidate/block in the public forest component is exactly
looking up that named slot in the underlying causal router. -/
theorem q16_coordinate_apply_eq_named_slot_coordinate
    {residual : Nat}
    (router : CausalSlotRouter Digest256 Q16DigestSlot Finset.univ residual)
    (tape : FreshAnswerTape Digest256 (512 + residual))
    (counter : Fin 64) (block : Fin 8) :
    (router.q16CoordinateEquiv tape).1 counter block =
      (router.coordinateEquiv (q16NamedSlotInputTape tape)).1
        ⟨(counter, block), Finset.mem_univ _⟩ := by
  simp only [CausalSlotRouter.q16CoordinateEquiv,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, q16DigestSlotFunctionEquiv,
    univSubtypeEquiv, q16NamedSlotInputTape]
  rfl

/-- Pointwise equality of all named slots identifies the complete forest
component of the generic q16 coordinate equivalence. -/
theorem q16_coordinate_forest_eq_of_every_slot_eq
    {residual : Nat}
    (router : CausalSlotRouter Digest256 Q16DigestSlot Finset.univ residual)
    (tape : FreshAnswerTape Digest256 (512 + residual))
    (forest : Q16CandidateDigestForest)
    (slotExact : ∀ counter block,
      (router.q16CoordinateEquiv tape).1 counter block =
        forest counter block) :
    (router.q16CoordinateEquiv tape).1 = forest := by
  funext counter block
  exact slotExact counter block

/-- A literal trace may establish the 512 recursive lookup equations instead
of reasoning about equivalences.  Those equations already determine the
whole digest forest. -/
theorem q16_coordinate_forest_eq_of_every_routed_lookup
    {residual : Nat}
    (router : CausalSlotRouter Digest256 Q16DigestSlot Finset.univ residual)
    (tape : FreshAnswerTape Digest256 (512 + residual))
    (forest : Q16CandidateDigestForest)
    (routed : ∀ counter block,
      causalRoutedAnswer? (counter, block) router
          (q16NamedSlotInputTape tape) =
        some (forest counter block)) :
    (router.q16CoordinateEquiv tape).1 = forest := by
  apply q16_coordinate_forest_eq_of_every_slot_eq router tape forest
  intro counter block
  rw [q16_coordinate_apply_eq_named_slot_coordinate]
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (q16NamedSlotInputTape tape) (counter, block) (Finset.mem_univ _)
    (forest counter block) (routed counter block)

/-- The exact compiler tape, aligned once to its `512 + residual` q16
factorisation. -/
def exactCompilerQ16InputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (512 + ((exactCompilerTargetCaps parameters).length - 512)) :=
  castFreshAnswerTape (by
    have enough : 512 ≤ (exactCompilerTargetCaps parameters).length :=
      exact_compiler_tape_has_q16_coordinate_capacity parameters
    omega) tape

/-- The final exact-compiler coordinates merely swap residual and forest;
there is no further cryptographic transformation. -/
theorem exact_compiler_coordinates_forest_eq_of_q16_coordinate_eq
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (forest : Q16CandidateDigestForest)
    (forestExact :
      (router.q16CoordinateEquiv
        (exactCompilerQ16InputTape parameters tape)).1 = forest) :
    (exactCompilerCausalQ16Coordinates parameters router tape).2 = forest := by
  change
    (router.q16CoordinateEquiv
      (castFreshAnswerTape (by
        have enough : 512 ≤
            (exactCompilerTargetCaps parameters).length :=
          exact_compiler_tape_has_q16_coordinate_capacity parameters
        omega) tape)).1 = forest
  simpa [exactCompilerQ16InputTape] using forestExact

/-- Final operational handoff: following every named slot through the literal
causal router suffices to identify the exact forest returned by the compiler
coordinate equivalence. -/
theorem exact_compiler_coordinates_forest_eq_of_every_routed_lookup
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (forest : Q16CandidateDigestForest)
    (routed : ∀ counter block,
      causalRoutedAnswer? (counter, block) router
          (q16NamedSlotInputTape (exactCompilerQ16InputTape parameters tape)) =
        some (forest counter block)) :
    (exactCompilerCausalQ16Coordinates parameters router tape).2 = forest := by
  apply exact_compiler_coordinates_forest_eq_of_q16_coordinate_eq parameters
    router tape forest
  exact q16_coordinate_forest_eq_of_every_routed_lookup router
    (exactCompilerQ16InputTape parameters tape) forest routed

#print axioms q16_coordinate_forest_eq_of_every_slot_eq
#print axioms q16_coordinate_apply_eq_named_slot_coordinate
#print axioms q16_coordinate_forest_eq_of_every_routed_lookup
#print axioms exact_compiler_coordinates_forest_eq_of_q16_coordinate_eq
#print axioms exact_compiler_coordinates_forest_eq_of_every_routed_lookup

end

end AspisK1.V7Tag73CausalQ16ForestRealization
