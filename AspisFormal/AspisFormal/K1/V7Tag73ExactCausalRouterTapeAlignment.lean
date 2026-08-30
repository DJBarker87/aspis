import AspisFormal.K1.V7Tag73CausalFinalWorkQ16UsedForest
import AspisFormal.K1.V7Tag73ExactCompilerSourceAnchoredCut
import AspisFormal.K1.V7Tag73ExactRootFreshInputUniqueness

/-!
# Exact compiler tape alignment for the causal q16 router

The joint final-work/q16 equivalence consumes a proof-indexed cast of the
exact compiler master tape.  This file proves that those casts do not change
the chronological answer list and identifies its root prefix with the
literal adversary-then-verifier fresh-query answers.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCausalRouterTapeAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootFreshInputUniqueness
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Transporting a length-indexed tape across a proof of equal lengths does
not change its chronological list of values. -/
theorem fresh_answer_tape_to_list_cast
    {Output : Type} {source target : Nat} (equal : source = target)
    (tape : FreshAnswerTape Output source) :
    freshAnswerTapeToList (castFreshAnswerTape equal tape) =
      freshAnswerTapeToList tape := by
  subst target
  rfl

/-- The two public alignment casts used by the 513-slot router retain every
master coordinate in the original order. -/
theorem final_work_q16_named_slot_tape_preserves_master_list
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters tape)) =
      freshAnswerTapeToList tape := by
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]

/-- On the accepted exact source run, the causal router sees precisely the
combined root fresh-query answers first, followed by the verifier's literal
untouched suffix of the compiler tape. -/
theorem exact_causal_router_tape_has_literal_root_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      (exactRootFreshQueries input).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  rw [final_work_q16_named_slot_tape_preserves_master_list]
  exact (exactCompilerInitialGammaCursorAlignment input).answersExact

/-- A selected record in the root prefix therefore carries the master-tape
answer at the same strict chronological position. -/
theorem exact_causal_router_tape_selected_root_answer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior later : List (ShaInput × Digest256))
    (selected : ShaInput × Digest256)
    (decomposition : exactRootFreshQueries input =
      prior ++ selected :: later) :
    freshAnswerTapeToList
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2)) =
      prior.map Prod.snd ++ selected.2 ::
        (later.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
  rw [exact_causal_router_tape_has_literal_root_prefix input, decomposition]
  simp [List.map_append, List.append_assoc]

#print axioms fresh_answer_tape_to_list_cast
#print axioms final_work_q16_named_slot_tape_preserves_master_list
#print axioms exact_causal_router_tape_has_literal_root_prefix
#print axioms exact_causal_router_tape_selected_root_answer

end

end AspisK1.V7Tag73ExactCausalRouterTapeAlignment
