import AspisFormal.K1.V7Tag73AlphaZeroBoundaryInvariant
import AspisFormal.K1.V7Tag73CausalDagProducerInvariant

/-!
# Structural disjointness of alpha-zero and q16 producer inventories

Equal producer digests would force equal literal source inputs.  The roots of
the two producer grammars have different fixed widths (43-byte alpha boundary
versus 35-byte q16 candidate), and their recursive advance edges reduce the
logical block rank.  Strong induction therefore excludes every collision
without assuming injectivity of SHA-256.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaQ16InventoryDisjoint

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaZeroBoundaryInvariant
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem alpha_q16_producer_digest_ne_bounded
    (alphaProducers : List AlphaZeroProducer)
    (q16Producers : List Q16DagProducer)
    (base : Digest256)
    (alphaValid : AlphaZeroProducerInventoryValid alphaProducers)
    (alphaBoundary : AlphaZeroBlockZeroBoundaryValid alphaProducers)
    (q16Valid : Q16DagProducerInventoryValid base q16Producers)
    (equalDigestFixesSource : ∀ alpha ∈ alphaProducers,
      ∀ q16 ∈ q16Producers, alpha.digest = q16.digest →
        alpha.sourceInput = q16.sourceInput) :
    ∀ rank alpha, alpha ∈ alphaProducers →
      ∀ q16, q16 ∈ q16Producers →
        alpha.block.val + q16.slot.2.val = rank →
        alpha.digest ≠ q16.digest := by
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro alpha alphaMember q16 q16Member rankExact digestEqual
      have sourceEqual := equalDigestFixesSource alpha alphaMember q16
        q16Member digestEqual
      rcases alphaValid alpha alphaMember with alphaZero |
          ⟨alphaParent, alphaParentMember, alphaStep, alphaSource⟩
      · have alphaLength := alphaBoundary alpha alphaMember alphaZero
        rcases q16Valid q16 q16Member with q16Zero |
            ⟨q16Parent, q16ParentMember, _sameCounter, q16Step, q16Source⟩
        · have q16Length : q16.sourceInput.length = 35 := by
            rw [q16Zero.2]
            simp
          have lengths := congrArg List.length sourceEqual
          omega
        · have q16Length : q16.sourceInput.length = 33 := by
            rw [q16Source]
            simp
          have lengths := congrArg List.length sourceEqual
          omega
      · rcases q16Valid q16 q16Member with q16Zero |
            ⟨q16Parent, q16ParentMember, _sameCounter, q16Step, q16Source⟩
        · have alphaLength : alpha.sourceInput.length = 33 := by
            rw [alphaSource]
            simp
          have q16Length : q16.sourceInput.length = 35 := by
            rw [q16Zero.2]
            simp
          have lengths := congrArg List.length sourceEqual
          omega
        · have advanceEqual : gammaAdvanceInput alphaParent.digest =
              gammaAdvanceInput q16Parent.digest := by
            change bytes alphaParent.digest ++ [domAdvance] =
              bytes q16Parent.digest ++ [domAdvance]
            rw [← alphaSource, ← q16Source]
            exact sourceEqual
          have parentDigestEqual : alphaParent.digest = q16Parent.digest :=
            advance_input_eq_implies_state_eq alphaParent.digest
              q16Parent.digest advanceEqual
          have parentRankLt :
              alphaParent.block.val + q16Parent.slot.2.val < rank := by
            rw [← rankExact]
            omega
          exact ih (alphaParent.block.val + q16Parent.slot.2.val) parentRankLt
            alphaParent alphaParentMember q16Parent q16ParentMember rfl
              parentDigestEqual

theorem alpha_q16_producer_digests_disjoint
    (alphaProducers : List AlphaZeroProducer)
    (q16Producers : List Q16DagProducer)
    (base : Digest256)
    (alphaValid : AlphaZeroProducerInventoryValid alphaProducers)
    (alphaBoundary : AlphaZeroBlockZeroBoundaryValid alphaProducers)
    (q16Valid : Q16DagProducerInventoryValid base q16Producers)
    (equalDigestFixesSource : ∀ alpha ∈ alphaProducers,
      ∀ q16 ∈ q16Producers, alpha.digest = q16.digest →
        alpha.sourceInput = q16.sourceInput) :
    ∀ alpha ∈ alphaProducers, ∀ q16 ∈ q16Producers,
      alpha.digest ≠ q16.digest := by
  intro alpha alphaMember q16 q16Member
  exact alpha_q16_producer_digest_ne_bounded alphaProducers q16Producers base
    alphaValid alphaBoundary q16Valid equalDigestFixesSource
      (alpha.block.val + q16.slot.2.val) alpha alphaMember q16 q16Member rfl

#print axioms alpha_q16_producer_digest_ne_bounded
#print axioms alpha_q16_producer_digests_disjoint

end

end AspisK1.V7Tag73AlphaQ16InventoryDisjoint
