import AspisFormal.K1.V7Tag73ExactCompilerResources
import AspisFormal.K1.V7Tag73Q16DigestDrawReindex

/-!
# Exact compiler-tape coordinates for the Tag-73 q16 forest

The deployed q16 scan has sixty-four candidate branches and each candidate
uses at most eight full SHA-256 output blocks.  This file proves the finite
coordinate fact needed by the eventual operational coupling: the exact
compiler master tape always contains enough coordinates to split off a
complete `64 * 8` digest forest, leaving an independent residual tape.

This is deliberately only a type-level, measure-preserving finite
factorisation.  It does not claim that the static coordinates split off here
are already the adaptive q16 calls made by the scheduler.  That chronological
alignment remains a separate theorem about the literal execution trace.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16CompilerTapeCoordinates

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Generic finite-tape factorisations -/

/-- A length-indexed fresh tape is exactly a function on `Fin length`. -/
def freshAnswerTapeFinEquiv (Output : Type) :
    (length : Nat) → FreshAnswerTape Output length ≃ (Fin length → Output)
  | 0 =>
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => PUnit.unit
        left_inv := by intro tape; cases tape; rfl
        right_inv := by intro values; funext index; exact Fin.elim0 index }
  | length + 1 =>
      (Equiv.prodCongr (Equiv.refl Output)
        (freshAnswerTapeFinEquiv Output length)).trans
          (Fin.consEquiv (fun _ : Fin (length + 1) => Output))

/-- Split a left-to-right fresh-answer tape after exactly `left` entries. -/
def freshAnswerTapeAppendEquiv (Output : Type) (left right : Nat) :
    FreshAnswerTape Output (left + right) ≃
      FreshAnswerTape Output left × FreshAnswerTape Output right :=
  (freshAnswerTapeFinEquiv Output (left + right)).trans
    (((finSumFinEquiv : Fin left ⊕ Fin right ≃ Fin (left + right)).arrowCongr
        (Equiv.refl Output)).symm.trans
      ((Equiv.sumArrowEquivProdArrow (Fin left) (Fin right) Output).trans
        (Equiv.prodCongr (freshAnswerTapeFinEquiv Output left).symm
          (freshAnswerTapeFinEquiv Output right).symm)))

/-- Flattening the two q16 forest indices gives exactly 512 digest blocks. -/
def flatDigestBlocksEquiv :
    (Fin (64 * 8) → Digest256) ≃ Q16CandidateDigestForest where
  toFun flat counter block :=
    flat (finProdFinEquiv (counter, block))
  invFun forest index :=
    let pair : Fin 64 × Fin 8 := finProdFinEquiv.symm index
    forest pair.1 pair.2
  left_inv flat := by
    funext index
    simp
  right_inv forest := by
    funext counter block
    simp

/-- Exactly 512 fresh full-output coordinates are a complete q16 digest
forest, including the counterfactual suffix after the first successful
candidate. -/
def q16DigestForestTapeEquiv :
    FreshAnswerTape Digest256 512 ≃ Q16CandidateDigestForest :=
  (freshAnswerTapeFinEquiv Digest256 512).trans
    ((Equiv.cast (by norm_num :
      (Fin 512 → Digest256) = (Fin (64 * 8) → Digest256))).trans
        flatDigestBlocksEquiv)

/-! ## Exact compiler specialization -/

theorem exact_compiler_tape_has_q16_coordinate_capacity
    (parameters : ExactCompilerResourceParameters) :
    512 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

/-- Static factorisation of the exact compiler master tape into every
non-q16 coordinate and one complete 64-by-8 q16 digest forest.  The residual
length is exact, so no entropy is discarded or duplicated. -/
def exactCompilerStaticQ16Coordinates
    (parameters : ExactCompilerResourceParameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      FreshAnswerTape Digest256
          ((exactCompilerTargetCaps parameters).length - 512) ×
        Q16CandidateDigestForest := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 512 ≤ total := by
    exact exact_compiler_tape_has_q16_coordinate_capacity parameters
  have totalEq : total = (total - 512) + 512 :=
    (Nat.sub_add_cancel enough).symm
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((freshAnswerTapeAppendEquiv Digest256 (total - 512) 512).trans
        (Equiv.prodCongr (Equiv.refl _ ) q16DigestForestTapeEquiv))

theorem exact_compiler_static_q16_residual_plus_forest_length
    (parameters : ExactCompilerResourceParameters) :
    ((exactCompilerTargetCaps parameters).length - 512) + 64 * 8 =
      (exactCompilerTargetCaps parameters).length := by
  have enough := exact_compiler_tape_has_q16_coordinate_capacity parameters
  norm_num at enough ⊢
  exact Nat.sub_add_cancel enough

#print axioms freshAnswerTapeAppendEquiv
#print axioms freshAnswerTapeFinEquiv
#print axioms flatDigestBlocksEquiv
#print axioms q16DigestForestTapeEquiv
#print axioms exact_compiler_tape_has_q16_coordinate_capacity
#print axioms exactCompilerStaticQ16Coordinates
#print axioms exact_compiler_static_q16_residual_plus_forest_length

end

end AspisK1.V7Tag73Q16CompilerTapeCoordinates
