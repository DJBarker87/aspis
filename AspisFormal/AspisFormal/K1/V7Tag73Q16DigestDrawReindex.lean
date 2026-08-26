import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity
import AspisFormal.K1.V7Tag73DeployedDecoderFiberCap

/-!
# Exact SHA-256-block to q16 draw-tape reindexing

One Tag-73 q16 candidate consumes at most eight SHA-256 output halves.  Each
output half is read as eight little-endian `u32` words and masked to eighteen
bits.  This file proves that this deployed byte operation is exactly a
projection from sixty-four independent 32-bit words to sixty-four `Fin 2^18`
draws, with a constant `2^(14*64)`-element fibre.

Together with `V7Tag73Q16FirstCompactUniformity`, this removes two tempting
but unjustified shortcuts: treating SHA bytes as abstract q16 coins without a
codec proof, and treating the first cap-203 branch as an unconstrained uniform
schedule.  SHA-256/random-oracle security remains the intended external
boundary; the finite representation and constant-fibre claims below are
kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73Q16DigestDrawReindex

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisV5ComponentCRejectionSampler

noncomputable section

abbrev Q16Position := Fin (2 ^ 18)
abbrev Q16HighBits := Fin (2 ^ 14)
abbrev CandidateDigestBlocks := Fin 8 → Digest256
abbrev CandidateHighTape := Fin 64 → Q16HighBits

/-- `u32 = low18 + 2^18 * high14`, packaged as a finite equivalence. -/
def q16PositionHighEquivRawWord : Q16Position × Q16HighBits ≃ RawWord :=
  (Equiv.prodComm Q16Position Q16HighBits).trans
    (finProdFinEquiv.trans (finCongr (by
      norm_num [RawWord, rawWordCount])))

/-- The first component of the exact split is precisely Rust's low-18 mask. -/
@[simp] theorem q16PositionHighEquivRawWord_low18
    (value : Q16Position × Q16HighBits) :
    q16Candidate (q16PositionHighEquivRawWord value).val = value.1.val := by
  simp [q16Candidate, q16Bound, q16PositionHighEquivRawWord,
    finProdFinEquiv, Nat.add_mul_mod_self_left]

@[simp] theorem q16PositionHighEquivRawWord_symm_low18
    (word : RawWord) :
    ((q16PositionHighEquivRawWord.symm word).1 : Nat) =
      q16Candidate word.val := by
  let split := q16PositionHighEquivRawWord.symm word
  have reconstructed : q16PositionHighEquivRawWord split = word :=
    q16PositionHighEquivRawWord.apply_symm_apply word
  have low := q16PositionHighEquivRawWord_low18 split
  rw [reconstructed] at low
  exact low.symm

def blockWordIndexEquiv : Fin 8 × Fin 8 ≃ Fin 64 :=
  finProdFinEquiv.trans (finCongr (by norm_num))

/-- Exact reindexing of all eight deployed output blocks.  The first component
is the low-18 draw tape; the second retains every discarded high bit. -/
def candidateDigestBlocksEquiv :
    CandidateDigestBlocks ≃ Q16DrawTape × CandidateHighTape where
  toFun blocks :=
    (fun draw =>
      let coordinate := blockWordIndexEquiv.symm draw
      (q16PositionHighEquivRawWord.symm
        (digestWordsEquiv (blocks coordinate.1) coordinate.2)).1,
    fun draw =>
      let coordinate := blockWordIndexEquiv.symm draw
      (q16PositionHighEquivRawWord.symm
        (digestWordsEquiv (blocks coordinate.1) coordinate.2)).2)
  invFun tapes block :=
    digestWordsEquiv.symm fun word =>
      let draw := blockWordIndexEquiv (block, word)
      q16PositionHighEquivRawWord (tapes.1 draw, tapes.2 draw)
  left_inv blocks := by
    funext block
    apply digestWordsEquiv.injective
    funext word
    simp [blockWordIndexEquiv]
  right_inv tapes := by
    apply Prod.ext
    · funext draw
      simp [blockWordIndexEquiv]
    · funext draw
      simp [blockWordIndexEquiv]

def deployedQ16DrawTape (blocks : CandidateDigestBlocks) : Q16DrawTape :=
  (candidateDigestBlocksEquiv blocks).1

@[simp] theorem deployedQ16DrawTape_apply
    (blocks : CandidateDigestBlocks) (draw : Fin 64) :
    (deployedQ16DrawTape blocks draw : Nat) =
      q16Candidate
        (littleEndianWord
          (blocks (blockWordIndexEquiv.symm draw).1)
          (blockWordIndexEquiv.symm draw).2) := by
  simp [deployedQ16DrawTape, candidateDigestBlocksEquiv,
    digestWordsEquiv_apply_val]

/-- Fixing all sixty-four low-18 draws leaves exactly the sixty-four discarded
high-14 coordinates. -/
def candidateDigestDrawFibreEquiv (draws : Q16DrawTape) :
    {blocks : CandidateDigestBlocks // deployedQ16DrawTape blocks = draws} ≃
      CandidateHighTape where
  toFun blocks := (candidateDigestBlocksEquiv blocks.1).2
  invFun high :=
    ⟨candidateDigestBlocksEquiv.symm (draws, high), by
      simp [deployedQ16DrawTape]⟩
  left_inv blocks := by
    apply Subtype.ext
    apply candidateDigestBlocksEquiv.injective
    rw [candidateDigestBlocksEquiv.apply_symm_apply]
    apply Prod.ext
    · simpa [deployedQ16DrawTape] using blocks.2.symm
    · rfl
  right_inv high := by
    simp

theorem candidate_digest_draw_fibre_card_exact (draws : Q16DrawTape) :
    Fintype.card
        {blocks : CandidateDigestBlocks // deployedQ16DrawTape blocks = draws} =
      2 ^ 896 := by
  rw [Fintype.card_congr (candidateDigestDrawFibreEquiv draws)]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  calc
    ((2 : Nat) ^ 14) ^ 64 = (2 : Nat) ^ (14 * 64) :=
      (pow_mul 2 14 64).symm
    _ = (2 : Nat) ^ 896 := by norm_num

/-! ## All sixty-four cloned candidate branches at once -/

abbrev Q16CandidateDigestForest := Fin 64 → CandidateDigestBlocks
abbrev Q16CandidateDrawForest := Fin 64 → Q16DrawTape
abbrev Q16CandidateHighForest := Fin 64 → CandidateHighTape

def q16CandidateDigestForestEquiv :
    Q16CandidateDigestForest ≃
      Q16CandidateDrawForest × Q16CandidateHighForest where
  toFun forest :=
    (fun counter => (candidateDigestBlocksEquiv (forest counter)).1,
      fun counter => (candidateDigestBlocksEquiv (forest counter)).2)
  invFun tapes counter :=
    candidateDigestBlocksEquiv.symm
      (tapes.1 counter, tapes.2 counter)
  left_inv forest := by
    funext counter
    simp
  right_inv tapes := by
    apply Prod.ext <;> funext counter <;> simp

def deployedQ16DrawForest
    (forest : Q16CandidateDigestForest) : Q16CandidateDrawForest :=
  (q16CandidateDigestForestEquiv forest).1

def q16DigestForestDrawFibreEquiv (draws : Q16CandidateDrawForest) :
    {forest : Q16CandidateDigestForest //
      deployedQ16DrawForest forest = draws} ≃
      Q16CandidateHighForest where
  toFun forest := (q16CandidateDigestForestEquiv forest.1).2
  invFun high :=
    ⟨q16CandidateDigestForestEquiv.symm (draws, high), by
      simp [deployedQ16DrawForest]⟩
  left_inv forest := by
    apply Subtype.ext
    apply q16CandidateDigestForestEquiv.injective
    rw [q16CandidateDigestForestEquiv.apply_symm_apply]
    apply Prod.ext
    · simpa [deployedQ16DrawForest] using forest.2.symm
    · rfl
  right_inv high := by simp

/-- Every complete ideal draw forest has the same number of deployed digest
forests above it.  This is the exact finite statement that uniform full-output
ROM blocks project to uniform q16 candidate draws. -/
theorem q16_digest_forest_draw_fibres_equal
    (source target : Q16CandidateDrawForest) :
    Fintype.card
        {forest : Q16CandidateDigestForest //
          deployedQ16DrawForest forest = source} =
      Fintype.card
        {forest : Q16CandidateDigestForest //
          deployedQ16DrawForest forest = target} := by
  rw [Fintype.card_congr (q16DigestForestDrawFibreEquiv source),
    Fintype.card_congr (q16DigestForestDrawFibreEquiv target)]

/-! ## Audit -/

#print axioms q16PositionHighEquivRawWord_low18
#print axioms q16PositionHighEquivRawWord_symm_low18
#print axioms candidateDigestBlocksEquiv
#print axioms deployedQ16DrawTape_apply
#print axioms candidate_digest_draw_fibre_card_exact
#print axioms q16CandidateDigestForestEquiv
#print axioms q16_digest_forest_draw_fibres_equal

end

end AspisK1.V7Tag73Q16DigestDrawReindex
