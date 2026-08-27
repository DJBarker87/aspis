import AspisFormal.K1.V7Tag73Q16SemanticProbability
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Raw ideal K1.3 error ledger for Tag-73

This module records the three genuine K1.3 losses before any proof-of-work
normalization:

* the exact first-cap-203 q16 compact-schedule ratio; and
* the published one-fold challenge cap over the complete QM31 field; and
* the degree-at-most-16 joint query/relation collision at nonzero `rho`; and
* the three later degree-six relation-alpha repair sets.

The raw sum is below `2^-73`.  No 31- or 34-bit work factor appears in any
definition or theorem consumed by the classical-ROM AoK closure.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K13IdealErrorLedger

open scoped ENNReal
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Frozen output of the independent cap-203 recurrence certificate.  Its
equality with `semanticCompactFavourable` is intentionally kept in the
certificate bridge, so this small arithmetic ledger does not force all 4,150
generated certificate modules into an ordinary local build. -/
def exactK13CompactFavourable : Nat :=
  2168847668270364480248463894820533103335517458992692508721007794996625408

/-- Exact raw q16 consistency loss. -/
def exactQ16IdealRawError : ENNReal :=
  (Nat.choose 9557 16 : ENNReal) /
    (exactK13CompactFavourable : ENNReal)

/-- Exact raw one-fold list-decoding loss.  Alpha is sampled from all of
QM31, whose cardinality is `P^4`. -/
def exactOneFoldIdealRawError : ENNReal :=
  (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)

/-- Exact loss for the repaired joint degree-at-most-16 `rho` polynomial.
The source samples `rho` uniformly from nonzero QM31. -/
def exactJointQueryBatchIdealRawError : ENNReal :=
  (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)

/-- Conservative union of the three post-query relation rounds, each with an
exact degree-six alpha collision set. -/
def exactLaterRelationAlphaIdealRawError : ENNReal :=
  (18 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)

/-- The complete raw K1.3 error term installed in the end-to-end theorem. -/
def exactK13IdealRawError : ENNReal :=
  exactQ16IdealRawError + exactOneFoldIdealRawError +
    exactJointQueryBatchIdealRawError + exactLaterRelationAlphaIdealRawError

/-- The unnormalized q16, one-fold and query-batch loss is already below
`2^-73`. -/
theorem exact_k13_ideal_raw_error_le_two_pow_neg73 :
    exactK13IdealRawError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 73) := by
  unfold exactK13IdealRawError exactQ16IdealRawError
    exactOneFoldIdealRawError exactJointQueryBatchIdealRawError
    exactLaterRelationAlphaIdealRawError
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have q16Finite :
      (((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
        (exactK13CompactFavourable : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp)
      (by norm_num [exactK13CompactFavourable])
  have oneFoldFinite :
      ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  have firstFinite :
      (((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
          (exactK13CompactFavourable : ENNReal) +
        (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨q16Finite, oneFoldFinite⟩
  have jointBatchFinite :
      ((16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  have firstThreeFinite :
      ((((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
            (exactK13CompactFavourable : ENNReal) +
          (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) +
        (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨firstFinite, jointBatchFinite⟩
  have laterAlphaFinite :
      ((18 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.2 ⟨firstThreeFinite, laterAlphaFinite⟩)
    (by norm_num)).mp
  rw [ENNReal.toReal_add firstThreeFinite laterAlphaFinite,
    ENNReal.toReal_add firstFinite jointBatchFinite,
    ENNReal.toReal_add q16Finite oneFoldFinite]
  norm_num [exactK13CompactFavourable, foldChallengeCap, P,
    Nat.descFactorial, Nat.factorial]

end

#print axioms exact_k13_ideal_raw_error_le_two_pow_neg73

end AspisK1.V7Tag73K13IdealErrorLedger
