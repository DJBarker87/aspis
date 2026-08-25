import AspisFormal.V5SaltedMerkleSimulator

/-!
# V6 shared-salt two-tree hiding interface

Each V6 logical leaf carries one 256-bit hidden salt and two typed leaf
records, one for the 26-M31 C1 tree and one for the 3-QM31 C2 tree.  The two
hash inputs therefore have to be treated as one paired experiment rather
than as two independent-salt experiments.

The statistical theorem below reuses the generic fixed-function simulator on
the paired digest.  Its named `PairedSaltHidingHash` premise is intentionally
explicit: it is not a theorem about SHA-256.  The final section separately
checks the bounded-random-oracle input inventory and the resulting 102-bit
integer bound required by the V6 assurance blueprint.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

open scoped ENNReal

namespace AspisV6PairedSaltHiding

open AspisV5SaltedMerkleSimulator

variable {ι S V1 V2 D Tag Out : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype S] [DecidableEq S] [Nonempty S]

/-- One hash call for each typed tree, using exactly the same hidden salt. -/
def pairedLeafHash
    (leafH : Tag → Sum V1 V2 → S → D)
    (c1Tag c2Tag : Tag) : Unit → (V1 × V2) → S → (D × D) :=
  fun _ values salt =>
    (leafH c1Tag (.inl values.1) salt,
      leafH c2Tag (.inr values.2) salt)

/-- Named fixed-function premise for a pair of distinct typed leaf inputs
under one fresh 256-bit salt. -/
structure PairedSaltHidingHash
    (leafH : Tag → Sum V1 V2 → S → D)
    (c1Tag c2Tag : Tag) (ζ : ℝ≥0∞) : Prop where
  distinctTags : c1Tag ≠ c2Tag
  pairIndist : SaltHidingHash (pairedLeafHash leafH c1Tag c2Tag) ζ

/-- The generic simulator can consume the paired-salt premise without
splitting or resampling the common salt. -/
theorem paired_fullView_hiding
    {leafH : Tag → Sum V1 V2 → S → D}
    {c1Tag c2Tag : Tag} {ζ : ℝ≥0∞}
    (hH : PairedSaltHidingHash leafH c1Tag c2Tag ζ)
    (Q : Finset ι) (left right : ι → V1 × V2)
    (hagree : ∀ i ∈ Q, left i = right i) :
    statDist
        ((PMF.uniformOfFintype (ι → S)).map
          (fullView (pairedLeafHash leafH c1Tag c2Tag) () Q left))
        ((PMF.uniformOfFintype (ι → S)).map
          (fullView (pairedLeafHash leafH c1Tag c2Tag) () Q right))
      ≤ ((Fintype.card ι - Q.card : Nat) : ℝ≥0∞) * ζ := by
  exact fullView_hiding hH.pairIndist () Q left right hagree

/-- Any deterministic packaging of the fine paired view—including the two
binary roots, both minimal frontiers, and the shared opened records—can only
decrease the statistical distance. -/
theorem paired_binary_packaging_hiding
    {leafH : Tag → Sum V1 V2 → S → D}
    {c1Tag c2Tag : Tag} {ζ : ℝ≥0∞}
    (hH : PairedSaltHidingHash leafH c1Tag c2Tag ζ)
    (Q : Finset ι) (left right : ι → V1 × V2)
    (hagree : ∀ i ∈ Q, left i = right i)
    (package : MerkleView ι (V1 × V2) S (D × D) → Out) :
    statDist
        (((PMF.uniformOfFintype (ι → S)).map
          (fullView (pairedLeafHash leafH c1Tag c2Tag) () Q left)).map package)
        (((PMF.uniformOfFintype (ι → S)).map
          (fullView (pairedLeafHash leafH c1Tag c2Tag) () Q right)).map package)
      ≤ ((Fintype.card ι - Q.card : Nat) : ℝ≥0∞) * ζ := by
  exact (statDist_map_le _ _ package).trans
    (paired_fullView_hiding hH Q left right hagree)

omit [Fintype ι] [Fintype S] [DecidableEq S] [Nonempty S] in
/-- A queried record releases both typed values and their one common salt. -/
theorem opened_pair_uses_exactly_one_shared_salt
    (Q : Finset ι) (values : ι → V1 × V2) (salts : ι → S)
    (i : ι) (hi : i ∈ Q) :
    openedRecords Q values salts i = some (values i, salts i) := by
  simp [openedRecords, hi]

/-! ## Exact bounded-random-oracle inventory -/

/-- Two depth-18 binary trees have `2^18` logical paired leaves. -/
def leafCount : Nat := 262_144

/-- Exact distinct-input inventory from the V6 blueprint:

* two typed leaf inputs per logical leaf;
* one salt-derivation input per logical leaf;
* both binary trees' internal nodes;
* transcript/compiler inputs, fixed overhead, and deployment framing.
-/
def distinctInputCount : Nat :=
  2 * leafCount + leafCount + 2 * (leafCount - 1) + 53_892 + 8 + 637

def attemptCap : Nat := 17
def cappedInputCount : Nat := attemptCap * distinctInputCount
def unorderedPairs (n : Nat) : Nat := n * (n - 1) / 2

theorem exact_leaf_count : leafCount = 2 ^ 18 := by
  norm_num [leafCount]

theorem exact_distinct_input_inventory : distinctInputCount = 1_365_255 := by
  norm_num [distinctInputCount, leafCount]

theorem exact_capped_input_inventory : cappedInputCount = 23_209_335 := by
  norm_num [cappedInputCount, attemptCap, distinctInputCount, leafCount]

/-- Oracle-relative bad-event bound: an adversary making `QH` hash queries
hits one of the capped hidden inputs, or two compiler inputs collide. -/
noncomputable def eproBadEventUpper (QH : Real) : Real :=
  cappedInputCount * QH / 2 ^ 256 +
    unorderedPairs cappedInputCount / 2 ^ 256

/-- With at most `2^128` adversarial hash queries, the exact paired-input
inventory is below `2^-102`.  This keeps the full factor two for the two typed
leaf inputs sharing each salt. -/
theorem paired_epro_bad_event_le_two_pow_neg_102
    (QH : Real) (_hQHnonnegative : 0 ≤ QH) (hQH : QH ≤ 2 ^ 128) :
    eproBadEventUpper QH ≤ (1 : Real) / 2 ^ 102 := by
  have hscaled :
      (cappedInputCount : Real) * QH ≤
        (cappedInputCount : Real) * 2 ^ 128 := by
    exact mul_le_mul_of_nonneg_left hQH (by positivity)
  unfold eproBadEventUpper
  calc
    (cappedInputCount : Real) * QH / 2 ^ 256 +
          (unorderedPairs cappedInputCount : Real) / 2 ^ 256
      ≤ (cappedInputCount : Real) * 2 ^ 128 / 2 ^ 256 +
          (unorderedPairs cappedInputCount : Real) / 2 ^ 256 := by
        gcongr
    _ ≤ (1 : Real) / 2 ^ 102 := by
      norm_num [cappedInputCount, attemptCap, distinctInputCount, leafCount,
        unorderedPairs]

#print axioms paired_fullView_hiding
#print axioms paired_binary_packaging_hiding
#print axioms opened_pair_uses_exactly_one_shared_salt
#print axioms paired_epro_bad_event_le_two_pow_neg_102

end AspisV6PairedSaltHiding
