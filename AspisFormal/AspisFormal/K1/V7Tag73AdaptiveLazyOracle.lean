import AspisFormal.K1.V7Tag73ResourceLazyOracle

/-!
# Causal finite lazy-oracle target counting for Tag 73

This file proves the adaptive finite-uniform lemma that the resource module
deliberately did not assume.  A `CausalTargetTree` is an operational decision
tree: at each fresh 256-bit answer it chooses a finite target set, and only
after seeing that answer does it choose the subtree used at the next step.
Consequently every target set is a deterministic function of prior answers;
it cannot depend on the current or any future answer.

The proof counts complete fresh-answer tapes.  It neither assumes independent
bad events nor takes one-event probability bounds as premises.  The only
uniformity used is the explicit uniform PMF on the finite tape type.  No BCS
coefficient, compiler conclusion, restoration premise, or extraction premise
occurs here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AdaptiveLazyOracle

set_option maxRecDepth 2048

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73ResourceLazyOracle

noncomputable section

/-! ## Finite fresh-answer tapes -/

/-- A length-indexed tape, exposed from left to right. -/
def FreshAnswerTape (Output : Type) : Nat → Type
  | 0 => PUnit
  | steps + 1 => Output × FreshAnswerTape Output steps

instance freshAnswerTapeFintype {Output : Type} [Fintype Output] :
    ∀ steps, Fintype (FreshAnswerTape Output steps)
  | 0 => inferInstanceAs (Fintype PUnit)
  | steps + 1 =>
      letI := freshAnswerTapeFintype (Output := Output) steps
      inferInstanceAs (Fintype (Output × FreshAnswerTape Output steps))

instance freshAnswerTapeNonempty {Output : Type} [Nonempty Output] :
    ∀ steps, Nonempty (FreshAnswerTape Output steps)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | steps + 1 =>
      letI := freshAnswerTapeNonempty (Output := Output) steps
      inferInstanceAs (Nonempty (Output × FreshAnswerTape Output steps))

theorem fresh_answer_tape_card
    {Output : Type} [Fintype Output] (steps : Nat) :
    Fintype.card (FreshAnswerTape Output steps) =
      Fintype.card Output ^ steps := by
  induction steps with
  | zero => simp [FreshAnswerTape]
  | succ steps ih =>
      change Fintype.card (Output × FreshAnswerTape Output steps) =
        Fintype.card Output ^ (steps + 1)
      rw [Fintype.card_prod, ih, pow_succ]
      exact Nat.mul_comm _ _

/-! ## Causal target decision trees -/

/-- The list index contains one target-cardinality cap per fresh exposure.
The continuation is selected only after the current answer is revealed, which
makes causality structural rather than an external predicate. -/
inductive CausalTargetTree (Output : Type) : List Nat → Type
  | done : CausalTargetTree Output []
  | step {cap : Nat} {caps : List Nat}
      (targets : Finset Output)
      (targetCardLe : targets.card ≤ cap)
      (next : Output → CausalTargetTree Output caps) :
      CausalTargetTree Output (cap :: caps)

def CausalTargetTree.everHits
    {Output : Type} [DecidableEq Output] :
    {caps : List Nat} → CausalTargetTree Output caps →
      FreshAnswerTape Output caps.length → Prop
  | [], .done, _ => False
  | _ :: _, .step targets _ next, tape =>
      tape.1 ∈ targets ∨ (next tape.1).everHits tape.2

def causalHitEvent
    {Output : Type} [DecidableEq Output]
    {caps : List Nat} (tree : CausalTargetTree Output caps) :
    Set (FreshAnswerTape Output caps.length) :=
  {tape | tree.everHits tape}

noncomputable def causalHitCount
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {caps : List Nat} (tree : CausalTargetTree Output caps) : Nat := by
  classical
  exact Fintype.card
    {tape : FreshAnswerTape Output caps.length // tree.everHits tape}

/-! ## One-step subtype decomposition -/

private def headTargetEquiv
    {Output Tail : Type} [DecidableEq Output]
    (targets : Finset Output) :
    {pair : Output × Tail // pair.1 ∈ targets} ≃ (↥targets × Tail) where
  toFun pair := (⟨pair.1.1, pair.2⟩, pair.1.2)
  invFun pair := ⟨(pair.1.1, pair.2), pair.1.2⟩
  left_inv pair := by cases pair with | mk pair property => cases pair; rfl
  right_inv pair := by cases pair with | mk head tail => cases head; rfl

private def residualHitEquiv
    {Output : Type} [DecidableEq Output]
    {caps : List Nat}
    (next : Output → CausalTargetTree Output caps) :
    {pair : Output × FreshAnswerTape Output caps.length //
      (next pair.1).everHits pair.2} ≃
      Σ output : Output,
        {tail : FreshAnswerTape Output caps.length //
          (next output).everHits tail} where
  toFun pair := ⟨pair.1.1, ⟨pair.1.2, pair.2⟩⟩
  invFun pair := ⟨(pair.1, pair.2.1), pair.2.2⟩
  left_inv pair := by cases pair with | mk pair property => cases pair; rfl
  right_inv pair := by cases pair with | mk output tail => cases tail; rfl

/-- One causal step is covered by the paths hitting the current target set
and the paths missing it but hitting a later target.  The inequality is a
plain subtype-union bound; no probabilistic independence is used. -/
theorem causal_hit_count_step_le
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {cap : Nat} {caps : List Nat}
    (targets : Finset Output) (targetCardLe : targets.card ≤ cap)
    (next : Output → CausalTargetTree Output caps) :
    causalHitCount (.step targets targetCardLe next) ≤
      targets.card * Fintype.card (FreshAnswerTape Output caps.length) +
      ∑ output : Output, causalHitCount (next output) := by
  classical
  let current : (Output × FreshAnswerTape Output caps.length) → Prop :=
    fun pair => pair.1 ∈ targets
  let later : (Output × FreshAnswerTape Output caps.length) → Prop :=
    fun pair => (next pair.1).everHits pair.2
  let stepHitEquiv :
      {tape : FreshAnswerTape Output (cap :: caps).length //
        (CausalTargetTree.step targets targetCardLe next).everHits tape} ≃
      {pair : Output × FreshAnswerTape Output caps.length //
        pair.1 ∈ targets ∨ (next pair.1).everHits pair.2} :=
    { toFun := fun tape =>
        ⟨(tape.1.1, tape.1.2), by
          simpa [CausalTargetTree.everHits, FreshAnswerTape] using tape.2⟩
      invFun := fun pair =>
        ⟨(pair.1.1, pair.1.2), by
          simpa [CausalTargetTree.everHits, FreshAnswerTape] using pair.2⟩
      left_inv := by
        intro tape
        cases tape with
        | mk tape property => cases tape; rfl
      right_inv := by
        intro pair
        cases pair with
        | mk pair property => cases pair; rfl }
  have countUnfold :
      causalHitCount (.step targets targetCardLe next) =
        Fintype.card
          {pair : Output × FreshAnswerTape Output caps.length //
            pair.1 ∈ targets ∨ (next pair.1).everHits pair.2} := by
    unfold causalHitCount
    exact Fintype.card_congr stepHitEquiv
  rw [countUnfold]
  change Fintype.card
      {pair : Output × FreshAnswerTape Output caps.length //
        current pair ∨ later pair} ≤ _
  calc
    Fintype.card {pair : Output × FreshAnswerTape Output caps.length //
          current pair ∨ later pair} ≤
        Fintype.card {pair : Output × FreshAnswerTape Output caps.length //
          current pair} +
        Fintype.card {pair : Output × FreshAnswerTape Output caps.length //
          later pair} := by
      exact Fintype.card_subtype_or current later
    _ = targets.card *
          Fintype.card (FreshAnswerTape Output caps.length) +
        ∑ output : Output, causalHitCount (next output) := by
      rw [Fintype.card_congr (headTargetEquiv targets)]
      rw [Fintype.card_congr (residualHitEquiv next)]
      simp [causalHitCount, current, later]

private theorem causal_count_recurrence
    (outputCard cap : Nat) (caps : List Nat) :
    cap * outputCard ^ caps.length +
        outputCard * (caps.sum * outputCard ^ (caps.length - 1)) =
      (cap + caps.sum) * outputCard ^ caps.length := by
  cases caps with
  | nil => simp
  | cons first rest =>
      simp only [List.length_cons, List.sum_cons, Nat.succ_sub_one]
      rw [pow_succ]
      ring

/-! ## Main adaptive counting theorem -/

/-- Strong causal finite-tape theorem.  If exposure `i` has an adaptively
chosen target set of size at most `caps[i]`, then the number of complete tapes
that ever hit a target is at most

`sum(caps) * |Output|^(number_of_exposures - 1)`.

The target tree itself enforces that the current target set depends only on
answers already exposed. -/
theorem causal_hit_count_le_target_caps
    {Output : Type} [Fintype Output] [DecidableEq Output] :
    ∀ {caps : List Nat} (tree : CausalTargetTree Output caps),
      causalHitCount tree ≤
        caps.sum * Fintype.card Output ^ (caps.length - 1)
  | [], .done => by
      simp [causalHitCount, CausalTargetTree.everHits]
  | cap :: caps, .step targets targetCardLe next => by
      have firstStep :=
        causal_hit_count_step_le targets targetCardLe next
      have tails : ∀ output : Output,
          causalHitCount (next output) ≤
            caps.sum * Fintype.card Output ^ (caps.length - 1) := by
        intro output
        exact causal_hit_count_le_target_caps (next output)
      have tailSum :
          (∑ output : Output, causalHitCount (next output)) ≤
            Fintype.card Output *
              (caps.sum * Fintype.card Output ^ (caps.length - 1)) := by
        calc
          (∑ output : Output, causalHitCount (next output)) ≤
              ∑ _output : Output,
                caps.sum * Fintype.card Output ^ (caps.length - 1) := by
            exact Finset.sum_le_sum fun output _ => tails output
          _ = Fintype.card Output *
                (caps.sum * Fintype.card Output ^ (caps.length - 1)) := by
            simp
      have firstTarget :
          targets.card *
              Fintype.card (FreshAnswerTape Output caps.length) ≤
            cap * Fintype.card Output ^ caps.length := by
        rw [fresh_answer_tape_card]
        exact Nat.mul_le_mul_right _ targetCardLe
      calc
        causalHitCount (.step targets targetCardLe next) ≤
            targets.card *
                Fintype.card (FreshAnswerTape Output caps.length) +
              ∑ output : Output, causalHitCount (next output) := firstStep
        _ ≤ cap * Fintype.card Output ^ caps.length +
              Fintype.card Output *
                (caps.sum * Fintype.card Output ^ (caps.length - 1)) := by
          exact Nat.add_le_add firstTarget tailSum
        _ = (cap + caps.sum) * Fintype.card Output ^ caps.length :=
          causal_count_recurrence (Fintype.card Output) cap caps
        _ = (cap :: caps).sum *
              Fintype.card Output ^ ((cap :: caps).length - 1) := by
          simp

/-! ## Uniform Digest256 law -/

noncomputable def uniformDigestFreshTape (steps : Nat) :
    PMF (FreshAnswerTape Digest256 steps) :=
  PMF.uniformOfFintype (FreshAnswerTape Digest256 steps)

private theorem ennreal_natCast_le_of_nat_le {left right : Nat}
    (bound : left ≤ right) :
    (left : ENNReal) ≤ (right : ENNReal) := by
  exact_mod_cast bound

/-- Exact probability/count identity for the explicit uniform fresh-answer
tape. -/
theorem uniform_digest_causal_hit_probability_eq
    {caps : List Nat} (tree : CausalTargetTree Digest256 caps) :
    (uniformDigestFreshTape caps.length).toOuterMeasure
        (causalHitEvent tree) =
      (causalHitCount tree : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ caps.length) := by
  classical
  unfold uniformDigestFreshTape
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change (causalHitCount tree : ENNReal) /
      (Fintype.card (FreshAnswerTape Digest256 caps.length) : ENNReal) = _
  rw [fresh_answer_tape_card, deployed_digest_256_cardinality]
  norm_num

/-- Exact-equivalent probability form of the causal target theorem.  This
avoids any cancellation convention at zero exposures; for every nonempty cap
list its right side simplifies mathematically to `sum(caps)/2^256`. -/
theorem uniform_digest_causal_hit_probability_le_exact_count
    {caps : List Nat} (tree : CausalTargetTree Digest256 caps) :
    (uniformDigestFreshTape caps.length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((caps.sum * (2 ^ 256) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ caps.length) := by
  rw [uniform_digest_causal_hit_probability_eq]
  apply ENNReal.div_le_div_right
  have bound := causal_hit_count_le_target_caps tree
  rw [deployed_digest_256_cardinality] at bound
  exact ennreal_natCast_le_of_nat_le bound

/-! ## Collision tree: targets are exactly the prior answers -/

def collisionTargetTreeFrom (step remaining : Nat)
    (seen : Finset Digest256) (seenCardLe : seen.card ≤ step) :
    CausalTargetTree Digest256 (List.range' step remaining) := by
  induction remaining generalizing step seen with
  | zero => exact .done
  | succ remaining ih =>
      rw [List.range'_succ]
      exact .step seen seenCardLe fun output =>
        ih (step + 1) (insert output seen)
          ((Finset.card_insert_le output seen).trans
            (Nat.add_le_add_right seenCardLe 1))

def collisionTargetTree (freshExposures : Nat) :
    CausalTargetTree Digest256 (List.range' 0 freshExposures) :=
  collisionTargetTreeFrom 0 freshExposures ∅ (by simp)

theorem collision_caps_sum_exact (freshExposures : Nat) :
    (List.range' 0 freshExposures).sum =
      freshExposures.choose 2 := by
  rw [List.sum_range', Nat.choose_two_right]
  simp

/-- First-principles adaptive birthday count.  The coefficient is exactly the
number of unordered pairs, not a generic quadratic slogan. -/
theorem collision_tree_hit_count_le_choose_two
    (freshExposures : Nat) :
    causalHitCount (collisionTargetTree freshExposures) ≤
      freshExposures.choose 2 *
        (2 ^ 256) ^ (freshExposures - 1) := by
  have bound := causal_hit_count_le_target_caps
    (collisionTargetTree freshExposures)
  rw [collision_caps_sum_exact, deployed_digest_256_cardinality] at bound
  simp only [List.length_range'] at bound
  exact bound

theorem strict_envelope_collision_tree_hit_count_le
    (envelope : StrictTag73ResourceEnvelope) :
    causalHitCount
        (collisionTargetTree envelope.full256FreshExposures) ≤
      envelope.full256FreshExposures.choose 2 *
        (2 ^ 256) ^ (envelope.full256FreshExposures - 1) :=
  collision_tree_hit_count_le_choose_two envelope.full256FreshExposures

/-! ## Reusable rectangular target families -/

/-- A target tree with `attempts` causal exposures and at most `targetsPerStep`
targets at every exposure has coefficient exactly
`attempts * targetsPerStep`.  This is the shape used after an operational
forward-reference/programming-conflict reduction. -/
theorem replicated_target_tree_hit_count_le
    (attempts targetsPerStep : Nat)
    (tree : CausalTargetTree Digest256
      (List.replicate attempts targetsPerStep)) :
    causalHitCount tree ≤
      (attempts * targetsPerStep) *
        (2 ^ 256) ^ (attempts - 1) := by
  have bound := causal_hit_count_le_target_caps tree
  rw [deployed_digest_256_cardinality] at bound
  simpa [List.sum_replicate] using bound

/-- Programming-conflict target-count specialization from the strict
resource envelope.  This theorem applies to a concrete causal tree; it does
not assert that every programming conflict has already been mapped to it. -/
theorem strict_envelope_programming_target_tree_hit_count_le
    (envelope : StrictTag73ResourceEnvelope)
    (tree : CausalTargetTree Digest256
      (List.replicate envelope.programmedPoints
        envelope.full256FreshExposures)) :
    causalHitCount tree ≤
      (envelope.programmedPoints * envelope.full256FreshExposures) *
        (2 ^ 256) ^ (envelope.programmedPoints - 1) :=
  replicated_target_tree_hit_count_le _ _ tree

/-- q16-forest target-count specialization.  Padding a shorter actual forest
with empty target nodes is an operational query-DAG obligation, not assumed by
this counting theorem. -/
theorem strict_envelope_q16_target_tree_hit_count_le
    (envelope : StrictTag73ResourceEnvelope)
    (tree : CausalTargetTree Digest256
      (List.replicate 1088 envelope.full256FreshExposures)) :
    causalHitCount tree ≤
      (1088 * envelope.full256FreshExposures) *
        (2 ^ 256) ^ (1088 - 1) :=
  replicated_target_tree_hit_count_le _ _ tree

#print axioms fresh_answer_tape_card
#print axioms causal_hit_count_step_le
#print axioms causal_hit_count_le_target_caps
#print axioms uniform_digest_causal_hit_probability_eq
#print axioms uniform_digest_causal_hit_probability_le_exact_count
#print axioms collision_caps_sum_exact
#print axioms collision_tree_hit_count_le_choose_two
#print axioms strict_envelope_collision_tree_hit_count_le
#print axioms replicated_target_tree_hit_count_le
#print axioms strict_envelope_programming_target_tree_hit_count_le
#print axioms strict_envelope_q16_target_tree_hit_count_le

end

end AspisK1.V7Tag73AdaptiveLazyOracle
