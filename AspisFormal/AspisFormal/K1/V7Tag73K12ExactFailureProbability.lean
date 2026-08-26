import AspisFormal.K1.V7Tag73K12CollisionSchedulerTree

/-!
# Exact Tag-73 K1.2 failure probability

The late-resolution and 208-bit-prefix-collision trees use different indexed
presentations of the same full 256-bit master tape.  This module proves those
presentations are exact equivalences, transports their uniform probabilities
without an independence assumption, and takes one union bound on the common
compiler sample space.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K12ExactFailureProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7BudgetedAdaptiveTargets
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73K12CollisionSchedulerTree
open AspisPool.V7MerkleQueryExtractor

noncomputable section

/-! ## Exact reindexing of the common fresh-answer tape -/

def setPreimageSubtypeEquiv
    {α β : Type} (equiv : α ≃ β) (event : Set β) :
    {value : α // value ∈ equiv ⁻¹' event} ≃
      {value : β // value ∈ event} where
  toFun value := ⟨equiv value.1, value.2⟩
  invFun value := ⟨equiv.symm value.1, by
    show equiv (equiv.symm value.1) ∈ event
    rw [equiv.apply_symm_apply]
    exact value.2⟩
  left_inv value := by ext; simp
  right_inv value := by ext; simp

theorem uniform_of_fintype_equiv_preimage_probability_eq
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (equiv : α ≃ β) (event : Set β) :
    (PMF.uniformOfFintype α).toOuterMeasure (equiv ⁻¹' event) =
      (PMF.uniformOfFintype β).toOuterMeasure event := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (setPreimageSubtypeEquiv equiv event),
    Fintype.card_congr equiv]

def k12RuntimeTapeEquiv {Output : Type} :
    ∀ remaining : Nat,
      FreshAnswerTape Output remaining ≃
        FreshAnswerTape Output (k12RuntimeCaps remaining).length
  | 0 => Equiv.refl _
  | remaining + 1 =>
      Equiv.prodCongr (Equiv.refl Output) (k12RuntimeTapeEquiv remaining)

@[simp] theorem k12_runtime_tape_equiv_apply
    {Output : Type} {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    k12RuntimeTapeEquiv remaining tape = k12RuntimeTape tape := by
  induction remaining with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      change (tape.1, k12RuntimeTapeEquiv remaining tape.2) =
        (tape.1, k12RuntimeTape tape.2)
      rw [inductionHypothesis]

def projectedPrefixCollisionTapeEquivFrom {Output : Type} (step : Nat) :
    ∀ remaining : Nat,
      FreshAnswerTape Output remaining ≃
        FreshAnswerTape Output
          (projectedPrefixCollisionCapsFrom step remaining).length
  | 0 => Equiv.refl _
  | remaining + 1 =>
      Equiv.prodCongr (Equiv.refl Output)
        (projectedPrefixCollisionTapeEquivFrom (step + 1) remaining)

@[simp] theorem projected_prefix_collision_tape_equiv_from_apply
    {Output : Type} (step : Nat) {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    projectedPrefixCollisionTapeEquivFrom step remaining tape =
      projectedPrefixCollisionTapeFrom step tape := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      change
        (tape.1,
          projectedPrefixCollisionTapeEquivFrom (step + 1) remaining tape.2) =
        (tape.1, projectedPrefixCollisionTapeFrom (step + 1) tape.2)
      rw [inductionHypothesis (step + 1)]

abbrev projectedPrefixCollisionTapeEquiv {Output : Type}
    (remaining : Nat) :
    FreshAnswerTape Output remaining ≃
      FreshAnswerTape Output
        (projectedPrefixCollisionCapsFrom 0 remaining).length :=
  projectedPrefixCollisionTapeEquivFrom 0 remaining

@[simp] theorem projected_prefix_collision_tape_equiv_apply
    {Output : Type} {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    projectedPrefixCollisionTapeEquiv remaining tape =
      projectedPrefixCollisionTape tape := by
  exact projected_prefix_collision_tape_equiv_from_apply 0 tape

/-! ## Both events on the canonical exact-compiler tape -/

def canonicalK12BudgetedHitEvent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    Set (FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :=
  {tape |
    (exactK12BudgetedSchedulerTree configuration transitionFuel hidden).toCausal
      |>.everHits (k12RuntimeTape tape)}

def canonicalK12CollisionHitEvent (freshExposures : Nat) :
    Set (FreshAnswerTape Digest256 freshExposures) :=
  {tape |
    (projectedPrefixCollisionTree freshExposures).everHits
      (projectedPrefixCollisionTape tape)}

theorem canonical_k12_budgeted_hit_probability_le_exact_count
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    (uniformDigestFreshTape
        (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (canonicalK12BudgetedHitEvent configuration transitionFuel hidden) ≤
      ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
          ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (exactCompilerTargetCaps parameters).length) := by
  let equiv := k12RuntimeTapeEquiv (Output := Digest256)
    (exactCompilerTargetCaps parameters).length
  have transported := uniform_of_fintype_equiv_preimage_probability_eq equiv
    (causalHitEvent
      (exactK12BudgetedSchedulerTree configuration transitionFuel hidden).toCausal)
  have counted :
      (uniformDigestFreshTape
          (k12RuntimeCaps
            (exactCompilerTargetCaps parameters).length).length).toOuterMeasure
          (causalHitEvent
            (exactK12BudgetedSchedulerTree configuration transitionFuel
              hidden).toCausal) ≤
        ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
            (2 ^ 256) ^
              ((k12RuntimeCaps
                (exactCompilerTargetCaps parameters).length).length - 1) :
            Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (k12RuntimeCaps
              (exactCompilerTargetCaps parameters).length).length) := by
    rw [uniform_digest_causal_hit_probability_eq]
    apply ENNReal.div_le_div_right
    have bound := budgeted_causal_hit_count_le
      (exactK12BudgetedSchedulerTree configuration transitionFuel hidden)
    rw [deployed_digest_256_cardinality] at bound
    exact_mod_cast bound
  rw [show equiv ⁻¹' causalHitEvent
      (exactK12BudgetedSchedulerTree configuration transitionFuel hidden).toCausal =
        canonicalK12BudgetedHitEvent configuration transitionFuel hidden by
      ext tape
      simp [equiv, canonicalK12BudgetedHitEvent, causalHitEvent]] at transported
  have transported' :
      (uniformDigestFreshTape
          (exactCompilerTargetCaps parameters).length).toOuterMeasure
          (canonicalK12BudgetedHitEvent configuration transitionFuel hidden) =
        (uniformDigestFreshTape
          (k12RuntimeCaps
            (exactCompilerTargetCaps parameters).length).length).toOuterMeasure
          (causalHitEvent
            (exactK12BudgetedSchedulerTree configuration transitionFuel
              hidden).toCausal) := by
    simpa only [uniformDigestFreshTape] using transported
  rw [transported']
  simpa [k12_runtime_caps_length] using counted

theorem canonical_k12_collision_hit_probability_le_exact_count
    (freshExposures : Nat) :
    (uniformDigestFreshTape freshExposures).toOuterMeasure
        (canonicalK12CollisionHitEvent freshExposures) ≤
      (((freshExposures.choose 2 * 2 ^ 48) *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  let equiv := projectedPrefixCollisionTapeEquiv
    (Output := Digest256) freshExposures
  have transported := uniform_of_fintype_equiv_preimage_probability_eq equiv
    (causalHitEvent (projectedPrefixCollisionTree freshExposures))
  have counted :=
    projected_prefix_collision_tree_probability_le_exact_count freshExposures
  rw [show equiv ⁻¹' causalHitEvent
      (projectedPrefixCollisionTree freshExposures) =
        canonicalK12CollisionHitEvent freshExposures by
      ext tape
      simp [equiv, canonicalK12CollisionHitEvent, causalHitEvent,
        projectedPrefixCollisionTape]] at transported
  have transported' :
      (uniformDigestFreshTape freshExposures).toOuterMeasure
          (canonicalK12CollisionHitEvent freshExposures) =
        (uniformDigestFreshTape
          (projectedPrefixCollisionCapsFrom 0 freshExposures).length).toOuterMeasure
          (causalHitEvent
            (projectedPrefixCollisionTree freshExposures)) := by
    simpa only [uniformDigestFreshTape] using transported
  rw [transported']
  exact counted

def exactK12CountedSchedulerEvent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) :
    Set (HiddenTape × FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :=
  {sample |
    sample.2 ∈ canonicalK12BudgetedHitEvent configuration transitionFuel
        sample.1 ∨
      sample.2 ∈ canonicalK12CollisionHitEvent
        (exactCompilerTargetCaps parameters).length}

/-- Exact same-tape K1.2 union bound.  No independence is used: each fixed
hidden-tape slice is bounded by ordinary subadditivity. -/
theorem exact_k12_counted_scheduler_event_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (exactK12CountedSchedulerEvent configuration transitionFuel) ≤
      ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
          ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (exactCompilerTargetCaps parameters).length) +
        ((((exactCompilerTargetCaps parameters).length.choose 2 * 2 ^ 48) *
          (2 ^ 256) ^
            ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
          ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (exactCompilerTargetCaps parameters).length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  have budgeted := canonical_k12_budgeted_hit_probability_le_exact_count
    configuration transitionFuel hidden
  have collision := canonical_k12_collision_hit_probability_le_exact_count
    (exactCompilerTargetCaps parameters).length
  have unionBound := measure_union_le
    (μ := (uniformDigestFreshTape
      (exactCompilerTargetCaps parameters).length).toOuterMeasure)
    (canonicalK12BudgetedHitEvent configuration transitionFuel hidden)
    (canonicalK12CollisionHitEvent
      (exactCompilerTargetCaps parameters).length)
  exact (by
    change (uniformDigestFreshTape
        (exactCompilerTargetCaps parameters).length).toOuterMeasure
      (canonicalK12BudgetedHitEvent configuration transitionFuel hidden ∪
        canonicalK12CollisionHitEvent
          (exactCompilerTargetCaps parameters).length) ≤ _
    exact unionBound.trans (add_le_add budgeted collision))

/-! ## The executable K1.2 classifier error event -/

/-- Canonical proof-relevant K1.2 error event.  The opening-acceptance and
source-trace coverage conjuncts are the exact Rust/source obligations; the
error itself is returned by the executable Lean classifier. -/
def exactPrefixK12ClassifiedErrorEvent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance sample,
    accepted_two_tree_openings (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input) ∧
      ExactPrefixK12SuppliedCoverage input ∧
      Nonempty (ExactPrefixK12Error input)}

theorem exact_prefix_k12_classified_error_subset_counted_scheduler_event
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 2 ≤ transitionFuel) :
    exactPrefixK12ClassifiedErrorEvent transitionFuel configuration projection
        fixedInstance ⊆
      exactK12CountedSchedulerEvent configuration transitionFuel := by
  intro sample member
  rcases member with
    ⟨input, openingsAccepted, suppliedCovered, ⟨error⟩⟩
  rcases exact_prefix_k12_error_implies_counted_scheduler_events
      transitionRoom openingsAccepted suppliedCovered error with late | collision
  · exact Or.inl late
  · exact Or.inr collision

/-- The concrete executable K1.2 error probability, under the exact compiler
joint law, inherits the same two-term same-tape bound. -/
theorem exact_prefix_k12_classified_error_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (transitionRoom : 2 ≤ transitionFuel) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPrefixK12ClassifiedErrorEvent transitionFuel configuration
          projection fixedInstance) ≤
      ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
          ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (exactCompilerTargetCaps parameters).length) +
        ((((exactCompilerTargetCaps parameters).length.choose 2 * 2 ^ 48) *
          (2 ^ 256) ^
            ((exactCompilerTargetCaps parameters).length - 1) : Nat) :
          ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (exactCompilerTargetCaps parameters).length) := by
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPrefixK12ClassifiedErrorEvent transitionFuel configuration
          projection fixedInstance) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactK12CountedSchedulerEvent configuration transitionFuel) :=
      measure_mono
        (exact_prefix_k12_classified_error_subset_counted_scheduler_event
          transitionFuel configuration projection fixedInstance transitionRoom)
    _ ≤ _ := by
      unfold exactCompilerJointLaw
      exact exact_k12_counted_scheduler_event_probability_le hiddenLaw
        configuration transitionFuel

#print axioms uniform_of_fintype_equiv_preimage_probability_eq
#print axioms k12_runtime_tape_equiv_apply
#print axioms projected_prefix_collision_tape_equiv_apply
#print axioms canonical_k12_budgeted_hit_probability_le_exact_count
#print axioms canonical_k12_collision_hit_probability_le_exact_count
#print axioms exact_k12_counted_scheduler_event_probability_le
#print axioms exact_prefix_k12_classified_error_subset_counted_scheduler_event
#print axioms exact_prefix_k12_classified_error_probability_le

end

end AspisK1.V7Tag73K12ExactFailureProbability
