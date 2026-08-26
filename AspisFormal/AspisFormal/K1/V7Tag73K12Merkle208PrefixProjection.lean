import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73K12Merkle208CollisionProbability
import AspisFormal.K1.V7Tag73HiddenTapeAveraging
import AspisFormal.K1.V7BudgetedAdaptiveTargets

/-!
# Uniform 256-to-208 prefix projection for Tag-73 K1.2

The deployed SHA oracle returns 32 runtime bytes, while K1.2 consumes its
first 26 bytes through the exact runtime-byte equivalence.  This module proves
that projection is uniform by splitting every 32-byte digest bijectively into
its 26-byte Merkle prefix and six-byte tail.  It is the distribution bridge
between the existing full-output lazy oracle and the shared-208-bit collision
counting theorem; no SHA security or extraction-failure inclusion is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K12Merkle208PrefixProjection

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7BudgetedAdaptiveTargets
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73K12Merkle208CollisionProbability
open AspisPool.V7MerkleQueryGrammar

noncomputable section

abbrev RuntimeDigest256 := AspisK1.V7Tag73TranscriptSchedule.Digest256
abbrev MerkleDigest208 := AspisPool.V7MerkleQueryGrammar.Digest208
abbrev RuntimeDigestTail48 := Fin 6 → UInt8

def digestIndexSplitEquiv : Fin 26 ⊕ Fin 6 ≃ Fin 32 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

def runtimePrefixEquivMerkle : (Fin 26 → UInt8) ≃ MerkleDigest208 :=
  { toFun := fun pfx index => runtimeByteEquivMerkleByte (pfx index)
    invFun := fun pfx index => runtimeByteEquivMerkleByte.symm (pfx index)
    left_inv := by intro pfx; ext index; simp
    right_inv := by intro pfx; ext index; simp }

def runtimeDigestSplitEquiv :
    RuntimeDigest256 ≃ (MerkleDigest208 × RuntimeDigestTail48) :=
  ((Equiv.piCongrLeft (fun _ : Fin 32 ↦ UInt8)
      digestIndexSplitEquiv).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin 26 ⊕ Fin 6 ↦ UInt8))).trans
      (Equiv.prodCongr runtimePrefixEquivMerkle (Equiv.refl _))

theorem runtime_digest_split_prefix_is_deployed_projection
    (digest : RuntimeDigest256) :
    (runtimeDigestSplitEquiv digest).1 =
      runtimeDigest256PrefixToMerkleDigest digest := by
  apply funext
  intro index
  change runtimeByteEquivMerkleByte
      (digest (digestIndexSplitEquiv (Sum.inl index))) =
    runtimeByteEquivMerkleByte (digest ⟨index.val, by omega⟩)
  apply congrArg runtimeByteEquivMerkleByte
  apply congrArg digest
  apply Fin.ext
  rfl

def deployedPrefixFiber
    (target : MerkleDigest208) : Set RuntimeDigest256 :=
  {digest | runtimeDigest256PrefixToMerkleDigest digest = target}

def deployedPrefixFiberEquiv (target : MerkleDigest208) :
    ↑(deployedPrefixFiber target) ≃ RuntimeDigestTail48 where
  toFun digest := (runtimeDigestSplitEquiv digest.1).2
  invFun tail :=
    ⟨runtimeDigestSplitEquiv.symm (target, tail), by
      change runtimeDigest256PrefixToMerkleDigest
          (runtimeDigestSplitEquiv.symm (target, tail)) = target
      rw [← runtime_digest_split_prefix_is_deployed_projection]
      simp⟩
  left_inv digest := by
    apply Subtype.ext
    apply runtimeDigestSplitEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · calc
        target = runtimeDigest256PrefixToMerkleDigest digest.1 := digest.2.symm
        _ = (runtimeDigestSplitEquiv digest.1).1 :=
          (runtime_digest_split_prefix_is_deployed_projection digest.1).symm
    · simp
  right_inv tail := by
    simp

theorem runtime_digest_tail48_cardinality :
    Fintype.card RuntimeDigestTail48 = 2 ^ 48 := by
  calc
    Fintype.card RuntimeDigestTail48 =
        Fintype.card (Fin 6 → Fin 256) :=
      Fintype.card_congr
        (Equiv.arrowCongr (Equiv.refl (Fin 6)) uint8EquivFin256)
    _ = 2 ^ 48 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      calc
        256 ^ 6 = (2 ^ 8) ^ 6 := by norm_num
        _ = 2 ^ (8 * 6) := by rw [pow_mul]
        _ = 2 ^ 48 := by norm_num

noncomputable instance deployedPrefixFiberFintype
    (target : MerkleDigest208) : Fintype ↑(deployedPrefixFiber target) :=
  Fintype.ofFinite _

theorem deployed_prefix_fiber_cardinality (target : MerkleDigest208) :
    Fintype.card ↑(deployedPrefixFiber target) = 2 ^ 48 := by
  rw [Fintype.card_congr (deployedPrefixFiberEquiv target)]
  exact runtime_digest_tail48_cardinality

/-! ## Full-output preimages of 208-bit target sets

The operational scheduler branches on the complete 256-bit answer.  It is
therefore not sound to represent a later target set by a decision tree whose
continuations see only the 208-bit projection.  Instead, every 208-bit target
set is lifted to its full 256-bit preimage.  The next-node continuation still
receives the complete answer, while the exact `2^48` fiber factor preserves
the desired `2^-208` probability per target.
-/

def deployedPrefixTargetPreimage (targets : Finset MerkleDigest208) :
    Finset RuntimeDigest256 :=
  Finset.univ.filter fun digest =>
    runtimeDigest256PrefixToMerkleDigest digest ∈ targets

def deployedPrefixTargetPreimageEquiv (targets : Finset MerkleDigest208) :
    ↑(deployedPrefixTargetPreimage targets) ≃
      (↑targets × RuntimeDigestTail48) where
  toFun digest :=
    (⟨runtimeDigest256PrefixToMerkleDigest digest.1, by
        exact (Finset.mem_filter.mp digest.2).2⟩,
      (runtimeDigestSplitEquiv digest.1).2)
  invFun value :=
    ⟨runtimeDigestSplitEquiv.symm (value.1.1, value.2), by
      simp only [deployedPrefixTargetPreimage, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [← runtime_digest_split_prefix_is_deployed_projection]
      simpa using value.1.2⟩
  left_inv digest := by
    apply Subtype.ext
    apply runtimeDigestSplitEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact runtime_digest_split_prefix_is_deployed_projection digest.1
    · rfl
  right_inv value := by
    rcases value with ⟨target, tail⟩
    apply Prod.ext
    · apply Subtype.ext
      change
        runtimeDigest256PrefixToMerkleDigest
            (runtimeDigestSplitEquiv.symm (target.1, tail)) = target.1
      rw [← runtime_digest_split_prefix_is_deployed_projection]
      simp
    · simp

theorem deployed_prefix_target_preimage_cardinality
    (targets : Finset MerkleDigest208) :
    (deployedPrefixTargetPreimage targets).card = targets.card * 2 ^ 48 := by
  rw [← Fintype.card_coe, Fintype.card_congr
    (deployedPrefixTargetPreimageEquiv targets), Fintype.card_prod,
    Fintype.card_coe, runtime_digest_tail48_cardinality]

theorem deployed_prefix_target_preimage_card_le
    (targets : Finset MerkleDigest208) {targetCap : Nat}
    (targetCardLe : targets.card ≤ targetCap) :
    (deployedPrefixTargetPreimage targets).card ≤ targetCap * 2 ^ 48 := by
  rw [deployed_prefix_target_preimage_cardinality]
  exact Nat.mul_le_mul_right _ targetCardLe

/-- Every concrete 208-bit prefix has exactly `2^48` full SHA outputs above
it, hence exactly mass `2^-208` under the deployed uniform 256-bit law. -/
theorem uniform_digest256_deployed_prefix_probability_exact
    (target : MerkleDigest208) :
    uniformDigest256.toOuterMeasure (deployedPrefixFiber target) =
      (1 : ENNReal) / ((2 : ENNReal) ^ 208) := by
  classical
  unfold uniformDigest256
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [deployed_prefix_fiber_cardinality]
  have digestCard :
      (Fintype.card RuntimeDigest256 : ENNReal) = (2 : ENNReal) ^ 256 := by
    rw [deployed_digest_256_cardinality]
    norm_num
  rw [digestCard]
  have cast48 :
      ((2 ^ 48 : Nat) : ENNReal) = (2 : ENNReal) ^ 48 := by
    norm_num
  rw [cast48, show 256 = 48 + 208 by norm_num, pow_add]
  simpa using
    (ENNReal.mul_div_mul_left (c := (2 : ENNReal) ^ 48)
      1 ((2 : ENNReal) ^ 208) (by positivity) (by finiteness))

/-! ## Exact multi-exposure projection

The single-output fiber calculation is not enough for an adaptive K1.2 game:
the verifier exposes a sequence of fresh SHA answers.  The following explicit
equivalence splits an entire fresh-answer tape into its 208-bit prefix tape
and independent 48-bit tail tape.  Consequently every event depending only
on the deployed prefixes has exactly the same probability under the uniform
256-bit tape as it has under the uniform 208-bit tape used by the causal
target-counting theorem.
-/

def interleaveProductEquiv {A B C D : Type} :
    ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun value := ((value.1.1, value.2.1), (value.1.2, value.2.2))
  invFun value := ((value.1.1, value.2.1), (value.1.2, value.2.2))
  left_inv := by intro value; rcases value with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv := by intro value; rcases value with ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl

def runtimeFreshTapeSplitEquiv : ∀ steps : Nat,
    FreshAnswerTape RuntimeDigest256 steps ≃
      (FreshAnswerTape MerkleDigest208 steps ×
        FreshAnswerTape RuntimeDigestTail48 steps)
  | 0 =>
      { toFun := fun _ => (PUnit.unit, PUnit.unit)
        invFun := fun _ => PUnit.unit
        left_inv := by intro tape; cases tape; rfl
        right_inv := by
          intro tape
          rcases tape with ⟨pfx, tail⟩
          cases pfx
          cases tail
          rfl }
  | steps + 1 => by
      change (RuntimeDigest256 × FreshAnswerTape RuntimeDigest256 steps) ≃
        ((MerkleDigest208 × FreshAnswerTape MerkleDigest208 steps) ×
          (RuntimeDigestTail48 ×
            FreshAnswerTape RuntimeDigestTail48 steps))
      exact (Equiv.prodCongr runtimeDigestSplitEquiv
        (runtimeFreshTapeSplitEquiv steps)).trans interleaveProductEquiv

def runtimeFreshPrefixTape (steps : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 steps) :
    FreshAnswerTape MerkleDigest208 steps :=
  (runtimeFreshTapeSplitEquiv steps tape).1

def liftedMerklePrefixEvent (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) :
    Set (FreshAnswerTape RuntimeDigest256 steps) :=
  {tape | runtimeFreshPrefixTape steps tape ∈ event}

def liftedMerklePrefixEventEquiv (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) :
    ↑(liftedMerklePrefixEvent steps event) ≃
      (↑event × FreshAnswerTape RuntimeDigestTail48 steps) where
  toFun tape :=
    (⟨(runtimeFreshTapeSplitEquiv steps tape.1).1, tape.2⟩,
      (runtimeFreshTapeSplitEquiv steps tape.1).2)
  invFun value :=
    ⟨(runtimeFreshTapeSplitEquiv steps).symm (value.1.1, value.2), by
      change
        (runtimeFreshTapeSplitEquiv steps
          ((runtimeFreshTapeSplitEquiv steps).symm
            (value.1.1, value.2))).1 ∈ event
      simpa using value.1.2⟩
  left_inv tape := by
    apply Subtype.ext
    change
      (runtimeFreshTapeSplitEquiv steps).symm
        ((runtimeFreshTapeSplitEquiv steps tape.1).1,
          (runtimeFreshTapeSplitEquiv steps tape.1).2) = tape.1
    exact (runtimeFreshTapeSplitEquiv steps).symm_apply_apply tape.1
  right_inv value := by
    rcases value with ⟨prefixMember, tail⟩
    have split := (runtimeFreshTapeSplitEquiv steps).apply_symm_apply
      (prefixMember.1, tail)
    apply Prod.ext
    · apply Subtype.ext
      change
        (runtimeFreshTapeSplitEquiv steps
          ((runtimeFreshTapeSplitEquiv steps).symm
            (prefixMember.1, tail))).1 = prefixMember.1
      exact congrArg Prod.fst split
    · change
        (runtimeFreshTapeSplitEquiv steps
          ((runtimeFreshTapeSplitEquiv steps).symm
            (prefixMember.1, tail))).2 = tail
      exact congrArg Prod.snd split

noncomputable instance liftedMerklePrefixEventFintype (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) :
    Fintype ↑(liftedMerklePrefixEvent steps event) :=
  Fintype.ofFinite _

noncomputable instance merkleFreshEventFintype (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) : Fintype ↑event :=
  Fintype.ofFinite _

theorem runtime_tail_fresh_tape_cardinality (steps : Nat) :
    Fintype.card (FreshAnswerTape RuntimeDigestTail48 steps) =
      (2 ^ 48) ^ steps := by
  rw [fresh_answer_tape_card, runtime_digest_tail48_cardinality]

theorem lifted_merkle_prefix_event_cardinality (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) :
    Fintype.card ↑(liftedMerklePrefixEvent steps event) =
      Fintype.card ↑event * (2 ^ 48) ^ steps := by
  rw [Fintype.card_congr (liftedMerklePrefixEventEquiv steps event),
    Fintype.card_prod, runtime_tail_fresh_tape_cardinality]

/-- Exact distributional bridge for any event over a finite prefix tape. -/
theorem uniform_digest256_lifted_prefix_event_probability_exact
    (steps : Nat)
    (event : Set (FreshAnswerTape MerkleDigest208 steps)) :
    (uniformDigestFreshTape steps).toOuterMeasure
        (liftedMerklePrefixEvent steps event) =
      (uniformMerkleDigest208FreshTape steps).toOuterMeasure event := by
  classical
  unfold uniformDigestFreshTape uniformMerkleDigest208FreshTape
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply,
    lifted_merkle_prefix_event_cardinality,
    fresh_answer_tape_card, fresh_answer_tape_card,
    deployed_digest_256_cardinality, merkle_digest208_cardinality]
  push_cast
  have two48 :
      (281474976710656 : ENNReal) = (2 : ENNReal) ^ 48 := by norm_num
  have two208 :
      (411376139330301510538742295639337626245683966408394965837152256 :
        ENNReal) = (2 : ENNReal) ^ 208 := by norm_num
  have two256 :
      (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
        ENNReal) = (2 : ENNReal) ^ 256 := by norm_num
  rw [two48, two208, two256]
  have fullPower :
      (((2 : ENNReal) ^ 256) ^ steps) =
        ((2 : ENNReal) ^ 48) ^ steps *
          ((2 : ENNReal) ^ 208) ^ steps := by
    rw [← mul_pow, ← pow_add]
  rw [fullPower]
  simpa [mul_comm] using
    (ENNReal.mul_div_mul_left
      (c := ((2 : ENNReal) ^ 48) ^ steps)
      (Fintype.card ↑event : ENNReal)
      (((2 : ENNReal) ^ 208) ^ steps)
      (by positivity) (by finiteness))

/-! ## Deployed-law specializations

These corollaries eliminate the temporary 208-bit probability space from the
two K1.2 counting bounds.  Their left sides are events on the actual uniform
256-bit SHA-answer tape; the only observation made by the events is the exact
deployed 26-byte prefix projection proved above.
-/

theorem uniform_digest256_lifted_resolution_probability_le_exact_count
    (tree : CausalTargetTree MerkleDigest208
      (List.replicate prefixFixedVerifierExposureCap
        prefixFixedResolutionTargetCap)) :
    (uniformDigestFreshTape
        (List.replicate prefixFixedVerifierExposureCap
          prefixFixedResolutionTargetCap).length).toOuterMeasure
        (liftedMerklePrefixEvent
          (List.replicate prefixFixedVerifierExposureCap
            prefixFixedResolutionTargetCap).length
          (causalHitEvent tree)) ≤
      ((prefixFixedResolutionTargetCoefficient *
          (2 ^ 208) ^ (prefixFixedVerifierExposureCap - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ prefixFixedVerifierExposureCap) := by
  rw [uniform_digest256_lifted_prefix_event_probability_exact]
  exact uniform_merkle_digest208_resolution_probability_le_exact_count tree

theorem uniform_digest256_lifted_partial_raw_collision_probability_le_exact_count
    (parameters : ExactCompilerResourceParameters) :
    (uniformDigestFreshTape
        (List.range' 0
          (k12PartialRawCollisionExposureCap parameters)).length).toOuterMeasure
        (liftedMerklePrefixEvent
          (List.range' 0
            (k12PartialRawCollisionExposureCap parameters)).length
          (causalHitEvent
            (prefixCollisionTargetTree
              (k12PartialRawCollisionExposureCap parameters)))) ≤
      (((k12PartialRawCollisionExposureCap parameters).choose 2 *
          (2 ^ 208) ^
            (k12PartialRawCollisionExposureCap parameters - 1) : Nat) :
          ENNReal) /
        (((2 : ENNReal) ^ 208) ^
          k12PartialRawCollisionExposureCap parameters) := by
  rw [uniform_digest256_lifted_prefix_event_probability_exact]
  exact uniform_partial_raw_collision_probability_le_exact_count parameters

/-! ## Hidden-tape averaging under the deployed 256-bit law -/

def hiddenDependentLiftedMerkleCausalHitEvent
    {HiddenTape : Type} {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree MerkleDigest208 caps) :
    Set (HiddenTape × FreshAnswerTape RuntimeDigest256 caps.length) :=
  {pair | (tree pair.1).everHits
    (runtimeFreshPrefixTape caps.length pair.2)}

theorem hidden_dependent_lifted_merkle_causal_joint_event_slice
    {HiddenTape : Type} {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree MerkleDigest208 caps)
    (hidden : HiddenTape) :
    jointEventSlice (hiddenDependentLiftedMerkleCausalHitEvent tree) hidden =
      liftedMerklePrefixEvent caps.length (causalHitEvent (tree hidden)) := by
  rfl

/-- Averaging over an arbitrary finite prover tape introduces no loss.  The
fresh coordinates remain the actual uniform 256-bit SHA outputs, while the
hidden-dependent causal tree sees precisely their deployed 208-bit prefixes.
-/
theorem hidden_dependent_lifted_merkle_causal_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) {caps : List Nat}
    (tree : HiddenTape → CausalTargetTree MerkleDigest208 caps) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw caps.length).toOuterMeasure
        (hiddenDependentLiftedMerkleCausalHitEvent tree) ≤
      ((caps.sum * (2 ^ 208) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ caps.length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [hidden_dependent_lifted_merkle_causal_joint_event_slice,
    uniform_digest256_lifted_prefix_event_probability_exact]
  exact uniform_merkle_digest208_causal_hit_probability_le_exact_count
    (tree hidden)

theorem hidden_dependent_lifted_resolution_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (tree : HiddenTape → CausalTargetTree MerkleDigest208
      (List.replicate prefixFixedVerifierExposureCap
        prefixFixedResolutionTargetCap)) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (List.replicate prefixFixedVerifierExposureCap
          prefixFixedResolutionTargetCap).length).toOuterMeasure
        (hiddenDependentLiftedMerkleCausalHitEvent tree) ≤
      ((prefixFixedResolutionTargetCoefficient *
          (2 ^ 208) ^ (prefixFixedVerifierExposureCap - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ prefixFixedVerifierExposureCap) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [hidden_dependent_lifted_merkle_causal_joint_event_slice]
  exact uniform_digest256_lifted_resolution_probability_le_exact_count
    (tree hidden)

/-! ## Answer-dependent verifier phase with an exact charged budget -/

def hiddenDependentLiftedBudgetedMerkleHitEvent
    {HiddenTape : Type} {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree MerkleDigest208 targetCap caps budget) :
    Set (HiddenTape × FreshAnswerTape RuntimeDigest256 caps.length) :=
  {pair | (tree pair.1).toCausal.everHits
    (runtimeFreshPrefixTape caps.length pair.2)}

theorem hidden_dependent_lifted_budgeted_merkle_joint_event_slice
    {HiddenTape : Type} {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree MerkleDigest208 targetCap caps budget)
    (hidden : HiddenTape) :
    jointEventSlice
        (hiddenDependentLiftedBudgetedMerkleHitEvent tree) hidden =
      liftedMerklePrefixEvent caps.length
        (budgetedCausalHitEvent (tree hidden)) := by
  rfl

/-- A phase may begin at a tape-dependent coordinate without charging every
padded coordinate.  Only the structurally consumed charged budget appears in
the numerator. -/
theorem hidden_dependent_lifted_budgeted_merkle_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree MerkleDigest208 targetCap caps budget) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw caps.length).toOuterMeasure
        (hiddenDependentLiftedBudgetedMerkleHitEvent tree) ≤
      ((budget * targetCap *
          (2 ^ 208) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^ caps.length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [hidden_dependent_lifted_budgeted_merkle_joint_event_slice,
    uniform_digest256_lifted_prefix_event_probability_exact]
  change
    (uniformMerkleDigest208FreshTape caps.length).toOuterMeasure
        (causalHitEvent (tree hidden).toCausal) ≤ _
  rw [uniform_merkle_digest208_causal_hit_probability_eq]
  apply ENNReal.div_le_div_right
  have bound := budgeted_causal_hit_count_le (tree hidden)
  rw [merkle_digest208_cardinality] at bound
  exact_mod_cast bound

/-- Root-verifier specialization.  The verifier can start after an adaptive
number of prover coordinates, yet at most its exact 1,511 fresh-call budget is
charged and every charged target set contains at most the 32 two-tree first
unresolved digests. -/
theorem hidden_dependent_lifted_root_verifier_resolution_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (steps : Nat)
    (tree : HiddenTape →
      BudgetedCausalTargetTree MerkleDigest208
        prefixFixedResolutionTargetCap
        (List.replicate steps prefixFixedResolutionTargetCap)
        deployedFull256VerifierCallCap) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (List.replicate steps prefixFixedResolutionTargetCap).length).toOuterMeasure
        (hiddenDependentLiftedBudgetedMerkleHitEvent tree) ≤
      ((deployedFull256VerifierCallCap * prefixFixedResolutionTargetCap *
          (2 ^ 208) ^
            ((List.replicate steps prefixFixedResolutionTargetCap).length - 1) :
          Nat) : ENNReal) /
        (((2 : ENNReal) ^ 208) ^
          (List.replicate steps prefixFixedResolutionTargetCap).length) := by
  simpa using
    (hidden_dependent_lifted_budgeted_merkle_probability_le_exact_count
      hiddenLaw tree)

/-! ## Fully adaptive 256-bit scheduler specialization

Unlike the prefix-only bridge above, this is the form consumed by the actual
Tag-73 scheduler.  Its continuations observe the complete 256-bit answer.
At a charged coordinate the operational construction installs
`deployedPrefixTargetPreimage targets`, whose cap is exactly the 32-target
inventory times the `2^48` suffix fiber.
-/

def hiddenDependentBudgetedRuntimeHitEvent
    {HiddenTape : Type} {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree RuntimeDigest256 targetCap caps budget) :
    Set (HiddenTape × FreshAnswerTape RuntimeDigest256 caps.length) :=
  {pair | (tree pair.1).toCausal.everHits pair.2}

theorem hidden_dependent_budgeted_runtime_joint_event_slice
    {HiddenTape : Type} {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree RuntimeDigest256 targetCap caps budget)
    (hidden : HiddenTape) :
    jointEventSlice (hiddenDependentBudgetedRuntimeHitEvent tree) hidden =
      budgetedCausalHitEvent (tree hidden) := by
  rfl

theorem hidden_dependent_budgeted_runtime_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) {targetCap budget : Nat} {caps : List Nat}
    (tree : HiddenTape →
      BudgetedCausalTargetTree RuntimeDigest256 targetCap caps budget) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw caps.length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent tree) ≤
      ((budget * targetCap *
          (2 ^ 256) ^ (caps.length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ caps.length) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  rw [hidden_dependent_budgeted_runtime_joint_event_slice]
  change
    (uniformDigestFreshTape caps.length).toOuterMeasure
        (causalHitEvent (tree hidden).toCausal) ≤ _
  rw [uniform_digest_causal_hit_probability_eq]
  apply ENNReal.div_le_div_right
  have bound := budgeted_causal_hit_count_le (tree hidden)
  rw [deployed_digest_256_cardinality] at bound
  exact_mod_cast bound

/-- The operational root-verifier form.  Full 256-bit continuations are
retained, but at most 1,511 coordinates are charged and every installed
full-output target set is the preimage of at most 32 Merkle digests. -/
theorem hidden_dependent_budgeted_runtime_root_verifier_probability_le_exact_count
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape) (steps : Nat)
    (tree : HiddenTape →
      BudgetedCausalTargetTree RuntimeDigest256
        (prefixFixedResolutionTargetCap * 2 ^ 48)
        (List.replicate steps
          (prefixFixedResolutionTargetCap * 2 ^ 48))
        deployedFull256VerifierCallCap) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (List.replicate steps
          (prefixFixedResolutionTargetCap * 2 ^ 48)).length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent tree) ≤
      ((deployedFull256VerifierCallCap *
          (prefixFixedResolutionTargetCap * 2 ^ 48) *
          (2 ^ 256) ^
            ((List.replicate steps
              (prefixFixedResolutionTargetCap * 2 ^ 48)).length - 1) : Nat) :
        ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (List.replicate steps
            (prefixFixedResolutionTargetCap * 2 ^ 48)).length) := by
  simpa using
    (hidden_dependent_budgeted_runtime_probability_le_exact_count
      hiddenLaw tree)

#print axioms runtime_digest_split_prefix_is_deployed_projection
#print axioms deployed_prefix_fiber_cardinality
#print axioms uniform_digest256_deployed_prefix_probability_exact
#print axioms runtimeFreshTapeSplitEquiv
#print axioms lifted_merkle_prefix_event_cardinality
#print axioms uniform_digest256_lifted_prefix_event_probability_exact
#print axioms uniform_digest256_lifted_resolution_probability_le_exact_count
#print axioms uniform_digest256_lifted_partial_raw_collision_probability_le_exact_count
#print axioms hidden_dependent_lifted_merkle_causal_probability_le_exact_count
#print axioms hidden_dependent_lifted_resolution_probability_le_exact_count
#print axioms hidden_dependent_lifted_budgeted_merkle_probability_le_exact_count
#print axioms hidden_dependent_lifted_root_verifier_resolution_probability_le_exact_count
#print axioms deployed_prefix_target_preimage_cardinality
#print axioms deployed_prefix_target_preimage_card_le
#print axioms hidden_dependent_budgeted_runtime_probability_le_exact_count
#print axioms hidden_dependent_budgeted_runtime_root_verifier_probability_le_exact_count

end

end AspisK1.V7Tag73K12Merkle208PrefixProjection
