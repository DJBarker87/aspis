import AspisFormal.Pool.V7K15FailureProbabilityComposition
import AspisFormal.Pool.V7DeployedCopyLogUpCollisionBounds
import AspisFormal.Pool.V7PointClaimBatchBinding

/-!
# Exact algebraic-root inventory for the V7 K1.5 ledger

The deterministic K1.5 endpoint names thirteen failure branches.  This file
records the effective one-field root numerator for each branch and proves the
one overlap-sensitive refinement: after the earlier active-pole branch has
been excluded, a `CopyChiCollision` occupies at most 365 further `chi`
values, not the coarse 731-value pole-plus-Wronskian set.

The resulting numerator is 4078.  This is a root inventory, not yet a
probability theorem: the later state-restoration layer must prove that each
bad set is fixed at the corresponding Tag-73 challenge prefix.  In
particular, the selected width-29 component tuple may have been chosen after
`gamma`, so no pre-challenge consistency is hidden here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7K15FailureRootInventory

open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyLogUpCollisionBounds
open AspisPool.V7K15FailureProbabilityComposition
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact

/-- Effective `1 / |QM31|` numerator of each canonical K1.5 branch.

`tenRoundRepair`, `zerocheckEvaluation`, `oodMix`, `relationAlpha`, and
`gammaPointLane` already include their finite coordinate/round unions.  The
`copyChi` value is the non-pole Wronskian cap because `.activePole` precedes
it in the canonical classifier. -/
def effectiveRootCap : FailureKind → Nat
  | .tenRoundRepair => 10 * 27
  | .helperCancellation => 1
  | .zerocheckEvaluation => 10
  | .thetaLane => 24
  | .muZero => 1
  | .inactiveChi => 1
  | .activePole => 366
  | .copyChi => 365
  | .tupleCompression => 2928
  | .oodMix => 2
  | .relationAlpha => 4 * 6
  | .kappaPointRow => 2
  | .gammaPointLane => 3 * 28

/-- Exact non-duplicated numerator obtained from all thirteen canonical
branches. -/
theorem effectiveRootCap_sum_eq_4078 :
    (orderedFailureKinds.map effectiveRootCap).sum = 4078 := by
  decide

/-- K1.5 inventory after the strengthened restoration-wide K1.4 certificate
has already fixed all 87 point claims.  At that boundary
`.gammaPointLane` is impossible, so its old local 84-root allowance is not
charged again. -/
def pointCompatibleK14RootCap : FailureKind → Nat
  | .gammaPointLane => 0
  | kind => effectiveRootCap kind

theorem pointCompatibleK14RootCap_sum_eq_3994 :
    (orderedFailureKinds.map pointCompatibleK14RootCap).sum = 3994 := by
  decide

/-- The remaining twelve K1.5 algebraic branches are conservatively below
`2^-112` once point compatibility has been extracted at K1.4. -/
theorem pointCompatibleK14_root_inventory_le_two_pow_neg_112 :
    (3994 : ℝ) /
        ((Fintype.card QM31Exact : ℝ) - 1) ≤
      (1 : ℝ) / 2 ^ 112 := by
  rw [qm31Exact_card]
  norm_num [P]

/-- Even if every branch is conservatively charged against the nonzero-QM31
denominator, the complete 4078-root inventory is below `2^-112`.  Ordinary
samplers actually have denominator `|QM31|`; using `|QM31|-1` here safely
covers the nonzero `gamma` and `kappa` samplers as well. -/
theorem deployed_effective_root_inventory_le_two_pow_neg_112 :
    (4078 : ℝ) /
        ((Fintype.card QM31Exact : ℝ) - 1) ≤
      (1 : ℝ) / 2 ^ 112 := by
  rw [qm31Exact_card]
  norm_num [P]

theorem activePole_iff_mem_copyChiPoleSet
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda chi : QM31Exact) :
    DeployedCopyActivePole source lambda chi ↔
      chi ∈ copyChiPoleSet source lambda := by
  classical
  simp only [DeployedCopyActivePole, copyChiPoleSet, Finset.mem_filter,
    Finset.mem_univ, true_and, producerCompressedMultiset,
    consumerCompressedMultiset, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ]
  constructor
  · rintro (⟨link, equal⟩ | ⟨link, equal⟩)
    · exact Or.inl ⟨link, equal.symm⟩
    · exact Or.inr ⟨link, equal.symm⟩
  · rintro (⟨link, equal⟩ | ⟨link, equal⟩)
    · exact Or.inl ⟨link, equal.symm⟩
    · exact Or.inr ⟨link, equal.symm⟩

/-- Once the canonical earlier pole branch is absent, an actual chi
collision lies in the strict non-pole Wronskian set. -/
theorem copyChiCollision_mem_nonPole_of_not_activePole
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda chi : QM31Exact)
    (collision : CopyChiCollision source lambda chi)
    (notActivePole : ¬ DeployedCopyActivePole source lambda chi) :
    chi ∈ copyChiNonPoleCollisionSet source lambda := by
  classical
  have notPoleSet : chi ∉ copyChiPoleSet source lambda := by
    simpa [activePole_iff_mem_copyChiPoleSet source lambda chi] using
      notActivePole
  have notProducer :
      chi ∉ producerCompressedMultiset source lambda := by
    intro member
    apply notPoleSet
    simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl member
  have notConsumer :
      chi ∉ consumerCompressedMultiset source lambda := by
    intro member
    apply notPoleSet
    simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr member
  simp only [copyChiNonPoleCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨collision, notProducer, notConsumer⟩

/-- The canonical post-pole chi branch has the strict 365-root cap. -/
theorem canonical_copyChi_branch_card_le_365
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiNonPoleCollisionSet source lambda).card ≤
      effectiveRootCap .copyChi := by
  simpa [effectiveRootCap] using
    copyChiNonPoleCollisionSet_card_le_365 source lambda

/-- The preceding pole branch has exactly the separately budgeted cap. -/
theorem canonical_activePole_branch_card_le_366
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiPoleSet source lambda).card ≤ effectiveRootCap .activePole := by
  simpa [effectiveRootCap] using copyChiPoleSet_card_le_366 source lambda

/-- The two canonical active-pole/non-pole-collision branches together cost
at most 731 chi values, with poles counted once. -/
theorem canonical_activePole_union_copyChi_card_le_731
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiPoleSet source lambda ∪
      copyChiNonPoleCollisionSet source lambda).card ≤ 731 := by
  calc
    (copyChiPoleSet source lambda ∪
        copyChiNonPoleCollisionSet source lambda).card ≤
        (copyChiPoleSet source lambda).card +
          (copyChiNonPoleCollisionSet source lambda).card :=
      Finset.card_union_le _ _
    _ ≤ 366 + 365 := Nat.add_le_add
      (copyChiPoleSet_card_le_366 source lambda)
      (copyChiNonPoleCollisionSet_card_le_365 source lambda)
    _ = 731 := by norm_num

/-- The fixed-C1 tagged-tuple collision branch has its literal degree cap. -/
theorem canonical_tupleCompression_branch_card_le_2928
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (copyLambdaCollisionSet source).card ≤
      effectiveRootCap .tupleCompression := by
  simpa [effectiveRootCap] using copyLambdaCollisionSet_card_le_2928 source

#print axioms effectiveRootCap_sum_eq_4078
#print axioms pointCompatibleK14RootCap_sum_eq_3994
#print axioms pointCompatibleK14_root_inventory_le_two_pow_neg_112
#print axioms deployed_effective_root_inventory_le_two_pow_neg_112
#print axioms activePole_iff_mem_copyChiPoleSet
#print axioms copyChiCollision_mem_nonPole_of_not_activePole
#print axioms canonical_copyChi_branch_card_le_365
#print axioms canonical_activePole_branch_card_le_366
#print axioms canonical_activePole_union_copyChi_card_le_731
#print axioms canonical_tupleCompression_branch_card_le_2928

end AspisPool.V7K15FailureRootInventory
