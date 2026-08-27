import Mathlib

/-!
# Public-variant routing for the pair copy registry

The private-transfer and withdrawal traces use different stable sources for
the output pair and for the second value.  The copy registry must nevertheless
have one fixed active-row inventory.  Both source links are therefore always
present and receive complementary weights from the public transition-kind
bit.  This file proves the exact algebraic routing consequence.
-/

set_option autoImplicit false

namespace AspisPool.V7PairVariantCopyRouting

def transferWeight {K : Type} (variant : K) : K := variant
def withdrawalWeight {K : Type} [One K] [Sub K] (variant : K) : K := 1 - variant

def PublicVariantBit {K : Type} [Ring K] (variant : K) : Prop :=
  variant * (variant - 1) = 0

/-- Both fixed links remain in the registry.  Only their public weights select
which stable source must equal the common output-pair destination. -/
def VariantRoutedEquality {K : Type} [Ring K]
    (variant transferSource withdrawalSource destination : K) : Prop :=
  PublicVariantBit variant ∧
    transferWeight variant * (transferSource - destination) = 0 ∧
    withdrawalWeight variant * (withdrawalSource - destination) = 0

theorem public_variant_cases
    {K : Type} [CommRing K] [NoZeroDivisors K]
    {variant : K} (valid : PublicVariantBit variant) :
    variant = 0 ∨ variant = 1 := by
  rcases eq_zero_or_eq_zero_of_mul_eq_zero valid with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

theorem transfer_variant_routes_transfer_source
    {K : Type} [Ring K]
    {transferSource withdrawalSource destination : K}
    (routed : VariantRoutedEquality (1 : K) transferSource withdrawalSource
      destination) :
    transferSource = destination := by
  have selected := routed.2.1
  have difference : transferSource - destination = 0 := by
    simpa [transferWeight] using selected
  exact sub_eq_zero.mp difference

theorem withdrawal_variant_routes_withdrawal_source
    {K : Type} [Ring K]
    {transferSource withdrawalSource destination : K}
    (routed : VariantRoutedEquality (0 : K) transferSource withdrawalSource
      destination) :
    withdrawalSource = destination := by
  have selected := routed.2.2
  have difference : withdrawalSource - destination = 0 := by
    simpa [withdrawalWeight] using selected
  exact sub_eq_zero.mp difference

/-- For any valid public variant the routed destination equals exactly the
selected source. -/
theorem valid_variant_routes_selected_source
    {K : Type} [CommRing K] [NoZeroDivisors K]
    {variant transferSource withdrawalSource destination : K}
    (routed : VariantRoutedEquality variant transferSource withdrawalSource
      destination) :
    (variant = 1 ∧ transferSource = destination) ∨
      (variant = 0 ∧ withdrawalSource = destination) := by
  rcases public_variant_cases routed.1 with zero | one
  · right
    refine ⟨zero, ?_⟩
    subst variant
    exact withdrawal_variant_routes_withdrawal_source routed
  · left
    refine ⟨one, ?_⟩
    subst variant
    exact transfer_variant_routes_transfer_source routed

theorem complementary_weights_sum_to_one
    {K : Type} [Ring K] (variant : K) :
    transferWeight variant + withdrawalWeight variant = 1 := by
  simp [transferWeight, withdrawalWeight]

/-- The row inventory is independent of the public variant: both endpoints
exist even when one link has zero weight. -/
def fixedVariantLinkCount : Nat := 2

theorem exact_fixed_variant_link_count : fixedVariantLinkCount = 2 := rfl

#print axioms public_variant_cases
#print axioms transfer_variant_routes_transfer_source
#print axioms withdrawal_variant_routes_withdrawal_source
#print axioms valid_variant_routes_selected_source
#print axioms complementary_weights_sum_to_one
#print axioms exact_fixed_variant_link_count

end AspisPool.V7PairVariantCopyRouting
