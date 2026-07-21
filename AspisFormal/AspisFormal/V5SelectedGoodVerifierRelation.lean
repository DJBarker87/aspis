import AspisFormal.V5SelectionHidingAbort
import AspisFormal.SoundnessWorkNormalizedEndpoint

/-!
# The v5 selected-good verifier relation

The honest prover continues to use the deterministic three-branch
`AspisV5SelectionHidingAbort.select` rule and therefore releases the least good
schedule.  The verifier does not need to re-execute that honest-prover policy:
it checks that the serialized selector is in `Fin 3` and that the selected
public schedule satisfies `Good`.

This distinction is deliberate:

* honest-prover hiding is still the already-proved least-good transcript law;
* verifier soundness ranges over the union of the three selectable branches;
* the release endpoint already carries exactly this `selectorInflation = 3`.

Selected-good acceptance is not itself a hiding statement about arbitrary
accepted provers.  A prover that deliberately chooses between several good
branches as a function of its witness can leak through the serialized selector.
The honest prover does not do that: its least-good choice is a deterministic
public function of the candidate schedules.  The negative model below keeps
this soundness/hiding boundary explicit.

The file proves only those logical and arithmetic glue facts.  It does not
re-prove the cited BCS transform, identify `Good` with Rust arithmetic, or
claim that the current candidate construction is ready for deployment.
Computational PCS/Merkle binding, SHA/random-oracle behavior, the Fiat--Shamir
compiler, and exact Rust transcript correspondence remain named premises.
-/

namespace AspisV5SelectedGoodVerifierRelation

open AspisV5SelectionHidingAbort
open AspisWorkNormalizedEndpoint

variable {Schedule : Type*}

/-- The algebraic relation enforced by the selected-only verifier.  The
selector's range is represented by its type; the deployed parser must still
prove that its byte decodes to `Fin 3`. -/
def verifierAccepts
    (Good : Schedule → Bool) (schedules : Fin 3 → Schedule) (selected : Fin 3) : Prop :=
  Good (schedules selected) = true

/-! ## Fixed authenticated prefix and candidate order -/

/-- Exact order required of the executable transcript boundary.  The same
authenticated prefix, final polynomial and verified grinding nonce are fixed
for all three branches; only then is the selector absorbed and its schedule
derived.  `fixedAuthenticated` is deliberately a premise: it is where exact
Rust serialization/transcript correspondence and computational PCS/Merkle,
SHA/RO and Fiat--Shamir assumptions remain named rather than being faked as
information-theoretic Lean facts. -/
def FixedAuthenticatedCandidateOrder
    {Prefix Final Nonce State : Type*}
    (fixedAuthenticated : Prefix → Final → Nonce → Prop)
    (absorbFinal : Prefix → Final → State)
    (absorbNonce : State → Nonce → State)
    (absorbSelector : State → Fin 3 → State)
    (deriveSchedule : State → Schedule)
    (commonPrefix : Prefix) (final : Final) (nonce : Nonce)
    (schedules : Fin 3 → Schedule) : Prop :=
  fixedAuthenticated commonPrefix final nonce ∧
    ∀ selected,
      schedules selected =
        deriveSchedule
          (absorbSelector
            (absorbNonce (absorbFinal commonPrefix final) nonce) selected)

/-- Under the named executable/cryptographic order premise, selected-good
acceptance applies to exactly the branch derived after the fixed final value,
nonce and selector absorptions. -/
theorem accepted_schedule_has_fixed_authenticated_order
    {Prefix Final Nonce State : Type*}
    {fixedAuthenticated : Prefix → Final → Nonce → Prop}
    {absorbFinal : Prefix → Final → State}
    {absorbNonce : State → Nonce → State}
    {absorbSelector : State → Fin 3 → State}
    {deriveSchedule : State → Schedule}
    {commonPrefix : Prefix} {final : Final} {nonce : Nonce}
    {Good : Schedule → Bool} {schedules : Fin 3 → Schedule}
    {selected : Fin 3}
    (horder : FixedAuthenticatedCandidateOrder fixedAuthenticated
      absorbFinal absorbNonce absorbSelector deriveSchedule
      commonPrefix final nonce schedules)
    (haccept : verifierAccepts Good schedules selected) :
    fixedAuthenticated commonPrefix final nonce ∧
      Good
        (deriveSchedule
          (absorbSelector
            (absorbNonce (absorbFinal commonPrefix final) nonce) selected)) = true := by
  refine ⟨horder.1, ?_⟩
  rw [← horder.2 selected]
  exact haccept

/-- Every transcript produced by the honest least-good selector is accepted by
the selected-good verifier relation. -/
theorem honest_leastGood_is_accepted
    {Good : Schedule → Bool} {schedules : Fin 3 → Schedule} {selected : Fin 3}
    (hselected : select Good schedules = some selected) :
    verifierAccepts Good schedules selected := by
  exact good_of_select_eq_some hselected

/-- The selected-good relation is intentionally weaker than rechecking the
least-good policy: when branches zero and one are both good, selector one is
accepted even though it is not the honest selector.  This is a concrete tooth
against accidentally claiming verifier-enforced leastness. -/
theorem selectedGood_strictly_weaker_than_leastGood :
    ∃ (Good : Fin 3 → Bool) (schedules : Fin 3 → Fin 3) (selected : Fin 3),
      verifierAccepts Good schedules selected ∧
        select Good schedules ≠ some selected := by
  refine ⟨fun _ => true, id, 1, ?_, ?_⟩
  · rfl
  · simp [select]

/-! ## Hiding is an honest-prover property, not a soundness consequence -/

/-- Witness-independence of the released selector metadata.  The honest
least-good law proves this as part of the stronger composed transcript law;
selected-good verifier acceptance alone does not. -/
def SelectorMetadataWitnessIndependent {W : Type*} (choose : W → Fin 3) : Prop :=
  ∀ w₁ w₂, choose w₁ = choose w₂

/-- Concrete malicious-prover tooth.  All schedules are public and good and
the branch view may be constant, yet an accepted prover can serialize selector
zero for one witness and selector one for another.  Thus selected-good
soundness cannot be promoted to hiding of arbitrary accepted proofs. -/
theorem selectedGood_acceptance_does_not_imply_selector_hiding :
    ∃ (Good : Unit → Bool) (schedules : Fin 3 → Unit)
        (choose : Bool → Fin 3),
      (∀ witness, verifierAccepts Good schedules (choose witness)) ∧
        ¬ SelectorMetadataWitnessIndependent choose := by
  let choose : Bool → Fin 3
    | false => 0
    | true => 1
  refine ⟨fun _ => true, fun _ => (), choose, ?_, ?_⟩
  · intro witness
    cases witness <;> rfl
  · intro h
    have hfalseTrue := h false true
    simp [choose] at hfalseTrue

/-! ## Both selected-good checks are load-bearing -/

/-- A deliberately weakened relation that checks only that the selector was
decoded into `Fin 3`, while omitting `Good (schedules selected)`. -/
def selectorBoundOnlyAccepts
    (_Good : Schedule → Bool) (_schedules : Fin 3 → Schedule)
    (_selected : Fin 3) : Prop :=
  True

/-- Dropping the selected-Good check accepts an explicitly bad branch even
though the selector remains in range. -/
theorem dropping_selected_good_accepts_bad_branch :
    ∃ (Good : Fin 3 → Bool) (schedules : Fin 3 → Fin 3)
        (selected : Fin 3),
      selectorBoundOnlyAccepts Good schedules selected ∧
        Good (schedules selected) = false ∧
        ¬ verifierAccepts Good schedules selected := by
  refine ⟨fun _ => false, id, 0, trivial, rfl, ?_⟩
  simp [verifierAccepts]

/-- A deliberately weakened selected-good relation over an unbounded natural
selector. -/
def unboundedSelectedGoodAccepts
    (Good : Schedule → Bool) (schedules : ℕ → Schedule)
    (selected : ℕ) : Prop :=
  Good (schedules selected) = true

/-- Dropping the byte-to-`Fin 3` range check admits the concrete selector
value three. -/
theorem dropping_selector_bound_accepts_out_of_range :
    ∃ (Good : Unit → Bool) (schedules : ℕ → Unit) (selected : ℕ),
      ¬ selected < 3 ∧
        unboundedSelectedGoodAccepts Good schedules selected := by
  exact ⟨fun _ => true, fun _ => (), 3, by norm_num, rfl⟩

/-- Arithmetic form of the three-event union bound.  The actual probability
union is the named premise `hUnion`; this theorem only closes the exact
factor-three arithmetic used by the release ledger. -/
theorem three_selected_branches_union_bound
    (unionError branch0 branch1 branch2 eps : ℝ)
    (hUnion : unionError ≤ branch0 + branch1 + branch2)
    (h0 : branch0 ≤ eps) (h1 : branch1 ≤ eps) (h2 : branch2 ≤ eps) :
    unionError ≤ selectorInflation * eps := by
  unfold selectorInflation
  linarith

/-- Exact composition of the semantic three-event union premise with the
work-normalized release endpoint.  `hUnion` and the three per-branch bounds are
the load-bearing soundness/BCS interface; this theorem proves only their
factor-three arithmetic consequence. -/
theorem three_selected_branches_release_endpoint
    (unionError branch0 branch1 branch2 R capErr T : ℝ)
    (hUnion : unionError ≤ branch0 + branch1 + branch2)
    (h0 : branch0 ≤ bcsError roundError T R capErr)
    (h1 : branch1 ≤ bcsError roundError T R capErr)
    (h2 : branch2 ≤ bcsError roundError T R capErr)
    (hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    unionError ≤ 1 / 2 ^ 100 := by
  calc
    unionError ≤ selectorInflation * bcsError roundError T R capErr :=
      three_selected_branches_union_bound unionError branch0 branch1 branch2
        (bcsError roundError T R capErr) hUnion h0 h1 h2
    _ ≤ 1 / 2 ^ 100 :=
      release_endpoint R capErr T hRnn hR hcapnn hcap hT1 hTmax

/-- The maintained release theorem already budgets the selected-good
three-branch union through `selectorInflation = 3`.  All BCS, random-oracle and
capacity assumptions remain exactly the explicit assumptions of
`release_endpoint`. -/
theorem selectedGood_release_endpoint
    (R capErr T : ℝ)
    (hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation * bcsError roundError T R capErr ≤ 1 / 2 ^ 100 :=
  release_endpoint R capErr T hRnn hR hcapnn hcap hT1 hTmax

end AspisV5SelectedGoodVerifierRelation

#print axioms AspisV5SelectedGoodVerifierRelation.accepted_schedule_has_fixed_authenticated_order
#print axioms AspisV5SelectedGoodVerifierRelation.honest_leastGood_is_accepted
#print axioms AspisV5SelectedGoodVerifierRelation.selectedGood_strictly_weaker_than_leastGood
#print axioms
  AspisV5SelectedGoodVerifierRelation.selectedGood_acceptance_does_not_imply_selector_hiding
#print axioms AspisV5SelectedGoodVerifierRelation.dropping_selected_good_accepts_bad_branch
#print axioms AspisV5SelectedGoodVerifierRelation.dropping_selector_bound_accepts_out_of_range
#print axioms AspisV5SelectedGoodVerifierRelation.three_selected_branches_union_bound
#print axioms AspisV5SelectedGoodVerifierRelation.three_selected_branches_release_endpoint
#print axioms AspisV5SelectedGoodVerifierRelation.selectedGood_release_endpoint
