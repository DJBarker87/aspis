import AspisFormal.V5FriWeightedCorrelatedAgreementFinalization

/-!
# Four adaptive arity-four FRI reductions

`V5FriWeightedCorrelatedAgreementFinalization` proves the one-round result
needed here.  For a word, candidate list, prefix-consistency weight, and whole
response strategy fixed before challenge `z`, the set of challenges where the
response is valid but has no close predecessor folding to its selected
candidate has the degree-three curve-decoding cardinality cap.

This file handles the remaining four-round logic.  Extraction runs backwards
from the published final polynomial.  When analysing an earlier challenge we
fix the later challenge suffix and deterministically select the candidate
returned by the already-analysed continuation.  This selection is a proof
device, not a protocol message: the committed word, decoder list, and
prefix-consistency weight at the round still depend only on the earlier
transcript prefix.  Once the other three challenge coordinates are fixed, the
bad set is fixed while the current challenge varies.

Lean proves two facts:

* outside four such fibrewise bad sets, one initial candidate has an exact
  four-fold chain to the published final candidate; and
* if the four fibre caps are `b0`, `b1`, `b2`, and `b3`, the union contains at
  most `|K|^3 * (b0 + b1 + b2 + b3)` challenge quadruples.

The theorem does not pretend that four independently selected proximity
witnesses are compatible.  Compatibility is the backwards induction
invariant in the hypotheses: the predecessor extracted from a later round is
the target passed to the preceding round.

## V5 instantiation still required

For each transcript prefix and each fixed suffix of ideal independent fold
challenges, a concrete V5 caller must still:

1. construct the deterministic response strategy selecting the
   suffix-compatible next-layer candidate;
2. show that the actual prefix-consistency support is a
   `WeightedValidResponse` at the sampled challenge;
3. turn joint component agreement into the previous layer's supported-near
   predicate and use the proved encoder/fold commutation to reconstruct its
   exact coefficient vector;
4. instantiate `DegreeThreeCurveDecodable` for the four concrete circle/line
   output codes with the claimed caps; and
5. identify the last selected candidate with the published four coefficients
   (the final overlap lemma is already isolated elsewhere).

Merkle binding, Fiat--Shamir/public-coin replacement, and the Rust initial-FFT
identification remain separate implementation/cryptographic boundaries.
-/

namespace AspisV5FriAdaptiveUnmatched

open AspisV5FriWeightedCorrelatedAgreementFinalization

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ## Suffix-conditioned bad fibres -/

/-- Four challenge-dependent bad sets.  Each set may depend on the other three
fixed challenges, including later suffix challenges used by backwards
candidate selection, but never on the challenge whose membership it tests. -/
structure SuffixConditionedBadSets
    (K : Type*) [Fintype K] [DecidableEq K]
    (cap : Fin 4 -> Nat) where
  /-- Vary `z0`; fix suffix `(z1,z2,z3)`. -/
  round0 : K -> K -> K -> Finset K
  /-- Vary `z1`; fix prefix `z0` and suffix `(z2,z3)`. -/
  round1 : K -> K -> K -> Finset K
  /-- Vary `z2`; fix prefix `(z0,z1)` and suffix `z3`. -/
  round2 : K -> K -> K -> Finset K
  /-- Vary `z3`; fix prefix `(z0,z1,z2)`. -/
  round3 : K -> K -> K -> Finset K
  round0_card_le : forall z1 z2 z3, (round0 z1 z2 z3).card <= cap 0
  round1_card_le : forall z0 z2 z3, (round1 z0 z2 z3).card <= cap 1
  round2_card_le : forall z0 z1 z3, (round2 z0 z1 z3).card <= cap 2
  round3_card_le : forall z0 z1 z2, (round3 z0 z1 z2).card <= cap 3

/-- Membership in at least one of the four suffix-conditioned bad fibres. -/
def SuffixConditionedBadSets.Occurs
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) : Prop :=
  z0 ∈ bad.round0 z1 z2 z3 \/
  z1 ∈ bad.round1 z0 z2 z3 \/
  z2 ∈ bad.round2 z0 z1 z3 \/
  z3 ∈ bad.round3 z0 z1 z2

/-! ## Backwards extraction -/

/-- One backwards extraction step at the actual challenge: either a
predecessor folds exactly to the supplied target, or this challenge is in the
round's fixed bad fibre. -/
def ReverseStepAt {Previous Next : Type*}
    (fold : K -> Previous -> Next) (z : K) (target : Next)
    (bad : Finset K) : Prop :=
  (exists predecessor, fold z predecessor = target) \/ z ∈ bad

/-- Adapter from the one-round theorem in the imported module.  The response
strategy's selected candidate at the actual challenge is the backwards
target, so a matching predecessor is exactly a `ReverseStepAt`; the other
branch retains membership in the already-cardinality-bounded bad set. -/
theorem reverseStepAt_of_matching_predecessor_or_counted
    {Previous Next Domain : Type*}
    [Field K] [Fintype Domain] [DecidableEq Domain]
    (fold : K -> Previous -> Next) (previousNear : Previous -> Prop)
    (strategy : AspisV5FriDegreeThreeCorrelatedAgreement.ProximateStrategy
      K Domain Next)
    (z : K) (target : Next) (bad : Finset K) (challengeCap : Nat)
    (htarget : strategy.candidate z = target)
    (hstep : HasMatchingPredecessor fold previousNear strategy z \/
      (z ∈ bad /\ bad.card <= challengeCap)) :
    ReverseStepAt fold z target bad := by
  rcases hstep with ⟨predecessor, _hnear, hfold⟩ | ⟨hbad, _hcard⟩
  · exact Or.inl ⟨predecessor, hfold.trans htarget⟩
  · exact Or.inr hbad

/-- **Four-round adaptive extraction.**  Starting from the published final
candidate, apply the one-round valid-but-unmatched result backwards.  Earlier
steps receive the exact predecessor selected by the later continuation.  If
all four steps match, their equations form one actual-challenge chain; if a
step does not match, its current challenge lies in that round's fibrewise
counted set. -/
theorem suffix_conditioned_four_round_extraction
    {C0 C1 C2 C3 C4 : Type*}
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (fold0 : K -> C0 -> C1) (fold1 : K -> C1 -> C2)
    (fold2 : K -> C2 -> C3) (fold3 : K -> C3 -> C4)
    (z0 z1 z2 z3 : K) (published : C4)
    (step3 : ReverseStepAt fold3 z3 published (bad.round3 z0 z1 z2))
    (step2 : forall c3, fold3 z3 c3 = published ->
      ReverseStepAt fold2 z2 c3 (bad.round2 z0 z1 z3))
    (step1 : forall c2 c3,
      fold2 z2 c2 = c3 -> fold3 z3 c3 = published ->
      ReverseStepAt fold1 z1 c2 (bad.round1 z0 z2 z3))
    (step0 : forall c1 c2 c3,
      fold1 z1 c1 = c2 -> fold2 z2 c2 = c3 ->
      fold3 z3 c3 = published ->
      ReverseStepAt fold0 z0 c1 (bad.round0 z1 z2 z3)) :
    (exists c0 c1 c2 c3,
      fold0 z0 c0 = c1 /\ fold1 z1 c1 = c2 /\
      fold2 z2 c2 = c3 /\ fold3 z3 c3 = published) \/
      bad.Occurs z0 z1 z2 z3 := by
  rcases step3 with ⟨c3, hc3⟩ | hbad3
  · rcases step2 c3 hc3 with ⟨c2, hc2⟩ | hbad2
    · rcases step1 c2 c3 hc2 hc3 with ⟨c1, hc1⟩ | hbad1
      · rcases step0 c1 c2 c3 hc1 hc2 hc3 with ⟨c0, hc0⟩ | hbad0
        · exact Or.inl ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3⟩
        · exact Or.inr (Or.inl hbad0)
      · exact Or.inr (Or.inr (Or.inl hbad1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hbad2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hbad3)))

/-! ## Counting the four fibrewise events -/

/-- Four uniformly sampled fold challenges in transcript order. -/
abbrev FourChallenges (K : Type*) := ((K × K) × K) × K

/-- Add one varying challenge to a fixed three-challenge context. -/
noncomputable def extendByBadChallenge
    {Context Choice : Type*}
    [Fintype Context] [DecidableEq Context] [DecidableEq Choice]
    (bad : Context -> Finset Choice) : Finset (Context × Choice) :=
  Finset.univ.biUnion fun context =>
    (bad context).image fun choice => (context, choice)

@[simp] theorem mem_extendByBadChallenge
    {Context Choice : Type*}
    [Fintype Context] [DecidableEq Context] [DecidableEq Choice]
    (bad : Context -> Finset Choice) (context : Context) (choice : Choice) :
    (context, choice) ∈ extendByBadChallenge bad <-> choice ∈ bad context := by
  classical
  simp [extendByBadChallenge]

/-- Fibre counting is valid even when the set depends arbitrarily on all
fixed prefix and suffix coordinates. -/
theorem extendByBadChallenge_card_le
    {Context Choice : Type*}
    [Fintype Context] [DecidableEq Context] [DecidableEq Choice]
    (bad : Context -> Finset Choice) (bound : Nat)
    (hbad : forall context, (bad context).card <= bound) :
    (extendByBadChallenge bad).card <= Fintype.card Context * bound := by
  classical
  calc
    (extendByBadChallenge bad).card <=
        ∑ context : Context,
          ((bad context).image fun choice => (context, choice)).card := by
      exact Finset.card_biUnion_le
    _ = ∑ context : Context, (bad context).card := by
      apply Fintype.sum_congr
      intro context
      exact Finset.card_image_of_injective _
        (Prod.mk_right_injective context)
    _ <= ∑ _context : Context, bound := by
      exact Finset.sum_le_sum fun context _ => hbad context
    _ = Fintype.card Context * bound := by simp

private abbrev ThreeChallenges (K : Type*) := (K × K) × K

private def tupleFromRound0
    (entry : ThreeChallenges K × K) : FourChallenges K :=
  (((entry.2, entry.1.1.1), entry.1.1.2), entry.1.2)

private def tupleFromRound1
    (entry : ThreeChallenges K × K) : FourChallenges K :=
  (((entry.1.1.1, entry.2), entry.1.1.2), entry.1.2)

private def tupleFromRound2
    (entry : ThreeChallenges K × K) : FourChallenges K :=
  (((entry.1.1.1, entry.1.1.2), entry.2), entry.1.2)

private def tupleFromRound3
    (entry : ThreeChallenges K × K) : FourChallenges K :=
  (entry.1, entry.2)

private theorem tupleFromRound0_injective :
    Function.Injective (tupleFromRound0 (K := K)) := by
  intro left right h
  rcases left with ⟨⟨⟨l1, l2⟩, l3⟩, l0⟩
  rcases right with ⟨⟨⟨r1, r2⟩, r3⟩, r0⟩
  simp only [tupleFromRound0, Prod.mk.injEq] at h ⊢
  tauto

private theorem tupleFromRound1_injective :
    Function.Injective (tupleFromRound1 (K := K)) := by
  intro left right h
  rcases left with ⟨⟨⟨l0, l2⟩, l3⟩, l1⟩
  rcases right with ⟨⟨⟨r0, r2⟩, r3⟩, r1⟩
  simp only [tupleFromRound1, Prod.mk.injEq] at h ⊢
  tauto

private theorem tupleFromRound2_injective :
    Function.Injective (tupleFromRound2 (K := K)) := by
  intro left right h
  rcases left with ⟨⟨⟨l0, l1⟩, l3⟩, l2⟩
  rcases right with ⟨⟨⟨r0, r1⟩, r3⟩, r2⟩
  simp only [tupleFromRound2, Prod.mk.injEq] at h ⊢
  tauto

private theorem tupleFromRound3_injective :
    Function.Injective (tupleFromRound3 (K := K)) := by
  intro left right h
  simpa only [tupleFromRound3] using h

/-- All challenge tuples charged to round zero. -/
noncomputable def round0TupleEvent
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Finset (FourChallenges K) :=
  (extendByBadChallenge fun context : ThreeChallenges K =>
    bad.round0 context.1.1 context.1.2 context.2).image tupleFromRound0

/-- All challenge tuples charged to round one. -/
noncomputable def round1TupleEvent
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Finset (FourChallenges K) :=
  (extendByBadChallenge fun context : ThreeChallenges K =>
    bad.round1 context.1.1 context.1.2 context.2).image tupleFromRound1

/-- All challenge tuples charged to round two. -/
noncomputable def round2TupleEvent
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Finset (FourChallenges K) :=
  (extendByBadChallenge fun context : ThreeChallenges K =>
    bad.round2 context.1.1 context.1.2 context.2).image tupleFromRound2

/-- All challenge tuples charged to round three. -/
noncomputable def round3TupleEvent
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Finset (FourChallenges K) :=
  (extendByBadChallenge fun context : ThreeChallenges K =>
    bad.round3 context.1.1 context.1.2 context.2).image tupleFromRound3

@[simp] theorem mem_round0TupleEvent_iff
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ round0TupleEvent bad <->
      z0 ∈ bad.round0 z1 z2 z3 := by
  classical
  simp [round0TupleEvent, tupleFromRound0, extendByBadChallenge]

@[simp] theorem mem_round1TupleEvent_iff
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ round1TupleEvent bad <->
      z1 ∈ bad.round1 z0 z2 z3 := by
  classical
  simp [round1TupleEvent, tupleFromRound1, extendByBadChallenge]

@[simp] theorem mem_round2TupleEvent_iff
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ round2TupleEvent bad <->
      z2 ∈ bad.round2 z0 z1 z3 := by
  classical
  simp [round2TupleEvent, tupleFromRound2, extendByBadChallenge]

@[simp] theorem mem_round3TupleEvent_iff
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ round3TupleEvent bad <->
      z3 ∈ bad.round3 z0 z1 z2 := by
  classical
  simp [round3TupleEvent, tupleFromRound3, extendByBadChallenge]

/-- Union of all four suffix-conditioned events on one common tuple space. -/
noncomputable def allBadChallengeTuples
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    Finset (FourChallenges K) :=
  round0TupleEvent bad ∪ round1TupleEvent bad ∪
    round2TupleEvent bad ∪ round3TupleEvent bad

@[simp] theorem mem_allBadChallengeTuples_iff
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap)
    (z0 z1 z2 z3 : K) :
    (((z0, z1), z2), z3) ∈ allBadChallengeTuples bad <->
      bad.Occurs z0 z1 z2 z3 := by
  simp [allBadChallengeTuples, SuffixConditionedBadSets.Occurs]

private theorem threeChallenges_card :
    Fintype.card (ThreeChallenges K) = Fintype.card K ^ 3 := by
  simp [ThreeChallenges, pow_succ]

theorem round0TupleEvent_card_le
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    (round0TupleEvent bad).card <= Fintype.card K ^ 3 * cap 0 := by
  rw [round0TupleEvent, Finset.card_image_of_injective _ tupleFromRound0_injective]
  rw [<- threeChallenges_card (K := K)]
  exact extendByBadChallenge_card_le _ _ fun context =>
    bad.round0_card_le context.1.1 context.1.2 context.2

theorem round1TupleEvent_card_le
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    (round1TupleEvent bad).card <= Fintype.card K ^ 3 * cap 1 := by
  rw [round1TupleEvent, Finset.card_image_of_injective _ tupleFromRound1_injective]
  rw [<- threeChallenges_card (K := K)]
  exact extendByBadChallenge_card_le _ _ fun context =>
    bad.round1_card_le context.1.1 context.1.2 context.2

theorem round2TupleEvent_card_le
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    (round2TupleEvent bad).card <= Fintype.card K ^ 3 * cap 2 := by
  rw [round2TupleEvent, Finset.card_image_of_injective _ tupleFromRound2_injective]
  rw [<- threeChallenges_card (K := K)]
  exact extendByBadChallenge_card_le _ _ fun context =>
    bad.round2_card_le context.1.1 context.1.2 context.2

theorem round3TupleEvent_card_le
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    (round3TupleEvent bad).card <= Fintype.card K ^ 3 * cap 3 := by
  rw [round3TupleEvent, Finset.card_image_of_injective _ tupleFromRound3_injective]
  rw [<- threeChallenges_card (K := K)]
  exact extendByBadChallenge_card_le _ _ fun context =>
    bad.round3_card_le context.1.1 context.1.2 context.2

/-- Exact four-fibre union count.  Dividing by `|K|^4` gives the familiar
`(b0+b1+b2+b3)/|K|` ideal independent-challenge bound. -/
theorem allBadChallengeTuples_card_le
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    (allBadChallengeTuples bad).card <=
      Fintype.card K ^ 3 * (cap 0 + cap 1 + cap 2 + cap 3) := by
  let event0 := round0TupleEvent bad
  let event1 := round1TupleEvent bad
  let event2 := round2TupleEvent bad
  let event3 := round3TupleEvent bad
  have hunion01 : (event0 ∪ event1).card <= event0.card + event1.card :=
    Finset.card_union_le _ _
  have hunion012 : ((event0 ∪ event1) ∪ event2).card <=
      event0.card + event1.card + event2.card := by
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right hunion01 event2.card)
  have hunion0123 : (((event0 ∪ event1) ∪ event2) ∪ event3).card <=
      event0.card + event1.card + event2.card + event3.card := by
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right hunion012 event3.card)
  calc
    (allBadChallengeTuples bad).card <=
        (round0TupleEvent bad).card + (round1TupleEvent bad).card +
          (round2TupleEvent bad).card + (round3TupleEvent bad).card := by
      simpa only [allBadChallengeTuples, event0, event1, event2, event3] using
        hunion0123
    _ <= Fintype.card K ^ 3 * cap 0 + Fintype.card K ^ 3 * cap 1 +
          Fintype.card K ^ 3 * cap 2 + Fintype.card K ^ 3 * cap 3 := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (round0TupleEvent_card_le bad)
            (round1TupleEvent_card_le bad))
          (round2TupleEvent_card_le bad))
        (round3TupleEvent_card_le bad)
    _ = Fintype.card K ^ 3 * (cap 0 + cap 1 + cap 2 + cap 3) := by
      simp only [Nat.mul_add]

/-- Exact mass of the four counted events under four independent uniform
field challenges. -/
noncomputable def uniformBadChallengeProbability
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) : Rat :=
  (allBadChallengeTuples bad).card / Fintype.card K ^ 4

/-- Probability form of `allBadChallengeTuples_card_le`.  Suffix-conditioned
candidate selection costs no extra list factor: fixing the other three coins
leaves one bad fibre of the stated cardinality. -/
theorem uniformBadChallengeProbability_le
    [Nonempty K]
    {cap : Fin 4 -> Nat} (bad : SuffixConditionedBadSets K cap) :
    uniformBadChallengeProbability bad <=
      (cap 0 + cap 1 + cap 2 + cap 3 : Rat) / Fintype.card K := by
  let fieldCard := Fintype.card K
  let capSum := cap 0 + cap 1 + cap 2 + cap 3
  have hfieldNat : 0 < fieldCard := Fintype.card_pos_iff.mpr inferInstance
  have hfield : (0 : Rat) < fieldCard := by exact_mod_cast hfieldNat
  have hcount := allBadChallengeTuples_card_le bad
  unfold uniformBadChallengeProbability
  have hcapCast :
      (cap 0 : Rat) + cap 1 + cap 2 + cap 3 = (capSum : Nat) := by
    simp [capSum]
  rw [hcapCast]
  change ((allBadChallengeTuples bad).card : Rat) / (fieldCard : Rat) ^ 4 <=
    (capSum : Rat) / (fieldCard : Rat)
  rw [div_le_iff₀ (pow_pos hfield 4)]
  calc
    ((allBadChallengeTuples bad).card : Rat) <=
        (fieldCard : Rat) ^ 3 * (capSum : Rat) := by
      exact_mod_cast hcount
    _ = (capSum : Rat) / (fieldCard : Rat) * (fieldCard : Rat) ^ 4 := by
      field_simp

/-! ## Axiom audit -/

#print axioms suffix_conditioned_four_round_extraction
#print axioms extendByBadChallenge_card_le
#print axioms allBadChallengeTuples_card_le
#print axioms uniformBadChallengeProbability_le

end AspisV5FriAdaptiveUnmatched
