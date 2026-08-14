import AspisFormal.V5FriCoherentCandidateExtraction

/-!
# What the two V5 OOD samples do to a FRI candidate list

The V5 transcript carries two out-of-domain (OOD) evaluations at each of the
four coefficient sizes `1024`, `256`, `64`, and `16`.  This file states their
deterministic role without treating a probability calculation as a protocol
proof.

For one finite candidate list, absence of a pairwise two-sample collision
makes the two claimed evaluations select at most one member of that list.  For
the four exact V5 list types, that uniqueness turns *two-evaluation fold
links* into equality of complete coefficient vectors, and therefore into one
coherent chain whose initial member reaches the published final polynomial.

The fold links are essential.  Two OOD samples do not, by themselves, show
that the fold of the selected member of one list has the two claimed
evaluations in the next list.  The final section gives a finite counterexample
and an explicit event split exposing exactly that remaining round-reduction
obligation.

The numeric theorem `AspisSoundnessLedger.ood_list_union` bounds the proposed
union of pairwise collision probabilities.  It does not prove the existence
of matching list members, the fold links, independence of the two samples, or
the polynomial root bounds used by that probability expression.
-/

namespace AspisV5FriOodCandidateBinding

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction

/-! ## Two evaluations select at most one member of a fixed list -/

/-- One finite candidate list, two evaluation points, and the two values
claimed by the proof. -/
structure TwoOodView (Candidate Point Value : Type*) where
  candidates : Finset Candidate
  point : Fin 2 -> Point
  claimed : Fin 2 -> Value
  evaluate : Candidate -> Point -> Value

/-- The two evaluations of one candidate at this layer. -/
def TwoOodView.signature
    {Candidate Point Value : Type*}
    (view : TwoOodView Candidate Point Value) (candidate : Candidate) :
    Fin 2 -> Value :=
  fun sample => view.evaluate candidate (view.point sample)

/-- A list member agrees with both values claimed in the proof. -/
def TwoOodView.Matches
    {Candidate Point Value : Type*} [DecidableEq Candidate]
    (view : TwoOodView Candidate Point Value) (candidate : Candidate) : Prop :=
  candidate ∈ view.candidates /\ view.signature candidate = view.claimed

/-- Two distinct members of one list have equal evaluations at both sampled
points.  This is the deterministic event whose proposed probability is the
corresponding summand in the two-sample OOD-list union. -/
def TwoOodView.PairCollision
    {Candidate Point Value : Type*} [DecidableEq Candidate]
    (view : TwoOodView Candidate Point Value) : Prop :=
  ∃ first, first ∈ view.candidates ∧
    ∃ second, second ∈ view.candidates ∧ first ≠ second ∧
      view.signature first = view.signature second

/-- If no pair collides on the two evaluations, list membership plus equality
of signatures implies equality of the complete candidates. -/
theorem TwoOodView.eq_of_mem_of_signature_eq
    {Candidate Point Value : Type*} [DecidableEq Candidate]
    (view : TwoOodView Candidate Point Value)
    {first second : Candidate}
    (hno : ¬ view.PairCollision)
    (hfirst : first ∈ view.candidates)
    (hsecond : second ∈ view.candidates)
    (hsignature : view.signature first = view.signature second) :
    first = second := by
  by_contra hne
  exact hno ⟨first, hfirst, second, hsecond, hne, hsignature⟩

/-- In particular, two candidates that both match the two proof-carried
values are equal. -/
theorem TwoOodView.eq_of_matches
    {Candidate Point Value : Type*} [DecidableEq Candidate]
    (view : TwoOodView Candidate Point Value)
    {first second : Candidate}
    (hno : ¬ view.PairCollision)
    (hfirst : view.Matches first)
    (hsecond : view.Matches second) :
    first = second := by
  exact view.eq_of_mem_of_signature_eq hno hfirst.1 hsecond.1
    (hfirst.2.trans hsecond.2.symm)

/-! ## The four exact V5 candidate-list types -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The actual V5 OOD point shapes: two secure-circle points in round zero,
then two extension-field line points in each later round.  Evaluation
functions remain explicit data because identifying them with the deployed
Rust evaluators is a separate implementation theorem. -/
structure V5OodData (K : Type*) where
  circlePoint : Fin 2 -> K × K
  line1Point : Fin 2 -> K
  line2Point : Fin 2 -> K
  line3Point : Fin 2 -> K
  claimed0 : Fin 2 -> K
  claimed1 : Fin 2 -> K
  claimed2 : Fin 2 -> K
  claimed3 : Fin 2 -> K
  evaluate0 : Coeff0 K -> (K × K) -> K
  evaluate1 : Coeff1 K -> K -> K
  evaluate2 : Coeff2 K -> K -> K
  evaluate3 : Coeff3 K -> K -> K

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Round-zero OOD view over the actual initial decoder list. -/
noncomputable def initialView
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : TwoOodView (Coeff0 K) (K × K) K where
  candidates := initialCandidateList encoders transcript
  point := ood.circlePoint
  claimed := ood.claimed0
  evaluate := ood.evaluate0

/-- Round-one OOD view over the actual `256`-coefficient decoder list. -/
noncomputable def layer1View
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : TwoOodView (Coeff1 K) K K where
  candidates := layer1CandidateList encoders transcript
  point := ood.line1Point
  claimed := ood.claimed1
  evaluate := ood.evaluate1

/-- Round-two OOD view over the actual `64`-coefficient decoder list. -/
noncomputable def layer2View
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : TwoOodView (Coeff2 K) K K where
  candidates := layer2CandidateList encoders transcript
  point := ood.line2Point
  claimed := ood.claimed2
  evaluate := ood.evaluate2

/-- Round-three OOD view over the actual `16`-coefficient decoder list. -/
noncomputable def layer3View
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : TwoOodView (Coeff3 K) K K where
  candidates := layer3CandidateList encoders transcript
  point := ood.line3Point
  claimed := ood.claimed3
  evaluate := ood.evaluate3

/-- The exact four-list collision event represented by the four summands with
root caps `[1024, 255, 63, 15]` in `ood_list_union`. -/
def V5OodCollision
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : Prop :=
  (initialView encoders transcript ood).PairCollision ∨
  (layer1View encoders transcript ood).PairCollision ∨
  (layer2View encoders transcript ood).PairCollision ∨
  (layer3View encoders transcript ood).PairCollision

/-- Four independently selected list members, each matching its layer's two
proof-carried OOD values. -/
def SelectedCandidatesMatchOod
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K)
    (c0 : Coeff0 K) (c1 : Coeff1 K) (c2 : Coeff2 K) (c3 : Coeff3 K) : Prop :=
  (initialView encoders transcript ood).Matches c0 ∧
  (layer1View encoders transcript ood).Matches c1 ∧
  (layer2View encoders transcript ood).Matches c2 ∧
  (layer3View encoders transcript ood).Matches c3

/-- At least one of the four exact decoder lists supplies no member matching
its two proof-carried OOD values.  A protocol reduction must either exclude
or charge this event before pairwise collision-freedom can select candidates.
-/
def OodSelectionFailure
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) : Prop :=
  ¬ ∃ c0 c1 c2 c3,
    SelectedCandidatesMatchOod encoders transcript ood c0 c1 c2 c3

/-- The smallest deterministic link still needed after the OOD values select
one member of each list.

For each transition, the fold image must itself lie in the next list and have
the same two-evaluation signature as the member selected there.  The last
clause is the exact final-polynomial equality.  Absence of OOD collisions can
turn these signature equalities into coefficient-vector equalities; it cannot
create these equalities. -/
def FoldOodLinks
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K)
    (c0 : Coeff0 K) (c1 : Coeff1 K) (c2 : Coeff2 K) (c3 : Coeff3 K) : Prop :=
  fold0 schedule c0 ∈ (layer1View encoders transcript ood).candidates ∧
  (layer1View encoders transcript ood).signature (fold0 schedule c0) =
    (layer1View encoders transcript ood).signature c1 ∧
  fold1 schedule c1 ∈ (layer2View encoders transcript ood).candidates ∧
  (layer2View encoders transcript ood).signature (fold1 schedule c1) =
    (layer2View encoders transcript ood).signature c2 ∧
  fold2 schedule c2 ∈ (layer3View encoders transcript ood).candidates ∧
  (layer3View encoders transcript ood).signature (fold2 schedule c2) =
    (layer3View encoders transcript ood).signature c3 ∧
  fold3 schedule c3 = transcript.publishedFinal

/-- Exact failure event left when independently selected layer candidates do
not form a chain.  This is the event that an applicable FRI round-reduction
theorem must bound; it is not part of the pairwise OOD-collision event. -/
def FoldOodLinkFailure
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K)
    (c0 : Coeff0 K) (c1 : Coeff1 K) (c2 : Coeff2 K) (c3 : Coeff3 K) : Prop :=
  ¬ FoldOodLinks schedule encoders transcript ood c0 c1 c2 c3

/-- **Deterministic OOD binding theorem.**  If each of the four exact decoder
lists supplies a member matching its two claimed evaluations, none of the
four lists has a two-sample collision, and the three fold-signature links plus
the final equality hold, then those independently selected members are one
coherent chain.  Its unique initial OOD match reaches the published final
polynomial under the four exact V5 coefficient folds. -/
theorem two_ood_links_select_one_coherent_initial_candidate
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K)
    (c0 : Coeff0 K) (c1 : Coeff1 K) (c2 : Coeff2 K) (c3 : Coeff3 K)
    (hselected : SelectedCandidatesMatchOod encoders transcript ood
      c0 c1 c2 c3)
    (hnoCollision : ¬ V5OodCollision encoders transcript ood)
    (hlinks : FoldOodLinks schedule encoders transcript ood c0 c1 c2 c3) :
    ∃ chain : CoherentChain schedule,
      chain.initial = c0 ∧ chain.layer1 = c1 ∧ chain.layer2 = c2 ∧
      chain.layer3 = c3 ∧ chain.final = transcript.publishedFinal ∧
      finalCoefficientMap schedule c0 = transcript.publishedFinal ∧
      ∀ other, (initialView encoders transcript ood).Matches other ->
        other = c0 := by
  rcases hselected with ⟨hc0, hc1, hc2, hc3⟩
  rcases hlinks with ⟨hf0mem, hf0sig, hf1mem, hf1sig,
    hf2mem, hf2sig, hfinal⟩
  have hno0 : ¬ (initialView encoders transcript ood).PairCollision := by
    intro h
    exact hnoCollision (Or.inl h)
  have hno1 : ¬ (layer1View encoders transcript ood).PairCollision := by
    intro h
    exact hnoCollision (Or.inr (Or.inl h))
  have hno2 : ¬ (layer2View encoders transcript ood).PairCollision := by
    intro h
    exact hnoCollision (Or.inr (Or.inr (Or.inl h)))
  have hno3 : ¬ (layer3View encoders transcript ood).PairCollision := by
    intro h
    exact hnoCollision (Or.inr (Or.inr (Or.inr h)))
  have hf0 : fold0 schedule c0 = c1 :=
    (layer1View encoders transcript ood).eq_of_mem_of_signature_eq
      hno1 hf0mem hc1.1 hf0sig
  have hf1 : fold1 schedule c1 = c2 :=
    (layer2View encoders transcript ood).eq_of_mem_of_signature_eq
      hno2 hf1mem hc2.1 hf1sig
  have hf2 : fold2 schedule c2 = c3 :=
    (layer3View encoders transcript ood).eq_of_mem_of_signature_eq
      hno3 hf2mem hc3.1 hf2sig
  have hmap : finalCoefficientMap schedule c0 = transcript.publishedFinal := by
    rw [finalCoefficientMap_eq_four_folds, hf0, hf1, hf2, hfinal]
  let chain := CoherentChain.fromInitial schedule c0
  refine ⟨chain, rfl, ?_, ?_, ?_, ?_, hmap, ?_⟩
  · exact hf0
  · change fold1 schedule (fold0 schedule c0) = c2
    rw [hf0, hf1]
  · change fold2 schedule (fold1 schedule (fold0 schedule c0)) = c3
    rw [hf0, hf1, hf2]
  · change fold3 schedule
      (fold2 schedule (fold1 schedule (fold0 schedule c0))) =
        transcript.publishedFinal
    rw [hf0, hf1, hf2, hfinal]
  · intro other hother
    exact (initialView encoders transcript ood).eq_of_matches
      hno0 hother hc0

/-- Event-decomposition form.  Given four list members that match the eight
claimed OOD values, either a pairwise OOD collision occurred, the explicit
fold/OOD link failed, or one coherent initial candidate reaches the published
final polynomial.  The second branch cannot be absorbed into the first. -/
theorem selected_candidates_collision_or_link_failure_or_coherent_chain
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K)
    (c0 : Coeff0 K) (c1 : Coeff1 K) (c2 : Coeff2 K) (c3 : Coeff3 K)
    (hselected : SelectedCandidatesMatchOod encoders transcript ood
      c0 c1 c2 c3) :
    V5OodCollision encoders transcript ood ∨
      FoldOodLinkFailure schedule encoders transcript ood c0 c1 c2 c3 ∨
      ∃ chain : CoherentChain schedule,
        chain.initial = c0 ∧ chain.layer1 = c1 ∧ chain.layer2 = c2 ∧
        chain.layer3 = c3 ∧ chain.final = transcript.publishedFinal ∧
        finalCoefficientMap schedule c0 = transcript.publishedFinal ∧
        ∀ other, (initialView encoders transcript ood).Matches other ->
          other = c0 := by
  classical
  by_cases hcollision : V5OodCollision encoders transcript ood
  · exact Or.inl hcollision
  · by_cases hlinks : FoldOodLinks schedule encoders transcript ood c0 c1 c2 c3
    · exact Or.inr (Or.inr
        (two_ood_links_select_one_coherent_initial_candidate schedule encoders
          transcript ood c0 c1 c2 c3 hselected hcollision hlinks))
    · exact Or.inr (Or.inl hlinks)

/-- Full deterministic event split for the two-OOD layer.  With no premises,
one of four things is true:

1. some list has no member matching its claimed OOD pair;
2. two members of one list collide on both OOD samples;
3. selected members exist but a fold-signature/final link fails; or
4. one unique initial OOD match has a coherent four-fold chain to the
   published final polynomial.

Only branch 2 is represented by `AspisSoundnessLedger.ood_list_union`.
Branches 1 and 3 require the still-missing protocol-specific FRI reduction.
-/
theorem ood_selection_collision_link_failure_or_coherent_chain
    (schedule : FixedSchedule F K)
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (ood : V5OodData K) :
    OodSelectionFailure encoders transcript ood ∨
      V5OodCollision encoders transcript ood ∨
      (∃ c0 c1 c2 c3,
        SelectedCandidatesMatchOod encoders transcript ood c0 c1 c2 c3 ∧
        FoldOodLinkFailure schedule encoders transcript ood c0 c1 c2 c3) ∨
      ∃ c0 c1 c2 c3,
        SelectedCandidatesMatchOod encoders transcript ood c0 c1 c2 c3 ∧
        ∃ chain : CoherentChain schedule,
          chain.initial = c0 ∧ chain.layer1 = c1 ∧ chain.layer2 = c2 ∧
          chain.layer3 = c3 ∧ chain.final = transcript.publishedFinal ∧
          finalCoefficientMap schedule c0 = transcript.publishedFinal ∧
          ∀ other, (initialView encoders transcript ood).Matches other ->
            other = c0 := by
  classical
  by_cases hselection : ∃ c0 c1 c2 c3,
      SelectedCandidatesMatchOod encoders transcript ood c0 c1 c2 c3
  · rcases hselection with ⟨c0, c1, c2, c3, hselected⟩
    rcases selected_candidates_collision_or_link_failure_or_coherent_chain
        schedule encoders transcript ood c0 c1 c2 c3 hselected with
      hcollision | hlink | hchain
    · exact Or.inr (Or.inl hcollision)
    · exact Or.inr (Or.inr (Or.inl
        ⟨c0, c1, c2, c3, hselected, hlink⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨c0, c1, c2, c3, hselected, hchain⟩))
  · exact Or.inl hselection

end FiniteField

/-! ## Why collision-freedom alone cannot prove a fold link -/

private def boolOodView (claim : Bool) : TwoOodView Bool Unit Bool where
  candidates := Finset.univ
  point := fun _ => ()
  claimed := fun _ => claim
  evaluate := fun candidate _ => candidate

private theorem boolOodView_no_pair_collision (claim : Bool) :
    ¬ (boolOodView claim).PairCollision := by
  intro h
  rcases h with ⟨first, _hfirst, second, _hsecond, hne, hsignature⟩
  have heq := congrFun hsignature 0
  exact hne heq

private theorem boolOodView_matches (claim : Bool) :
    (boolOodView claim).Matches claim := by
  constructor
  · simp [boolOodView]
  · funext sample
    rfl

/-- Concrete counterexample: both adjacent lists have collision-free
two-sample evaluations, each claimed pair selects a unique member, and the
fold image is still a member of the next list.  Nevertheless the fold image
is not the member selected by the next claimed pair.  What is missing is
exactly equality of those two evaluation signatures. -/
theorem two_ood_collision_freedom_does_not_create_fold_link :
    ∃ (current next : TwoOodView Bool Unit Bool)
      (fold : Bool -> Bool) (currentCandidate nextCandidate : Bool),
      (¬ current.PairCollision) ∧ (¬ next.PairCollision) ∧
      current.Matches currentCandidate ∧ next.Matches nextCandidate ∧
      fold currentCandidate ∈ next.candidates ∧
      fold currentCandidate ≠ nextCandidate := by
  refine ⟨boolOodView false, boolOodView true, id, false, true,
    boolOodView_no_pair_collision false,
    boolOodView_no_pair_collision true,
    boolOodView_matches false, boolOodView_matches true, ?_, ?_⟩
  · simp [boolOodView]
  · decide

/-! ## Axiom audit -/

#print axioms TwoOodView.eq_of_mem_of_signature_eq
#print axioms TwoOodView.eq_of_matches
#print axioms two_ood_links_select_one_coherent_initial_candidate
#print axioms selected_candidates_collision_or_link_failure_or_coherent_chain
#print axioms ood_selection_collision_link_failure_or_coherent_chain
#print axioms two_ood_collision_freedom_does_not_create_fold_link

end AspisV5FriOodCandidateBinding
