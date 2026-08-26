import AspisFormal.V5FriJohnsonListBound
import AspisFormal.Pool.V7C1ConcreteProjectionBinding
import AspisFormal.Pool.V7Width29ComponentExtraction

/-!
# A fixed pre-challenge list of width-29 component tuples

The correlated width-29 theorem may choose its matching component tuple only
after seeing `gamma`.  That selection is harmless for later point claims, but
it is too late to justify root counts for the ten earlier semantic challenges.

This file constructs the missing causal object directly.  For one fixed set of
twenty-nine committed received lanes, it lists every component tuple whose
encoded lanes agree *jointly* on at least 38,230 positions.  View a row of
twenty-nine field elements as one symbol.  Two distinct component tuples differ
in some lane, and the exact circle-code distance theorem bounds the overlap in
that lane by 1,024 positions.  The generic Johnson second-moment argument then
shows that this one fixed tuple list has at most 100 members.

No decoding theorem is assumed here.  The only code fact used is the already
proved distance of the concrete mathematical log-20 circle encoder.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisPool.V7FixedWidth29TupleList

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5FriJohnsonListBound
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

/-- Every jointly close component tuple, determined only by the fixed received
lanes and therefore fixed before `gamma` and the later fold transcript. -/
noncomputable def fixedWidth29TupleList
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact) :
    Finset (Width29InitialMessages QM31Exact) := by
  classical
  exact (componentCandidateSet decoder lanes).filter fun components =>
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
      (width29JointAgreementSet exactInitialEncoder lanes components).card

@[simp] theorem mem_fixedWidth29TupleList_iff
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (components : Width29InitialMessages QM31Exact) :
    components ∈ fixedWidth29TupleList decoder lanes ↔
      (∀ lane, components lane ∈ decoder.initialDecode (lanes lane)) ∧
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
          (width29JointAgreementSet exactInitialEncoder lanes components).card := by
  classical
  simp [fixedWidth29TupleList]

/-- The candidate type used for a fixed-family union bound. -/
abbrev FixedWidth29TupleCandidate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact) :=
  {components // components ∈ fixedWidth29TupleList decoder lanes}

/-- Joint agreement of two distinct tuples can occur only where the concrete
circle encodings of one differing lane agree. -/
theorem distinct_tuple_joint_agreement_overlap_le_1024
    (lanes : Width29InitialWords QM31Exact)
    (left right : Width29InitialMessages QM31Exact)
    (different : left ≠ right) :
    ((width29JointAgreementSet exactInitialEncoder lanes left) ∩
      (width29JointAgreementSet exactInitialEncoder lanes right)).card ≤
        1024 := by
  classical
  have laneDifferent : ∃ lane, left lane ≠ right lane := by
    simpa only [Function.ne_iff] using different
  obtain ⟨lane, differentAtLane⟩ := laneDifferent
  have subset :
      (width29JointAgreementSet exactInitialEncoder lanes left) ∩
          (width29JointAgreementSet exactInitialEncoder lanes right) ⊆
        Finset.univ.filter fun index =>
          exactInitialEncoder (left lane) index =
            exactInitialEncoder (right lane) index := by
    intro index member
    have leftMember := (Finset.mem_inter.mp member).1
    have rightMember := (Finset.mem_inter.mp member).2
    have leftAll : ∀ component,
        lanes component index =
          exactInitialEncoder (left component) index := by
      simpa only [width29JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using leftMember
    have rightAll : ∀ component,
        lanes component index =
          exactInitialEncoder (right component) index := by
      simpa only [width29JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using rightMember
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (leftAll lane).symm.trans (rightAll lane)⟩
  calc
    ((width29JointAgreementSet exactInitialEncoder lanes left) ∩
        (width29JointAgreementSet exactInitialEncoder lanes right)).card ≤
        (Finset.univ.filter fun index =>
          exactInitialEncoder (left lane) index =
            exactInitialEncoder (right lane) index).card :=
      Finset.card_le_card subset
    _ = agreementCount (exactInitialEncoder (left lane))
          (exactInitialEncoder (right lane)) := by
      rfl
    _ ≤ 1024 := exactInitialEncoder_overlap_cap
      (left lane) (right lane) differentAtLane

/-- Exact Johnson arithmetic for the V7 initial geometry, stated first for an
arbitrary finite family whose members are all jointly close. -/
theorem jointlyCloseWidth29CandidateSet_card_le_100
    (lanes : Width29InitialWords QM31Exact) :
    ∀ candidates : Finset (Width29InitialMessages QM31Exact),
      (∀ components ∈ candidates,
        38230 ≤
          (width29JointAgreementSet exactInitialEncoder lanes components).card) →
      candidates.card ≤ 100 := by
  classical
  intro candidates allLarge
  let Candidate := {components // components ∈ candidates}
  let agreement : Candidate →
      Finset (Fin 1048576) := fun candidate =>
    width29JointAgreementSet exactInitialEncoder lanes candidate.1
  have large : ∀ candidate : Candidate,
      38230 ≤ (agreement candidate).card := by
    intro candidate
    simpa [agreement] using allLarge candidate.1 candidate.2
  have overlap : ∀ left right : Candidate, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ 1024 := by
    intro left right different
    have valuesDifferent : left.1 ≠ right.1 := by
      intro valuesEqual
      apply different
      exact Subtype.ext valuesEqual
    simpa [agreement] using
      distinct_tuple_joint_agreement_overlap_le_1024
        lanes left.1 right.1 valuesDifferent
  have forbidden : Fintype.card Candidate < 101 :=
    list_card_lt_of_johnson_parameters agreement
      1048576 38230 1024 101 (by simp) large overlap
      (by norm_num) (by norm_num) (by norm_num)
  rw [Fintype.card_coe] at forbidden
  omega

/-- The concrete decoder-backed family is fixed by the received lanes and has
at most 100 members.  Decoder soundness is not needed: the final filter itself
requires exact joint closeness. -/
theorem fixedWidth29TupleList_card_le_100
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact) :
    (fixedWidth29TupleList decoder lanes).card ≤ 100 := by
  apply jointlyCloseWidth29CandidateSet_card_le_100 lanes
    (fixedWidth29TupleList decoder lanes)
  intro components member
  have close := (mem_fixedWidth29TupleList_iff
    decoder lanes components).mp member
  have strict : 38229 <
      (width29JointAgreementSet exactInitialEncoder lanes components).card := by
    simpa [AspisV6PublishedTheoremInterfaces.initialAgreementThreshold] using
      close.2
  omega

/-- Cardinality form used by the existing fixed-candidate probability
experiments. -/
theorem fixedWidth29TupleCandidate_card_le_100
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact) :
    Fintype.card (FixedWidth29TupleCandidate decoder lanes) ≤ 100 := by
  rw [Fintype.card_coe]
  exact fixedWidth29TupleList_card_le_100 decoder lanes

/-- A tuple with a support larger than the deployed strict threshold belongs
to the one fixed pre-challenge family. -/
theorem mem_fixedWidth29TupleList_of_shared_support
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (components : Width29InitialMessages QM31Exact)
    (support : Finset (Fin 1048576))
    (large : AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
      support.card)
    (shared : support ⊆
      width29JointAgreementSet exactInitialEncoder lanes components)
    (decoded : ∀ lane,
      components lane ∈ decoder.initialDecode (lanes lane)) :
    components ∈ fixedWidth29TupleList decoder lanes := by
  rw [mem_fixedWidth29TupleList_iff]
  exact ⟨decoded, large.trans_le (Finset.card_le_card shared)⟩

/-! ## The C1-only family fixed before lambda and chi -/

abbrev C1InitialWords := Fin 26 → InitialWord QM31Exact
abbrev C1InitialMessages := Fin 26 → InitialMessage QM31Exact

noncomputable def c1JointAgreementSet
    (lanes : C1InitialWords) (components : C1InitialMessages) :
    Finset (Fin 1048576) := by
  classical
  exact Finset.univ.filter fun index =>
    ∀ column, lanes column index =
      exactInitialEncoder (components column) index

def c1ComponentCandidateSet
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) : Finset C1InitialMessages :=
  Fintype.piFinset fun column =>
    (decoder.initialDecode (lanes column)).toFinset

noncomputable def fixedC1TupleList
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) : Finset C1InitialMessages := by
  classical
  exact (c1ComponentCandidateSet decoder lanes).filter fun components =>
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
      (c1JointAgreementSet lanes components).card

@[simp] theorem mem_fixedC1TupleList_iff
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) (components : C1InitialMessages) :
    components ∈ fixedC1TupleList decoder lanes ↔
      (∀ column,
        components column ∈ decoder.initialDecode (lanes column)) ∧
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
        (c1JointAgreementSet lanes components).card := by
  classical
  simp [fixedC1TupleList, c1ComponentCandidateSet]

abbrev FixedC1TupleCandidate
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) :=
  {components // components ∈ fixedC1TupleList decoder lanes}

theorem distinct_c1_tuple_joint_agreement_overlap_le_1024
    (lanes : C1InitialWords) (left right : C1InitialMessages)
    (different : left ≠ right) :
    ((c1JointAgreementSet lanes left) ∩
      (c1JointAgreementSet lanes right)).card ≤ 1024 := by
  classical
  have columnDifferent : ∃ column, left column ≠ right column := by
    simpa only [Function.ne_iff] using different
  obtain ⟨column, differentAtColumn⟩ := columnDifferent
  have subset :
      (c1JointAgreementSet lanes left) ∩
          (c1JointAgreementSet lanes right) ⊆
        Finset.univ.filter fun index =>
          exactInitialEncoder (left column) index =
            exactInitialEncoder (right column) index := by
    intro index member
    have leftMember := (Finset.mem_inter.mp member).1
    have rightMember := (Finset.mem_inter.mp member).2
    have leftAll : ∀ c,
        lanes c index = exactInitialEncoder (left c) index := by
      simpa only [c1JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using leftMember
    have rightAll : ∀ c,
        lanes c index = exactInitialEncoder (right c) index := by
      simpa only [c1JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using rightMember
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        (leftAll column).symm.trans (rightAll column)⟩
  calc
    ((c1JointAgreementSet lanes left) ∩
        (c1JointAgreementSet lanes right)).card ≤
        (Finset.univ.filter fun index =>
          exactInitialEncoder (left column) index =
            exactInitialEncoder (right column) index).card :=
      Finset.card_le_card subset
    _ = agreementCount (exactInitialEncoder (left column))
          (exactInitialEncoder (right column)) := by rfl
    _ ≤ 1024 := exactInitialEncoder_overlap_cap
      (left column) (right column) differentAtColumn

theorem fixedC1TupleList_card_le_100
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) :
    (fixedC1TupleList decoder lanes).card ≤ 100 := by
  classical
  let Candidate := FixedC1TupleCandidate decoder lanes
  let agreement : Candidate → Finset (Fin 1048576) := fun candidate =>
    c1JointAgreementSet lanes candidate.1
  have large : ∀ candidate : Candidate,
      38230 ≤ (agreement candidate).card := by
    intro candidate
    have member := (mem_fixedC1TupleList_iff
      decoder lanes candidate.1).mp candidate.2
    have strict : 38229 < (c1JointAgreementSet lanes candidate.1).card := by
      simpa [AspisV6PublishedTheoremInterfaces.initialAgreementThreshold] using
        member.2
    simpa [agreement] using (show 38230 ≤
      (c1JointAgreementSet lanes candidate.1).card by omega)
  have overlap : ∀ left right : Candidate, left ≠ right →
      ((agreement left) ∩ (agreement right)).card ≤ 1024 := by
    intro left right different
    have valuesDifferent : left.1 ≠ right.1 := by
      intro valuesEqual
      apply different
      exact Subtype.ext valuesEqual
    simpa [agreement] using
      distinct_c1_tuple_joint_agreement_overlap_le_1024
        lanes left.1 right.1 valuesDifferent
  have forbidden : Fintype.card Candidate < 101 :=
    list_card_lt_of_johnson_parameters agreement
      1048576 38230 1024 101 (by simp) large overlap
      (by norm_num) (by norm_num) (by norm_num)
  rw [Fintype.card_coe] at forbidden
  omega

theorem fixedC1TupleCandidate_card_le_100
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : C1InitialWords) :
    Fintype.card (FixedC1TupleCandidate decoder lanes) ≤ 100 := by
  rw [Fintype.card_coe]
  exact fixedC1TupleList_card_le_100 decoder lanes

/-- Restriction of a width-29 tuple to the C1 columns. -/
def projectWidth29ToC1
    (components : Width29InitialMessages QM31Exact) : C1InitialMessages :=
  fun column => components (c1LaneIndex column)

/-- The full joint-agreement set is contained in the C1-only set of the
projected tuple. -/
theorem width29_jointAgreement_subset_c1_projection
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (components : Width29InitialMessages QM31Exact) :
    width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) components ⊆
      c1JointAgreementSet (c1Received words) (projectWidth29ToC1 components) := by
  classical
  intro index member
  have allLanes : ∀ lane,
      extractedWidth29InitialWords words lane index =
        exactInitialEncoder (components lane) index := by
    simpa only [width29JointAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and] using member
  simp only [c1JointAgreementSet, Finset.mem_filter, Finset.mem_univ,
    true_and, projectWidth29ToC1]
  intro column
  rw [← extractedWidth29_c1_lane]
  exact allLanes (c1LaneIndex column)

/-- Every member of the post-C2 width-29 family projects into one C1 family
that was already fixed before lambda and chi were sampled. -/
theorem width29_member_projects_to_fixedC1TupleList
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (components : Width29InitialMessages QM31Exact)
    (member : components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words)) :
    projectWidth29ToC1 components ∈
      fixedC1TupleList decoder (c1Received words) := by
  have full := (mem_fixedWidth29TupleList_iff decoder
    (extractedWidth29InitialWords words) components).mp member
  rw [mem_fixedC1TupleList_iff]
  constructor
  · intro column
    simpa only [projectWidth29ToC1, extractedWidth29_c1_lane] using
      full.1 (c1LaneIndex column)
  · exact full.2.trans_le (Finset.card_le_card
      (width29_jointAgreement_subset_c1_projection words components))

#print axioms distinct_tuple_joint_agreement_overlap_le_1024
#print axioms jointlyCloseWidth29CandidateSet_card_le_100
#print axioms fixedWidth29TupleList_card_le_100
#print axioms fixedWidth29TupleCandidate_card_le_100
#print axioms mem_fixedWidth29TupleList_of_shared_support
#print axioms distinct_c1_tuple_joint_agreement_overlap_le_1024
#print axioms fixedC1TupleList_card_le_100
#print axioms fixedC1TupleCandidate_card_le_100
#print axioms width29_jointAgreement_subset_c1_projection
#print axioms width29_member_projects_to_fixedC1TupleList

end AspisPool.V7FixedWidth29TupleList
