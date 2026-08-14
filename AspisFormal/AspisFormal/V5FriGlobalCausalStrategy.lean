import AspisFormal.V5FriReleasedAdaptiveExtraction

/-!
# Constructing the global backwards FRI strategy

The adaptive FRI counting theorem needs one response strategy fixed over the
entire four-challenge space.  This file constructs that strategy directly from
one causal transcript family.  Starting with the published final polynomial,
it chooses close predecessors backwards.  Each response support is the exact
set of coordinates where the selected codeword agrees with the decoded fold.

No production-code or cryptographic premise is used here.  The construction
is a finite, classical proof device over the ideal transcript family.
-/

namespace AspisV5FriGlobalCausalStrategy

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriAdaptiveUnmatched
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriWeightedCorrelatedAgreementFinalization
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Exact response supports -/

/-- Coordinates where one selected response codeword agrees with the decoded
degree-three fold at one challenge. -/
noncomputable def exactResponseSupport
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (candidate : Message) (z : K) : Finset Domain := by
  classical
  exact Finset.univ.filter fun x =>
    curveValue lanes z x = encoder candidate x

/-- The deterministic response strategy with a caller-chosen candidate and
the complete exact agreement support for that candidate. -/
noncomputable def exactResponseStrategy
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (candidate : K → Message) : ProximateStrategy K Domain Message where
  candidate := candidate
  support z := exactResponseSupport encoder lanes (candidate z) z

@[simp] theorem mem_exactResponseSupport_iff
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (candidate : Message) (z : K) (x : Domain) :
    x ∈ exactResponseSupport encoder lanes candidate z ↔
      curveValue lanes z x = encoder candidate x := by
  classical
  simp [exactResponseSupport]

@[simp] theorem exactResponseStrategy_candidate
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (candidate : K → Message) (z : K) :
    (exactResponseStrategy encoder lanes candidate).candidate z = candidate z :=
  rfl

@[simp] theorem exactResponseStrategy_support
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (candidate : K → Message) (z : K) :
    (exactResponseStrategy encoder lanes candidate).support z =
      exactResponseSupport encoder lanes (candidate z) z := rfl

theorem exactResponseStrategy_weightedValid
    {Domain Message : Type*} [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (weight : Domain → Nat)
    (weightThreshold : Nat) (lanes : Fin 4 → Domain → K)
    (candidate : K → Message) (z : K)
    (hmass : weightThreshold <
      weightMass weight (exactResponseSupport encoder lanes (candidate z) z)) :
    WeightedValidResponse encoder weight weightThreshold lanes
      (exactResponseStrategy encoder lanes candidate) z := by
  constructor
  · simpa only [exactResponseStrategy_support] using hmass
  · intro x hx
    exact (mem_exactResponseSupport_iff encoder lanes (candidate z) z x).mp
      (by simpa only [exactResponseStrategy_support] using hx)

/-! ## Backwards candidate choice -/

/-- Select one close predecessor when one exists, and return zero otherwise.
The fallback is never used by a theorem whose premise supplies a predecessor. -/
noncomputable def chooseMatchingPredecessor
    {Previous Next : Type*} [Zero Previous]
    (near : Previous → Prop) (fold : Previous → Next) (target : Next) :
    Previous := by
  classical
  exact if h : ∃ previous, near previous ∧ fold previous = target
    then Classical.choose h
    else 0

theorem chooseMatchingPredecessor_spec
    {Previous Next : Type*} [Zero Previous]
    (near : Previous → Prop) (fold : Previous → Next) (target : Next)
    (h : ∃ previous, near previous ∧ fold previous = target) :
    near (chooseMatchingPredecessor near fold target) ∧
      fold (chooseMatchingPredecessor near fold target) = target := by
  classical
  simp only [chooseMatchingPredecessor, dif_pos h]
  exact Classical.choose_spec h

/-! ## The four suffix-conditioned strategies -/

noncomputable def selectedRound3
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) : Coeff3 K :=
  chooseMatchingPredecessor
    (PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
      (transcriptBeforeRound3 family z0 z1 z2))
    (coefficientFoldLayer 4 z3)
    (family.final z0 z1 z2 z3)

noncomputable def selectedRound2
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) : Coeff2 K :=
  chooseMatchingPredecessor
    (PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
      (transcriptBeforeRound2 family z0 z1))
    (coefficientFoldLayer 16 z2)
    (selectedRound3 base family z0 z1 z2 z3)

noncomputable def selectedRound1
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) : Coeff1 K :=
  chooseMatchingPredecessor
    (PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0))
    (coefficientFoldLayer 64 z1)
    (selectedRound2 base family z0 z1 z2 z3)

noncomputable def constructedAdaptiveStrategies
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K) :
    AdaptiveStrategies (K := K) where
  round3 z0 z1 z2 :=
    exactResponseStrategy
      (encoder4 (scheduleAfter2 base z0 z1 z2))
      (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
        (transcriptBeforeRound3 family z0 z1 z2))
      (family.final z0 z1 z2)
  round2 z0 z1 z3 :=
    exactResponseStrategy
      (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
      (line2DecodedLanes (scheduleAfter1 base z0 z1)
        (transcriptBeforeRound2 family z0 z1))
      (fun z2 => selectedRound3 base family z0 z1 z2 z3)
  round1 z0 z2 z3 :=
    exactResponseStrategy
      (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
      (line1DecodedLanes (scheduleAfter0 base z0)
        (transcriptBeforeRound1 family z0))
      (fun z1 => selectedRound2 base family z0 z1 z2 z3)
  round0 z1 z2 z3 :=
    exactResponseStrategy
      (encoder1 base releasedEvaluationPoints)
      (circleDecodedLanes base (transcriptBeforeRound0 family))
      (fun z0 => selectedRound1 base family z0 z1 z2 z3)

@[simp] theorem constructed_round3_candidate
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) :
    ((constructedAdaptiveStrategies base family).round3 z0 z1 z2).candidate z3 =
      family.final z0 z1 z2 z3 := rfl

@[simp] theorem constructed_round2_candidate
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) :
    ((constructedAdaptiveStrategies base family).round2 z0 z1 z3).candidate z2 =
      selectedRound3 base family z0 z1 z2 z3 := rfl

@[simp] theorem constructed_round1_candidate
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) :
    ((constructedAdaptiveStrategies base family).round1 z0 z2 z3).candidate z1 =
      selectedRound2 base family z0 z1 z2 z3 := rfl

@[simp] theorem constructed_round0_candidate
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K) :
    ((constructedAdaptiveStrategies base family).round0 z1 z2 z3).candidate z0 =
      selectedRound1 base family z0 z1 z2 z3 := rfl

/-! ## Prefix proximity gives the next backwards response -/

theorem round0_exactResponse_valid_of_prefixNear1
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (candidate : K → Coeff1 K) (z0 : K)
    (hnear : PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
      (transcriptBeforeRound1 family z0) (candidate z0)) :
    WeightedValidResponse (encoder1 base releasedEvaluationPoints)
      (round0Weight base (transcriptBeforeRound0 family)) 6082
      (circleDecodedLanes base (transcriptBeforeRound0 family))
      (exactResponseStrategy (encoder1 base releasedEvaluationPoints)
        (circleDecodedLanes base (transcriptBeforeRound0 family)) candidate)
  z0 := by
  classical
  apply exactResponseStrategy_weightedValid
  unfold round0Weight
  rw [weightMass_projectedSupportWeight_eq_card beforeRound0Set
    round0Projection]
  apply hnear.trans_le
  apply Finset.card_le_card
  intro q hq
  have hparts :
      q ∈ beforeRound1Set (scheduleAfter0 base z0)
          (transcriptBeforeRound1 family z0) ∧
        (transcriptBeforeRound1 family z0).layer1 q =
          encoder1 (scheduleAfter0 base z0) releasedEvaluationPoints
            (candidate z0) q := by
    simpa only [prefixAgreement1, Finset.mem_filter] using hq
  have hround0 : Round0Consistent (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0) q := by
    simpa only [beforeRound1Set, Finset.mem_filter, Finset.mem_univ, true_and]
      using hparts.1
  have hcurve := curve_circleDecodedLanes_eq_circleFold
    (scheduleAfter0 base z0) releasedEvaluationPoints
    (inverseTablesMatch_scheduleAt base z0 0 0 0 htables)
    (transcriptBeforeRound1 family z0) q
  have hagree :
      curveValue (circleDecodedLanes base (transcriptBeforeRound0 family)) z0 q =
        encoder1 base releasedEvaluationPoints (candidate z0) q := by
    calc
      curveValue (circleDecodedLanes base (transcriptBeforeRound0 family)) z0 q =
          circleFoldLayer 131072 z0 base.circleInv2x base.circleInv2y
            family.layer0 q := by
        have hcurve' := hcurve
        change curveValue
            (circleDecodedLanes base (transcriptBeforeRound0 family)) z0 q =
          circleFoldLayer 131072 z0 base.circleInv2x base.circleInv2y
            family.layer0 q at hcurve'
        exact hcurve'
      _ = (transcriptBeforeRound1 family z0).layer1 q := by
        simpa [Round0Consistent, scheduleAfter0, scheduleAt,
          transcriptBeforeRound1] using hround0
      _ = encoder1 (scheduleAfter0 base z0) releasedEvaluationPoints
          (candidate z0) q := hparts.2
      _ = encoder1 base releasedEvaluationPoints (candidate z0) q := by
        rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    beforeRound0Set, round0Projection]
  exact (mem_exactResponseSupport_iff
    (encoder1 base releasedEvaluationPoints)
    (circleDecodedLanes base (transcriptBeforeRound0 family))
    (candidate z0) z0 q).2 hagree

theorem round1_exactResponse_valid_of_prefixNear2
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (candidate : K → Coeff2 K) (z0 z1 : K)
    (hnear : PrefixNear2 (scheduleAfter1 base z0 z1)
      releasedEvaluationPoints (transcriptBeforeRound2 family z0 z1)
      (candidate z1)) :
    WeightedValidResponse
      (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
      (round1Weight (scheduleAfter0 base z0)
        (transcriptBeforeRound1 family z0)) 6082
      (line1DecodedLanes (scheduleAfter0 base z0)
        (transcriptBeforeRound1 family z0))
      (exactResponseStrategy
        (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
        (line1DecodedLanes (scheduleAfter0 base z0)
          (transcriptBeforeRound1 family z0)) candidate)
      z1 := by
  classical
  apply exactResponseStrategy_weightedValid
  unfold round1Weight
  rw [weightMass_projectedSupportWeight_eq_card
    (beforeRound1Set (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0)) round1Projection]
  apply hnear.trans_le
  apply Finset.card_le_card
  intro q hq
  have hparts :
      q ∈ beforeRound2Set (scheduleAfter1 base z0 z1)
          (transcriptBeforeRound2 family z0 z1) ∧
        (transcriptBeforeRound2 family z0 z1).layer2 (queryParent1 q) =
          encoder2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
            (candidate z1) (queryParent1 q) := by
    simpa only [prefixAgreement2, Finset.mem_filter] using hq
  have hround01 : Round01Consistent (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1) q := by
    simpa only [beforeRound2Set, Finset.mem_filter, Finset.mem_univ, true_and]
      using hparts.1
  have hsource : q ∈ beforeRound1Set (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0) := by
    simp only [beforeRound1Set, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [Round01Consistent, Round0Consistent, scheduleAfter0, scheduleAfter1,
      scheduleAt, transcriptBeforeRound1, transcriptBeforeRound2]
      using hround01.1
  have hcurve := curve_line1DecodedLanes_eq_lineFold
    (scheduleAfter1 base z0 z1) releasedEvaluationPoints
    (inverseTablesMatch_scheduleAt base z0 z1 0 0 htables)
    (transcriptBeforeRound2 family z0 z1) (queryParent1 q)
  have hagree :
      curveValue
          (line1DecodedLanes (scheduleAfter0 base z0)
            (transcriptBeforeRound1 family z0)) z1 (queryParent1 q) =
        encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints
          (candidate z1) (queryParent1 q) := by
    calc
      curveValue
          (line1DecodedLanes (scheduleAfter0 base z0)
            (transcriptBeforeRound1 family z0)) z1 (queryParent1 q) =
          lineFoldLayer 32768 z1 base.line1Inverse
            (family.layer1 z0) (queryParent1 q) := by
        have hcurve' := hcurve
        change curveValue
            (line1DecodedLanes (scheduleAfter0 base z0)
              (transcriptBeforeRound1 family z0)) z1 (queryParent1 q) =
          lineFoldLayer 32768 z1 base.line1Inverse
            (family.layer1 z0) (queryParent1 q) at hcurve'
        exact hcurve'
      _ = (transcriptBeforeRound2 family z0 z1).layer2
          (queryParent1 q) := by
        simpa [Round01Consistent, scheduleAfter1, scheduleAt,
          transcriptBeforeRound2] using hround01.2
      _ = encoder2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (candidate z1) (queryParent1 q) := hparts.2
      _ = encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints
          (candidate z1) (queryParent1 q) := by
        rfl
  simp only [Finset.mem_filter, hsource, true_and, round1Projection]
  exact (mem_exactResponseSupport_iff
    (encoder2 (scheduleAfter0 base z0) releasedEvaluationPoints)
    (line1DecodedLanes (scheduleAfter0 base z0)
      (transcriptBeforeRound1 family z0))
    (candidate z1) z1 (queryParent1 q)).2 hagree

theorem round2_exactResponse_valid_of_prefixNear3
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (candidate : K → Coeff3 K) (z0 z1 z2 : K)
    (hnear : PrefixNear3 (scheduleAfter2 base z0 z1 z2)
      releasedEvaluationPoints (transcriptBeforeRound3 family z0 z1 z2)
      (candidate z2)) :
    WeightedValidResponse
      (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
      (round2Weight (scheduleAfter1 base z0 z1)
        (transcriptBeforeRound2 family z0 z1)) 6082
      (line2DecodedLanes (scheduleAfter1 base z0 z1)
        (transcriptBeforeRound2 family z0 z1))
      (exactResponseStrategy
        (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
        (line2DecodedLanes (scheduleAfter1 base z0 z1)
          (transcriptBeforeRound2 family z0 z1)) candidate)
      z2 := by
  classical
  apply exactResponseStrategy_weightedValid
  unfold round2Weight
  rw [weightMass_projectedSupportWeight_eq_card
    (beforeRound2Set (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1)) round2Projection]
  apply hnear.trans_le
  apply Finset.card_le_card
  intro q hq
  have hparts :
      q ∈ beforeRound3Set (scheduleAfter2 base z0 z1 z2)
          (transcriptBeforeRound3 family z0 z1 z2) ∧
        (transcriptBeforeRound3 family z0 z1 z2).layer3 (queryParent2 q) =
          encoder3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
            (candidate z2) (queryParent2 q) := by
    simpa only [prefixAgreement3, Finset.mem_filter] using hq
  have hround012 : Round012Consistent (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2) q := by
    simpa only [beforeRound3Set, Finset.mem_filter, Finset.mem_univ, true_and]
      using hparts.1
  have hsource : q ∈ beforeRound2Set (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1) := by
    simp only [beforeRound2Set, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [Round012Consistent, Round01Consistent, Round0Consistent,
      scheduleAfter1, scheduleAfter2, scheduleAt, transcriptBeforeRound2,
      transcriptBeforeRound3] using hround012.1
  have hcurve := curve_line2DecodedLanes_eq_lineFold
    (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
    (inverseTablesMatch_scheduleAt base z0 z1 z2 0 htables)
    (transcriptBeforeRound3 family z0 z1 z2) (queryParent2 q)
  have hagree :
      curveValue
          (line2DecodedLanes (scheduleAfter1 base z0 z1)
            (transcriptBeforeRound2 family z0 z1)) z2 (queryParent2 q) =
        encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (candidate z2) (queryParent2 q) := by
    calc
      curveValue
          (line2DecodedLanes (scheduleAfter1 base z0 z1)
            (transcriptBeforeRound2 family z0 z1)) z2 (queryParent2 q) =
          lineFoldLayer 8192 z2 base.line2Inverse
            (family.layer2 z0 z1) (queryParent2 q) := by
        have hcurve' := hcurve
        change curveValue
            (line2DecodedLanes (scheduleAfter1 base z0 z1)
              (transcriptBeforeRound2 family z0 z1)) z2 (queryParent2 q) =
          lineFoldLayer 8192 z2 base.line2Inverse
            (family.layer2 z0 z1) (queryParent2 q) at hcurve'
        exact hcurve'
      _ = (transcriptBeforeRound3 family z0 z1 z2).layer3
          (queryParent2 q) := by
        simpa [Round012Consistent, scheduleAfter2, scheduleAt,
          transcriptBeforeRound3] using hround012.2
      _ = encoder3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
          (candidate z2) (queryParent2 q) := hparts.2
      _ = encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
          (candidate z2) (queryParent2 q) := by
        rfl
  simp only [Finset.mem_filter, hsource, true_and, round2Projection]
  exact (mem_exactResponseSupport_iff
    (encoder3 (scheduleAfter1 base z0 z1) releasedEvaluationPoints)
    (line2DecodedLanes (scheduleAfter1 base z0 z1)
      (transcriptBeforeRound2 family z0 z1))
    (candidate z2) z2 (queryParent2 q)).2 hagree

theorem round3_exactResponse_valid_of_dense_consistency
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (z0 z1 z2 z3 : K)
    (hdense : 6082 < (consistencySet (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3)).card) :
    WeightedValidResponse
      (encoder4 (scheduleAfter2 base z0 z1 z2))
      (round3Weight (scheduleAfter2 base z0 z1 z2)
        (transcriptBeforeRound3 family z0 z1 z2)) 6082
      (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
        (transcriptBeforeRound3 family z0 z1 z2))
      (exactResponseStrategy
        (encoder4 (scheduleAfter2 base z0 z1 z2))
        (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
          (transcriptBeforeRound3 family z0 z1 z2))
        (family.final z0 z1 z2))
      z3 := by
  classical
  apply exactResponseStrategy_weightedValid
  unfold round3Weight
  rw [weightMass_projectedSupportWeight_eq_card
    (beforeRound3Set (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2)) round3Projection]
  apply hdense.trans_le
  apply Finset.card_le_card
  intro q hq
  have hconsistent : QueryConsistent (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) q := by
    simpa only [consistencySet, Finset.mem_filter, Finset.mem_univ, true_and]
      using hq
  have hsource : q ∈ beforeRound3Set (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2) := by
    simp only [beforeRound3Set, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [QueryConsistent, Round012Consistent, Round01Consistent,
      Round0Consistent, scheduleAfter2, scheduleAt, transcriptBeforeRound3,
      fullTranscript] using
        And.intro (And.intro hconsistent.1 hconsistent.2.1)
          hconsistent.2.2.1
  have hcurve := curve_line3DecodedLanes_eq_lineFold
    (scheduleAt base z0 z1 z2 z3) releasedEvaluationPoints
    (inverseTablesMatch_scheduleAt base z0 z1 z2 z3 htables)
    (fullTranscript family z0 z1 z2 z3) (queryParent3 q)
  have hagree :
      curveValue
          (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
            (transcriptBeforeRound3 family z0 z1 z2)) z3 (queryParent3 q) =
        encoder4 (scheduleAfter2 base z0 z1 z2)
          (family.final z0 z1 z2 z3) (queryParent3 q) := by
    calc
      curveValue
          (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
            (transcriptBeforeRound3 family z0 z1 z2)) z3 (queryParent3 q) =
          lineFoldLayer 2048 z3 base.line3Inverse
            (family.layer3 z0 z1 z2) (queryParent3 q) := by
        have hcurve' := hcurve
        change curveValue
            (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
              (transcriptBeforeRound3 family z0 z1 z2)) z3 (queryParent3 q) =
          lineFoldLayer 2048 z3 base.line3Inverse
            (family.layer3 z0 z1 z2) (queryParent3 q) at hcurve'
        exact hcurve'
      _ = finalTensorValue
          (algebraMap (ZMod P) K (base.finalX (queryParent3 q)))
          (family.final z0 z1 z2 z3) := by
        simpa [QueryConsistent, scheduleAt, fullTranscript]
          using hconsistent.2.2.2
      _ = encoder4 (scheduleAfter2 base z0 z1 z2)
          (family.final z0 z1 z2 z3) (queryParent3 q) := by
        rfl
  simp only [Finset.mem_filter, hsource, true_and, round3Projection]
  exact (mem_exactResponseSupport_iff
    (encoder4 (scheduleAfter2 base z0 z1 z2))
    (line3DecodedLanes (scheduleAfter2 base z0 z1 z2)
      (transcriptBeforeRound3 family z0 z1 z2))
    (family.final z0 z1 z2 z3) z3 (queryParent3 q)).2 hagree

/-! ## The globally fixed backwards selection -/

theorem selectedRound3_spec_of_matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K)
    (hmatch : Round3Matches base family
      (constructedAdaptiveStrategies base family) z0 z1 z2 z3) :
    PrefixNear3 (scheduleAfter2 base z0 z1 z2) releasedEvaluationPoints
        (transcriptBeforeRound3 family z0 z1 z2)
        (selectedRound3 base family z0 z1 z2 z3) ∧
      coefficientFoldLayer 4 z3
          (selectedRound3 base family z0 z1 z2 z3) =
        family.final z0 z1 z2 z3 := by
  apply chooseMatchingPredecessor_spec
  simpa [Round3Matches, HasMatchingPredecessor,
    constructedAdaptiveStrategies] using hmatch

theorem selectedRound2_spec_of_matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K)
    (hmatch : Round2Matches base family
      (constructedAdaptiveStrategies base family) z0 z1 z2 z3) :
    PrefixNear2 (scheduleAfter1 base z0 z1) releasedEvaluationPoints
        (transcriptBeforeRound2 family z0 z1)
        (selectedRound2 base family z0 z1 z2 z3) ∧
      coefficientFoldLayer 16 z2
          (selectedRound2 base family z0 z1 z2 z3) =
        selectedRound3 base family z0 z1 z2 z3 := by
  apply chooseMatchingPredecessor_spec
  simpa [Round2Matches, HasMatchingPredecessor,
    constructedAdaptiveStrategies] using hmatch

theorem selectedRound1_spec_of_matches
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (z0 z1 z2 z3 : K)
    (hmatch : Round1Matches base family
      (constructedAdaptiveStrategies base family) z0 z1 z2 z3) :
    PrefixNear1 (scheduleAfter0 base z0) releasedEvaluationPoints
        (transcriptBeforeRound1 family z0)
        (selectedRound1 base family z0 z1 z2 z3) ∧
      coefficientFoldLayer 64 z1
          (selectedRound1 base family z0 z1 z2 z3) =
        selectedRound2 base family z0 z1 z2 z3 := by
  apply chooseMatchingPredecessor_spec
  simpa [Round1Matches, HasMatchingPredecessor,
    constructedAdaptiveStrategies] using hmatch

/-- Every causal transcript family has one backwards response strategy fixed
over the whole challenge space.  The only schedule premise is the proved
equality between the released inverse tables and the abstract FRI tables. -/
theorem constructed_globalCausalBackwardSelection
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (htables : InverseTablesMatch base releasedEvaluationPoints) :
    GlobalCausalBackwardSelection base family
      (constructedAdaptiveStrategies base family) := by
  intro z0 z1 z2 z3
  constructor
  · rfl
  · intro hdense
    exact round3_exactResponse_valid_of_dense_consistency
      base family htables z0 z1 z2 z3 hdense
  · intro hmatch
    simpa only [constructed_round2_candidate, constructed_round3_candidate]
      using selectedRound3_spec_of_matches base family z0 z1 z2 z3 hmatch
  · intro hmatch
    exact round2_exactResponse_valid_of_prefixNear3 base family htables
      (fun z2' => selectedRound3 base family z0 z1 z2' z3) z0 z1 z2
      (selectedRound3_spec_of_matches base family z0 z1 z2 z3 hmatch).1
  · intro hmatch
    simpa only [constructed_round1_candidate, constructed_round2_candidate]
      using selectedRound2_spec_of_matches base family z0 z1 z2 z3 hmatch
  · intro hmatch
    exact round1_exactResponse_valid_of_prefixNear2 base family htables
      (fun z1' => selectedRound2 base family z0 z1' z2 z3) z0 z1
      (selectedRound2_spec_of_matches base family z0 z1 z2 z3 hmatch).1
  · intro hmatch
    simpa only [constructed_round0_candidate, constructed_round1_candidate]
      using selectedRound1_spec_of_matches base family z0 z1 z2 z3 hmatch
  · intro hmatch
    exact round0_exactResponse_valid_of_prefixNear1 base family htables
      (fun z0' => selectedRound1 base family z0' z1 z2 z3) z0
      (selectedRound1_spec_of_matches base family z0 z1 z2 z3 hmatch).1

/-- The four adaptive bad-challenge fibres for the constructed strategy have
the same exact counting bound as the abstract suffix-conditioned theorem. -/
theorem constructed_adaptiveBadChallengeTuples_card_le
    (base : FixedSchedule (ZMod P) K) (family : CausalTranscriptFamily K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    (allBadChallengeTuples
      (adaptiveBadSets base family hfinal htables hpublished
        (constructedAdaptiveStrategies base family))).card ≤
      Fintype.card K ^ 3 *
        (releasedChallengeCap 0 + releasedChallengeCap 1 +
          releasedChallengeCap 2 + releasedChallengeCap 3) :=
  adaptiveBadChallengeTuples_card_le base family hfinal htables hpublished
    (constructedAdaptiveStrategies base family)

/-- Decisive ideal FRI inclusion with no caller-supplied backwards strategy:
accepted verification either reaches the query-miss event, one of the four
counted challenge fibres, or one member of the at-most-240 initial decoder
list whose four exact folds equal the published final polynomial. -/
theorem accepted_ideal_fri_extracts_with_constructed_strategy
    (base : FixedSchedule (ZMod P) K)
    (family : CausalTranscriptFamily K)
    (queries : QuerySchedule 18 131072)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (z0 z1 z2 z3 : K)
    (haccepts : IdealAccepts (scheduleAt base z0 z1 z2 z3)
      (fullTranscript family z0 z1 z2 z3) queries) :
    QueryPhaseFailure (scheduleAt base z0 z1 z2 z3)
        (fullTranscript family z0 z1 z2 z3) queries \/
      (adaptiveBadSets base family hfinal htables hpublished
        (constructedAdaptiveStrategies base family)).Occurs z0 z1 z2 z3 \/
      ∃ c0 : Coeff0 K,
        c0 ∈ initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family) /\
        (initialCandidateList
          (concreteCodeEncoders base releasedEvaluationPoints)
          (transcriptBeforeRound0 family)).card ≤ 240 /\
        coefficientFoldLayer 4 z3
          (coefficientFoldLayer 16 z2
            (coefficientFoldLayer 64 z1
              (coefficientFoldLayer 256 z0 c0))) =
            family.final z0 z1 z2 z3 :=
  accepted_ideal_fri_extracts_of_global_selection base family queries hfinal
    htables hpublished (constructedAdaptiveStrategies base family)
    (constructed_globalCausalBackwardSelection base family htables)
    z0 z1 z2 z3 haccepts

#print axioms chooseMatchingPredecessor_spec
#print axioms constructed_globalCausalBackwardSelection
#print axioms constructed_adaptiveBadChallengeTuples_card_le
#print axioms accepted_ideal_fri_extracts_with_constructed_strategy

end AspisV5FriGlobalCausalStrategy
