import AspisFormal.V5FriDegreeThreeCorrelatedAgreement
import AspisFormal.V5FriInitialListBound

/-!
# Common-domain correlated-agreement interface for the four V5 FRI rounds

The later V5 words are queried through the original `131072` query fibres.
Consequently layers two, three, and the final tensor must be lifted back to
that common domain by `q / 4`, `q / 16`, and `q / 64`.  Treating the four
native word lengths as unrelated unweighted codes would be wrong.

This file defines those exact lifts and gives a conservative interface using
four ordinary degree-three curve-decoding statements on the common lifted
domain.  This is useful for checking the event logic, but it is **not** an
instantiation of S-two's native-domain weighted bounds: applying an ordinary
theorem here naturally charges domain size `131072` in every round.  Recovering
the smaller native ledger terms requires a separate weighted-measure
instantiation of S-two Theorem 29.

No theorem here says that a missing predecessor is itself a bounded event.
The bounded event is always the explicit `goodChallenges` finset of a response
strategy, and its cardinality follows only from the curve-decoding premise.
-/

namespace AspisV5FriWeightedReductionBoundary

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriDegreeThreeCorrelatedAgreement

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K]

/-- Layer two lifted to the initial query-fibre domain.  Every native layer-two
coordinate is repeated over its four children. -/
def liftedLayer2Encoder (encoders : CodeEncoders K) :
    Coeff2 K -> Fin 131072 -> K :=
  fun candidate q => encoders.layer2 candidate (queryParent1 q)

/-- Layer three lifted over its sixteen initial-fibre descendants. -/
def liftedLayer3Encoder (encoders : CodeEncoders K) :
    Coeff3 K -> Fin 131072 -> K :=
  fun candidate q => encoders.layer3 candidate (queryParent2 q)

/-- The final four-coefficient tensor lifted over its sixty-four initial-fibre
descendants. -/
def liftedFinalEncoder (schedule : FixedSchedule F K) :
    Coeff4 K -> Fin 131072 -> K :=
  fun candidate q =>
    finalTensorValue
      (algebraMap F K (schedule.finalX (queryParent3 q))) candidate

/-- Conservative common-domain coding-theory premise.  `roundBound i` is an
explicit bound for the corresponding *lifted-domain* theorem; it must not be
identified with the smaller native weighted ledger bound without a separate
proof.  Keeping it explicit avoids hiding any estimate in a Boolean "fold
failed" predicate. -/
structure V5CommonDomainCurveDecodingBoundary
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (roundBound : Fin 4 -> Nat) : Prop where
  round0 : DegreeThreeCurveDecodable
    encoders.layer1 6082 (roundBound 0)
  round1 : DegreeThreeCurveDecodable
    (liftedLayer2Encoder encoders) 6082 (roundBound 1)
  round2 : DegreeThreeCurveDecodable
    (liftedLayer3Encoder encoders) 6082 (roundBound 2)
  round3 : DegreeThreeCurveDecodable
    (liftedFinalEncoder schedule) 6082 (roundBound 3)

/-- One-round inclusion for the circle-to-line reduction.  The strategy is
fixed before `alpha` is sampled. -/
theorem round0_response_is_joint_or_counted
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (roundBound : Fin 4 -> Nat)
    (hboundary : V5CommonDomainCurveDecodingBoundary
      schedule encoders roundBound)
    (lanes : Fin 4 -> Fin 131072 -> K)
    (strategy : ProximateStrategy K (Fin 131072) (Coeff1 K))
    (alpha : K)
    (hvalid : ValidResponse encoders.layer1 6082 lanes strategy alpha) :
    HasJointAgreement encoders.layer1 6082 lanes ∨
      (alpha ∈ goodChallenges encoders.layer1 6082 lanes strategy ∧
        (goodChallenges encoders.layer1 6082 lanes strategy).card ≤
          roundBound 0) :=
  accepted_response_is_counted encoders.layer1 6082 (roundBound 0)
    hboundary.round0 lanes strategy alpha hvalid

theorem round1_response_is_joint_or_counted
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (roundBound : Fin 4 -> Nat)
    (hboundary : V5CommonDomainCurveDecodingBoundary
      schedule encoders roundBound)
    (lanes : Fin 4 -> Fin 131072 -> K)
    (strategy : ProximateStrategy K (Fin 131072) (Coeff2 K))
    (alpha : K)
    (hvalid : ValidResponse (liftedLayer2Encoder encoders)
      6082 lanes strategy alpha) :
    HasJointAgreement (liftedLayer2Encoder encoders) 6082 lanes ∨
      (alpha ∈ goodChallenges (liftedLayer2Encoder encoders)
          6082 lanes strategy ∧
        (goodChallenges (liftedLayer2Encoder encoders)
          6082 lanes strategy).card ≤ roundBound 1) :=
  accepted_response_is_counted (liftedLayer2Encoder encoders)
    6082 (roundBound 1) hboundary.round1 lanes strategy alpha hvalid

theorem round2_response_is_joint_or_counted
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (roundBound : Fin 4 -> Nat)
    (hboundary : V5CommonDomainCurveDecodingBoundary
      schedule encoders roundBound)
    (lanes : Fin 4 -> Fin 131072 -> K)
    (strategy : ProximateStrategy K (Fin 131072) (Coeff3 K))
    (alpha : K)
    (hvalid : ValidResponse (liftedLayer3Encoder encoders)
      6082 lanes strategy alpha) :
    HasJointAgreement (liftedLayer3Encoder encoders) 6082 lanes ∨
      (alpha ∈ goodChallenges (liftedLayer3Encoder encoders)
          6082 lanes strategy ∧
        (goodChallenges (liftedLayer3Encoder encoders)
          6082 lanes strategy).card ≤ roundBound 2) :=
  accepted_response_is_counted (liftedLayer3Encoder encoders)
    6082 (roundBound 2) hboundary.round2 lanes strategy alpha hvalid

theorem round3_response_is_joint_or_counted
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (roundBound : Fin 4 -> Nat)
    (hboundary : V5CommonDomainCurveDecodingBoundary
      schedule encoders roundBound)
    (lanes : Fin 4 -> Fin 131072 -> K)
    (strategy : ProximateStrategy K (Fin 131072) (Coeff4 K))
    (alpha : K)
    (hvalid : ValidResponse (liftedFinalEncoder schedule)
      6082 lanes strategy alpha) :
    HasJointAgreement (liftedFinalEncoder schedule) 6082 lanes ∨
      (alpha ∈ goodChallenges (liftedFinalEncoder schedule)
          6082 lanes strategy ∧
        (goodChallenges (liftedFinalEncoder schedule)
          6082 lanes strategy).card ≤ roundBound 3) :=
  accepted_response_is_counted (liftedFinalEncoder schedule)
    6082 (roundBound 3) hboundary.round3 lanes strategy alpha hvalid

/-! ## Pure four-round event composition -/

/-- Once each concrete round has supplied its reverse implication, the only
logic left is this four-way event split.  It does not assign probabilities to
the events. -/
theorem four_round_reverse_composition
    {R0 R1 R2 R3 R4 B0 B1 B2 B3 : Prop}
    (h4 : R4)
    (hstep3 : R4 -> R3 ∨ B3)
    (hstep2 : R3 -> R2 ∨ B2)
    (hstep1 : R2 -> R1 ∨ B1)
    (hstep0 : R1 -> R0 ∨ B0) :
    R0 ∨ B0 ∨ B1 ∨ B2 ∨ B3 := by
  rcases hstep3 h4 with h3 | hB3
  · rcases hstep2 h3 with h2 | hB2
    · rcases hstep1 h2 with h1 | hB1
      · rcases hstep0 h1 with h0 | hB0
        · exact Or.inl h0
        · exact Or.inr (Or.inl hB0)
      · exact Or.inr (Or.inr (Or.inl hB1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hB2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hB3)))

#print axioms round0_response_is_joint_or_counted
#print axioms round1_response_is_joint_or_counted
#print axioms round2_response_is_joint_or_counted
#print axioms round3_response_is_joint_or_counted
#print axioms four_round_reverse_composition

end AspisV5FriWeightedReductionBoundary
