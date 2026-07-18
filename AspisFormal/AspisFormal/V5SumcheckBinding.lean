import AspisFormal.V5SumcheckCommitment

/-!
# What coefficient binding is sufficient for component B

`SumcheckMasking` proves that Boolean endpoint data do not determine a
degree-27 polynomial at a later challenge point.  This file records the
matching positive statement.  In an abstract model where a commitment is
injective on the complete coefficient message, equality of pre-challenge
commitments determines every subsequent coefficient evaluation.

The same argument is stated for the complete component-B state: one initial
claim and ten blocks of 27 tail coefficients.  It determines the exact
`terminalCovector` at every later challenge point, and hence the literal
ten-round recurrence by `tenRoundTerminal_eq_terminalCovector`.

The transcript-order predicate is deliberately abstract and remains an
explicit premise.  These theorems do not prove that a deployed PCS is
injective, computationally binding, correctly ordered, or sound.  They say
only what follows once those protocol premises have been established.
-/

namespace AspisV5SumcheckBinding

open AspisSumcheckMasking AspisV5SumcheckCommitment

/-- An ideal coefficient-binding commitment together with an abstract
transcript-order relation.  `commit_injective` is a premise of this model; it
is not inferred from a hash function or a PCS. -/
structure PreChallengeBinding
    (Message Commitment Challenge : Type*) where
  commit : Message → Commitment
  commit_injective : Function.Injective commit
  committedBeforeChallenge : Commitment → Challenge → Prop

/-- The first challenge is `eta`; the polynomial evaluation point is sampled
only afterwards. -/
structure RoundChallenges (K : Type*) where
  eta : K
  evaluationPoint : K

/-- One complete degree-27 coefficient vector. -/
abbrev Degree27Coeff (K : Type*) := RoundCoeff K 27

/-- An abstract binding interface for one degree-27 round message. -/
abbrev Degree27Binding (K Commitment : Type*) :=
  PreChallengeBinding (Degree27Coeff K) Commitment (RoundChallenges K)

section OneRound

variable {K Commitment : Type*} [Field K]

/-- Equality of ideal coefficient commitments fixes the complete degree-27
coefficient vector.  The order premise records that the common commitment was
present before `eta` and the evaluation point; injectivity alone has no
transcript-order content. -/
theorem degree27_coefficients_eq_of_preChallenge_commitment_eq
    (binding : Degree27Binding K Commitment)
    (left right : Degree27Coeff K) (challenges : RoundChallenges K)
    (_hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right) :
    left = right :=
  binding.commit_injective hcommit

/-- A coefficient-binding commitment made before `eta` determines the round
polynomial at every subsequently sampled evaluation point. -/
theorem degree27_coeffEval_eq_of_preChallenge_commitment_eq
    (binding : Degree27Binding K Commitment)
    (left right : Degree27Coeff K) (challenges : RoundChallenges K)
    (hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right) :
    coeffEval left challenges.evaluationPoint =
      coeffEval right challenges.evaluationPoint := by
  rw [degree27_coefficients_eq_of_preChallenge_commitment_eq
    binding left right challenges hbefore hcommit]

/-- The same pre-challenge commitment fixes evaluation at any later point,
not merely at the point stored in one transcript record. -/
theorem degree27_coeffEval_eq_at_any_later_point
    (binding : Degree27Binding K Commitment)
    (left right : Degree27Coeff K) (challenges : RoundChallenges K)
    (hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right)
    (laterPoint : K) :
    coeffEval left laterPoint = coeffEval right laterPoint := by
  rw [degree27_coefficients_eq_of_preChallenge_commitment_eq
    binding left right challenges hbefore hcommit]

end OneRound

/-- The 271 component-B state coordinates: one initial claim followed by ten
degree-27 tail blocks. -/
structure ComponentBState (K : Type*) where
  initial : K
  tails : Fin roundCount → Fin tailCount → K

/-- The challenge record drawn after the component-B state commitment. -/
structure ComponentBChallenges (K : Type*) where
  eta : K
  point : Fin roundCount → K

/-- An abstract binding interface for the complete 271-coordinate state. -/
abbrev ComponentBStateBinding (K Commitment : Type*) :=
  PreChallengeBinding (ComponentBState K) Commitment (ComponentBChallenges K)

section FullState

variable {K Commitment : Type*} [Field K]

/-- The incoming claim at a round, obtained from the already evaluated prefix
of the exact component-B recurrence. -/
def incomingClaim (state : ComponentBState K)
    (point : Fin roundCount → K) (round : Fin roundCount) : K :=
  chainContributions state.initial
    (List.ofFn (fun index : Fin (round : ℕ) =>
      tailEvaluation
        (state.tails ⟨index, lt_trans index.isLt round.isLt⟩)
        (point ⟨index, lt_trans index.isLt round.isLt⟩)))

/-- The complete degree-27 mask polynomial sent in one round of the chained
construction. -/
def roundCoeffAt (h2 : (2 : K) ≠ 0) (state : ComponentBState K)
    (point : Fin roundCount → K) (round : Fin roundCount) : RoundCoeff K 27 :=
  maskRoundCoeff (incomingClaim state point round)
    (zeroBoundaryFromTail h2 (state.tails round))

/-- Equality of ideal full-state commitments fixes all 271 coordinates. -/
theorem componentBState_eq_of_preChallenge_commitment_eq
    (binding : ComponentBStateBinding K Commitment)
    (left right : ComponentBState K) (challenges : ComponentBChallenges K)
    (_hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right) :
    left = right :=
  binding.commit_injective hcommit

/-- The full pre-`eta` state commitment determines every later degree-27
round evaluation, including the recursively derived incoming claim. -/
theorem componentB_roundCoeffEval_eq_of_preChallenge_commitment_eq
    (h2 : (2 : K) ≠ 0)
    (binding : ComponentBStateBinding K Commitment)
    (left right : ComponentBState K) (challenges : ComponentBChallenges K)
    (hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right)
    (round : Fin roundCount) :
    coeffEval (roundCoeffAt h2 left challenges.point round)
        (challenges.point round) =
      coeffEval (roundCoeffAt h2 right challenges.point round)
        (challenges.point round) := by
  rw [componentBState_eq_of_preChallenge_commitment_eq
    binding left right challenges hbefore hcommit]

/-- Equality of pre-`eta` full-state commitments determines the exact public
terminal covector at every subsequently sampled ten-coordinate point. -/
theorem componentB_terminalCovector_eq_of_preChallenge_commitment_eq
    (binding : ComponentBStateBinding K Commitment)
    (left right : ComponentBState K) (challenges : ComponentBChallenges K)
    (hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right) :
    terminalCovector challenges.point left.initial left.tails =
      terminalCovector challenges.point right.initial right.tails := by
  rw [componentBState_eq_of_preChallenge_commitment_eq
    binding left right challenges hbefore hcommit]

/-- The final sufficiency statement for component B.  It passes through the
kernel-checked terminal-covector identity, rather than identifying the
ten-round recurrence with a Boolean multilinear table. -/
theorem componentB_tenRoundTerminal_eq_of_preChallenge_commitment_eq
    (binding : ComponentBStateBinding K Commitment)
    (left right : ComponentBState K) (challenges : ComponentBChallenges K)
    (hbefore : binding.committedBeforeChallenge
      (binding.commit left) challenges)
    (hcommit : binding.commit left = binding.commit right) :
    tenRoundTerminal left.initial left.tails challenges.point =
      tenRoundTerminal right.initial right.tails challenges.point := by
  rw [tenRoundTerminal_eq_terminalCovector,
    tenRoundTerminal_eq_terminalCovector]
  exact componentB_terminalCovector_eq_of_preChallenge_commitment_eq
    binding left right challenges hbefore hcommit

end FullState

end AspisV5SumcheckBinding

#print axioms AspisV5SumcheckBinding.degree27_coeffEval_eq_at_any_later_point
#print axioms AspisV5SumcheckBinding.componentB_roundCoeffEval_eq_of_preChallenge_commitment_eq
#print axioms AspisV5SumcheckBinding.componentB_terminalCovector_eq_of_preChallenge_commitment_eq
#print axioms AspisV5SumcheckBinding.componentB_tenRoundTerminal_eq_of_preChallenge_commitment_eq
