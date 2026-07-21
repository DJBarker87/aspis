import ComponentBSamplerZeroBoundary
import ComponentBMaintainedTerminalBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBSamplerMaintainedPredicatesBridge

abbrev SamplerQM31 := ComponentBSamplerZeroBoundary.SamplerQM31
abbrev MaintainedQM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev SamplerPolynomial := ComponentBSamplerZeroBoundary.Polynomial
abbrev MaintainedPolynomial := ComponentBMaintainedTerminalBridge.Polynomial
abbrev SamplerMask := ComponentBSamplerZeroBoundary.Mask
abbrev MaintainedMask := ComponentBMaintainedTerminalBridge.Mask

local instance : Inhabited SamplerQM31 :=
  ⟨aspis_prover.aspis_core.field.QM31.ZERO⟩

/-- Coordinatewise identification of the two source-authentic Aeneas copies
of the same Rust `QM31` representation. -/
def toMaintainedQM31 (value : SamplerQM31) : MaintainedQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b },
    c1 := { a := value.c1.a, b := value.c1.b } }

def toMaintainedArray {n : Std.Usize}
    (values : Array SamplerQM31 n) : Array MaintainedQM31 n :=
  ⟨values.val.map toMaintainedQM31, by
    rw [List.length_map]
    exact values.property⟩

def toMaintainedRounds
    (rounds : Array SamplerPolynomial 10#usize) :
    Array MaintainedPolynomial 10#usize :=
  ⟨rounds.val.map toMaintainedArray, by
    rw [List.length_map]
    exact rounds.property⟩

/-- Representation-only bridge from the authentic sampler extraction to the
generated evaluator extraction.  It changes no coefficient or ordering. -/
def toMaintainedMask (mask : SamplerMask) : MaintainedMask :=
  { initial_claim := toMaintainedQM31 mask.initial_claim,
    zero_boundary_rounds := toMaintainedRounds mask.zero_boundary_rounds }

theorem canonical_to_maintained (value : SamplerQM31)
    (canonical : ComponentBSamplerZeroBoundary.Canonical value) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      (toMaintainedQM31 value) := by
  simpa [ComponentBSamplerZeroBoundary.Canonical,
    ComponentBSamplerZeroBoundary.toAdditive,
    AspisAeneasQM31Additive.CanonicalQM31,
    AspisAeneasQM31Additive.CanonicalCM31,
    AspisAeneasQM31Additive.CanonicalRawM31,
    AspisAeneasQM31Additive.m31Modulus,
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
    ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    toMaintainedQM31] using canonical

theorem toExact_toMaintained (value : SamplerQM31) :
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (toMaintainedQM31 value) =
      ComponentBSamplerZeroBoundary.toExact value := by
  rfl

theorem coefficientExact_to_maintained (polynomial : SamplerPolynomial)
    (coefficient : Fin 28) :
    ComponentBRealEvaluatorProof.generatedQm31ToExact
        (ComponentBRealEvaluatorProof.coefficientAt
          (toMaintainedArray polynomial) coefficient) =
      ComponentBSamplerZeroBoundary.toExact
        (ComponentBSamplerZeroBoundary.coefficientAt polynomial coefficient.val) := by
  have hsource :
      ComponentBSamplerZeroBoundary.coefficientAt polynomial coefficient.val =
        polynomial.val[coefficient.val] := by
    unfold ComponentBSamplerZeroBoundary.coefficientAt
    rw [Array.getElem!_Nat_eq]
    rw [← List.Inhabited_getElem_eq_getElem! polynomial.val coefficient.val]
    rw [polynomial.property]
    exact coefficient.isLt
  have htarget :
      ComponentBRealEvaluatorProof.coefficientAt
          (toMaintainedArray polynomial) coefficient =
        toMaintainedQM31 polynomial.val[coefficient.val] := by
    simp [ComponentBRealEvaluatorProof.coefficientAt, toMaintainedArray]
  rw [htarget, toExact_toMaintained, hsource]

private theorem sum_Ico_one_succ_eq_sum_range
    {A : Type*} [AddCommMonoid A] (f : Nat → A) :
    ∀ n : Nat,
      ∑ coefficient ∈ Finset.Ico 1 (n + 1), f coefficient =
        ∑ coefficient ∈ Finset.range n, f (coefficient + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_range_succ, ih]

theorem polynomialCanonical_to_maintained (polynomial : SamplerPolynomial)
    (canonical : ComponentBSamplerZeroBoundary.PolynomialCanonical polynomial) :
    ComponentBRealEvaluatorProof.CanonicalArray
      (toMaintainedArray polynomial) := by
  intro coefficient
  have h := canonical coefficient.val coefficient.isLt
  have hcoefficient :
      ComponentBSamplerZeroBoundary.coefficientAt polynomial coefficient.val =
        polynomial.val[coefficient.val] := by
    unfold ComponentBSamplerZeroBoundary.coefficientAt
    rw [Array.getElem!_Nat_eq]
    rw [← List.Inhabited_getElem_eq_getElem! polynomial.val coefficient.val]
    simpa [polynomial.property] using coefficient.isLt
  have hconverted :
      (toMaintainedArray polynomial).val[coefficient.val] =
        toMaintainedQM31 polynomial.val[coefficient.val] := by
    simp [toMaintainedArray]
  rw [hconverted, ← hcoefficient]
  exact canonical_to_maintained
    (ComponentBSamplerZeroBoundary.coefficientAt polynomial coefficient.val) h

theorem exactZeroBoundary_to_maintained (polynomial : SamplerPolynomial)
    (zeroBoundary : ComponentBSamplerZeroBoundary.ExactZeroBoundary polynomial) :
    ComponentBMaintainedTerminalBridge.ExactZeroBoundary
      (toMaintainedArray polynomial) := by
  have hconstant := coefficientExact_to_maintained polynomial ⟨0, by omega⟩
  have htail : ∀ coefficient : Fin 27,
      ComponentBMaintainedTerminalBridge.exactTail
          (toMaintainedArray polynomial) coefficient =
        ComponentBSamplerZeroBoundary.toExact
          (ComponentBSamplerZeroBoundary.coefficientAt polynomial
            (coefficient.val + 1)) := by
    intro coefficient
    exact coefficientExact_to_maintained polynomial
      ⟨coefficient.val + 1, by omega⟩
  unfold ComponentBMaintainedTerminalBridge.ExactZeroBoundary
    ComponentBMaintainedTerminalBridge.exactConstant
  rw [hconstant]
  simp_rw [htail]
  change
    (2 : ComponentBSamplerZeroBoundary.ExactQM31) *
        ComponentBSamplerZeroBoundary.toExact
          (ComponentBSamplerZeroBoundary.coefficientAt polynomial 0) +
      ∑ coefficient : Fin 27,
        ComponentBSamplerZeroBoundary.toExact
          (ComponentBSamplerZeroBoundary.coefficientAt polynomial
            (coefficient.val + 1)) = 0
  rw [Fin.sum_univ_eq_sum_range
    (fun coefficient : Nat ↦ ComponentBSamplerZeroBoundary.toExact
      (ComponentBSamplerZeroBoundary.coefficientAt polynomial
        (coefficient + 1))) 27]
  rw [← sum_Ico_one_succ_eq_sum_range
    (fun coefficient ↦ ComponentBSamplerZeroBoundary.toExact
      (ComponentBSamplerZeroBoundary.coefficientAt polynomial coefficient)) 27]
  simpa [ComponentBSamplerZeroBoundary.ExactZeroBoundary,
    ComponentBSamplerZeroBoundary.exactPrefix, two_mul] using zeroBoundary

theorem storedRound_to_maintained (mask : SamplerMask) (round : Fin 10) :
    ComponentBMaintainedTerminalBridge.storedRound
        (toMaintainedMask mask) round =
      toMaintainedArray
        (ComponentBSamplerZeroBoundary.storedRoundAt
          mask.zero_boundary_rounds round.val) := by
  have hsource :
      ComponentBSamplerZeroBoundary.storedRoundAt
          mask.zero_boundary_rounds round.val =
        mask.zero_boundary_rounds.val[round.val] := by
    unfold ComponentBSamplerZeroBoundary.storedRoundAt
    rw [Array.getElem!_Nat_eq]
    rw [← List.Inhabited_getElem_eq_getElem!
      mask.zero_boundary_rounds.val round.val]
    rw [mask.zero_boundary_rounds.property]
    exact round.isLt
  rw [hsource]
  apply Subtype.ext
  simp [ComponentBMaintainedTerminalBridge.storedRound,
    toMaintainedMask, toMaintainedRounds, toMaintainedArray]

/-- A successful call to the authentic generated sampler directly supplies
the maintained terminal bridge's canonical-input and exact zero-boundary
predicates.  `nextWordTotal` is consumed by the operational sampler theorem;
no distributional or uniformity statement is made here. -/
theorem sample_success_supplies_maintained_predicates
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (mask : SamplerMask)
    (run : aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample
      sourceInst source = .ok (.Ok mask, finalSource)) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        (toMaintainedMask mask).initial_claim ∧
      ∀ round : Fin 10,
        ComponentBRealEvaluatorProof.CanonicalArray
            (ComponentBMaintainedTerminalBridge.storedRound
              (toMaintainedMask mask) round) ∧
          ComponentBMaintainedTerminalBridge.ExactZeroBoundary
            (ComponentBMaintainedTerminalBridge.storedRound
              (toMaintainedMask mask) round) := by
  obtain ⟨initialCanonical, rounds⟩ :=
    ComponentBSamplerZeroBoundary.V5SumcheckMask_sample_success
      sourceInst nextWordTotal source finalSource mask run
  refine ⟨canonical_to_maintained mask.initial_claim initialCanonical, ?_⟩
  intro round
  obtain ⟨roundCanonical, roundZeroBoundary⟩ := rounds round
  rw [storedRound_to_maintained]
  exact ⟨polynomialCanonical_to_maintained _ roundCanonical,
    exactZeroBoundary_to_maintained _ roundZeroBoundary⟩

#print axioms canonical_to_maintained
#print axioms toExact_toMaintained
#print axioms coefficientExact_to_maintained
#print axioms polynomialCanonical_to_maintained
#print axioms exactZeroBoundary_to_maintained
#print axioms storedRound_to_maintained
#print axioms sample_success_supplies_maintained_predicates

end ComponentBSamplerMaintainedPredicatesBridge
