import ComponentBEvaluatorFieldBridge
import Mathlib.Algebra.BigOperators.Fin

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBRealEvaluatorProof

abbrev Polynomial := Array QM31 28#usize

def CanonicalArray {n : Std.Usize} (values : Array QM31 n) : Prop :=
  ∀ i : Fin n.val, GeneratedCanonicalQM31 values.val[i.val]

def coefficientAt (polynomial : Polynomial) (i : Fin 28) : QM31 :=
  polynomial.val[i.val]

def exactDegree27Evaluation (polynomial : Polynomial) (x : ExactQM31) : ExactQM31 :=
  generatedQm31ToExact (coefficientAt polynomial ⟨0, by omega⟩) +
  generatedQm31ToExact (coefficientAt polynomial ⟨1, by omega⟩) * x +
  generatedQm31ToExact (coefficientAt polynomial ⟨2, by omega⟩) * x^2 +
  generatedQm31ToExact (coefficientAt polynomial ⟨3, by omega⟩) * x^3 +
  generatedQm31ToExact (coefficientAt polynomial ⟨4, by omega⟩) * x^4 +
  generatedQm31ToExact (coefficientAt polynomial ⟨5, by omega⟩) * x^5 +
  generatedQm31ToExact (coefficientAt polynomial ⟨6, by omega⟩) * x^6 +
  generatedQm31ToExact (coefficientAt polynomial ⟨7, by omega⟩) * x^7 +
  generatedQm31ToExact (coefficientAt polynomial ⟨8, by omega⟩) * x^8 +
  generatedQm31ToExact (coefficientAt polynomial ⟨9, by omega⟩) * x^9 +
  generatedQm31ToExact (coefficientAt polynomial ⟨10, by omega⟩) * x^10 +
  generatedQm31ToExact (coefficientAt polynomial ⟨11, by omega⟩) * x^11 +
  generatedQm31ToExact (coefficientAt polynomial ⟨12, by omega⟩) * x^12 +
  generatedQm31ToExact (coefficientAt polynomial ⟨13, by omega⟩) * x^13 +
  generatedQm31ToExact (coefficientAt polynomial ⟨14, by omega⟩) * x^14 +
  generatedQm31ToExact (coefficientAt polynomial ⟨15, by omega⟩) * x^15 +
  generatedQm31ToExact (coefficientAt polynomial ⟨16, by omega⟩) * x^16 +
  generatedQm31ToExact (coefficientAt polynomial ⟨17, by omega⟩) * x^17 +
  generatedQm31ToExact (coefficientAt polynomial ⟨18, by omega⟩) * x^18 +
  generatedQm31ToExact (coefficientAt polynomial ⟨19, by omega⟩) * x^19 +
  generatedQm31ToExact (coefficientAt polynomial ⟨20, by omega⟩) * x^20 +
  generatedQm31ToExact (coefficientAt polynomial ⟨21, by omega⟩) * x^21 +
  generatedQm31ToExact (coefficientAt polynomial ⟨22, by omega⟩) * x^22 +
  generatedQm31ToExact (coefficientAt polynomial ⟨23, by omega⟩) * x^23 +
  generatedQm31ToExact (coefficientAt polynomial ⟨24, by omega⟩) * x^24 +
  generatedQm31ToExact (coefficientAt polynomial ⟨25, by omega⟩) * x^25 +
  generatedQm31ToExact (coefficientAt polynomial ⟨26, by omega⟩) * x^26 +
  generatedQm31ToExact (coefficientAt polynomial ⟨27, by omega⟩) * x^27

def exactBlock (polynomial : Polynomial) (x : ExactQM31) (block : Fin 7) : ExactQM31 :=
  generatedQm31ToExact (coefficientAt polynomial ⟨4 * block.val, by omega⟩) +
    x * generatedQm31ToExact (coefficientAt polynomial ⟨4 * block.val + 1, by omega⟩) +
    x ^ 2 * generatedQm31ToExact (coefficientAt polynomial ⟨4 * block.val + 2, by omega⟩) +
    x ^ 3 * generatedQm31ToExact (coefficientAt polynomial ⟨4 * block.val + 3, by omega⟩)

def exactRadixFour (polynomial : Polynomial) (x : ExactQM31) : ExactQM31 :=
  x ^ 4 * (x ^ 4 * (x ^ 4 * (x ^ 4 * (x ^ 4 * (x ^ 4 *
    exactBlock polynomial x ⟨6, by omega⟩ + exactBlock polynomial x ⟨5, by omega⟩) +
    exactBlock polynomial x ⟨4, by omega⟩) + exactBlock polynomial x ⟨3, by omega⟩) +
    exactBlock polynomial x ⟨2, by omega⟩) + exactBlock polynomial x ⟨1, by omega⟩) +
    exactBlock polynomial x ⟨0, by omega⟩

/-- The one residual arithmetic premise has no evaluator claim in it.  It
states only the exact semantics of the three optimized field primitives not
covered by the authenticated M31/CM31 arithmetic bundle. -/
structure OptimizedPrimitiveCorrespondence : Prop where
  targetWidth : System.Platform.numBits = 64
  square : ∀ x, GeneratedCanonicalQM31 x →
    ∃ out, ComponentBGenerated.aspis_core.field.QM31.square x = .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact x ^ 2
  prepared : ∀ x, GeneratedCanonicalQM31 x →
    ∃ prepared, ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new x = .ok prepared ∧
      ∀ y, GeneratedCanonicalQM31 y →
        ∃ out, ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul prepared y = .ok out ∧
          GeneratedCanonicalQM31 out ∧
          generatedQm31ToExact out =
            generatedQm31ToExact x * generatedQm31ToExact y
  sumProducts3 : ∀ left right,
    CanonicalArray left → CanonicalArray right →
    ∃ out, ComponentBGenerated.aspis_core.field.qm31_sum_products3 left right = .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        ∑ i : Fin 3,
          generatedQm31ToExact left.val[i.val] *
            generatedQm31ToExact right.val[i.val]

private theorem canonicalAt (polynomial : Polynomial)
    (canonical : CanonicalArray polynomial) (i : Nat) (hi : i < 28) :
    GeneratedCanonicalQM31 (coefficientAt polynomial ⟨i, hi⟩) :=
  canonical ⟨i, hi⟩

private theorem powersCanonical
    (x x2 x3 : QM31)
    (hx : GeneratedCanonicalQM31 x)
    (hx2 : GeneratedCanonicalQM31 x2)
    (hx3 : GeneratedCanonicalQM31 x3) :
    CanonicalArray (Array.make 3#usize [x, x2, x3]) := by
  intro i
  fin_cases i
  · simpa [Array.make] using hx
  · simpa [Array.make] using hx2
  · simpa [Array.make] using hx3

private theorem blockCoefficientsCanonical
    (polynomial : Polynomial) (canonical : CanonicalArray polynomial)
    (block : Nat) (hblock : block < 7) :
    CanonicalArray (Array.make 3#usize [
      coefficientAt polynomial ⟨4 * block + 1, by omega⟩,
      coefficientAt polynomial ⟨4 * block + 2, by omega⟩,
      coefficientAt polynomial ⟨4 * block + 3, by omega⟩]) := by
  intro i
  have h0 : 4 * block + 1 < 28 := by omega
  have h1 : 4 * block + 2 < 28 := by omega
  have h2 : 4 * block + 3 < 28 := by omega
  fin_cases i
  · simpa [Array.make] using canonicalAt polynomial canonical _ h0
  · simpa [Array.make] using canonicalAt polynomial canonical _ h1
  · simpa [Array.make] using canonicalAt polynomial canonical _ h2

private theorem generatedAddOfRun
    (x y out : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y)
    (run : ComponentBGenerated.aspis_core.field.QM31.add x y = .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generated_qm31_add_corresponds x y hx hy
  have : out = candidate := Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

private theorem generatedMulOfRun
    (x y out : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y)
    (run : ComponentBGenerated.aspis_core.field.QM31.mul x y = .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generated_qm31_mul_corresponds x y hx hy
  have : out = candidate := Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

/-- A universal algebraic identity, not a fixture: the seven radix-four
blocks in the generated order are exactly the ordinary degree-27 polynomial. -/
theorem exactRadixFour_eq_degree27
    (polynomial : Polynomial) (x : ExactQM31) :
    exactRadixFour polynomial x = exactDegree27Evaluation polynomial x := by
  simp [exactDegree27Evaluation, exactRadixFour, exactBlock, coefficientAt]
  ring

#print axioms exactRadixFour_eq_degree27

end ComponentBRealEvaluatorProof
