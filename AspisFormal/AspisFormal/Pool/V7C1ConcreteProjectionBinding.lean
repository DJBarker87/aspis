import AspisFormal.Pool.V7C1SubfieldRecovery
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V6EncoderDistance

/-!
# Concrete mathematical C1 projection binding

This module instantiates the algebraic part of the V7 C1 subfield-recovery
argument for the exact log-20 circle encoder.  The encoder here is a
mathematical evaluator on the deployed V6 circle coset:

`p₀(x) + y * p₁(x)`

where `p₀` and `p₁` are the existing degree-below-512 natural-basis
polynomials.  Projection onto the literal embedded M31 coordinate commutes
with this evaluator because every domain coordinate is in M31.  The existing
circle root-count theorem then gives the exact overlap cap 1024.

This file deliberately does not identify the mathematical evaluator with the
Rust FFT implementation.  The final packaging theorem exposes that equality
as an ordinary argument for the separate source bridge; it is not an axiom or
an encoder premise hidden in the mathematics below.
-/

set_option autoImplicit false

namespace AspisPool.V7C1ConcreteProjectionBinding

open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisCircleTensorBinding

/-! ## The base-coordinate projection is M31-linear -/

@[simp] theorem embedM31Exact_eq_algebraMap
    (value : ZMod AspisCircleGroupOrder.P) :
    embedM31Exact value =
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact value := by
  rfl

@[simp] theorem projectBase_add (left right : QM31Exact) :
    projectBase (left + right) = projectBase left + projectBase right := by
  ext <;> simp [projectBase, embedM31Exact]

@[simp] theorem projectBase_neg (value : QM31Exact) :
    projectBase (-value) = -projectBase value := by
  ext <;> simp [projectBase, embedM31Exact]

@[simp] theorem projectBase_mul_algebraMap
    (value : QM31Exact) (scalar : ZMod AspisCircleGroupOrder.P) :
    projectBase
        (value * algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact scalar) =
      projectBase value *
        algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact scalar := by
  rw [← embedM31Exact_eq_algebraMap]
  ext <;> simp [projectBase, embedM31Exact]

@[simp] theorem projectBase_algebraMap_mul
    (scalar : ZMod AspisCircleGroupOrder.P) (value : QM31Exact) :
    projectBase
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact scalar * value) =
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact scalar *
        projectBase value := by
  rw [mul_comm, projectBase_mul_algebraMap, mul_comm]

/-- Projection as an additive homomorphism, used to commute it through the
finite natural-basis evaluation sum without unfolding the field tower. -/
def projectBaseAddHom : QM31Exact →+ QM31Exact where
  toFun := projectBase
  map_zero' := projectBase_zero
  map_add' := projectBase_add

@[simp] theorem projectBaseAddHom_apply (value : QM31Exact) :
    projectBaseAddHom value = projectBase value := rfl

/-- The deployed extension field has odd characteristic.  Keeping this fact
local avoids importing an unrelated terminal-event module merely for its
instance. -/
private theorem qm31Exact_two_ne_zero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact (0 : M31Exact) := by
    calc
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
          (2 : QM31Exact) := map_ofNat _ 2
      _ = 0 := equalZero
      _ = algebraMap M31Exact QM31Exact (0 : M31Exact) := (map_zero _).symm
  have baseEqual :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31Exact_two_ne_zero⟩

/-! ## Natural-basis evaluation at embedded M31 points -/

private theorem doubledFactor_algebraMap
    (x : ZMod AspisCircleGroupOrder.P) : ∀ bit : Nat,
    doubledFactor
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) bit =
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (doubledFactor x bit)
  | 0 => rfl
  | bit + 1 => by
      rw [doubledFactor, doubledFactor, doubledFactor_algebraMap x bit]
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat]

private theorem naturalLineValue_algebraMap
    (x : ZMod AspisCircleGroupOrder.P) (index : Nat) :
    naturalLineValue
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) index =
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (naturalLineValue x index) := by
  simp only [naturalLineValue, map_prod]
  apply Finset.prod_congr rfl
  intro bit _
  exact doubledFactor_algebraMap x bit

/-- A natural-basis polynomial evaluated at an embedded M31 point commutes
with literal base-coordinate projection.  This is the reusable exact algebra
lemma needed by both halves of the circle polynomial. -/
theorem projectBase_naturalCoefficientPolynomial_eval
    {n : Nat} (hn : 0 < n) (coefficients : Fin n → QM31Exact)
    (x : ZMod AspisCircleGroupOrder.P) :
    projectBase
        ((naturalCoefficientPolynomial coefficients).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x)) =
      (naturalCoefficientPolynomial
          (fun index => projectBase (coefficients index))).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) := by
  rw [naturalCoefficientPolynomial_eval_eq_sum hn,
    naturalCoefficientPolynomial_eval_eq_sum hn]
  change projectBaseAddHom
      (∑ basis : Fin n,
        coefficients basis *
          naturalLineValue
            (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) basis) =
    ∑ basis : Fin n,
      projectBase (coefficients basis) *
        naturalLineValue
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) basis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro basis _
  rw [naturalLineValue_algebraMap, projectBaseAddHom_apply,
    projectBase_mul_algebraMap]

theorem projectBase_initialP0_eval
    (message : InitialMessage QM31Exact)
    (x : ZMod AspisCircleGroupOrder.P) :
    projectBase
        ((initialP0 message).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x)) =
      (initialP0 (projectMessage message)).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) := by
  unfold initialP0
  have coefficientEq :
      (fun index : Fin 512 =>
        projectBase (evenCoefficients (n := 512) message index)) =
        evenCoefficients (n := 512) (projectMessage message) := by
    funext index
    rfl
  have projected := projectBase_naturalCoefficientPolynomial_eval
    (n := 512) (by norm_num) (evenCoefficients (n := 512) message) x
  rw [coefficientEq] at projected
  exact projected

theorem projectBase_initialP1_eval
    (message : InitialMessage QM31Exact)
    (x : ZMod AspisCircleGroupOrder.P) :
    projectBase
        ((initialP1 message).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x)) =
      (initialP1 (projectMessage message)).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact x) := by
  unfold initialP1
  have coefficientEq :
      (fun index : Fin 512 =>
        projectBase (oddCoefficients (n := 512) message index)) =
        oddCoefficients (n := 512) (projectMessage message) := by
    funext index
    rfl
  have projected := projectBase_naturalCoefficientPolynomial_eval
    (n := 512) (by norm_num) (oddCoefficients (n := 512) message) x
  rw [coefficientEq] at projected
  exact projected

/-! ## Exact log-20 mathematical circle encoder -/

/-- The exact mathematical V6 initial encoder.  This is intentionally an
ordinary evaluator, not a claim about the production FFT implementation. -/
noncomputable def exactInitialEncoder :
    InitialMessage QM31Exact → InitialWord QM31Exact :=
  fun message index =>
    let point := AspisV6EncoderDistance.initialCirclePoint index
    let x := algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
      (AspisCircleGroupOrder.X point)
    let y := algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact point.1.2
    (initialP0 message).eval x + y * (initialP1 message).eval x

/-- Literal M31-coordinate projection commutes with the exact log-20 circle
encoder on every one of its 2^20 points. -/
theorem exactInitialEncoder_commutes (message : InitialMessage QM31Exact) :
    exactInitialEncoder (projectMessage message) =
      fun index => projectBase (exactInitialEncoder message index) := by
  funext index
  simp only [exactInitialEncoder]
  rw [projectBase_add, projectBase_algebraMap_mul,
    projectBase_initialP0_eval, projectBase_initialP1_eval]

theorem exactInitialP0_degree_lt (message : InitialMessage QM31Exact) :
    (initialP0 message).natDegree < 512 :=
  initialP0_degree_lt message

theorem exactInitialP1_degree_lt (message : InitialMessage QM31Exact) :
    (initialP1 message).natDegree < 512 :=
  initialP1_degree_lt message

theorem exactInitialPolynomialPair_injective :
    Function.Injective (fun message : InitialMessage QM31Exact =>
      (initialP0 message, initialP1 message)) :=
  initialPolynomialPair_injective

/-- The existing exact circle root-count theorem applied to the concrete
mathematical evaluator. -/
theorem exactInitialEncoder_overlap_cap
    (left right : InitialMessage QM31Exact) (different : left ≠ right) :
    agreementCount (exactInitialEncoder left)
      (exactInitialEncoder right) ≤ 1024 := by
  have cap := AspisV6EncoderDistance.exactInitialCoset_agreement_card_le_1024
    (K := QM31Exact) (Message := InitialMessage QM31Exact)
    exactInitialEncoder initialP0 initialP1
    exactInitialP0_degree_lt exactInitialP1_degree_lt
    exactInitialPolynomialPair_injective
    (by intro message index; rfl) left right different
  calc
    agreementCount (exactInitialEncoder left) (exactInitialEncoder right) =
        (AspisV5FriCoherentCandidateExtraction.agreementSet
          (exactInitialEncoder left) (exactInitialEncoder right)).card := by
      unfold agreementCount
        AspisV5FriCoherentCandidateExtraction.agreementSet
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro index _
      rfl
    _ ≤ 1024 := cap

/-! ## Decoder packaging with an explicit future source bridge -/

/-- Package the unconditional mathematical results for any decoder whose
initial encoder has separately been identified with `exactInitialEncoder`.
The equality argument is the complete remaining encoder/source bridge. -/
theorem initialProjectionBinding_of_initialEncoder_eq
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder) :
    InitialProjectionBinding decoder := by
  constructor
  · intro message
    rw [initialEncoderEq]
    exact exactInitialEncoder_commutes message
  · intro left right different
    rw [initialEncoderEq]
    exact exactInitialEncoder_overlap_cap left right different

#print axioms projectBase_naturalCoefficientPolynomial_eval
#print axioms exactInitialEncoder_commutes
#print axioms exactInitialEncoder_overlap_cap
#print axioms initialProjectionBinding_of_initialEncoder_eq

end AspisPool.V7C1ConcreteProjectionBinding
