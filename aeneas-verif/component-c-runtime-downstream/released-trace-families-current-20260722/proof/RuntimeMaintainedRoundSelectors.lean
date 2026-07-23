import AspisFormal.V5ComponentCDownstreamDeployed

set_option autoImplicit false

namespace AspisV5ComponentCDownstreamDeployed

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity

variable {K : Type*} [Field K]

/-- Stable proof-facing names for the two maintained arithmetic evaluators.
They keep concrete QM31 proof terms small while remaining definitionally the
same generic maps used by the deployed evaluator. -/
def maintainedSourceDot {n : Nat} (weights coefficients : Fin n → K) : K :=
  dotLinear weights coefficients

def maintainedSourcePolynomial (n : Nat) (weights coefficients : Fin (4 * n) → K)
    (degree : Fin 7) : K :=
  polynomialForExtension n weights coefficients degree

theorem maintainedSourceDot_eq {n : Nat} (weights coefficients : Fin n → K) :
    maintainedSourceDot weights coefficients = dotLinear weights coefficients :=
  rfl

theorem maintainedSourcePolynomial_eq (n : Nat)
    (weights coefficients : Fin (4 * n) → K) (degree : Fin 7) :
    maintainedSourcePolynomial n weights coefficients degree =
      polynomialForExtension n weights coefficients degree := rfl

theorem roundOodRows_zero_map (rt : FixedRelationSchedule K) :
    roundOodRows rt 0 = ood0Rows rt := by
  rfl

theorem ood0Rows_body_map (rt : FixedRelationSchedule K) :
    ood0Rows rt = LinearMap.pi (fun sample => dotLinear (rt.ood0 sample)) := by
  rfl

theorem roundOodRows_zero_scalar (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (sample : Fin 2) :
    roundOodRows rt 0 c sample = dotLinear (rt.ood0 sample) c := by
  calc
    roundOodRows rt 0 c sample = ood0Rows rt c sample :=
      congrArg (fun m => m c sample) (roundOodRows_zero_map rt)
    _ = (LinearMap.pi (fun s => dotLinear (rt.ood0 s)) c) sample :=
      congrArg (fun m => m c sample) (ood0Rows_body_map rt)
    _ = dotLinear (rt.ood0 sample) c :=
      LinearMap.pi_apply (fun s => dotLinear (rt.ood0 s)) c sample

theorem pi_dotLinear_apply {n : Nat} (weights : Fin 2 → Fin n → K)
    (c : Fin n → K) (sample : Fin 2) :
    (LinearMap.pi fun sample => dotLinear (weights sample)) c sample =
      dotLinear (weights sample) c :=
  LinearMap.pi_apply (fun sample => dotLinear (weights sample)) c sample

theorem dotLinear_transport {n : Nat} {weights weights' : Fin n → K}
    (h : weights = weights') (c : Fin n → K) :
    dotLinear weights c = dotLinear weights' c :=
  congrArg (fun w => dotLinear w c) h

theorem dotLinear_transport_1024 {weights weights' : Fin 1024 → K}
    (h : weights = weights') (c : Fin 1024 → K) :
    dotLinear weights c = dotLinear weights' c :=
  dotLinear_transport h c

theorem dotLinear_transport_256 {weights weights' : Fin 256 → K}
    (h : weights = weights') (c : Fin 256 → K) :
    dotLinear weights c = dotLinear weights' c :=
  dotLinear_transport h c

theorem dotLinear_transport_64 {weights weights' : Fin 64 → K}
    (h : weights = weights') (c : Fin 64 → K) :
    dotLinear weights c = dotLinear weights' c :=
  dotLinear_transport h c

theorem dotLinear_result_transport {n : Nat} {x : K}
    {sourceWeights targetWeights : Fin n → K} (c : Fin n → K)
    (hx : x = dotLinear sourceWeights c)
    (h : targetWeights = sourceWeights) :
    x = dotLinear targetWeights c :=
  hx.trans (dotLinear_transport h.symm c)

theorem dotLinear_result_transport_1024 {x : K}
    {sourceWeights targetWeights : Fin 1024 → K} (c : Fin 1024 → K)
    (hx : x = dotLinear sourceWeights c)
    (h : targetWeights = sourceWeights) :
    x = dotLinear targetWeights c :=
  dotLinear_result_transport c hx h

theorem dotLinear_result_transport_256 {x : K}
    {sourceWeights targetWeights : Fin 256 → K} (c : Fin 256 → K)
    (hx : x = dotLinear sourceWeights c)
    (h : targetWeights = sourceWeights) :
    x = dotLinear targetWeights c :=
  dotLinear_result_transport c hx h

theorem dotLinear_result_transport_64 {x : K}
    {sourceWeights targetWeights : Fin 64 → K} (c : Fin 64 → K)
    (hx : x = dotLinear sourceWeights c)
    (h : targetWeights = sourceWeights) :
    x = dotLinear targetWeights c :=
  dotLinear_result_transport c hx h

theorem roundOodRows_one (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (sample : Fin 2) :
    roundOodRows rt 1 c sample =
      dotLinear (rt.ood1 sample) (round1Coefficients rt c) := by
  rfl

theorem roundOodRows_two (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (sample : Fin 2) :
    roundOodRows rt 2 c sample =
      dotLinear (rt.ood2 sample) (round2Coefficients rt c) := by
  rfl

theorem roundOodRows_three (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (sample : Fin 2) :
    roundOodRows rt 3 c sample =
      dotLinear (rt.ood3 sample) (round3Coefficients rt c) := by
  rfl

theorem roundPolynomialRows_zero (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (degree : Fin 7) :
    roundPolynomialRows rt 0 c degree =
      polynomialForExtension 256 rt.poly0 c degree := by
  rfl

theorem roundPolynomialRows_one_map (rt : FixedRelationSchedule K) :
    roundPolynomialRows rt 1 = polynomial1Rows rt := by
  rfl

theorem polynomial1Rows_body_map (rt : FixedRelationSchedule K) :
    polynomial1Rows rt =
      polynomialForExtension 64 rt.poly1 ∘ₗ round1Coefficients rt := by
  rfl

theorem roundPolynomialRows_one_scalar (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (degree : Fin 7) :
    roundPolynomialRows rt 1 c degree =
      polynomialForExtension 64 rt.poly1 (round1Coefficients rt c) degree := by
  let f : (Fin 256 → K) →ₗ[K] (Fin 7 → K) :=
    polynomialForExtension 64 rt.poly1
  have hf : f = polynomialForExtension 64 rt.poly1 := by rfl
  have hs : roundPolynomialRows rt 1 c = polynomial1Rows rt c :=
    congrArg (fun m => m c) (roundPolynomialRows_one_map rt)
  have hbody : polynomial1Rows rt = f ∘ₗ round1Coefficients rt := by
    rw [hf]
    exact polynomial1Rows_body_map rt
  have hb : polynomial1Rows rt c = (f ∘ₗ round1Coefficients rt) c :=
    congrArg (fun m => m c) hbody
  have hc : (f ∘ₗ round1Coefficients rt) c =
      f (round1Coefficients rt c) :=
    LinearMap.comp_apply f (round1Coefficients rt) c
  have hfa : f (round1Coefficients rt c) =
      polynomialForExtension 64 rt.poly1 (round1Coefficients rt c) :=
    congrArg (fun m => m (round1Coefficients rt c)) hf
  exact congrFun (hs.trans (hb.trans (hc.trans hfa))) degree

theorem roundPolynomialRows_two (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (degree : Fin 7) :
    roundPolynomialRows rt 2 c degree =
      polynomialForExtension 16 rt.poly2 (round2Coefficients rt c) degree := by
  rfl

theorem roundPolynomialRows_three (rt : FixedRelationSchedule K)
    (c : AspisV5ComponentCRelationRowLinearity.Coefficients K) (degree : Fin 7) :
    roundPolynomialRows rt 3 c degree =
      polynomialForExtension 4 rt.poly3 (round3Coefficients rt c) degree := by
  rfl

#print axioms roundOodRows_zero_map
#print axioms ood0Rows_body_map
#print axioms roundOodRows_zero_scalar
#print axioms pi_dotLinear_apply
#print axioms dotLinear_transport
#print axioms dotLinear_transport_1024
#print axioms dotLinear_transport_256
#print axioms dotLinear_transport_64
#print axioms dotLinear_result_transport
#print axioms dotLinear_result_transport_1024
#print axioms dotLinear_result_transport_256
#print axioms dotLinear_result_transport_64
#print axioms roundOodRows_one
#print axioms roundOodRows_two
#print axioms roundOodRows_three
#print axioms roundPolynomialRows_zero
#print axioms roundPolynomialRows_one_map
#print axioms polynomial1Rows_body_map
#print axioms roundPolynomialRows_one_scalar
#print axioms roundPolynomialRows_two
#print axioms roundPolynomialRows_three

end AspisV5ComponentCDownstreamDeployed
