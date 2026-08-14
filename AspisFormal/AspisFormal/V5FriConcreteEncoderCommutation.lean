import AspisFormal.V5FriCoherentCandidateExtraction

/-!
# Explicit V5 FRI encoders and fold commutation

`V5FriCoherentCandidateExtraction` deliberately treats its four code encoders
as functions.  This file replaces that freedom with one explicit recursive
evaluation construction.  It starts from the final line tensor

`[1, x, 2*x^2-1, x*(2*x^2-1)]`

and expands one radix-four evaluation fibre at a time.  The first expansion
uses the circle basis `[1,y,x,xy]`; the remaining expansions use the same
line-basis recurrence with their three public coordinates.  The resulting
maps have exactly the V5 dimensions

`1024 -> 524288`, `256 -> 131072`, `64 -> 32768`, and `16 -> 8192`.

For this construction Lean proves:

* the local four-point evaluator is linear and injective;
* the normalized deployed fold of an evaluated fibre is exactly the natural
  coefficient fold with weights `[1, alpha, alpha^2, alpha^3]`;
* all four fixed-size encoder/fold squares commute; and
* if four final x-coordinates are distinct, all five recursive encoders are
  injective.

The inverse-table equations are explicit hypotheses:
`2*x*inverse = 1` at every deployed fibre.  They are ordinary finite-field
identities, not FRI soundness assumptions.

This file does **not** identify the recursive evaluator with the Rust FFT
encoder.  That remaining statement is isolated at the end as equality of two
concrete linear maps.  Nor does injectivity prove the relative-distance and
list-decoding bounds needed by S-two; those require the circle-code theorem.
-/

namespace AspisV5FriConcreteEncoderCommutation

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-! ## One explicit radix-four evaluation fibre -/

/-- Evaluation of four natural coefficients on one radix-four fibre.

The slots are

* `[1, x0,  x2,  x0*x2]`,
* `[1,-x0,  x2, -x0*x2]`,
* `[1, x1, -x2, -x1*x2]`, and
* `[1,-x1, -x2,  x1*x2]`.

For a line fibre, `x0`, `x1`, and `x2` are the two inner coordinates and the
outer coordinate.  For the first circle fibre they are `y`, `-y`, and `x`,
which gives the deployed point order
`(x,y),(x,-y),(-x,-y),(-x,y)`. -/
def radix4Evaluate (x0 x1 x2 : K) (c : Fin 4 → K) : Fin 4 → K :=
  ![c 0 + x0 * c 1 + x2 * c 2 + x0 * x2 * c 3,
    c 0 - x0 * c 1 + x2 * c 2 - x0 * x2 * c 3,
    c 0 + x1 * c 1 - x2 * c 2 - x1 * x2 * c 3,
    c 0 - x1 * c 1 - x2 * c 2 + x1 * x2 * c 3]

/-- The explicit local evaluator as a linear map in its four coefficients. -/
def radix4EvaluationLinear (x0 x1 x2 : K) :
    (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun := radix4Evaluate x0 x1 x2
  map_add' c d := by
    funext s
    fin_cases s <;> simp [radix4Evaluate] <;> ring
  map_smul' a c := by
    funext s
    fin_cases s <;> simp [radix4Evaluate, smul_eq_mul] <;> ring

@[simp] theorem radix4EvaluationLinear_apply (x0 x1 x2 : K) (c : Fin 4 → K) :
    radix4EvaluationLinear x0 x1 x2 c = radix4Evaluate x0 x1 x2 c :=
  rfl

/-- One normalized binary fold exactly evaluates the two natural
coefficients at the challenge. -/
theorem pairFoldValue_evaluate_pair (alpha x inverse even odd : K)
    (hinverse : 2 * x * inverse = 1) :
    pairFoldValue alpha inverse (even + x * odd) (even - x * odd) =
      even + alpha * odd := by
  have htwo : (2 : K) ≠ 0 := by
    intro hz
    rw [hz, zero_mul, zero_mul] at hinverse
    exact zero_ne_one hinverse
  calc
    pairFoldValue alpha inverse (even + x * odd) (even - x * odd) =
        even + alpha * (2 * x * inverse) * odd := by
      simp only [pairFoldValue]
      field_simp [htwo]
      ring
    _ = even + alpha * odd := by rw [hinverse]; ring

/-- Exact local line-fold/encoding commutation.  No code proximity or FRI
theorem is used: this is the four-symbol field identity. -/
theorem lineFoldValue_radix4Evaluate
    (alpha x0 x1 x2 inverse0 inverse1 inverse2 : K)
    (h0 : 2 * x0 * inverse0 = 1)
    (h1 : 2 * x1 * inverse1 = 1)
    (h2 : 2 * x2 * inverse2 = 1) (c : Fin 4 → K) :
    lineFoldValue alpha inverse0 inverse1 inverse2
        (radix4Evaluate x0 x1 x2 c) =
      coefficientFoldValue alpha c := by
  rw [lineFoldValue]
  change pairFoldValue (alpha ^ 2) inverse2
    (pairFoldValue alpha inverse0
      (c 0 + x0 * c 1 + x2 * c 2 + x0 * x2 * c 3)
      (c 0 - x0 * c 1 + x2 * c 2 - x0 * x2 * c 3))
    (pairFoldValue alpha inverse1
      (c 0 + x1 * c 1 - x2 * c 2 - x1 * x2 * c 3)
      (c 0 - x1 * c 1 - x2 * c 2 + x1 * x2 * c 3)) = _
  have hp0 := pairFoldValue_evaluate_pair alpha x0 inverse0
    (c 0 + x2 * c 2) (c 1 + x2 * c 3) h0
  have hp1 := pairFoldValue_evaluate_pair alpha x1 inverse1
    (c 0 - x2 * c 2) (c 1 - x2 * c 3) h1
  rw [show c 0 + x0 * c 1 + x2 * c 2 + x0 * x2 * c 3 =
        (c 0 + x2 * c 2) + x0 * (c 1 + x2 * c 3) by ring,
      show c 0 - x0 * c 1 + x2 * c 2 - x0 * x2 * c 3 =
        (c 0 + x2 * c 2) - x0 * (c 1 + x2 * c 3) by ring,
      hp0,
      show c 0 + x1 * c 1 - x2 * c 2 - x1 * x2 * c 3 =
        (c 0 - x2 * c 2) + x1 * (c 1 - x2 * c 3) by ring,
      show c 0 - x1 * c 1 - x2 * c 2 + x1 * x2 * c 3 =
        (c 0 - x2 * c 2) - x1 * (c 1 - x2 * c 3) by ring,
      hp1]
  rw [show c 0 + x2 * c 2 + alpha * (c 1 + x2 * c 3) =
        (c 0 + alpha * c 1) + x2 * (c 2 + alpha * c 3) by ring,
      show c 0 - x2 * c 2 + alpha * (c 1 - x2 * c 3) =
        (c 0 + alpha * c 1) - x2 * (c 2 + alpha * c 3) by ring,
      pairFoldValue_evaluate_pair (alpha ^ 2) x2 inverse2
        (c 0 + alpha * c 1) (c 2 + alpha * c 3) h2]
  simp only [coefficientFoldValue]
  ring

/-- The first circle fold is the same identity with the concrete circle
coordinates `(x0,x1,x2) = (y,-y,x)`. -/
theorem circleFoldValue_radix4Evaluate
    (alpha x y inverse2x inverse2y : K)
    (hx : 2 * x * inverse2x = 1)
    (hy : 2 * y * inverse2y = 1) (c : Fin 4 → K) :
    circleFoldValue alpha inverse2x inverse2y
        (radix4Evaluate y (-y) x c) =
      coefficientFoldValue alpha c := by
  apply lineFoldValue_radix4Evaluate alpha y (-y) x
    inverse2y (-inverse2y) inverse2x
  · exact hy
  · simpa only [neg_mul, mul_neg, neg_neg] using hy
  · exact hx

/-! ## A local decoder and injectivity -/

/-- Inverse interpolation of the local four-point evaluation matrix. -/
def radix4Decode (inverse0 inverse1 inverse2 : K) (v : Fin 4 → K) : Fin 4 → K :=
  let even0 := (v 0 + v 1) / 2
  let even1 := (v 2 + v 3) / 2
  let odd0 := (v 0 - v 1) * inverse0
  let odd1 := (v 2 - v 3) * inverse1
  ![(even0 + even1) / 2,
    (odd0 + odd1) / 2,
    (even0 - even1) * inverse2,
    (odd0 - odd1) * inverse2]

/-- The decoder is a left inverse whenever the three supplied entries really
are the inverses of twice the corresponding coordinates. -/
theorem radix4Decode_radix4Evaluate
    (x0 x1 x2 inverse0 inverse1 inverse2 : K)
    (h0 : 2 * x0 * inverse0 = 1)
    (h1 : 2 * x1 * inverse1 = 1)
    (h2 : 2 * x2 * inverse2 = 1) (c : Fin 4 → K) :
    radix4Decode inverse0 inverse1 inverse2
        (radix4Evaluate x0 x1 x2 c) = c := by
  have hx0 : x0 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h0; exact zero_ne_one h0
  have hx1 : x1 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h1; exact zero_ne_one h1
  have hx2 : x2 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h2; exact zero_ne_one h2
  have hi0 : inverse0 = (2 * x0)⁻¹ := eq_inv_of_mul_eq_one_right h0
  have hi1 : inverse1 = (2 * x1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hi2 : inverse2 = (2 * x2)⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [hi0, hi1, hi2]
  funext t
  fin_cases t <;> simp [radix4Decode, radix4Evaluate]
  all_goals
    have htwo : (2 : K) ≠ 0 := by
      intro hz
      rw [hz, zero_mul, zero_mul] at h0
      exact zero_ne_one h0
    field_simp [htwo]
  all_goals ring

/-- The other direction: every arbitrary four-symbol word is the evaluation
of the four coefficients returned by `radix4Decode`.  Thus the local
degree-three decomposition is an equality, not a codeword-membership premise. -/
theorem radix4Evaluate_radix4Decode
    (x0 x1 x2 inverse0 inverse1 inverse2 : K)
    (h0 : 2 * x0 * inverse0 = 1)
    (h1 : 2 * x1 * inverse1 = 1)
    (h2 : 2 * x2 * inverse2 = 1) (v : Fin 4 → K) :
    radix4Evaluate x0 x1 x2
        (radix4Decode inverse0 inverse1 inverse2 v) = v := by
  have hx0 : x0 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h0; exact zero_ne_one h0
  have hx1 : x1 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h1; exact zero_ne_one h1
  have hx2 : x2 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_mul] at h2; exact zero_ne_one h2
  have hi0 : inverse0 = (2 * x0)⁻¹ := eq_inv_of_mul_eq_one_right h0
  have hi1 : inverse1 = (2 * x1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hi2 : inverse2 = (2 * x2)⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [hi0, hi1, hi2]
  funext t
  fin_cases t <;> simp [radix4Decode, radix4Evaluate]
  all_goals
    have htwo : (2 : K) ≠ 0 := by
      intro hz
      rw [hz, zero_mul, zero_mul] at h0
      exact zero_ne_one h0
    field_simp [htwo]
  all_goals ring

/-- Exact arbitrary-word line decomposition.  The normalized fold of any
four symbols is evaluation at `alpha` of their decoded degree-three
coefficient vector. -/
theorem lineFoldValue_eq_coefficientFoldValue_decode
    (alpha x0 x1 x2 inverse0 inverse1 inverse2 : K)
    (h0 : 2 * x0 * inverse0 = 1)
    (h1 : 2 * x1 * inverse1 = 1)
    (h2 : 2 * x2 * inverse2 = 1) (v : Fin 4 → K) :
    lineFoldValue alpha inverse0 inverse1 inverse2 v =
      coefficientFoldValue alpha
        (radix4Decode inverse0 inverse1 inverse2 v) := by
  calc
    lineFoldValue alpha inverse0 inverse1 inverse2 v =
        lineFoldValue alpha inverse0 inverse1 inverse2
          (radix4Evaluate x0 x1 x2
            (radix4Decode inverse0 inverse1 inverse2 v)) := by
      rw [radix4Evaluate_radix4Decode x0 x1 x2 inverse0 inverse1 inverse2
        h0 h1 h2 v]
    _ = coefficientFoldValue alpha
          (radix4Decode inverse0 inverse1 inverse2 v) :=
      lineFoldValue_radix4Evaluate alpha x0 x1 x2
        inverse0 inverse1 inverse2 h0 h1 h2 _

/-- Circle form of the arbitrary-word decomposition. -/
theorem circleFoldValue_eq_coefficientFoldValue_decode
    (alpha x y inverse2x inverse2y : K)
    (hx : 2 * x * inverse2x = 1)
    (hy : 2 * y * inverse2y = 1) (v : Fin 4 → K) :
    circleFoldValue alpha inverse2x inverse2y v =
      coefficientFoldValue alpha
        (radix4Decode inverse2y (-inverse2y) inverse2x v) := by
  apply lineFoldValue_eq_coefficientFoldValue_decode alpha y (-y) x
    inverse2y (-inverse2y) inverse2x
  · exact hy
  · simpa only [neg_mul, mul_neg, neg_neg] using hy
  · exact hx

/-- The explicit local evaluation matrix is injective under the same three
checkable inverse identities. -/
theorem radix4Evaluate_injective
    (x0 x1 x2 inverse0 inverse1 inverse2 : K)
    (h0 : 2 * x0 * inverse0 = 1)
    (h1 : 2 * x1 * inverse1 = 1)
    (h2 : 2 * x2 * inverse2 = 1) :
    Function.Injective (radix4Evaluate x0 x1 x2) := by
  intro c d h
  rw [← radix4Decode_radix4Evaluate x0 x1 x2 inverse0 inverse1 inverse2
        h0 h1 h2 c,
      ← radix4Decode_radix4Evaluate x0 x1 x2 inverse0 inverse1 inverse2
        h0 h1 h2 d, h]

/-! ## Recursive explicit encoders -/

/-- Parent fibre of one flat fibre-major index. -/
def parentIndex {n : Nat} (k : Fin (4 * n)) : Fin n :=
  ⟨k.val / 4, by omega⟩

/-- Slot within one flat fibre-major index. -/
def slotIndex {n : Nat} (k : Fin (4 * n)) : Fin 4 :=
  ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩

@[simp] theorem parentIndex_childIndex {n : Nat} (i : Fin n) (s : Fin 4) :
    parentIndex (childIndex i s) = i := by
  apply Fin.ext
  simp only [parentIndex, childIndex_val]
  omega

@[simp] theorem slotIndex_childIndex {n : Nat} (i : Fin n) (s : Fin 4) :
    slotIndex (childIndex i s) = s := by
  apply Fin.ext
  simp only [slotIndex, childIndex_val]
  omega

@[simp] theorem childIndex_parentIndex_slotIndex {n : Nat} (k : Fin (4 * n)) :
    childIndex (parentIndex k) (slotIndex k) = k := by
  apply Fin.ext
  simp only [childIndex_val, parentIndex, slotIndex]
  omega

/-- Select one of the four consecutive natural coefficient lanes. -/
def coefficientLane (n : Nat) (slot : Fin 4) :
    (Fin (4 * n) → K) →ₗ[K] (Fin n → K) :=
  LinearMap.funLeft K K fun i => childIndex i slot

@[simp] theorem coefficientLane_apply (n : Nat) (slot : Fin 4)
    (c : Fin (4 * n) → K) (i : Fin n) :
    coefficientLane (K := K) n slot c i = c (childIndex i slot) :=
  rfl

/-- At one parent-domain position, encode the four coefficient lanes with the
same smaller encoder. -/
def encodedLanesAt {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (i : Fin m) :
    (Fin (4 * n) → K) →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi fun slot =>
    LinearMap.proj i ∘ₗ encoder ∘ₗ coefficientLane n slot

@[simp] theorem encodedLanesAt_apply {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (i : Fin m)
    (c : Fin (4 * n) → K) (slot : Fin 4) :
    encodedLanesAt encoder i c slot =
      encoder (coefficientLane n slot c) i :=
  rfl

/-- Expand a smaller explicit encoder by one line-style radix-four evaluation
layer.  This is a concrete linear map, not an arbitrary `CodeEncoder`. -/
def radix4LiftEncoder {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x0 x1 x2 : Fin m → K) :
    (Fin (4 * n) → K) →ₗ[K] (Fin (4 * m) → K) :=
  LinearMap.pi fun k =>
    LinearMap.proj (slotIndex k) ∘ₗ
      radix4EvaluationLinear (x0 (parentIndex k))
        (x1 (parentIndex k)) (x2 (parentIndex k)) ∘ₗ
      encodedLanesAt encoder (parentIndex k)

@[simp] theorem radix4LiftEncoder_apply_child {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x0 x1 x2 : Fin m → K) (c : Fin (4 * n) → K)
    (i : Fin m) (slot : Fin 4) :
    radix4LiftEncoder encoder x0 x1 x2 c (childIndex i slot) =
      radix4Evaluate (x0 i) (x1 i) (x2 i)
        (fun lane => encoder (coefficientLane n lane c) i) slot := by
  simp [radix4LiftEncoder, encodedLanesAt]
  congr 1

/-- Circle-specific first expansion. -/
def circleLiftEncoder {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x y : Fin m → K) :
    (Fin (4 * n) → K) →ₗ[K] (Fin (4 * m) → K) :=
  radix4LiftEncoder encoder y (-y) x

/-! ### Coefficient lanes and encoder linearity -/

theorem coefficientFoldLayer_eq_lane_combination (n : Nat) (alpha : K)
    (c : Fin (4 * n) → K) :
    coefficientFoldLayer n alpha c =
      coefficientLane n 0 c + alpha • coefficientLane n 1 c +
        alpha ^ 2 • coefficientLane n 2 c +
          alpha ^ 3 • coefficientLane n 3 c := by
  funext i
  simp only [coefficientFoldLayer_apply, coefficientFoldValue,
    Pi.add_apply, Pi.smul_apply, coefficientLane_apply, smul_eq_mul]

theorem encoder_coefficientFoldLayer_apply {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (alpha : K) (c : Fin (4 * n) → K) (i : Fin m) :
    encoder (coefficientFoldLayer n alpha c) i =
      coefficientFoldValue alpha
        (fun lane => encoder (coefficientLane n lane c) i) := by
  rw [coefficientFoldLayer_eq_lane_combination]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    coefficientFoldValue, smul_eq_mul]

/-! ### Generic commuting squares -/

/-- One line expansion commutes exactly with one deployed line fold. -/
theorem lineFoldLayer_radix4LiftEncoder {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (alpha : K) (x0 x1 x2 : Fin m → K)
    (inverse : Fin m → Fin 3 → F)
    (h0 : ∀ i, 2 * x0 i * algebraMap F K (inverse i 0) = 1)
    (h1 : ∀ i, 2 * x1 i * algebraMap F K (inverse i 1) = 1)
    (h2 : ∀ i, 2 * x2 i * algebraMap F K (inverse i 2) = 1) :
    lineFoldLayer m alpha inverse ∘ₗ
        radix4LiftEncoder encoder x0 x1 x2 =
      encoder ∘ₗ coefficientFoldLayer n alpha := by
  apply LinearMap.ext
  intro c
  funext i
  simp only [LinearMap.comp_apply, lineFoldLayer_apply]
  rw [show (fun slot =>
        radix4LiftEncoder encoder x0 x1 x2 c (childIndex i slot)) =
      radix4Evaluate (x0 i) (x1 i) (x2 i)
        (fun lane => encoder (coefficientLane n lane c) i) by
      funext slot
      exact radix4LiftEncoder_apply_child encoder x0 x1 x2 c i slot]
  rw [lineFoldValue_radix4Evaluate alpha (x0 i) (x1 i) (x2 i)
    (algebraMap F K (inverse i 0)) (algebraMap F K (inverse i 1))
    (algebraMap F K (inverse i 2)) (h0 i) (h1 i) (h2 i)]
  exact (encoder_coefficientFoldLayer_apply encoder alpha c i).symm

/-- The circle expansion commutes exactly with the deployed first fold. -/
theorem circleFoldLayer_circleLiftEncoder {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (alpha : K) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2 * x i * algebraMap F K (inverse2x i) = 1)
    (hy : ∀ i, 2 * y i * algebraMap F K (inverse2y i) = 1) :
    circleFoldLayer m alpha inverse2x inverse2y ∘ₗ
        circleLiftEncoder encoder x y =
      encoder ∘ₗ coefficientFoldLayer n alpha := by
  apply LinearMap.ext
  intro c
  funext i
  simp only [LinearMap.comp_apply, circleFoldLayer_apply]
  rw [show (fun slot =>
        circleLiftEncoder encoder x y c (childIndex i slot)) =
      radix4Evaluate (y i) (-y i) (x i)
        (fun lane => encoder (coefficientLane n lane c) i) by
      funext slot
      exact radix4LiftEncoder_apply_child encoder y (-y) x c i slot]
  rw [circleFoldValue_radix4Evaluate alpha (x i) (y i)
    (algebraMap F K (inverse2x i)) (algebraMap F K (inverse2y i))
    (hx i) (hy i)]
  exact (encoder_coefficientFoldLayer_apply encoder alpha c i).symm

/-! ### Recursive injectivity -/

/-- A radix-four expansion preserves injectivity of its smaller encoder. -/
theorem radix4LiftEncoder_injective {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (hencoder : Function.Injective encoder)
    (x0 x1 x2 : Fin m → K) (inverse0 inverse1 inverse2 : Fin m → K)
    (h0 : ∀ i, 2 * x0 i * inverse0 i = 1)
    (h1 : ∀ i, 2 * x1 i * inverse1 i = 1)
    (h2 : ∀ i, 2 * x2 i * inverse2 i = 1) :
    Function.Injective (radix4LiftEncoder encoder x0 x1 x2) := by
  intro c d hcd
  have hlane : ∀ lane, coefficientLane n lane c = coefficientLane n lane d := by
    intro lane
    apply hencoder
    funext i
    have hfibre :
        radix4Evaluate (x0 i) (x1 i) (x2 i)
            (fun t => encoder (coefficientLane n t c) i) =
          radix4Evaluate (x0 i) (x1 i) (x2 i)
            (fun t => encoder (coefficientLane n t d) i) := by
      funext slot
      simpa only [← radix4LiftEncoder_apply_child] using
        congrFun hcd (childIndex i slot)
    exact congrFun
      (radix4Evaluate_injective (x0 i) (x1 i) (x2 i)
        (inverse0 i) (inverse1 i) (inverse2 i) (h0 i) (h1 i) (h2 i) hfibre)
      lane
  funext k
  have := congrFun (hlane (slotIndex k)) (parentIndex k)
  simpa only [coefficientLane_apply, childIndex_parentIndex_slotIndex] using this

/-! ## The four fixed V5 encoders -/

/-- Coordinates used by the explicit recursive evaluator.  They are base-field
coordinates; embedding into the V5 extension is done by `algebraMap F K`. -/
structure EvaluationPoints (F : Type*) where
  circleX : Fin layer1Symbols → F
  circleY : Fin layer1Symbols → F
  line1 : Fin layer2Symbols → Fin 3 → F
  line2 : Fin layer3Symbols → Fin 3 → F
  line3 : Fin layer4Symbols → Fin 3 → F

/-- The exact finite-field identities required of the point and inverse
tables.  These are the checks that connect the explicit evaluation recurrence
to the denominators consumed by the verifier. -/
structure InverseTablesMatch
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) : Prop where
  circleX : ∀ i,
    2 * points.circleX i * schedule.circleInv2x i = 1
  circleY : ∀ i,
    2 * points.circleY i * schedule.circleInv2y i = 1
  line1 : ∀ i s,
    2 * points.line1 i s * schedule.line1Inverse i s = 1
  line2 : ∀ i s,
    2 * points.line2 i s * schedule.line2Inverse i s = 1
  line3 : ∀ i s,
    2 * points.line3 i s * schedule.line3Inverse i s = 1

/-- Embed one base-field coordinate table in the extension. -/
def extend1 {n : Nat} (x : Fin n → F) : Fin n → K :=
  fun i => algebraMap F K (x i)

/-- Embed one three-coordinate table in the extension. -/
def extend3 {n : Nat} (x : Fin n → Fin 3 → F) :
    Fin n → Fin 3 → K :=
  fun i s => algebraMap F K (x i s)

/-- The explicit final `4 -> 2048` line-tensor encoder. -/
def encoder4 (schedule : FixedSchedule F K) :
    Coeff4 K →ₗ[K] (Fin 2048 → K) :=
  LinearMap.pi fun i =>
    finalTensorLinear (algebraMap F K (schedule.finalX i))

@[simp] theorem encoder4_apply (schedule : FixedSchedule F K)
    (c : Coeff4 K) (i : Fin 2048) :
    encoder4 schedule c i =
      finalTensorValue (algebraMap F K (schedule.finalX i)) c :=
  rfl

/-- Explicit layer-three line encoder, `16 -> 8192`. -/
def encoder3 (schedule : FixedSchedule F K) (points : EvaluationPoints F) :
    Coeff3 K →ₗ[K] Word3 K :=
  radix4LiftEncoder (encoder4 schedule)
    (fun i => algebraMap F K (points.line3 i 0))
    (fun i => algebraMap F K (points.line3 i 1))
    (fun i => algebraMap F K (points.line3 i 2))

/-- Explicit layer-two line encoder, `64 -> 32768`. -/
def encoder2 (schedule : FixedSchedule F K) (points : EvaluationPoints F) :
    Coeff2 K →ₗ[K] Word2 K :=
  radix4LiftEncoder (encoder3 schedule points)
    (fun i => algebraMap F K (points.line2 i 0))
    (fun i => algebraMap F K (points.line2 i 1))
    (fun i => algebraMap F K (points.line2 i 2))

/-- Explicit layer-one line encoder, `256 -> 131072`. -/
def encoder1 (schedule : FixedSchedule F K) (points : EvaluationPoints F) :
    Coeff1 K →ₗ[K] Word1 K :=
  radix4LiftEncoder (encoder2 schedule points)
    (fun i => algebraMap F K (points.line1 i 0))
    (fun i => algebraMap F K (points.line1 i 1))
    (fun i => algebraMap F K (points.line1 i 2))

/-- Explicit initial circle encoder, `1024 -> 524288`. -/
def encoder0 (schedule : FixedSchedule F K) (points : EvaluationPoints F) :
    Coeff0 K →ₗ[K] Word0 K :=
  circleLiftEncoder (encoder1 schedule points)
    (extend1 points.circleX) (extend1 points.circleY)

/-- The non-arbitrary encoders packaged for the coherent-candidate model. -/
def concreteCodeEncoders
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) :
    CodeEncoders K where
  layer0 := encoder0 schedule points
  layer1 := encoder1 schedule points
  layer2 := encoder2 schedule points
  layer3 := encoder3 schedule points

/-- Base-field inverse identities remain exact after embedding in the
extension field. -/
theorem inverse_identity_ext (x inverse : F) (h : 2 * x * inverse = 1) :
    2 * algebraMap F K x * algebraMap F K inverse = 1 := by
  have hm := congrArg (algebraMap F K) h
  simpa only [map_mul, map_one, map_ofNat] using hm

/-! ### The four exact V5 commuting squares -/

/-- `1024 -> 256`: the explicit circle encoder commutes with the first fold. -/
theorem v5_circle_fold_encoder0_commutes
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points) :
    circleFoldLayer 131072 (schedule.alpha 0)
        schedule.circleInv2x schedule.circleInv2y ∘ₗ
        encoder0 schedule points =
      encoder1 schedule points ∘ₗ
        coefficientFoldLayer 256 (schedule.alpha 0) := by
  apply circleFoldLayer_circleLiftEncoder
  · intro i
    exact inverse_identity_ext _ _ (htables.circleX i)
  · intro i
    exact inverse_identity_ext _ _ (htables.circleY i)

/-- `256 -> 64`: the first line encoder commutes with the second fold. -/
theorem v5_line1_fold_encoder1_commutes
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points) :
    lineFoldLayer 32768 (schedule.alpha 1) schedule.line1Inverse ∘ₗ
        encoder1 schedule points =
      encoder2 schedule points ∘ₗ
        coefficientFoldLayer 64 (schedule.alpha 1) := by
  apply lineFoldLayer_radix4LiftEncoder
  · intro i
    exact inverse_identity_ext _ _ (htables.line1 i 0)
  · intro i
    exact inverse_identity_ext _ _ (htables.line1 i 1)
  · intro i
    exact inverse_identity_ext _ _ (htables.line1 i 2)

/-- `64 -> 16`: the second line encoder commutes with the third fold. -/
theorem v5_line2_fold_encoder2_commutes
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points) :
    lineFoldLayer 8192 (schedule.alpha 2) schedule.line2Inverse ∘ₗ
        encoder2 schedule points =
      encoder3 schedule points ∘ₗ
        coefficientFoldLayer 16 (schedule.alpha 2) := by
  apply lineFoldLayer_radix4LiftEncoder
  · intro i
    exact inverse_identity_ext _ _ (htables.line2 i 0)
  · intro i
    exact inverse_identity_ext _ _ (htables.line2 i 1)
  · intro i
    exact inverse_identity_ext _ _ (htables.line2 i 2)

/-- `16 -> 4`: the third line encoder commutes with the fourth fold and the
published final tensor encoder. -/
theorem v5_line3_fold_encoder3_commutes
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points) :
    lineFoldLayer 2048 (schedule.alpha 3) schedule.line3Inverse ∘ₗ
        encoder3 schedule points =
      encoder4 schedule ∘ₗ coefficientFoldLayer 4 (schedule.alpha 3) := by
  apply lineFoldLayer_radix4LiftEncoder
  · intro i
    exact inverse_identity_ext _ _ (htables.line3 i 0)
  · intro i
    exact inverse_identity_ext _ _ (htables.line3 i 1)
  · intro i
    exact inverse_identity_ext _ _ (htables.line3 i 2)

/-! ### Injectivity inherited from the final tensor -/

/-- All four committed-code encoders are injective once the explicit final
tensor encoder separates its four coefficients.  This is useful code
structure, but it is not a minimum-distance or list-size theorem. -/
theorem concrete_encoders_injective
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (htables : InverseTablesMatch schedule points)
    (hfinal : Function.Injective (encoder4 schedule)) :
    Function.Injective (encoder3 schedule points) ∧
      Function.Injective (encoder2 schedule points) ∧
      Function.Injective (encoder1 schedule points) ∧
      Function.Injective (encoder0 schedule points) := by
  have h3 : Function.Injective (encoder3 schedule points) := by
    apply radix4LiftEncoder_injective (encoder4 schedule) hfinal
      (fun i => algebraMap F K (points.line3 i 0))
      (fun i => algebraMap F K (points.line3 i 1))
      (fun i => algebraMap F K (points.line3 i 2))
      (fun i => algebraMap F K (schedule.line3Inverse i 0))
      (fun i => algebraMap F K (schedule.line3Inverse i 1))
      (fun i => algebraMap F K (schedule.line3Inverse i 2))
    · intro i; exact inverse_identity_ext _ _ (htables.line3 i 0)
    · intro i; exact inverse_identity_ext _ _ (htables.line3 i 1)
    · intro i; exact inverse_identity_ext _ _ (htables.line3 i 2)
  have h2 : Function.Injective (encoder2 schedule points) := by
    apply radix4LiftEncoder_injective (encoder3 schedule points) h3
      (fun i => algebraMap F K (points.line2 i 0))
      (fun i => algebraMap F K (points.line2 i 1))
      (fun i => algebraMap F K (points.line2 i 2))
      (fun i => algebraMap F K (schedule.line2Inverse i 0))
      (fun i => algebraMap F K (schedule.line2Inverse i 1))
      (fun i => algebraMap F K (schedule.line2Inverse i 2))
    · intro i; exact inverse_identity_ext _ _ (htables.line2 i 0)
    · intro i; exact inverse_identity_ext _ _ (htables.line2 i 1)
    · intro i; exact inverse_identity_ext _ _ (htables.line2 i 2)
  have h1 : Function.Injective (encoder1 schedule points) := by
    apply radix4LiftEncoder_injective (encoder2 schedule points) h2
      (fun i => algebraMap F K (points.line1 i 0))
      (fun i => algebraMap F K (points.line1 i 1))
      (fun i => algebraMap F K (points.line1 i 2))
      (fun i => algebraMap F K (schedule.line1Inverse i 0))
      (fun i => algebraMap F K (schedule.line1Inverse i 1))
      (fun i => algebraMap F K (schedule.line1Inverse i 2))
    · intro i; exact inverse_identity_ext _ _ (htables.line1 i 0)
    · intro i; exact inverse_identity_ext _ _ (htables.line1 i 1)
    · intro i; exact inverse_identity_ext _ _ (htables.line1 i 2)
  have h0 : Function.Injective (encoder0 schedule points) := by
    apply radix4LiftEncoder_injective (encoder1 schedule points) h1
      (extend1 points.circleY) (-extend1 points.circleY)
      (extend1 points.circleX)
      (extend1 schedule.circleInv2y) (-extend1 schedule.circleInv2y)
      (extend1 schedule.circleInv2x)
    · intro i; exact inverse_identity_ext _ _ (htables.circleY i)
    · intro i
      change 2 * (-algebraMap F K (points.circleY i)) *
        (-algebraMap F K (schedule.circleInv2y i)) = 1
      have hp := inverse_identity_ext (K := K) _ _ (htables.circleY i)
      linear_combination hp
    · intro i; exact inverse_identity_ext _ _ (htables.circleX i)
  exact ⟨h3, h2, h1, h0⟩

/-! ## Exact deployment boundary -/

/-- Source-shaped statement for the inverse tables.  The build script computes
each released table entry as the inverse of twice the corresponding coordinate;
the optional dynamic path computes the same values after rejecting zero.  This
record states exactly those computed values, so the cancellation equations in
`InverseTablesMatch` are field theorems rather than assumptions.

The remaining code-facing work is to connect the generated `RATE512_*` arrays
(or the values returned by `circle_fiber_point_for_domain_log`,
`line_fold_coordinates_for_circle`, and `inverse_double`) to these views. -/
structure InverseTablesComputed
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) : Prop where
  circleXNonzero : ∀ i, 2 * points.circleX i ≠ 0
  circleYNonzero : ∀ i, 2 * points.circleY i ≠ 0
  line1Nonzero : ∀ i s, 2 * points.line1 i s ≠ 0
  line2Nonzero : ∀ i s, 2 * points.line2 i s ≠ 0
  line3Nonzero : ∀ i s, 2 * points.line3 i s ≠ 0
  circleX : ∀ i,
    schedule.circleInv2x i = (2 * points.circleX i)⁻¹
  circleY : ∀ i,
    schedule.circleInv2y i = (2 * points.circleY i)⁻¹
  line1 : ∀ i s,
    schedule.line1Inverse i s = (2 * points.line1 i s)⁻¹
  line2 : ∀ i s,
    schedule.line2Inverse i s = (2 * points.line2 i s)⁻¹
  line3 : ∀ i s,
    schedule.line3Inverse i s = (2 * points.line3 i s)⁻¹

/-- Once the generated coordinate and inverse calls are identified with the
source-shaped record above, all finite-field inverse equations needed by the
four commuting squares follow inside Lean. -/
theorem inverseTablesMatch_of_computed
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (h : InverseTablesComputed schedule points) :
    InverseTablesMatch schedule points where
  circleX i := by
    rw [h.circleX i]
    exact mul_inv_cancel₀ (h.circleXNonzero i)
  circleY i := by
    rw [h.circleY i]
    exact mul_inv_cancel₀ (h.circleYNonzero i)
  line1 i s := by
    rw [h.line1 i s]
    exact mul_inv_cancel₀ (h.line1Nonzero i s)
  line2 i s := by
    rw [h.line2 i s]
    exact mul_inv_cancel₀ (h.line2Nonzero i s)
  line3 i s := by
    rw [h.line3 i s]
    exact mul_inv_cancel₀ (h.line3Nonzero i s)

/-- The only Rust encoder in this path is the initial circle FFT.  The later
three encoders above are mathematical line-code maps used to state proximity;
Rust obtains the later words by folding, not by calling three more encoders.

Consequently the smallest honest encoder implementation statement is one
pointwise equality for `CircleEncoder::encode_c2_message` (equivalently the
coordinatewise `encode_c1_message`) at domain log 19. -/
def RustInitialEncoderEquality
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (rustEncode : Coeff0 K → Word0 K) : Prop :=
  ∀ coefficients,
    rustEncode coefficients = encoder0 schedule points coefficients

/-- Function-equality spelling of the pointwise initial-encoder boundary. -/
theorem rustInitialEncoderEquality_iff
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (rustEncode : Coeff0 K → Word0 K) :
    RustInitialEncoderEquality schedule points rustEncode ↔
      rustEncode = encoder0 schedule points := by
  constructor
  · intro h
    funext coefficients
    exact h coefficients
  · intro h coefficients
    rw [h]

/-- The exact consequence of the two remaining code-facing facts.  If the
log-19 Rust FFT is the explicit initial encoder and the released inverse
tables are the values computed from the same points, then every subsequent
deployed fold stays in the corresponding explicit line code.  No additional
"Rust layer encoder" premise is needed. -/
theorem rust_initial_encoder_four_fold_tower
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (rustEncode : Coeff0 K → Word0 K)
    (hinverses : InverseTablesComputed schedule points)
    (hencoder : RustInitialEncoderEquality schedule points rustEncode)
    (coefficients : Coeff0 K) :
    circleFoldLayer 131072 (schedule.alpha 0)
        schedule.circleInv2x schedule.circleInv2y
        (rustEncode coefficients) =
      encoder1 schedule points (fold0 schedule coefficients) ∧
    lineFoldLayer 32768 (schedule.alpha 1) schedule.line1Inverse
        (encoder1 schedule points (fold0 schedule coefficients)) =
      encoder2 schedule points
        (fold1 schedule (fold0 schedule coefficients)) ∧
    lineFoldLayer 8192 (schedule.alpha 2) schedule.line2Inverse
        (encoder2 schedule points
          (fold1 schedule (fold0 schedule coefficients))) =
      encoder3 schedule points
        (fold2 schedule (fold1 schedule (fold0 schedule coefficients))) ∧
    lineFoldLayer 2048 (schedule.alpha 3) schedule.line3Inverse
        (encoder3 schedule points
          (fold2 schedule (fold1 schedule (fold0 schedule coefficients)))) =
      encoder4 schedule
        (fold3 schedule
          (fold2 schedule (fold1 schedule (fold0 schedule coefficients)))) := by
  let htables := inverseTablesMatch_of_computed schedule points hinverses
  have h0 := congrArg
    (fun m : (Coeff0 K →ₗ[K] Word1 K) => m coefficients)
    (v5_circle_fold_encoder0_commutes schedule points htables)
  have h1 := congrArg
    (fun m : (Coeff1 K →ₗ[K] Word2 K) => m (fold0 schedule coefficients))
    (v5_line1_fold_encoder1_commutes schedule points htables)
  have h2 := congrArg
    (fun m : (Coeff2 K →ₗ[K] Word3 K) =>
      m (fold1 schedule (fold0 schedule coefficients)))
    (v5_line2_fold_encoder2_commutes schedule points htables)
  have h3 := congrArg
    (fun m : (Coeff3 K →ₗ[K] (Fin 2048 → K)) =>
      m (fold2 schedule (fold1 schedule (fold0 schedule coefficients))))
    (v5_line3_fold_encoder3_commutes schedule points htables)
  simp only [LinearMap.comp_apply] at h0 h1 h2 h3
  rw [hencoder coefficients]
  exact ⟨h0, h1, h2, h3⟩

/-! ## Axiom audit -/

#print axioms lineFoldValue_radix4Evaluate
#print axioms circleFoldValue_radix4Evaluate
#print axioms radix4Decode_radix4Evaluate
#print axioms radix4Evaluate_radix4Decode
#print axioms lineFoldValue_eq_coefficientFoldValue_decode
#print axioms circleFoldValue_eq_coefficientFoldValue_decode
#print axioms radix4Evaluate_injective
#print axioms v5_circle_fold_encoder0_commutes
#print axioms v5_line1_fold_encoder1_commutes
#print axioms v5_line2_fold_encoder2_commutes
#print axioms v5_line3_fold_encoder3_commutes
#print axioms concrete_encoders_injective
#print axioms inverseTablesMatch_of_computed
#print axioms rustInitialEncoderEquality_iff
#print axioms rust_initial_encoder_four_fold_tower

end AspisV5FriConcreteEncoderCommutation
