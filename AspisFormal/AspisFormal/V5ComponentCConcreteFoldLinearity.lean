import Mathlib

/-!
# v5 Component C: concrete fixed-challenge fold linearity

This leaf removes one unnecessary abstraction from the Component-C audit.  For
a **fixed public transcript**, the four deployed FRI folds are explicit QM31
linear maps.  Establishing that fact does not require a circle-to-GRS
transport theorem or any applicability claim about a published FRI theorem.

The formulas and order below are transcribed from the deployed Rust:

* `crates/aspis-core/src/circle_fri.rs`:
  `normalized_circle_to_line_arity4_prepared_with_square`,
  `normalized_line_arity4_prepared_with_square`, and
  `normalized_arity4_prepared_polynomial_candidate`;
* `crates/aspis-core/src/circle_query.rs` and
  `programs/aspis-verifier/src/v5_fri_checks.rs`: the child order
  `4 * fibre + slot`, the three later-layer reads, and the terminal tensor
  `[1,x,2*x^2-1,x*(2*x^2-1)]`;
* `crates/aspis-prover/src/v5_component_c_fmat.rs`: the offline worst-case
  `F_sigma` row order and the natural coefficient folds with weights
  `[1, alpha, alpha^2, alpha^3]`; production's authenticated-parent arrays are
  deduplicated, so their actual three block lengths remain schedule fields.

The model is generic in a base field `F` (deployed M31) and an extension field
`K` (deployed QM31) with `Algebra F K`.  Every M31 inverse/twiddle is inserted
with `algebraMap F K`; every challenge and released value is in `K`.

## What is proved

* The nested butterfly and cubic-polynomial implementations are identical.
* A circle fold is literally the line fold with twiddles
  `(inv_2y, -inv_2y, inv_2x)`.
* The exact `2^19 -> 2^17 -> 2^15 -> 2^13 -> 2^11` codeword tower, all
  three `q18` later-layer read blocks, and the
  `1024 -> 256 -> 64 -> 16 -> 4` coefficient tower are linear maps.
* These maps pack, in the deployed order, into an honest coefficient-domain,
  schedule-indexed linear map with
  `Y_sigma = 40 + 4 * (n1 + n2 + n3)` rows, where `n1,n2,n3` are the actual
  deduplicated authenticated-parent counts.  The value `256` is proved only
  for the offline worst case `n1=n2=n3=18`; it is not asserted as the
  universal production serialization.  Rust's emitted `256 x 1023` F-matrix
  has one further, load-bearing composition: its 1023 free coordinates are
  first mapped into the 1024 coefficient hyperplane by
  `V5ComponentCLane::encode_free_coordinates`.  `concreteFreeF` records that
  composition explicitly rather than identifying the two differently typed
  maps.
* Concrete negative examples show that changing the slot order, changing a
  twiddle, or dropping the minus sign on the second circle pair changes the
  map.  These are mutation teeth, not comments.

## Honest boundary

This file does **not** prove that Rust bytes decode to the fields of
`FixedSchedule`, that the Rust free-coordinate encoder is `encodeFree`, that
the Rust circle encoder is `enc`, that the Rust relation evaluator is
`relationRows`, or that an accepted terminal opening satisfies the PCS
terminal identity.  Those are separate, named interfaces below and are left
unproved.  In particular this file proves neither C-DEC nor deployed zero
knowledge and never calls Component C closed.
-/

namespace AspisV5ComponentCConcreteFoldLinearity

/-! ## Frozen deployed dimensions and row counts -/

def coefficientCount : Nat := 1024
def layer0Symbols : Nat := 524288
def layer1Symbols : Nat := 131072
def layer2Symbols : Nat := 32768
def layer3Symbols : Nat := 8192
def layer4Symbols : Nat := 2048

def queryCount : Nat := 18
def relationRounds : Nat := 4
def relationRowsPerRound : Nat := 9
def relationRowsCount : Nat := 36
def maxLaterRowsCount : Nat := 216
def finalCoefficientCount : Nat := 4
def maxFRowsCount : Nat := 256

theorem codeword_dimension_teeth :
    layer0Symbols = 4 * layer1Symbols ∧
    layer1Symbols = 4 * layer2Symbols ∧
    layer2Symbols = 4 * layer3Symbols ∧
    layer3Symbols = 4 * layer4Symbols := by
  decide

theorem coefficient_dimension_teeth :
    coefficientCount = 4 * 256 ∧ 256 = 4 * 64 ∧ 64 = 4 * 16 ∧ 16 = 4 * 4 := by
  decide

theorem max_f_row_count_tooth :
    relationRowsCount + maxLaterRowsCount + finalCoefficientCount = maxFRowsCount ∧
    relationRowsCount = relationRounds * relationRowsPerRound ∧
    maxLaterRowsCount = 3 * queryCount * 4 := by
  decide

/-! ## Exact scalar fold formulas -/

section ScalarFolds

variable {K : Type*} [Field K]

/-- Rust's normalized binary fold
`(left + right)/2 + challenge * (left - right) * inverse`. -/
def pairFoldValue (challenge inverse left right : K) : K :=
  (left + right) / 2 + challenge * ((left - right) * inverse)

/-- The exact nested arity-four line fold.  The outer challenge is
`alpha^2`, not a fresh challenge. -/
def lineFoldValue (alpha inv0 inv1 inv2 : K) (v : Fin 4 → K) : K :=
  pairFoldValue (alpha ^ 2) inv2
    (pairFoldValue alpha inv0 (v 0) (v 1))
    (pairFoldValue alpha inv1 (v 2) (v 3))

/-- The exact cubic expansion used by the optimized verifier. -/
def lineFoldPolynomialValue (alpha inv0 inv1 inv2 : K) (v : Fin 4 → K) : K :=
  let leftSum := v 0 + v 1
  let rightSum := v 2 + v 3
  let leftScaledDifference := (v 0 - v 1) * inv0
  let rightScaledDifference := (v 2 - v 3) * inv1
  let constant := (leftSum + rightSum) / 2 / 2
  let linear := (leftScaledDifference + rightScaledDifference) / 2
  let quadratic := (leftSum - rightSum) / 2 * inv2
  let cubic := (leftScaledDifference - rightScaledDifference) * inv2
  constant + alpha * linear + alpha ^ 2 * quadratic + alpha ^ 3 * cubic

/-- The optimized cubic is exactly the nested butterfly, over every field and
for every fixed challenge/twiddle tuple. -/
theorem lineFoldValue_eq_polynomial (alpha inv0 inv1 inv2 : K) (v : Fin 4 → K) :
    lineFoldValue alpha inv0 inv1 inv2 v =
      lineFoldPolynomialValue alpha inv0 inv1 inv2 v := by
  simp only [lineFoldValue, lineFoldPolynomialValue, pairFoldValue]
  ring

/-- The circle-to-line fold is exactly the same arity-four polynomial with
twiddles `(inv_2y, -inv_2y, inv_2x)`.  The minus sign is the deployed slot
order `(x,y),(x,-y),(-x,-y),(-x,y)`. -/
def circleFoldValue (alpha inv2x inv2y : K) (v : Fin 4 → K) : K :=
  lineFoldValue alpha inv2y (-inv2y) inv2x v

/-- Bundled QM31-linear line fold for fixed public scalars. -/
def lineFoldLinear (alpha inv0 inv1 inv2 : K) : (Fin 4 → K) →ₗ[K] K where
  toFun := lineFoldValue alpha inv0 inv1 inv2
  map_add' v w := by
    simp only [lineFoldValue, pairFoldValue, Pi.add_apply]
    ring
  map_smul' a v := by
    simp only [lineFoldValue, pairFoldValue, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- Bundled QM31-linear circle fold, with the deployed sign/order fixed in
the definition rather than supplied by a transport assumption. -/
def circleFoldLinear (alpha inv2x inv2y : K) : (Fin 4 → K) →ₗ[K] K :=
  lineFoldLinear alpha inv2y (-inv2y) inv2x

@[simp] theorem lineFoldLinear_apply (alpha inv0 inv1 inv2 : K) (v : Fin 4 → K) :
    lineFoldLinear alpha inv0 inv1 inv2 v = lineFoldValue alpha inv0 inv1 inv2 v :=
  rfl

@[simp] theorem circleFoldLinear_apply (alpha inv2x inv2y : K) (v : Fin 4 → K) :
    circleFoldLinear alpha inv2x inv2y v = circleFoldValue alpha inv2x inv2y v :=
  rfl

/-- The natural coefficient fold used by `fold_sparse_terms`: consecutive
slots carry powers `alpha^0, ..., alpha^3` in exactly this order. -/
def coefficientFoldValue (alpha : K) (v : Fin 4 → K) : K :=
  v 0 + alpha * v 1 + alpha ^ 2 * v 2 + alpha ^ 3 * v 3

def coefficientFoldLinear (alpha : K) : (Fin 4 → K) →ₗ[K] K where
  toFun := coefficientFoldValue alpha
  map_add' v w := by
    simp only [coefficientFoldValue, Pi.add_apply]
    ring
  map_smul' a v := by
    simp only [coefficientFoldValue, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Natural final-line tensor `[1,x,pi(x),x*pi(x)]`, with
`pi(x) = 2*x^2 - 1`, as checked by `circle_query.rs`. -/
def finalTensorValue (x : K) (c : Fin 4 → K) : K :=
  let piX := 2 * x ^ 2 - 1
  c 0 + c 1 * x + c 2 * piX + c 3 * (x * piX)

def finalTensorLinear (x : K) : (Fin 4 → K) →ₗ[K] K where
  toFun := finalTensorValue x
  map_add' c d := by
    simp only [finalTensorValue, Pi.add_apply]
    ring
  map_smul' a c := by
    simp only [finalTensorValue, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end ScalarFolds

/-! ## Exact fibre-major layer maps -/

section LayerMaps

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Deployed fibre-major addressing: child slot `s` of parent `i` is
flat index `4*i+s`. -/
def childIndex {n : Nat} (i : Fin n) (s : Fin 4) : Fin (4 * n) :=
  ⟨4 * i.val + s.val, by omega⟩

@[simp] theorem childIndex_val {n : Nat} (i : Fin n) (s : Fin 4) :
    (childIndex i s).val = 4 * i.val + s.val :=
  rfl

/-- Gather one consecutive four-symbol fibre, preserving slot order. -/
def gatherFibre (n : Nat) (i : Fin n) :
    (Fin (4 * n) → K) →ₗ[K] (Fin 4 → K) :=
  LinearMap.funLeft K K (childIndex i)

/-- One complete circle-to-line layer with fixed public M31 inverse tables,
embedded coefficientwise into QM31. -/
def circleFoldLayer (n : Nat) (alpha : K) (inv2x inv2y : Fin n → F) :
    (Fin (4 * n) → K) →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i =>
    circleFoldLinear alpha (algebraMap F K (inv2x i)) (algebraMap F K (inv2y i)) ∘ₗ
      gatherFibre n i

/-- One complete later line layer with the three exact public inverse tables. -/
def lineFoldLayer (n : Nat) (alpha : K) (inverse : Fin n → Fin 3 → F) :
    (Fin (4 * n) → K) →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i =>
    lineFoldLinear alpha
        (algebraMap F K (inverse i 0))
        (algebraMap F K (inverse i 1))
        (algebraMap F K (inverse i 2)) ∘ₗ
      gatherFibre n i

/-- One natural coefficient fold layer. -/
def coefficientFoldLayer (n : Nat) (alpha : K) :
    (Fin (4 * n) → K) →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => coefficientFoldLinear alpha ∘ₗ gatherFibre n i

@[simp] theorem circleFoldLayer_apply (n : Nat) (alpha : K)
    (inv2x inv2y : Fin n → F) (v : Fin (4 * n) → K) (i : Fin n) :
    circleFoldLayer n alpha inv2x inv2y v i =
      circleFoldValue alpha (algebraMap F K (inv2x i)) (algebraMap F K (inv2y i))
        (fun s => v (childIndex i s)) := by
  rfl

@[simp] theorem lineFoldLayer_apply (n : Nat) (alpha : K)
    (inverse : Fin n → Fin 3 → F) (v : Fin (4 * n) → K) (i : Fin n) :
    lineFoldLayer n alpha inverse v i =
      lineFoldValue alpha
        (algebraMap F K (inverse i 0))
        (algebraMap F K (inverse i 1))
        (algebraMap F K (inverse i 2))
        (fun s => v (childIndex i s)) := by
  rfl

@[simp] theorem coefficientFoldLayer_apply (n : Nat) (alpha : K)
    (v : Fin (4 * n) → K) (i : Fin n) :
    coefficientFoldLayer n alpha v i =
      coefficientFoldValue alpha (fun s => v (childIndex i s)) := by
  rfl

/-- Read all four slots of each selected authenticated later-layer leaf. -/
def readFibres {n q : Nat} (queries : Fin q → Fin n) :
    (Fin (4 * n) → K) →ₗ[K] (Fin q × Fin 4 → K) :=
  LinearMap.funLeft K K fun qs => childIndex (queries qs.1) qs.2

@[simp] theorem readFibres_apply {n q : Nat} (queries : Fin q → Fin n)
    (v : Fin (4 * n) → K) (j : Fin q) (s : Fin 4) :
    readFibres (K := K) queries v (j, s) = v (childIndex (queries j) s) :=
  rfl

end LayerMaps

/-! ## The fixed four-round deployed schedule -/

section FixedTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

abbrev Coefficients := Fin coefficientCount → K
abbrev FreeCoordinateVector := Fin (coefficientCount - 1) → K
abbrev Layer0Word := Fin layer0Symbols → K
abbrev Layer1Word := Fin layer1Symbols → K
abbrev Layer2Word := Fin layer2Symbols → K
abbrev Layer3Word := Fin layer3Symbols → K
abbrev Layer4Word := Fin layer4Symbols → K

/-- Every schedule entry is public and fixed before the linear map is
applied.  Production authenticates deduplicated parent sets, so the three
later counts are schedule fields, not hard-coded `18`s.  Within each selected
leaf all four slots are released in increasing order. -/
structure FixedSchedule where
  alpha : Fin 4 → K
  circleInv2x : Fin layer1Symbols → F
  circleInv2y : Fin layer1Symbols → F
  line1Inverse : Fin layer2Symbols → Fin 3 → F
  line2Inverse : Fin layer3Symbols → Fin 3 → F
  line3Inverse : Fin layer4Symbols → Fin 3 → F
  later1Count : Nat
  later2Count : Nat
  later3Count : Nat
  later1Fibre : Fin later1Count → Fin layer2Symbols
  later2Fibre : Fin later2Count → Fin layer3Symbols
  later3Fibre : Fin later3Count → Fin layer4Symbols
  finalX : Fin layer4Symbols → F

variable {F K}

/-- First deployed round: circle codeword to the first line word. -/
def layer1Map (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] Layer1Word K :=
  circleFoldLayer layer1Symbols (schedule.alpha 0)
      schedule.circleInv2x schedule.circleInv2y ∘ₗ enc

/-- Second deployed round (first line fold). -/
def layer2Map (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] Layer2Word K :=
  lineFoldLayer layer2Symbols (schedule.alpha 1) schedule.line1Inverse ∘ₗ
    layer1Map schedule enc

/-- Third deployed round. -/
def layer3Map (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] Layer3Word K :=
  lineFoldLayer layer3Symbols (schedule.alpha 2) schedule.line2Inverse ∘ₗ
    layer2Map schedule enc

/-- Fourth deployed round.  This word is not separately serialized; accepted
queries compare it with `finalCoefficientMap` through the terminal tensor. -/
def layer4Map (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] Layer4Word K :=
  lineFoldLayer layer4Symbols (schedule.alpha 3) schedule.line3Inverse ∘ₗ
    layer3Map schedule enc

/-- The three committed, deduplicated later-layer read maps. -/
def later1ReadMap (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] (Fin schedule.later1Count × Fin 4 → K) :=
  readFibres schedule.later1Fibre ∘ₗ layer1Map schedule enc

def later2ReadMap (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] (Fin schedule.later2Count × Fin 4 → K) :=
  readFibres schedule.later2Fibre ∘ₗ layer2Map schedule enc

def later3ReadMap (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] (Fin schedule.later3Count × Fin 4 → K) :=
  readFibres schedule.later3Fibre ∘ₗ layer3Map schedule enc

/-- Exact four natural coefficient folds
`1024 -> 256 -> 64 -> 16 -> 4`. -/
def finalCoefficientMap (schedule : FixedSchedule F K) :
    Coefficients K →ₗ[K] (Fin 4 → K) :=
  coefficientFoldLayer 4 (schedule.alpha 3) ∘ₗ
    coefficientFoldLayer 16 (schedule.alpha 2) ∘ₗ
      coefficientFoldLayer 64 (schedule.alpha 1) ∘ₗ
        coefficientFoldLayer 256 (schedule.alpha 0)

/-! ### Exact, schedule-indexed `F_sigma` row order -/

abbrev RelationIndex := Fin relationRounds × Fin relationRowsPerRound

/-- Production later rows: layer 1, then layer 2, then layer 3; within each
layer, deduplicated parent ordinal then slot. -/
abbrev LaterIndex (schedule : FixedSchedule F K) :=
  (Fin schedule.later1Count × Fin 4) ⊕
    ((Fin schedule.later2Count × Fin 4) ⊕
      (Fin schedule.later3Count × Fin 4))

abbrev FTaggedIndex (schedule : FixedSchedule F K) :=
  RelationIndex ⊕ (LaterIndex schedule ⊕ Fin finalCoefficientCount)

def laterRows (schedule : FixedSchedule F K) : Nat :=
  schedule.later1Count * 4 +
    (schedule.later2Count * 4 + schedule.later3Count * 4)

/-- Exact deployed row count after parent deduplication. -/
def fRows (schedule : FixedSchedule F K) : Nat :=
  relationRowsCount + (laterRows schedule + finalCoefficientCount)

omit [Field F] [Field K] [Algebra F K] in
theorem fRows_formula (schedule : FixedSchedule F K) :
    fRows schedule = 40 + 4 *
      (schedule.later1Count + schedule.later2Count + schedule.later3Count) := by
  simp only [fRows, laterRows, relationRowsCount, finalCoefficientCount]
  omega

omit [Field F] [Field K] [Algebra F K] in
/-- `256` is only the no-dedup-loss maximum (`18,18,18`). -/
theorem fRows_eq_256_of_max_counts (schedule : FixedSchedule F K)
    (h1 : schedule.later1Count = queryCount)
    (h2 : schedule.later2Count = queryCount)
    (h3 : schedule.later3Count = queryCount) :
    fRows schedule = maxFRowsCount := by
  simp [fRows_formula, h1, h2, h3, queryCount, maxFRowsCount]

omit [Field F] [Field K] [Algebra F K] in
theorem fRows_le_256 (schedule : FixedSchedule F K)
    (h1 : schedule.later1Count ≤ queryCount)
    (h2 : schedule.later2Count ≤ queryCount)
    (h3 : schedule.later3Count ≤ queryCount) :
    fRows schedule ≤ maxFRowsCount := by
  rw [fRows_formula]
  simp only [queryCount, maxFRowsCount] at h1 h2 h3 ⊢
  omega

/-- `round*9 + withinRound`, matching two OOD rows then seven sumcheck rows. -/
def relationIndexEquiv : RelationIndex ≃ Fin relationRowsCount :=
  finProdFinEquiv

def laterIndexEquiv (schedule : FixedSchedule F K) :
    LaterIndex schedule ≃ Fin (laterRows schedule) :=
  (Equiv.sumCongr finProdFinEquiv
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
        finSumFinEquiv)).trans finSumFinEquiv

/-- Deployed serializer order: 36 relation rows, the three schedule-sized
later blocks, then four final coefficients. -/
def fTaggedIndexEquiv (schedule : FixedSchedule F K) :
    FTaggedIndex schedule ≃ Fin (fRows schedule) :=
  (Equiv.sumCongr relationIndexEquiv
      ((Equiv.sumCongr (laterIndexEquiv schedule)
        (Equiv.refl (Fin finalCoefficientCount))).trans finSumFinEquiv)).trans
    finSumFinEquiv

def packF (schedule : FixedSchedule F K) :
    (FTaggedIndex schedule → K) ≃ₗ[K] (Fin (fRows schedule) → K) :=
  LinearEquiv.funCongrLeft K K (fTaggedIndexEquiv schedule).symm

/-- The exact fixed-schedule `F` map before flattening. `relationRows` remains
a supplied linear map because its OOD/sumcheck Rust evaluator is a separate
correspondence seam.  The circle and coefficient folds are constructed here,
not assumed linear. -/
def taggedFMap (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) :
    Coefficients K →ₗ[K] (FTaggedIndex schedule → K) :=
  LinearMap.pi fun index =>
    match index with
    | .inl r => LinearMap.proj r ∘ₗ relationRows
    | .inr (.inl (.inl l)) => LinearMap.proj l ∘ₗ later1ReadMap schedule enc
    | .inr (.inl (.inr (.inl l))) => LinearMap.proj l ∘ₗ later2ReadMap schedule enc
    | .inr (.inl (.inr (.inr l))) => LinearMap.proj l ∘ₗ later3ReadMap schedule enc
    | .inr (.inr j) => LinearMap.proj j ∘ₗ finalCoefficientMap schedule

/-- Concrete fixed-challenge **coefficient-domain** Component-C view map.
This is an honest QM31-linear map from all 1024 coefficient vectors into the
exact schedule-dependent released-view space.  It is not yet Rust's emitted
`256 x 1023` F-matrix: that matrix first applies the free-coordinate encoder
defined below.  No circle/GRS transport premise occurs in this construction. -/
def concreteF (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) :
    Coefficients K →ₗ[K] (Fin (fRows schedule) → K) :=
  (packF schedule).toLinearMap ∘ₗ taggedFMap schedule enc relationRows

/-- The map with the same domain as Rust's 1023-column F-matrix.  The
load-bearing `encodeFree` argument is the coefficient-hyperplane embedding;
for deployed Rust it must correspond to
`V5ComponentCLane::encode_free_coordinates`. -/
def concreteFreeF (schedule : FixedSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] Coefficients K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) :
    FreeCoordinateVector K →ₗ[K] (Fin (fRows schedule) → K) :=
  concreteF schedule enc relationRows ∘ₗ encodeFree

@[simp] theorem concreteFreeF_apply (schedule : FixedSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] Coefficients K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (free : FreeCoordinateVector K) :
    concreteFreeF schedule encodeFree enc relationRows free =
      concreteF schedule enc relationRows (encodeFree free) :=
  rfl

/-- Reindexing is exact: a tagged coordinate lands in precisely its deployed
flat row, with no permutation left over. -/
theorem concreteF_at_tag (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (index : FTaggedIndex schedule) :
    concreteF schedule enc relationRows c (fTaggedIndexEquiv schedule index) =
      taggedFMap schedule enc relationRows c index := by
  simp [concreteF, packF]

theorem concreteF_relation_coordinate (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (r : RelationIndex) :
    concreteF schedule enc relationRows c (fTaggedIndexEquiv schedule (.inl r)) =
      relationRows c r := by
  rw [concreteF_at_tag]
  rfl

theorem concreteF_later1_coordinate (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (l : Fin schedule.later1Count × Fin 4) :
    concreteF schedule enc relationRows c
        (fTaggedIndexEquiv schedule (.inr (.inl (.inl l)))) =
      later1ReadMap schedule enc c l := by
  rw [concreteF_at_tag]
  rfl

theorem concreteF_later2_coordinate (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (l : Fin schedule.later2Count × Fin 4) :
    concreteF schedule enc relationRows c
        (fTaggedIndexEquiv schedule (.inr (.inl (.inr (.inl l))))) =
      later2ReadMap schedule enc c l := by
  rw [concreteF_at_tag]
  rfl

theorem concreteF_later3_coordinate (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (l : Fin schedule.later3Count × Fin 4) :
    concreteF schedule enc relationRows c
        (fTaggedIndexEquiv schedule (.inr (.inl (.inr (.inr l))))) =
      later3ReadMap schedule enc c l := by
  rw [concreteF_at_tag]
  rfl

theorem concreteF_final_coordinate (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c : Coefficients K) (j : Fin 4) :
    concreteF schedule enc relationRows c
        (fTaggedIndexEquiv schedule (.inr (.inr j))) =
      finalCoefficientMap schedule c j := by
  rw [concreteF_at_tag]
  rfl

theorem concreteF_add (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (c d : Coefficients K) :
    concreteF schedule enc relationRows (c + d) =
      concreteF schedule enc relationRows c + concreteF schedule enc relationRows d :=
  map_add _ _ _

theorem concreteF_smul (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K))
    (a : K) (c : Coefficients K) :
    concreteF schedule enc relationRows (a • c) =
      a • concreteF schedule enc relationRows c :=
  map_smul _ _ _

/-! ### Terminal opening: a separate PCS equality, not an `F` row -/

def terminalFoldReadMap (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) :
    Coefficients K →ₗ[K] (Fin schedule.later3Count → K) :=
  LinearMap.funLeft K K schedule.later3Fibre ∘ₗ layer4Map schedule enc

def terminalTensorReadMap (schedule : FixedSchedule F K) :
    Coefficients K →ₗ[K] (Fin schedule.later3Count → K) :=
  LinearMap.pi fun q =>
    finalTensorLinear (algebraMap F K (schedule.finalX (schedule.later3Fibre q))) ∘ₗ
      finalCoefficientMap schedule

def TerminalPCSCompatible (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K) : Prop :=
  terminalFoldReadMap schedule enc = terminalTensorReadMap schedule

theorem terminal_reads_equal_of_compatible (schedule : FixedSchedule F K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (h : TerminalPCSCompatible schedule enc) (c : Coefficients K) :
    terminalFoldReadMap schedule enc c = terminalTensorReadMap schedule c := by
  rw [h]

/-! ### Honest Rust/model correspondence seam -/

namespace UnmetDeployment

/-- Byte decoding, generated circle tables, dedup ordering, the Rust encoder,
and relation-row enumeration match the raw 1024-coefficient reference
evaluator.  This does **not** by itself identify Rust's 1023-column F-matrix;
that requires `RustFreeCoordinateFmatCorrespondence` below.  Definition only:
no theorem in this file proves it. -/
def RustFixedScheduleCorrespondence
    (schedule : FixedSchedule F K)
    (rustF : Coefficients K → Fin (fRows schedule) → K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) : Prop :=
  ∀ c, rustF c = concreteF schedule enc relationRows c

/-- The Rust F-matrix evaluator includes the load-bearing 1023-to-1024
free-coordinate encoding before the coefficient-domain view map.  This is the
type-correct correspondence seam for `V5ComponentCFmat::mul_vec`.  The
checked-in fixed `256`-row artifact additionally requires the collision-free
count equalities (or an explicit row reindexing); no padding is hidden here. -/
def RustFreeCoordinateFmatCorrespondence
    (schedule : FixedSchedule F K)
    (rustFmat : FreeCoordinateVector K → Fin (fRows schedule) → K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] Coefficients K)
    (enc : Coefficients K →ₗ[K] Layer0Word K)
    (relationRows : Coefficients K →ₗ[K] (RelationIndex → K)) : Prop :=
  ∀ free, rustFmat free = concreteFreeF schedule encodeFree enc relationRows free

/-- The arrays are Rust's deduplicated parent lists, in precisely the order
used by each authenticated opening.  This is distinct from a padded 18-row
offline matrix convention. -/
def RustDeduplicatedParentCorrespondence
    (schedule : FixedSchedule F K)
    (rustLayer1 : Fin schedule.later1Count → Nat)
    (rustLayer2 : Fin schedule.later2Count → Nat)
    (rustLayer3 : Fin schedule.later3Count → Nat)
    : Prop :=
  (∀ q, rustLayer1 q = (schedule.later1Fibre q).val) ∧
  (∀ q, rustLayer2 q = (schedule.later2Fibre q).val) ∧
  (∀ q, rustLayer3 q = (schedule.later3Fibre q).val)

/-- Any conversion of this schedule-sized view to a fixed 256-row artifact
must be specified and proved separately.  No such padding is assumed here. -/
def CanonicalPaddingTo256
    (schedule : FixedSchedule F K)
    (pad : (Fin (fRows schedule) → K) → (Fin maxFRowsCount → K)) : Prop :=
  Function.Injective pad

end UnmetDeployment

end FixedTower

/-! ## Mutation teeth

All three examples live in a concrete prime field and reduce in the kernel.
They prove that the exact order/twiddle choices above are observable. -/

section MutationTeeth

local instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

def teethValues : Fin 4 → ZMod 31 := ![1, 4, 9, 16]
def swapMiddleValues : Fin 4 → ZMod 31 := ![1, 9, 4, 16]

/-- Swapping slots 1 and 2 changes the arity-four fold. -/
theorem fold_slot_order_is_load_bearing :
    lineFoldValue (2 : ZMod 31) 3 5 7 teethValues ≠
      lineFoldValue (2 : ZMod 31) 3 5 7 swapMiddleValues := by
  have hinv : (2 : ZMod 31)⁻¹ = 16 :=
    ZMod.inv_eq_of_mul_eq_one 31 2 16 (by decide)
  norm_num [lineFoldValue, pairFoldValue, teethValues, swapMiddleValues,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, hinv] ; decide

/-- Changing the second-pair inverse changes the fold. -/
theorem fold_twiddle_is_load_bearing :
    lineFoldValue (2 : ZMod 31) 3 5 7 teethValues ≠
      lineFoldValue (2 : ZMod 31) 3 6 7 teethValues := by
  have hinv : (2 : ZMod 31)⁻¹ = 16 :=
    ZMod.inv_eq_of_mul_eq_one 31 2 16 (by decide)
  norm_num [lineFoldValue, pairFoldValue, teethValues,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, hinv] ; decide

/-- The negative `inv_2y` on the second circle pair is load-bearing. -/
theorem circle_second_pair_sign_is_load_bearing :
    circleFoldValue (2 : ZMod 31) 7 5 teethValues ≠
      lineFoldValue (2 : ZMod 31) 5 5 7 teethValues := by
  have hinv : (2 : ZMod 31)⁻¹ = 16 :=
    ZMod.inv_eq_of_mul_eq_one 31 2 16 (by decide)
  norm_num [circleFoldValue, lineFoldValue, pairFoldValue, teethValues,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, hinv] ; decide

end MutationTeeth

/-! ## Axiom audit -/

#print axioms lineFoldValue_eq_polynomial
#print axioms circleFoldLayer_apply
#print axioms lineFoldLayer_apply
#print axioms coefficientFoldLayer_apply
#print axioms concreteF_at_tag
#print axioms concreteFreeF_apply
#print axioms concreteF_relation_coordinate
#print axioms concreteF_later1_coordinate
#print axioms concreteF_later2_coordinate
#print axioms concreteF_later3_coordinate
#print axioms concreteF_final_coordinate
#print axioms concreteF_add
#print axioms concreteF_smul
#print axioms terminal_reads_equal_of_compatible
#print axioms fold_slot_order_is_load_bearing
#print axioms fold_twiddle_is_load_bearing
#print axioms circle_second_pair_sign_is_load_bearing

end AspisV5ComponentCConcreteFoldLinearity
