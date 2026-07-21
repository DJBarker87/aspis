import AspisFormal.V5ComponentATerminalRankPredicate
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Component-A deployed terminal applicability

This file gives the exact finite mathematical gate for the three Component-A
MLE releases.  The source remains the deployed M31 hyperplane.  Its 22
distinguished legal directions are

* `kernelPoly q18 * (X^i - 1)` in the ordinary x/p block, and
* the same polynomial in the ordinary y/q block,

for `1 <= i <= 11`.  Every direction has coefficient sum zero and vanishes at
all 72 q18 circle reads.  The deployed terminal model is the literal
ordinary-to-natural block conversion, interleaved placement at rows
`896+2k, 897+2k`, and big-endian MLE evaluation at `z`, `successor(z)`, and
`xor12(z)`.  The exact QM31 tower is expanded in Rust limb order to twelve M31
coordinates.

`GoodA` asks for the fixed first-twelve-column minor of the resulting public
12-by-22 matrix to be nonsingular.  It is a sufficient public predicate, not a
KAT: the main theorem constructs an M31 preimage for every three-QM31 target
and proves the existing exact terminal-rank predicate.  No universal rank claim
is made.

The 22-column certificate is deliberately only sufficient.  It omits the
legal cross-block direction `kernelPoly` in x/p minus `kernelPoly` in y/q;
that omitted direction is recorded and proved legal below rather than silently
identifying the chosen family with the entire legal difference space.

The all-zero point is still rejected.  The final namespace names the remaining
executable equalities.  In particular, this file does not assert that Rust's
conversion table, interleaved encoder, MLE fold, transcript point, or verifier
predicate implementation equals the mathematical objects below.
-/

open Matrix Polynomial

namespace AspisV5ComponentADeployedTerminalApplicability

open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability
open AspisCircleTensorBinding
open AspisV5AtomicComponentA
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentARankCompletion
open AspisV5FreezeAScheduleAvailability
open AspisV5ComponentATerminalRankPredicate
open AspisV5ComponentCQM31TowerExact

abbrev Base := DeployedField
abbrev Tower := QM31Exact
abbrev Source := Fin originalWidth → Base
abbrev TowerSource := Fin originalWidth → Tower
abbrev Message (K : Type*) := Fin traceRows → K
abbrev Direction := Fin 2 × Fin 11
abbrev TerminalLimb := Fin 3 × Fin 4

theorem direction_card : Fintype.card Direction = 22 := by
  simp [Direction]

theorem terminalLimb_card : Fintype.card TerminalLimb = 12 := by
  simp [TerminalLimb]

/-! ## The exact 22-dimensional legal kernel family -/

/-- Ordinary coefficients of a degree-`< 48` polynomial. -/
def polynomialBlock (P : Base[X]) : Fin originalHalf → Base :=
  fun i => P.coeff (i : ℕ)

/-- Put a polynomial in the ordinary p/x block or q/y block. -/
def ordinaryPolynomialDirection (block : Fin 2) (P : Base[X]) : Source :=
  if block = 0 then ordinaryOfBlocks (polynomialBlock P) 0
  else ordinaryOfBlocks 0 (polynomialBlock P)

/-- The 22 directions `kernelPoly * (X^(i+1)-1)` in the two ordinary blocks. -/
noncomputable def kernelDirection
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (direction : Direction) : Source :=
  ordinaryPolynomialDirection direction.1
    (kernelShift queries ((direction.2 : ℕ) + 1))

theorem polynomialBlock_sum_eq_eval_one (P : Base[X])
    (hdegree : P.natDegree < originalHalf) :
    (∑ i, polynomialBlock P i) = P.eval 1 := by
  change (∑ i : Fin originalHalf, P.coeff (i : ℕ)) = P.eval 1
  rw [Fin.sum_univ_eq_sum_range (fun n => P.coeff n) originalHalf]
  simpa using (eval_eq_sum_range' hdegree (1 : Base)).symm

theorem ordinaryPolynomialDirection_sum (block : Fin 2) (P : Base[X])
    (hdegree : P.natDegree < originalHalf) :
    coefficientSum (ordinaryPolynomialDirection block P) = P.eval 1 := by
  fin_cases block
  · change coefficientSum (ordinaryOfBlocks (polynomialBlock P) 0) = P.eval 1
    rw [coefficientSum_ordinaryOfBlocks, polynomialBlock_sum_eq_eval_one P hdegree]
    simp
  · change coefficientSum (ordinaryOfBlocks 0 (polynomialBlock P)) = P.eval 1
    rw [coefficientSum_ordinaryOfBlocks, polynomialBlock_sum_eq_eval_one P hdegree]
    simp

@[simp] theorem ordinaryPolynomialDirection_one_apply (P : Base[X])
    (j : Fin originalWidth) :
    ordinaryPolynomialDirection 1 P j =
      if (j : ℕ) < originalHalf then 0
      else P.coeff ((j : ℕ) - originalHalf) := by
  by_cases hj : (j : ℕ) < originalHalf
  · simp [ordinaryPolynomialDirection, ordinaryOfBlocks, hj]
  · simp [ordinaryPolynomialDirection, ordinaryOfBlocks, polynomialBlock, hj]

theorem kernelDirection_sum_zero
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (direction : Direction) :
    coefficientSum (kernelDirection queries direction) = 0 := by
  rw [kernelDirection, ordinaryPolynomialDirection_sum]
  · exact kernelShift_eval_one queries ((direction.2 : ℕ) + 1)
  · exact kernelShift_natDegree_lt queries (by omega) (by omega)

/-- A q/y-block polynomial is evaluated as `weight * y * P(x)`. -/
theorem mulVec_ordinaryPolynomialDirection_one
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (weight : FibreIndex → Base) (P : Base[X])
    (hdegree : P.natDegree < originalHalf) (row : FibreIndex) :
    (deployedFibreRectangularEval queries weight).mulVec
        (ordinaryPolynomialDirection 1 P) row =
      weight row * signedCoordinate row.2.2 (representativeY (queries row.1)) *
        P.eval (signedCoordinate row.2.1 (representativeX (queries row.1))) := by
  let x := signedCoordinate row.2.1 (representativeX (queries row.1))
  let y := signedCoordinate row.2.2 (representativeY (queries row.1))
  have hrange :
      (deployedFibreRectangularEval queries weight).mulVec
          (ordinaryPolynomialDirection 1 P) row =
        ∑ n ∈ Finset.range originalWidth,
          (weight row * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
            (if n < originalHalf then 0 else P.coeff (n - originalHalf)) := by
    change (∑ j : Fin originalWidth,
      (weight row *
          (if (j : ℕ) < originalHalf then x ^ (j : ℕ)
            else y * x ^ ((j : ℕ) - originalHalf))) *
        ordinaryPolynomialDirection 1 P j) = _
    simp_rw [ordinaryPolynomialDirection_one_apply]
    simpa only using Fin.sum_univ_eq_sum_range
      (fun n =>
        (weight row *
          (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
            (if n < originalHalf then 0 else P.coeff (n - originalHalf)))
      originalWidth
  rw [hrange, show originalWidth = originalHalf + originalHalf by
    norm_num [originalWidth, originalHalf], Finset.sum_range_add]
  have hfirst :
      (∑ n ∈ Finset.range originalHalf,
        (weight row * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
          (if n < originalHalf then 0 else P.coeff (n - originalHalf))) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn48 := Finset.mem_range.mp hn
    simp [hn48]
  rw [hfirst, zero_add]
  have hsecond :
      (∑ n ∈ Finset.range originalHalf,
        (weight row *
            (if originalHalf + n < originalHalf then x ^ (originalHalf + n)
              else y * x ^ (originalHalf + n - originalHalf))) *
          (if originalHalf + n < originalHalf then 0
            else P.coeff (originalHalf + n - originalHalf))) =
        ∑ n ∈ Finset.range originalHalf,
          (weight row * y) * (P.coeff n * x ^ n) := by
    apply Finset.sum_congr rfl
    intro n _
    have hnot : ¬ originalHalf + n < originalHalf := by omega
    simp only [hnot, ↓reduceIte, Nat.add_sub_cancel_left]
    ring
  rw [hsecond, ← Finset.mul_sum]
  rw [eval_eq_sum_range' hdegree]

theorem kernelDirection_mulVec_zero
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (weight : FibreIndex → Base) (direction : Direction) :
    (deployedFibreRectangularEval queries weight).mulVec
      (kernelDirection queries direction) = 0 := by
  funext row
  rw [Pi.zero_apply]
  rcases direction with ⟨block, shift⟩
  have hshift := shift.isLt
  fin_cases block
  · change (deployedFibreRectangularEval queries weight).mulVec
      (fun j => if (j : ℕ) < originalHalf then
        (kernelShift queries ((shift : ℕ) + 1)).coeff (j : ℕ) else 0) row = 0
    rw [mulVec_kernelEmbed queries weight _
        (kernelShift_natDegree_lt queries (by omega) (by omega)) row,
      kernelShift_eval_node_zero, mul_zero]
  · change (deployedFibreRectangularEval queries weight).mulVec
      (ordinaryPolynomialDirection 1
        (kernelShift queries ((shift : ℕ) + 1))) row = 0
    rw [mulVec_ordinaryPolynomialDirection_one queries weight _
        (kernelShift_natDegree_lt queries (by omega) (by omega)) row,
      kernelShift_eval_node_zero, mul_zero]

/-- The remaining evident legal direction, intentionally omitted from the
fixed 22-column sufficient certificate. -/
noncomputable def omittedCrossBlockDirection
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount) : Source :=
  ordinaryPolynomialDirection 0 (kernelPoly queries) -
    ordinaryPolynomialDirection 1 (kernelPoly queries)

theorem omittedCrossBlockDirection_sum_zero
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount) :
    coefficientSum (omittedCrossBlockDirection queries) = 0 := by
  rw [omittedCrossBlockDirection, map_sub,
    ordinaryPolynomialDirection_sum 0 (kernelPoly queries),
    ordinaryPolynomialDirection_sum 1 (kernelPoly queries), sub_self]
  all_goals rw [kernelPoly_natDegree]
  all_goals norm_num [originalHalf]

theorem omittedCrossBlockDirection_mulVec_zero
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (weight : FibreIndex → Base) :
    (deployedFibreRectangularEval queries weight).mulVec
      (omittedCrossBlockDirection queries) = 0 := by
  change (deployedFibreRectangularEval queries weight).mulVecLin
    (omittedCrossBlockDirection queries) = 0
  rw [omittedCrossBlockDirection, map_sub]
  have hx : (deployedFibreRectangularEval queries weight).mulVecLin
      (ordinaryPolynomialDirection 0 (kernelPoly queries)) = 0 := by
    funext row
    rw [Matrix.mulVecLin_apply, Pi.zero_apply]
    change (deployedFibreRectangularEval queries weight).mulVec
      (fun j => if (j : ℕ) < originalHalf then
        (kernelPoly queries).coeff (j : ℕ) else 0) row = 0
    rw [mulVec_kernelEmbed queries weight _ (by
      rw [kernelPoly_natDegree]
      norm_num [originalHalf]) row,
      kernelPoly_eval_node_zero, mul_zero]
  have hy : (deployedFibreRectangularEval queries weight).mulVecLin
      (ordinaryPolynomialDirection 1 (kernelPoly queries)) = 0 := by
    funext row
    rw [Matrix.mulVecLin_apply, Pi.zero_apply,
      mulVec_ordinaryPolynomialDirection_one queries weight _ (by
        rw [kernelPoly_natDegree]
        norm_num [originalHalf]) row,
      kernelPoly_eval_node_zero, mul_zero]
  rw [hx, hy, sub_zero]

/-! ## Exact deployed encoder and three-point MLE model -/

/-- A flat natural/ordinary index inside its 48-coordinate block. -/
def withinBlock (i : Fin originalWidth) : Fin originalHalf :=
  if h : (i : ℕ) < originalHalf then ⟨i, h⟩
  else ⟨(i : ℕ) - originalHalf, by
    have hi := i.isLt
    simp only [originalWidth, originalHalf] at hi ⊢
    omega⟩

/-- Literal block-diagonal ordinary-to-natural conversion used by Component A. -/
noncomputable def deployedAConversionMatrix :
    Matrix (Fin originalWidth) (Fin originalWidth) Tower :=
  fun natural ordinary =>
    if ((natural : ℕ) < originalHalf) = ((ordinary : ℕ) < originalHalf) then
      algebraMap Base Tower
        (monomialToNatural Base originalHalf (withinBlock natural) (withinBlock ordinary))
    else 0

/-- Tower-linear extension of the deployed two-block conversion. -/
noncomputable def deployedAConversion : TowerSource →ₗ[Tower] TowerSource :=
  deployedAConversionMatrix.mulVecLin

/-- The mathematical deployed A encoder: convert each block and interleave it
at rows `896+2k,897+2k`. -/
noncomputable def deployedAEncoder : TowerSource →ₗ[Tower] Message Tower :=
  (alignedReserveEmbed Tower).comp deployedAConversion

theorem deployedAEncoder_supported : EncoderOutputsAlignedReserve deployedAEncoder :=
  alignedReserveEmbed_comp_supported deployedAConversion

/-- Big-endian bit: coordinate zero is row bit nine. -/
def bigEndianBit (row : Fin traceRows) (coordinate : Fin 10) : Bool :=
  Nat.testBit (row : ℕ) (9 - (coordinate : ℕ))

/-- Equality-polynomial weight of one physical message row. -/
def mleRowWeight {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (row : Fin traceRows) : K :=
  ∏ coordinate, if bigEndianBit row coordinate then point coordinate
    else 1 - point coordinate

/-- The value underlying the literal big-endian multilinear fold.  Naming it
separately keeps application proofs from unfolding the linear-map structure. -/
noncomputable def multilinearEvalValue
    {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (message : Message K) : K :=
  ∑ row, mleRowWeight point row * message row

/-- Literal big-endian multilinear evaluation used by the Rust fold. -/
noncomputable def multilinearEvalAt
    {K : Type*} [CommRing K] (point : TranscriptPoint K) :
    Message K →ₗ[K] K :=
  ∑ row : Fin traceRows,
    (mleRowWeight point row) •
      (LinearMap.proj row : Message K →ₗ[K] K)

@[simp] theorem multilinearEvalAt_apply
    (point : TranscriptPoint Tower) (message : Message Tower) :
    multilinearEvalAt point message = multilinearEvalValue point message := by
  simp only [multilinearEvalAt, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, multilinearEvalValue]

/-- Carry entering one coordinate of the polynomial binary successor. -/
def successorCarry {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (coordinate : Fin 10) : K :=
  ∏ later ∈ Finset.univ.filter (fun later : Fin 10 => coordinate < later), point later

/-- Exact polynomial binary increment used by host and verifier. -/
def deployedSuccessorPoint {K : Type*} [CommRing K]
    (point : TranscriptPoint K) : TranscriptPoint K :=
  fun coordinate =>
    let carry := successorCarry point coordinate
    let product := point coordinate * carry
    point coordinate + carry - (product + product)

/-- Exact toggle of row-index bits two and three. -/
def deployedXor12Point {K : Type*} [CommRing K]
    (point : TranscriptPoint K) : TranscriptPoint K :=
  fun coordinate => if coordinate = 6 ∨ coordinate = 7 then 1 - point coordinate
    else point coordinate

def deployedRelationPoint {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (which : Fin 3) : TranscriptPoint K :=
  ![point, deployedSuccessorPoint point, deployedXor12Point point] which

/-- Three point-major MLE values on one physical message. -/
noncomputable def deployedMessageTerminal
    {K : Type*} [CommRing K] (point : TranscriptPoint K) :
    Message K →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun which => multilinearEvalAt (deployedRelationPoint point which)

@[simp] theorem deployedMessageTerminal_apply
    (point : TranscriptPoint Tower) (message : Message Tower) (which : Fin 3) :
    deployedMessageTerminal point message which =
      multilinearEvalAt (deployedRelationPoint point which) message := by
  exact LinearMap.pi_apply
    (fun which => multilinearEvalAt (deployedRelationPoint point which))
    message which

/-- Generic terminal composition, separated so its application theorem remains
abstract in the field rather than unfolding the concrete QM31 tower. -/
noncomputable def terminalAfterEncoder
    {K : Type*} [Field K]
    (encode : (Fin originalWidth → K) →ₗ[K] Message K)
    (point : TranscriptPoint K) :
    (Fin originalWidth → K) →ₗ[K] (Fin 3 → K) :=
  (deployedMessageTerminal point).comp encode

@[simp] theorem terminalAfterEncoder_apply
    (encode : TowerSource →ₗ[Tower] Message Tower)
    (point : TranscriptPoint Tower) (coins : TowerSource) :
    terminalAfterEncoder encode point coins =
      deployedMessageTerminal point (encode coins) := by
  simp only [terminalAfterEncoder, LinearMap.comp_apply]

/-- The actual fixed public terminal model after conversion and interleaving. -/
noncomputable def deployedTerminalModel : PublicTerminalModel Tower :=
  fun point => terminalAfterEncoder deployedAEncoder point

@[simp] theorem deployedTerminalModel_apply
    (point : TranscriptPoint Tower) (coins : TowerSource) :
    deployedTerminalModel point coins =
      deployedMessageTerminal point (deployedAEncoder coins) := by
  change terminalAfterEncoder deployedAEncoder point coins =
    deployedMessageTerminal point (deployedAEncoder coins)
  exact terminalAfterEncoder_apply deployedAEncoder point coins

/-! ## Literal QM31-to-M31 coordinate expansion -/

def towerCoordinates (value : Tower) : Fin 4 → Base :=
  ![value.re.re, value.re.im, value.im.re, value.im.im]

def towerCoordinatesLinear : Tower →ₗ[Base] (Fin 4 → Base) where
  toFun := towerCoordinates
  map_add' left right := by
    funext limb
    fin_cases limb <;> rfl
  map_smul' scalar value := by
    funext limb
    fin_cases limb <;> simp [towerCoordinates]

theorem towerCoordinates_injective : Function.Injective towerCoordinates := by
  intro left right equal
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact congrFun equal 0
    · exact congrFun equal 1
  · apply QuadraticAlgebra.ext
    · exact congrFun equal 2
    · exact congrFun equal 3

def terminalCoordinatesLinear :
    (Fin 3 → Tower) →ₗ[Base] (TerminalLimb → Base) where
  toFun values output := towerCoordinates (values output.1) output.2
  map_add' left right := by
    funext output
    rcases output with ⟨point, limb⟩
    fin_cases limb <;> rfl
  map_smul' scalar value := by
    funext output
    rcases output with ⟨point, limb⟩
    fin_cases limb <;> simp [towerCoordinates]

theorem terminalCoordinatesLinear_injective :
    Function.Injective terminalCoordinatesLinear := by
  intro left right equal
  funext point
  apply towerCoordinates_injective
  funext limb
  exact congrFun equal (point, limb)

/-- Coefficientwise base-to-tower inclusion as a base-linear map. -/
def liftBaseCoinsLinear : Source →ₗ[Base] TowerSource :=
  LinearMap.pi fun i =>
    (Algebra.linearMap Base Tower).comp (LinearMap.proj i)

@[simp] theorem liftBaseCoinsLinear_apply (coins : Source) :
    liftBaseCoinsLinear coins = liftBaseCoins coins := by
  rfl

/-- The exact twelve-M31-coordinate terminal map on actual base-field coins. -/
noncomputable def deployedTerminalLimbMap (point : TranscriptPoint Tower) :
    Source →ₗ[Base] (TerminalLimb → Base) :=
  terminalCoordinatesLinear.comp
    (((deployedTerminalModel point).restrictScalars Base).comp liftBaseCoinsLinear)

theorem deployedTerminalLimbMap_apply (point : TranscriptPoint Tower)
    (coins : Source) (output : TerminalLimb) :
    deployedTerminalLimbMap point coins output =
      towerCoordinates
        (deployedTerminalModel point (liftBaseCoins coins) output.1) output.2 := by
  simp only [deployedTerminalLimbMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, terminalCoordinatesLinear,
    liftBaseCoinsLinear_apply]
  rfl

theorem deployedTerminalLimbMap_eq_coordinates
    (point : TranscriptPoint Tower) (coins : Source) :
    deployedTerminalLimbMap point coins =
      terminalCoordinatesLinear
        (deployedTerminalModel point (liftBaseCoins coins)) := by
  ext output
  rw [deployedTerminalLimbMap_apply]
  rfl

/-! ## The exact public 12-by-22 minor predicate -/

noncomputable def terminalDirectionMatrix
    (schedule : PublicTerminalSchedule Tower) : Matrix TerminalLimb Direction Base :=
  fun output direction =>
    deployedTerminalLimbMap schedule.point
      (kernelDirection schedule.q18 direction) output

def terminalLimbIndex (output : TerminalLimb) : Fin 12 :=
  ⟨4 * (output.1 : ℕ) + (output.2 : ℕ), by
    have hpoint := output.1.isLt
    have hlimb := output.2.isLt
    omega⟩

/-- The first twelve directions in block-major order: all eleven x/p shifts,
then the first y/q shift. -/
def fixedFirstTwelveDirection (output : TerminalLimb) : Direction :=
  if h : (terminalLimbIndex output : ℕ) < 11 then
    (0, ⟨terminalLimbIndex output, h⟩)
  else
    (1, 0)

noncomputable def selectedTerminalMinor
    (schedule : PublicTerminalSchedule Tower) :
    Matrix TerminalLimb TerminalLimb Base :=
  (terminalDirectionMatrix schedule).submatrix id fixedFirstTwelveDirection

/-- Public sufficient predicate: the fixed first-twelve-column minor of the
exact deployed terminal image of the 22 legal directions has nonzero
determinant. -/
def GoodA (schedule : PublicTerminalSchedule Tower) : Prop :=
  (selectedTerminalMinor schedule).det ≠ 0

noncomputable def goodADecision (schedule : PublicTerminalSchedule Tower) :
    Decidable (GoodA schedule) := by
  unfold GoodA
  letI : DecidableEq Base := ZMod.decidableEq _
  exact inferInstance

/-- Boolean form of the finite determinant gate. -/
noncomputable def goodABool (schedule : PublicTerminalSchedule Tower) : Bool :=
  @decide (GoodA schedule) (goodADecision schedule)

theorem goodABool_eq_true_iff (schedule : PublicTerminalSchedule Tower) :
    goodABool schedule = true ↔ GoodA schedule := by
  letI : Decidable (GoodA schedule) := goodADecision schedule
  change decide (GoodA schedule) = true ↔ GoodA schedule
  exact Bool.decide_iff (GoodA schedule)

/-- Embed the twelve fixed-minor coefficients into all 22 directions. -/
def selectionMatrix : Matrix Direction TerminalLimb Base :=
  fun direction output => if direction = fixedFirstTwelveDirection output then 1 else 0

theorem terminalDirectionMatrix_mul_selectionMatrix
    (schedule : PublicTerminalSchedule Tower) :
    terminalDirectionMatrix schedule * selectionMatrix =
      selectedTerminalMinor schedule := by
  ext output column
  simp [Matrix.mul_apply, selectionMatrix, selectedTerminalMinor]

theorem terminalDirectionMatrix_mulVec
    (schedule : PublicTerminalSchedule Tower) (coefficients : Direction → Base) :
    (terminalDirectionMatrix schedule).mulVec coefficients =
      deployedTerminalLimbMap schedule.point
        (∑ direction, coefficients direction • kernelDirection schedule.q18 direction) := by
  funext output
  simp only [Matrix.mulVec, dotProduct, terminalDirectionMatrix, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun direction _ => mul_comm _ _

theorem goodA_implies_exactTerminalRankPredicate
    (weightModel : PublicWeightModel)
    (schedule : PublicTerminalSchedule Tower)
    (hgood : GoodA schedule) :
    ExactTerminalRankPredicate weightModel deployedTerminalModel schedule := by
  have hminorUnit : IsUnit (selectedTerminalMinor schedule) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hgood)
  have hminorSurjective : Function.Surjective
      (selectedTerminalMinor schedule).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hminorUnit
  intro target
  let targetCoordinates : TerminalLimb → Base :=
    terminalCoordinatesLinear target
  obtain ⟨minorCoefficients, hminor⟩ := hminorSurjective targetCoordinates
  let A : Matrix TerminalLimb Direction Base := terminalDirectionMatrix schedule
  let S : Matrix Direction TerminalLimb Base := selectionMatrix
  let M : Matrix TerminalLimb TerminalLimb Base := selectedTerminalMinor schedule
  have hAS : A * S = M := by
    simpa only [A, S, M] using terminalDirectionMatrix_mul_selectionMatrix schedule
  have hminorM : M.mulVec minorCoefficients = targetCoordinates := by
    simpa only [M] using hminor
  let coefficients : Direction → Base :=
    S.mulVec minorCoefficients
  let coins : Source :=
    ∑ direction, coefficients direction • kernelDirection schedule.q18 direction
  have hcoordinates :
      deployedTerminalLimbMap schedule.point coins = targetCoordinates := by
    rw [← terminalDirectionMatrix_mulVec]
    change A.mulVec (S.mulVec minorCoefficients) = targetCoordinates
    calc
      A.mulVec (S.mulVec minorCoefficients) =
          (A * S).mulVec minorCoefficients :=
        Matrix.mulVec_mulVec minorCoefficients A S
      _ = M.mulVec minorCoefficients := by rw [hAS]
      _ = targetCoordinates := hminorM
  refine ⟨coins, ?_, ?_, ?_⟩
  · change coefficientSum coins = 0
    simp only [coins, map_sum, map_smul, kernelDirection_sum_zero, smul_zero,
      Finset.sum_const_zero]
  · change (deployedFibreRectangularEval schedule.q18
      (weightModel schedule.q18)).mulVec coins = 0
    change (deployedFibreRectangularEval schedule.q18
      (weightModel schedule.q18)).mulVecLin coins = 0
    change (deployedFibreRectangularEval schedule.q18
      (weightModel schedule.q18)).mulVecLin
        (∑ direction, coefficients direction •
          kernelDirection schedule.q18 direction) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro direction _
    rw [map_smul, Matrix.mulVecLin_apply,
      kernelDirection_mulVec_zero, smul_zero]
  · apply terminalCoordinatesLinear_injective
    rw [← deployedTerminalLimbMap_eq_coordinates]
    exact hcoordinates

/-- Passing the finite public minor gate supplies the exact terminal-kernel
coverage premise consumed by the existing Component-A capstone. -/
theorem goodA_implies_deployedTerminalCoverage
    (weightModel : PublicWeightModel)
    (schedule : PublicTerminalSchedule Tower)
    (hgood : GoodA schedule) :
    EqTerminalTripleCoversDeployedKernel schedule.q18
      (weightModel schedule.q18) (deployedTerminalModel schedule.point) :=
  accepted_implies_terminal_coverage weightModel deployedTerminalModel schedule
    (goodA_implies_exactTerminalRankPredicate weightModel schedule hgood)

/-- `GoodA` has no witness argument: equal public q18/point schedules receive
the same answer. -/
theorem goodA_public_ext
    {left right : PublicTerminalSchedule Tower} (hpublic : left = right) :
    GoodA left ↔ GoodA right := by
  subst right
  exact Iff.rfl

/-! ## Retained all-zero regression tooth -/

/-- The existing all-zero support counterexample, specialized to the exact
ordinary-to-natural conversion and aligned Component-A encoder. -/
theorem deployed_allZero_reserved_counterexample
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (weight : FibreIndex → Base) :
    ¬ EqTerminalTripleCoversDeployedKernel queries weight
      (inducedDegenerateEqTriple deployedAEncoder) := by
  simpa only [deployedAEncoder] using
    (allZero_reserved_conversion_counterexample_retained
      queries weight deployedAConversion)

/-- Every one of the three deployed relation points has coordinate zero equal
to zero at the all-zero transcript point. -/
theorem deployedRelationPoint_allZero_coordinate_zero (which : Fin 3) :
    deployedRelationPoint (allZeroPoint Tower) which 0 = 0 := by
  fin_cases which
  · rfl
  · change deployedSuccessorPoint (allZeroPoint Tower) 0 = 0
    have hcarry : successorCarry (allZeroPoint Tower) 0 = 0 := by
      rw [successorCarry]
      apply Finset.prod_eq_zero (i := (1 : Fin 10))
      · simp
      · rfl
    simp [deployedSuccessorPoint, allZeroPoint, hcarry]
  · change deployedXor12Point (allZeroPoint Tower) 0 = 0
    simp [deployedXor12Point, allZeroPoint]

/-- Physical rows inside the aligned reserve have big-endian coordinate zero
set: it is numeric bit nine of every row in the half-open interval 896 to 992. -/
theorem reserveRow_bigEndianBit_zero
    (row : Fin traceRows)
    (hlow : reserveStart ≤ (row : ℕ))
    (hhigh : (row : ℕ) < reserveStart + reserveWidth) :
    bigEndianBit row 0 = true := by
  change Nat.testBit (row : ℕ) 9 = true
  have hpow : 2 ^ 9 ≤ (row : ℕ) := by
    norm_num [reserveStart] at hlow ⊢
    omega
  have htail : (row : ℕ) - 2 ^ 9 < 2 ^ 9 := by
    norm_num [reserveStart, reserveWidth] at hhigh ⊢
    omega
  have hsplit : (row : ℕ) = 2 ^ 9 + ((row : ℕ) - 2 ^ 9) := by
    omega
  rw [hsplit, Nat.testBit_two_pow_add_eq,
    Nat.testBit_eq_false_of_lt htail]
  rfl

/-- At zero, every relation-point MLE weight vanishes on every aligned-reserve
row, using only coordinate zero of the product. -/
theorem mleRowWeight_relation_allZero_zero_on_reserve
    (which : Fin 3) (row : Fin traceRows)
    (hlow : reserveStart ≤ (row : ℕ))
    (hhigh : (row : ℕ) < reserveStart + reserveWidth) :
    mleRowWeight (deployedRelationPoint (allZeroPoint Tower) which) row = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 10))
  rw [if_pos (reserveRow_bigEndianBit_zero row hlow hhigh)]
  exact deployedRelationPoint_allZero_coordinate_zero which

/-- Every supported message has zero MLE value at each of the three deployed
all-zero relation points. -/
theorem multilinearEvalAt_relation_allZero_zero_of_supported
    (which : Fin 3) (message : Message Tower)
    (hsupport : SupportedOnAlignedReserve message) :
    multilinearEvalAt
      (deployedRelationPoint (allZeroPoint Tower) which) message = 0 := by
  rw [multilinearEvalAt_apply]
  unfold multilinearEvalValue
  apply Finset.sum_eq_zero
  intro row _
  by_cases houtside :
      (row : ℕ) < reserveStart ∨ reserveStart + reserveWidth ≤ (row : ℕ)
  · rw [hsupport row houtside, mul_zero]
  · have hlow : reserveStart ≤ (row : ℕ) :=
      Nat.le_of_not_gt (fun h => houtside (Or.inl h))
    have hhigh : (row : ℕ) < reserveStart + reserveWidth :=
      Nat.lt_of_not_ge (fun h => houtside (Or.inr h))
    rw [mleRowWeight_relation_allZero_zero_on_reserve which row hlow hhigh,
      zero_mul]

theorem deployedMessageTerminal_allZero_zero_of_supported
    (message : Message Tower) (hsupport : SupportedOnAlignedReserve message) :
    deployedMessageTerminal (allZeroPoint Tower) message = 0 := by
  funext which
  rw [Pi.zero_apply, deployedMessageTerminal_apply]
  exact multilinearEvalAt_relation_allZero_zero_of_supported
    which message hsupport

/-- The actual deployed encoder's terminal image is zero at the all-zero
point, independently of the ordinary-to-natural conversion entries. -/
theorem deployedTerminalModel_allZero_apply_zero (coins : TowerSource) :
    deployedTerminalModel (allZeroPoint Tower) coins = 0 := by
  rw [deployedTerminalModel_apply]
  exact deployedMessageTerminal_allZero_zero_of_supported
    (deployedAEncoder coins) (deployedAEncoder_supported coins)

/-- The exact public minor gate unconditionally rejects the all-zero
ten-round point for every public q18 schedule. -/
theorem deployed_allZero_goodA_rejected
    (queries : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount) :
    ¬ GoodA (allZeroSchedule queries) := by
  intro hgood
  let zeroWeightModel : PublicWeightModel := fun _ _ => 0
  have haccepted := goodA_implies_exactTerminalRankPredicate zeroWeightModel
    (allZeroSchedule queries) hgood
  let target : Fin 3 → Tower := fun which => if which = 0 then 1 else 0
  obtain ⟨coins, _, _, hterminal⟩ := haccepted target
  have hzero := deployedTerminalModel_allZero_apply_zero (liftBaseCoins coins)
  have hcoordinate := congrFun hterminal (0 : Fin 3)
  have hzeroCoordinate := congrFun hzero (0 : Fin 3)
  have hschedulePoint :
      (allZeroSchedule (L := Tower) queries).point = allZeroPoint Tower := rfl
  rw [hschedulePoint] at hcoordinate
  rw [hzeroCoordinate] at hcoordinate
  simp only [Pi.zero_apply, target, if_pos] at hcoordinate
  exact zero_ne_one hcoordinate

/-! ## Kernel-checked concrete public nonvacuity witness -/

namespace ConcreteProbeWitness

/-- Literal four-limb constructor in Rust `(c0.a,c0.b,c1.a,c1.b)` order. -/
def ofLimbs (c0a c0b c1a c1b : Base) : Tower :=
  ⟨⟨c0a, c0b⟩, ⟨c1a, c1b⟩⟩

/-- Total constructor for public fibre constants.  Every literal below is
strictly below `fibreCount`; the modulo is therefore extensionally inert. -/
def fibreLiteral (value : ℕ) :
    Fin AspisCircleDiscreteAvailability.fibreCount :=
  ⟨value % AspisCircleDiscreteAvailability.fibreCount,
    Nat.mod_lt value (by
      norm_num [AspisCircleDiscreteAvailability.fibreCount])⟩

/-- Natural representative q18 printed by the current selector-zero public
probe. -/
def naturalQ18 :
    Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount :=
  ![fibreLiteral 94535, fibreLiteral 99494, fibreLiteral 75565,
    fibreLiteral 74538, fibreLiteral 52121, fibreLiteral 76097,
    fibreLiteral 112249, fibreLiteral 110002, fibreLiteral 73563,
    fibreLiteral 30889, fibreLiteral 47857, fibreLiteral 94766,
    fibreLiteral 31621, fibreLiteral 100579, fibreLiteral 54037,
    fibreLiteral 61143, fibreLiteral 70991, fibreLiteral 58721]

/-- Ten exact public QM31 challenges printed by the same public probe, in
deployed limb order. -/
def probePoint : TranscriptPoint Tower :=
  ![ofLimbs 404107582 1727074950 929436228 337050246,
    ofLimbs 1551059663 276722441 1042656822 513863785,
    ofLimbs 164049145 1996763382 1728701267 1725471872,
    ofLimbs 1579020738 1603896284 1206833734 1303440574,
    ofLimbs 444095533 1733870221 271870451 46368227,
    ofLimbs 1281619349 328022466 1429624261 972991110,
    ofLimbs 1204014726 1716417842 1524198052 774277607,
    ofLimbs 1082422057 694365077 591158920 1683812251,
    ofLimbs 1577214774 1016671131 411456236 1648869862,
    ofLimbs 758441825 1940717419 1517866177 737596238]

/-- The public schedule represented by the current selector-zero probe. -/
def concreteSchedule : PublicTerminalSchedule Tower where
  q18 := naturalQ18
  point := probePoint

/-- Point-major, then limb-major ordinal used by the printed Rust matrix. -/
def terminalLimbOrdinal (output : TerminalLimb) : Fin 12 :=
  terminalLimbIndex output

/-- Exact 12-by-12 M31 matrix printed by the current public probe. -/
def printedTerminalMatrixFin : Matrix (Fin 12) (Fin 12) Base :=
  ![![478933871, 1389306168, 1301508847, 601113137,
      1343064338, 1116107897, 538315754, 208360263,
      1619472116, 1226019598, 422135760, 1423216147],
    ![513823415, 1128317070, 478783203, 491820112,
      1663526088, 1108316311, 1683940281, 251046859,
      130572886, 570517234, 1499570247, 48852529],
    ![1362468244, 264300151, 1435388776, 1697501892,
      1686929892, 1301551981, 1352208899, 775121542,
      1410083153, 1095277642, 166362380, 267574853],
    ![1098962808, 609194254, 2126440640, 353607599,
      1020076395, 1811117627, 443708284, 1489519528,
      433151634, 755881888, 963533458, 2071033599],
    ![1595969664, 393999516, 1395352878, 438605900,
      857312908, 1879763202, 1224249377, 2040748501,
      645394943, 1898127716, 1030972322, 994411103],
    ![1132164920, 2053621945, 1022434451, 1539148183,
      1420907131, 1295171113, 374496010, 1866729958,
      1073579588, 2064159009, 548050728, 1931373637],
    ![1170000740, 1887260042, 1617024355, 1579797109,
      81616899, 1483738249, 210169269, 492665207,
      563015342, 1522742364, 1371280460, 1653655386],
    ![435053671, 803250683, 434008863, 1524952018,
      171243022, 474171660, 1831492465, 1557070114,
      1205148058, 32644510, 1607857114, 417531636],
    ![845922390, 1405338316, 1503773937, 1612209634,
      1326207377, 2099734683, 1827704055, 1578902566,
      1046416700, 541230732, 1219268093, 780505556],
    ![52240688, 840593458, 620201061, 503657710,
      1257098218, 1042118120, 649053095, 375490688,
      1025554698, 1009494594, 900838602, 520035018],
    ![1102552152, 565947668, 2046331480, 2043436497,
      1394058347, 1948571232, 175563703, 2139482202,
      2016739051, 1411298040, 1076631, 1511589546],
    ![140626554, 970617680, 1383172367, 731297219,
      831824231, 519396000, 1942619378, 359211631,
      2005256770, 2015081168, 255765726, 1480652075]]

/-- Kernel-checked inverse of the printed probe matrix. -/
def printedTerminalInverseFin : Matrix (Fin 12) (Fin 12) Base :=
  ![![413593211, 951276504, 1677853204, 1256190779,
      1991296288, 29845352, 522714608, 545926163,
      66051276, 994769081, 2079986264, 496536554],
    ![1775628546, 154965322, 1460925696, 1303893947,
      259713302, 485673072, 1802231322, 1181722692,
      1009712019, 1228775618, 2104917132, 84568041],
    ![46926262, 1031666020, 655699360, 176476521,
      2013368027, 770886489, 701787669, 2113906471,
      655124568, 671949360, 829845320, 756975008],
    ![639610348, 1393458371, 121565713, 2110872490,
      444129842, 954760803, 1915926845, 1181485648,
      440467001, 669638695, 884085314, 1673721031],
    ![1081346733, 1528817403, 574431101, 655973377,
      663741352, 254075315, 1249174728, 642493899,
      1525064310, 1773680636, 25228767, 838461393],
    ![45215619, 1668035775, 23359902, 2026138003,
      415419976, 873153785, 1739002213, 1773365692,
      892726844, 1984935690, 754670405, 1505931075],
    ![1794416256, 699603300, 853805287, 497051030,
      535573372, 235312589, 1337864493, 1824142594,
      1288795523, 1032292019, 1730847232, 1575366103],
    ![1150263716, 2012013692, 956831825, 1206332539,
      1796354929, 645604145, 1521444267, 754640372,
      2115955341, 528746336, 114859159, 1045369222],
    ![927322754, 582750220, 1746438331, 1622295238,
      1748374495, 1244644887, 55922730, 1688311783,
      881454147, 1784613206, 1063400652, 1554883001],
    ![2144207993, 1775576279, 1573645585, 805265508,
      1112225288, 924540505, 606803955, 1928825714,
      1398277533, 342265467, 908121131, 686162535],
    ![1030143012, 1684653777, 1809255447, 1299281417,
      1998777149, 157282417, 1805745786, 302377507,
      866737749, 688270038, 365960173, 843063639],
    ![1301891631, 1888592675, 1711217475, 1773110786,
      667219036, 624252581, 998505065, 1535120072,
      502243345, 1947873667, 146774292, 897253934]]

/-- Reindex the printed point-major matrix by the deployed terminal-limb type. -/
def printedTerminalMatrix : Matrix TerminalLimb TerminalLimb Base :=
  fun row column =>
    printedTerminalMatrixFin (terminalLimbOrdinal row)
      (terminalLimbOrdinal column)

/-- Reindex the printed inverse by the deployed terminal-limb type. -/
def printedTerminalInverse : Matrix TerminalLimb TerminalLimb Base :=
  fun row column =>
    printedTerminalInverseFin (terminalLimbOrdinal row)
      (terminalLimbOrdinal column)

/-- Exact finite Rust-to-Lean equality still required to turn the printed
regression matrix into a concrete mathematical acceptance certificate.  It is
a named premise, not an axiom and not inferred from the public probe. -/
def ConcreteProbeTerminalMatrixEquality : Prop :=
  selectedTerminalMinor concreteSchedule = printedTerminalMatrix

/-- Independent default-limit kernel check of all 144 matrix-product entries. -/
theorem printedTerminalMatrix_mul_inverse :
    printedTerminalMatrix * printedTerminalInverse = 1 := by
  decide

theorem printedTerminalMatrix_det_ne_zero :
    printedTerminalMatrix.det ≠ 0 := by
  have hunit : IsUnit printedTerminalMatrix :=
    IsUnit.of_mul_eq_one printedTerminalInverse
      printedTerminalMatrix_mul_inverse
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det printedTerminalMatrix).mp hunit)

/-- The exact matrix equality implies that the concrete public schedule passes
the sufficient deployed terminal-rank predicate.  The equality remains an
explicit Rust↔Lean correspondence premise. -/
theorem concreteProbe_goodA_of_terminal_matrix_equality
    (hequality : ConcreteProbeTerminalMatrixEquality) :
    GoodA concreteSchedule := by
  unfold GoodA
  rw [hequality]
  exact printedTerminalMatrix_det_ne_zero

end ConcreteProbeWitness


/-! ## Honest executable boundaries -/

namespace UnmetDeployment

/-- Convert the stored Merkle-layer index into the natural fibre index used by
the Lean circle representatives.  Rust computes the same operation as
`stored.reverse_bits() >> 15` on a `u32`. -/
def normalizeStoredFibreIndex
    (stored : Fin AspisCircleDiscreteAvailability.fibreCount) :
    Fin AspisCircleDiscreteAvailability.fibreCount :=
  ⟨(BitVec.ofNat 17 stored).reverse.toNat, by
    change (BitVec.ofNat 17 stored).reverse.toNat < 2 ^ 17
    exact (BitVec.ofNat 17 stored).reverse.isLt⟩

/-- Rust's 48-by-48 conversion table and orientation equal the canonical
`monomialToNatural` table used above. -/
def RustConversionAndInterleaveMatch
    (rustEncode : TowerSource →ₗ[Tower] Message Tower) : Prop :=
  rustEncode = deployedAEncoder

/-- Rust's reverse-coordinate fold and point transforms equal the exact
big-endian model above. -/
def RustThreePointMLEMatches
    (rustTerminal : TranscriptPoint Tower →
      Message Tower →ₗ[Tower] (Fin 3 → Tower)) : Prop :=
  rustTerminal = deployedMessageTerminal

/-- The bit-reversal-normalized runtime q18 and terminal point equal the
public schedule checked by Lean.  Direct equality with the stored Merkle
indices would use the wrong representative convention. -/
def RuntimeScheduleMatches
    (runtimeStoredQ18 : Fin AspisCircleDiscreteAvailability.queryCount →
      Fin AspisCircleDiscreteAvailability.fibreCount)
    (runtimePoint : TranscriptPoint Tower)
    (schedule : PublicTerminalSchedule Tower) : Prop :=
  (fun query => normalizeStoredFibreIndex (runtimeStoredQ18 query)) = schedule.q18 ∧
    runtimePoint = schedule.point

/-- The verifier computes the exact finite predicate and accepts exactly its
true branch.  No theorem in this file asserts that the current verifier does. -/
def VerifierEnforcesGoodA
    (verifierAccepts : PublicTerminalSchedule Tower → Prop) : Prop :=
  ∀ schedule, verifierAccepts schedule ↔ GoodA schedule

end UnmetDeployment

/-! ## Axiom audit -/

#print axioms direction_card
#print axioms terminalLimb_card
#print axioms polynomialBlock_sum_eq_eval_one
#print axioms ordinaryPolynomialDirection_sum
#print axioms ordinaryPolynomialDirection_one_apply
#print axioms kernelDirection_sum_zero
#print axioms mulVec_ordinaryPolynomialDirection_one
#print axioms kernelDirection_mulVec_zero
#print axioms omittedCrossBlockDirection_sum_zero
#print axioms omittedCrossBlockDirection_mulVec_zero
#print axioms deployedAEncoder_supported
#print axioms multilinearEvalAt_apply
#print axioms deployedMessageTerminal_apply
#print axioms terminalAfterEncoder_apply
#print axioms deployedTerminalModel_apply
#print axioms towerCoordinates_injective
#print axioms terminalCoordinatesLinear_injective
#print axioms liftBaseCoinsLinear_apply
#print axioms deployedTerminalLimbMap_apply
#print axioms deployedTerminalLimbMap_eq_coordinates
#print axioms terminalDirectionMatrix_mul_selectionMatrix
#print axioms terminalDirectionMatrix_mulVec
#print axioms goodABool_eq_true_iff
#print axioms goodA_implies_exactTerminalRankPredicate
#print axioms goodA_implies_deployedTerminalCoverage
#print axioms goodA_public_ext
#print axioms deployed_allZero_reserved_counterexample
#print axioms deployedRelationPoint_allZero_coordinate_zero
#print axioms reserveRow_bigEndianBit_zero
#print axioms mleRowWeight_relation_allZero_zero_on_reserve
#print axioms multilinearEvalAt_relation_allZero_zero_of_supported
#print axioms deployedMessageTerminal_allZero_zero_of_supported
#print axioms deployedTerminalModel_allZero_apply_zero
#print axioms deployed_allZero_goodA_rejected
#print axioms ConcreteProbeWitness.printedTerminalMatrix_mul_inverse
#print axioms ConcreteProbeWitness.printedTerminalMatrix_det_ne_zero
#print axioms ConcreteProbeWitness.concreteProbe_goodA_of_terminal_matrix_equality

end AspisV5ComponentADeployedTerminalApplicability
