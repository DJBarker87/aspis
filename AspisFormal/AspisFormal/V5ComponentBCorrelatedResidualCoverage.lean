import AspisFormal.V5FreezeBTranscriptAuthentication
import AspisFormal.V5InactiveClaimDeployedCorrespondence
import AspisFormal.V5ComponentARankCompletion

/-!
# Component-B correlated residual coverage on the deployed structured layout

This closure attempt transcribes the live Component-B shape rather than the
older 1,024-coordinate diagnostic commitment:

* 271 state coordinates, ordered as the initial claim followed by ten blocks
  of 27 freely sampled tail coefficients;
* 255 pad coordinates at physical rows 224 through 478;
* one caller-owned pivot scalar, written dependently at row 993 so the
  copy-inactive functional equals that scalar;
* the independent residual target in the order
  `inactive || 72 q18 values || 3 point-major MLE values`.

The attempted universal rank-76 gate is false even at the concrete Boolean
point with big-endian row ordinal 976.  Its relation points read rows 976,
977 and 988.  Those rows are disjoint from both the 255 pad rows 224--478 and
the dependent pivot row 993, so the complete residual map has rank at most
73, independently of the circle encoder and independently of the inactive
covector.  The counterexample uses the existing injective `sampleQueries`
q18 schedule.  This is a structural counterexample, not a diagnostic rank
vector.  The all-zero point is retained below as a separate local tooth.

The exact equality between the transcribed definitions and the Rust encoder,
parser, transcript and field codec remains an executable-correspondence
premise.  Computational PCS/Merkle binding and Fiat--Shamir hash/RO behavior
remain external cryptographic assumptions.  Neither kind of premise can turn
the false universal rank statement into a theorem.
-/

namespace AspisV5ComponentBCorrelatedResidualCoverage

open AspisV5CompactTerminal
open AspisV5ComponentBTriangularHiding
open AspisV5InactiveClaimJointHiding
open AspisV5SumcheckTranscriptBinding
open AspisV5CompleteView

/-! ## Exact finite coordinate types and orders -/

abbrev StateCoordinate := Unit ⊕ (Round × TailDegree)
abbrev PadCoordinate := Fin 255
abbrev QueryCoordinate := Fin 18
abbrev FibreSlot := Fin 4
abbrev RawCoordinate := QueryCoordinate × FibreSlot
abbrev MLECoordinate := Fin 3
abbrev ResidualCoordinate := Unit ⊕ (RawCoordinate ⊕ MLECoordinate)

abbrev Message (K : Type*) := Row → K
abbrev StateSample (K : Type*) := K × (Round → TailDegree → K)
abbrev PadVector (K : Type*) := PadCoordinate → K
abbrev PadSample (K : Type*) := PadVector K × K
abbrev ResidualView (K : Type*) :=
  K × (RawCoordinate → K) × (MLECoordinate → K)
abbrev ReducedResidualView (K : Type*) := K × (RawCoordinate → K)

/-- The exact cardinalities used by the live structured B lane. -/
theorem exact_coordinate_counts :
    Fintype.card StateCoordinate = 271 ∧
      Fintype.card PadCoordinate = 255 ∧
      Fintype.card RawCoordinate = 72 ∧
      Fintype.card MLECoordinate = 3 ∧
      Fintype.card ResidualCoordinate = 76 := by
  norm_num [AspisV5SumcheckCommitment.roundCount,
    AspisV5SumcheckCommitment.tailCount]

/-- State serialization order: initial first, then round-major and
degree-major tails. -/
def stateWireOrdinal : StateCoordinate → Fin 271
  | .inl _ => ⟨0, by omega⟩
  | .inr (round, degree) =>
      ⟨1 + 27 * (round : ℕ) + (degree : ℕ), by
        have hr := round.isLt
        have hd := degree.isLt
        simp only [AspisV5SumcheckCommitment.roundCount] at hr
        simp only [AspisV5SumcheckCommitment.tailCount] at hd
        omega⟩

@[simp] theorem stateWireOrdinal_initial :
    stateWireOrdinal (.inl ()) = 0 := rfl

@[simp] theorem stateWireOrdinal_tail_val (round : Round) (degree : TailDegree) :
    (stateWireOrdinal (.inr (round, degree)) : ℕ) =
      1 + 27 * (round : ℕ) + (degree : ℕ) := rfl

theorem stateWireOrdinal_injective : Function.Injective stateWireOrdinal := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right => simp
      | inr right =>
          exfalso
          have hval := congrArg Fin.val equal
          simp only [stateWireOrdinal] at hval
          omega
  | inr left =>
      cases right with
      | inl right =>
          exfalso
          have hval := congrArg Fin.val equal
          simp only [stateWireOrdinal] at hval
          omega
      | inr right =>
          rcases left with ⟨leftRound, leftDegree⟩
          rcases right with ⟨rightRound, rightDegree⟩
          have hval := congrArg Fin.val equal
          simp only [stateWireOrdinal] at hval
          have hlr := leftRound.isLt
          have hrr := rightRound.isLt
          have hld := leftDegree.isLt
          have hrd := rightDegree.isLt
          simp only [AspisV5SumcheckCommitment.roundCount] at hlr hrr
          simp only [AspisV5SumcheckCommitment.tailCount] at hld hrd
          have hround : leftRound = rightRound := by
            apply Fin.ext
            omega
          have hdegree : leftDegree = rightDegree := by
            apply Fin.ext
            omega
          rw [hround, hdegree]

/-- Physical row of every freely sampled state coordinate.  The ten derived
constant coefficients at block offset zero are deliberately absent. -/
def stateRow : StateCoordinate → Row
  | .inl _ => initialRow
  | .inr (round, degree) => coefficientRow (round, degree.succ)

/-- Value represented by one state coordinate. -/
def stateValue {K : Type*} (state : StateSample K) : StateCoordinate → K
  | .inl _ => state.1
  | .inr (round, degree) => state.2 round degree

/-- The existing exact row-message definition recovers all 271 state
coordinates at the transcribed rows. -/
theorem rowMessage_recovers_state {K : Type*} [Field K]
    (state : StateSample K) (coordinate : StateCoordinate) :
    rowMessage state.1 state.2 (stateRow coordinate) =
      stateValue state coordinate := by
  cases coordinate with
  | inl coordinate =>
      cases coordinate
      exact rowMessage_at_initial state.1 state.2
  | inr coordinate =>
      rcases coordinate with ⟨round, degree⟩
      simpa [stateRow, stateValue] using
        (rowMessage_at_coefficient state.1 state.2 (round, degree.succ)).trans
          (storedCoefficient_succ state.2 round degree)

/-- Physical pad rows 224 through 478, in Rust slice order. -/
def structuredPadRow (coordinate : PadCoordinate) : Row :=
  ⟨224 + (coordinate : ℕ), by omega⟩

@[simp] theorem structuredPadRow_val (coordinate : PadCoordinate) :
    (structuredPadRow coordinate : ℕ) = 224 + (coordinate : ℕ) := rfl

theorem structuredPadRow_injective : Function.Injective structuredPadRow := by
  intro left right equal
  apply Fin.ext
  have hval := congrArg Fin.val equal
  simp only [structuredPadRow_val] at hval
  omega

theorem structuredPadRow_ne_pivot (coordinate : PadCoordinate) :
    structuredPadRow coordinate ≠ pivotRow := by
  intro equal
  have hval := congrArg Fin.val equal
  simp only [structuredPadRow_val] at hval
  have hpivot : (pivotRow : ℕ) = 993 := rfl
  omega

/-- State and pad rows are disjoint in the actual low/high-block layout. -/
theorem structuredPadRow_ne_stateRow
    (pad : PadCoordinate) (state : StateCoordinate) :
    structuredPadRow pad ≠ stateRow state := by
  intro equal
  cases state with
  | inl state =>
      cases state
      have hval := congrArg Fin.val equal
      simp only [structuredPadRow_val, stateRow] at hval
      have hinitial : (initialRow : ℕ) = 992 := rfl
      omega
  | inr state =>
      rcases state with ⟨round, degree⟩
      have hval := congrArg Fin.val equal
      simp only [structuredPadRow_val, stateRow, coefficientRow_val] at hval
      by_cases hlow : (round : ℕ) < 7
      · simp only [blockSelector, if_pos hlow] at hval
        have hdegree := degree.isLt
        simp only [AspisV5SumcheckCommitment.tailCount] at hdegree
        omega
      · simp only [blockSelector, if_neg hlow] at hval
        omega

/-! ## Exact pad-plus-dependent-pivot encoder -/

/-- The 255 pads embedded unchanged at rows 224 through 478. -/
noncomputable def structuredPadMessage (K : Type*) [Field K] :
    PadVector K →ₗ[K] Message K where
  toFun pads := ∑ coordinate, basis (structuredPadRow coordinate) (pads coordinate)
  map_add' left right := by
    funext row
    simp only [Pi.add_apply, Finset.sum_apply, basis]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    by_cases hrow : row = structuredPadRow coordinate <;> simp [hrow]
  map_smul' scalar pads := by
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.sum_apply,
      basis]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    by_cases hrow : row = structuredPadRow coordinate <;> simp [hrow]

@[simp] theorem structuredPadMessage_at {K : Type*} [Field K]
    (pads : PadVector K) (coordinate : PadCoordinate) :
    structuredPadMessage K pads (structuredPadRow coordinate) = pads coordinate := by
  classical
  change (∑ other, basis (structuredPadRow other) (pads other))
      (structuredPadRow coordinate) = pads coordinate
  simp only [Finset.sum_apply, basis]
  rw [Finset.sum_eq_single coordinate]
  · simp
  · intro other _ hne
    rw [if_neg]
    exact fun equal => hne (structuredPadRow_injective equal.symm)
  · simp

/-- Scalar embedding at the deployed dependent pivot row 993. -/
def pivotMessage (K : Type*) [Field K] : K →ₗ[K] Message K where
  toFun value := basis pivotRow value
  map_add' left right := by
    funext row
    by_cases hrow : row = pivotRow <;> simp [basis, hrow]
  map_smul' scalar value := by
    funext row
    by_cases hrow : row = pivotRow <;> simp [basis, hrow]

/-- The exact affine-input linearization used by `V5StructuredBLane`: write
all pads, then write `pivot - inactive(pads)` at row 993. -/
noncomputable def padPlusPivotEncoder {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) : PadSample K →ₗ[K] Message K where
  toFun sample :=
    structuredPadMessage K sample.1 +
      basis pivotRow (sample.2 - inactive (structuredPadMessage K sample.1))
  map_add' left right := by
    change structuredPadMessage K (left.1 + right.1) +
        basis pivotRow
          (left.2 + right.2 -
            inactive (structuredPadMessage K (left.1 + right.1))) =
      structuredPadMessage K left.1 +
          basis pivotRow
            (left.2 - inactive (structuredPadMessage K left.1)) +
        (structuredPadMessage K right.1 +
          basis pivotRow
            (right.2 - inactive (structuredPadMessage K right.1)))
    rw [map_add, map_add]
    funext row
    by_cases hrow : row = pivotRow <;>
      simp [basis, hrow, Pi.add_apply]
    ring
  map_smul' scalar sample := by
    change structuredPadMessage K (scalar • sample.1) +
        basis pivotRow
          (scalar * sample.2 -
            inactive (structuredPadMessage K (scalar • sample.1))) =
      scalar •
        (structuredPadMessage K sample.1 +
          basis pivotRow
            (sample.2 - inactive (structuredPadMessage K sample.1)))
    rw [map_smul, map_smul]
    funext row
    by_cases hrow : row = pivotRow <;>
      simp [basis, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem padPlusPivotEncoder_apply {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (sample : PadSample K) :
    padPlusPivotEncoder inactive sample =
      structuredPadMessage K sample.1 +
        basis pivotRow (sample.2 - inactive (structuredPadMessage K sample.1)) :=
  rfl

/-- Under the deployed unit pivot coefficient, the dependent write makes the
inactive claim exactly the caller-owned pivot scalar. -/
theorem inactive_padPlusPivotEncoder {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (hpivot : inactive (basis pivotRow 1) = 1)
    (sample : PadSample K) :
    inactive (padPlusPivotEncoder inactive sample) = sample.2 := by
  rw [padPlusPivotEncoder_apply, map_add]
  have hpivotValue :
      inactive (basis pivotRow
        (sample.2 - inactive (structuredPadMessage K sample.1))) =
        sample.2 - inactive (structuredPadMessage K sample.1) := by
    rw [AspisV5InactiveClaimDeployedCorrespondence.basis_eq_smul_basis_one,
      map_smul, hpivot, smul_eq_mul, mul_one]
  rw [hpivotValue]
  abel

/-- Legal post-state-coupling message differences are exactly the range of
the 255-pad-plus-pivot encoder. -/
noncomputable def legalDifferenceSpace {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) : Submodule K (Message K) :=
  LinearMap.range (padPlusPivotEncoder inactive)

theorem padPlusPivotEncoder_mem_legalDifferenceSpace
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (sample : PadSample K) :
    padPlusPivotEncoder inactive sample ∈ legalDifferenceSpace inactive :=
  ⟨sample, rfl⟩

/-! ## Complete 76-coordinate residual map -/

/-- The 72 raw coordinates are query-major, with four fibre slots per q18
query. -/
def rawWireOrdinal (coordinate : RawCoordinate) : Fin 72 :=
  ⟨4 * (coordinate.1 : ℕ) + (coordinate.2 : ℕ), by omega⟩

@[simp] theorem rawWireOrdinal_val (coordinate : RawCoordinate) :
    (rawWireOrdinal coordinate : ℕ) =
      4 * (coordinate.1 : ℕ) + (coordinate.2 : ℕ) := rfl

/-- The three all-zero-point Boolean MLE rows in point-major order:
`z`, `successor(z)`, `xor12(z)`. -/
def degenerateMLERow : MLECoordinate → Row :=
  ![⟨0, by omega⟩, ⟨1, by omega⟩, ⟨12, by omega⟩]

theorem degenerateMLERow_below_pads (point : MLECoordinate) :
    (degenerateMLERow point : ℕ) < 224 := by
  fin_cases point <;> norm_num [degenerateMLERow]

/-- Exact MLE triple at the all-zero ten-round point. -/
def degenerateMLE (K : Type*) [Field K] :
    Message K →ₗ[K] (MLECoordinate → K) :=
  LinearMap.pi fun point => LinearMap.proj (degenerateMLERow point)

@[simp] theorem degenerateMLE_apply {K : Type*} [Field K]
    (message : Message K) (point : MLECoordinate) :
    degenerateMLE K message point = message (degenerateMLERow point) := rfl

/-! ### The concrete A-admissible Boolean point at row 976 -/

/-- The three Boolean relation points `z`, `successor(z)`, and `xor12(z)`
for `z = 1111010000₂`.  Coordinates are in the deployed big-endian MLE
order. -/
def row976BooleanRelationPoint : MLECoordinate → Round → Bool :=
  ![![true, true, true, true, false, true, false, false, false, false],
    ![true, true, true, true, false, true, false, false, false, true],
    ![true, true, true, true, false, true, true, true, false, false]]

/-- Big-endian Boolean row ordinal, stated in `Nat` so no modulo operation is
silently inserted into the code/model seam. -/
def booleanPointRowNat (point : Round → Bool) : ℕ :=
  ∑ coordinate, if point coordinate then 2 ^ (9 - (coordinate : ℕ)) else 0

/-- The exact physical rows read by a Boolean multilinear evaluation at the
three relation points above. -/
def row976MLERow : MLECoordinate → Row :=
  ![⟨976, by omega⟩, ⟨977, by omega⟩, ⟨988, by omega⟩]

/-- **Exact point-to-MLE-row correspondence.**  Under the Rust big-endian
fold convention, the three explicit Boolean points have row ordinals 976,
977 and 988, respectively.  This theorem is deliberately named for a later
one-line cross-gate corollary from Component A. -/
theorem row976_relation_points_to_mle_rows_exact (point : MLECoordinate) :
    booleanPointRowNat (row976BooleanRelationPoint point) =
      (row976MLERow point : ℕ) := by
  fin_cases point <;> decide

/-- The field-valued ten-round transcript point corresponding to Boolean row
976. -/
def row976Point (K : Type*) [Field K] : Round → K :=
  fun coordinate ↦ if row976BooleanRelationPoint 0 coordinate then 1 else 0

/-- All three row-976 relation MLE reads, as an exact linear map. -/
def row976MLE (K : Type*) [Field K] :
    Message K →ₗ[K] (MLECoordinate → K) :=
  LinearMap.pi fun point ↦ LinearMap.proj (row976MLERow point)

@[simp] theorem row976MLE_apply {K : Type*} [Field K]
    (message : Message K) (point : MLECoordinate) :
    row976MLE K message point = message (row976MLERow point) := rfl

theorem row976MLERow_above_pads (point : MLECoordinate) :
    479 ≤ (row976MLERow point : ℕ) := by
  fin_cases point <;> norm_num [row976MLERow]

theorem row976MLERow_below_pivot (point : MLECoordinate) :
    (row976MLERow point : ℕ) < 993 := by
  fin_cases point <;> norm_num [row976MLERow]

/-- Complete independent residual map, in the exact triangular order:
inactive, 72 raw values, then three MLE values.  The deterministic terminal
is intentionally absent. -/
noncomputable def completeResidualMap {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (mle : Message K →ₗ[K] (MLECoordinate → K)) :
    PadSample K →ₗ[K] ResidualView K where
  toFun sample :=
    let message := padPlusPivotEncoder inactive sample
    (inactive message, raw message, mle message)
  map_add' left right := by
    simp only [map_add]
    rfl
  map_smul' scalar sample := by
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp] theorem completeResidualMap_apply {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (mle : Message K →ₗ[K] (MLECoordinate → K))
    (sample : PadSample K) :
    completeResidualMap inactive raw mle sample =
      (inactive (padPlusPivotEncoder inactive sample),
        raw (padPlusPivotEncoder inactive sample),
        mle (padPlusPivotEncoder inactive sample)) := rfl

theorem degenerateMLE_padPlusPivot_zero {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (sample : PadSample K) :
    degenerateMLE K (padPlusPivotEncoder inactive sample) = 0 := by
  funext point
  rw [degenerateMLE_apply, Pi.zero_apply, padPlusPivotEncoder_apply,
    Pi.add_apply]
  have hpad :
      structuredPadMessage K sample.1 (degenerateMLERow point) = 0 := by
    change (∑ coordinate,
      basis (structuredPadRow coordinate) (sample.1 coordinate))
        (degenerateMLERow point) = 0
    simp only [Finset.sum_apply, basis]
    apply Finset.sum_eq_zero
    intro coordinate _
    rw [if_neg]
    intro equal
    have hval := congrArg Fin.val equal
    have hlow := degenerateMLERow_below_pads point
    simp only [structuredPadRow_val] at hval
    omega
  rw [hpad, zero_add]
  rw [basis, if_neg]
  intro equal
  have hval := congrArg Fin.val equal
  have hlow := degenerateMLERow_below_pads point
  have hpivot : (pivotRow : ℕ) = 993 := rfl
  omega

/-- At row 976, all three MLE reads annihilate the entire legal
255-pad-plus-dependent-pivot difference space. -/
theorem row976MLE_padPlusPivot_zero {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (sample : PadSample K) :
    row976MLE K (padPlusPivotEncoder inactive sample) = 0 := by
  funext point
  rw [row976MLE_apply, Pi.zero_apply, padPlusPivotEncoder_apply,
    Pi.add_apply]
  have hpad :
      structuredPadMessage K sample.1 (row976MLERow point) = 0 := by
    change (∑ coordinate,
      basis (structuredPadRow coordinate) (sample.1 coordinate))
        (row976MLERow point) = 0
    simp only [Finset.sum_apply, basis]
    apply Finset.sum_eq_zero
    intro coordinate _
    rw [if_neg]
    intro equal
    have hval := congrArg Fin.val equal
    have habove := row976MLERow_above_pads point
    have hcoordinate := coordinate.isLt
    simp only [structuredPadRow_val] at hval
    omega
  rw [hpad, zero_add]
  rw [basis, if_neg]
  intro equal
  have hval := congrArg Fin.val equal
  have hbelow := row976MLERow_below_pivot point
  have hpivot : (pivotRow : ℕ) = 993 := rfl
  omega

/-- The residual map with the three known-zero coordinates removed. -/
noncomputable def reducedResidualMap {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    PadSample K →ₗ[K] ReducedResidualView K where
  toFun sample :=
    let message := padPlusPivotEncoder inactive sample
    (inactive message, raw message)
  map_add' left right := by
    simp only [map_add]
    rfl
  map_smul' scalar sample := by
    simp only [map_smul, RingHom.id_apply]
    rfl

/-- Embed the at-most-73-dimensional residual view with a zero MLE triple. -/
def includeZeroMLE (K : Type*) [Field K] :
    ReducedResidualView K →ₗ[K] ResidualView K where
  toFun view := (view.1, view.2, 0)
  map_add' left right := by
    ext <;> simp
  map_smul' scalar view := by
    ext <;> simp

theorem row976_completeResidualMap_eq_factored
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    completeResidualMap inactive raw (row976MLE K) =
      (includeZeroMLE K).comp (reducedResidualMap inactive raw) := by
  apply LinearMap.ext
  intro sample
  rw [completeResidualMap_apply]
  change
    (inactive (padPlusPivotEncoder inactive sample),
        raw (padPlusPivotEncoder inactive sample),
        row976MLE K (padPlusPivotEncoder inactive sample)) =
      (inactive (padPlusPivotEncoder inactive sample),
        raw (padPlusPivotEncoder inactive sample), 0)
  rw [row976MLE_padPlusPivot_zero]

/-- **Numerical structural bound.**  The complete 76-coordinate map at the
row-976 point has rank at most 73, for every raw encoder and inactive
functional. -/
theorem row976_completeResidualMap_rank_le_73
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    Module.finrank K
      (LinearMap.range (completeResidualMap inactive raw (row976MLE K))) ≤
        73 := by
  rw [row976_completeResidualMap_eq_factored]
  calc
    Module.finrank K
        (LinearMap.range
          ((includeZeroMLE K).comp (reducedResidualMap inactive raw))) ≤
        Module.finrank K (LinearMap.range (includeZeroMLE K)) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ Module.finrank K (ReducedResidualView K) :=
      LinearMap.finrank_range_le (includeZeroMLE K)
    _ = 73 := by
      simp [ReducedResidualView]

/-- A target selecting only the first MLE coordinate. -/
def missingMLETarget {K : Type*} [Field K] : ResidualView K :=
  (0, 0, fun point => if point = 0 then 1 else 0)

/-- **Fatal structural counterexample.**  At the all-zero terminal point the
complete 76-coordinate pad-plus-pivot map is not surjective, for every raw
circle encoder and every inactive covector. -/
theorem degenerate_completeResidualMap_not_surjective
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ Function.Surjective
      (completeResidualMap inactive raw (degenerateMLE K)) := by
  intro hsurjective
  obtain ⟨sample, heq⟩ := hsurjective missingMLETarget
  rw [completeResidualMap_apply] at heq
  have hcoordinate := congrArg (fun view : ResidualView K => view.2.2 0) heq
  have hzero := congrFun (degenerateMLE_padPlusPivot_zero inactive sample) 0
  change degenerateMLE K (padPlusPivotEncoder inactive sample) 0 = 1 at hcoordinate
  rw [hzero] at hcoordinate
  exact zero_ne_one hcoordinate

/-- Hence the existing named `rank76` deployment interface is false at this
allowed point; its finrank conjunct cannot rescue failed surjectivity. -/
theorem degenerate_CurrentPadsPlusPivotMapHasRank76_fails
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ UnmetDeployment.CurrentPadsPlusPivotMapHasRank76
      (completeResidualMap inactive raw (degenerateMLE K)) := by
  intro hcoverage
  exact degenerate_completeResidualMap_not_surjective inactive raw hcoverage.2

/-- The row-976 instance is not surjective; equivalently, rank 76 cannot
hold.  This direct coordinate proof is independent of the numerical rank
bound above. -/
theorem row976_completeResidualMap_not_surjective
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ Function.Surjective
      (completeResidualMap inactive raw (row976MLE K)) := by
  intro hsurjective
  obtain ⟨sample, heq⟩ := hsurjective missingMLETarget
  rw [completeResidualMap_apply] at heq
  have hcoordinate := congrArg (fun view : ResidualView K ↦ view.2.2 0) heq
  have hzero := congrFun (row976MLE_padPlusPivot_zero inactive sample) 0
  change row976MLE K (padPlusPivotEncoder inactive sample) 0 = 1 at hcoordinate
  rw [hzero] at hcoordinate
  exact zero_ne_one hcoordinate

theorem row976_CurrentPadsPlusPivotMapHasRank76_fails
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ UnmetDeployment.CurrentPadsPlusPivotMapHasRank76
      (completeResidualMap inactive raw (row976MLE K)) := by
  intro hcoverage
  exact row976_completeResidualMap_not_surjective inactive raw hcoverage.2

/-! ## The counterexample is an accepted transcript schedule -/

/-- A deterministic accepted-run model whose eta and all ten round
challenges are zero. -/
def zeroSchedule (K : Type*) [Field K] : FiatShamirSchedule Unit Unit K where
  eta _ := 0
  roundChallenge _ _ _ := 0

def zeroAcceptedRun (K : Type*) [Field K] : AcceptedRun (zeroSchedule K) where
  preEta := ⟨(), ()⟩
  eta := 0
  messages := 0
  point := 0
  eta_eq := rfl
  point_eq := rfl

/-- Runtime applicability data: an accepted transcript plus 18 distinct q18
fibre indices. -/
structure ApplicableSchedule
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K) where
  run : AcceptedRun scheme
  fibres : QueryCoordinate → Fin 131072
  withoutReplacement : Function.Injective fibres

/-- The zero-point run coexists with a perfectly valid distinct q18 fibre
schedule. -/
def zeroApplicableSchedule (K : Type*) [Field K] :
    ApplicableSchedule (zeroSchedule K) where
  run := zeroAcceptedRun K
  fibres := fun query => ⟨query, by omega⟩
  withoutReplacement := by
    intro left right equal
    apply Fin.ext
    simpa using congrArg Fin.val equal

@[simp] theorem zeroApplicableSchedule_point
    {K : Type*} [Field K] :
    (zeroApplicableSchedule K).run.point = 0 := rfl

/-- A deterministic accepted transcript whose ten challenges are the exact
Boolean point of row 976. -/
def prefixRound {K : Type*} [Field K]
    (messages : List (Degree27RoundMessage K)) : Round :=
  ⟨(messages.length - 1) % 10, Nat.mod_lt _ (by omega)⟩

def row976Schedule (K : Type*) [Field K] : FiatShamirSchedule Unit Unit K where
  eta _ := 0
  roundChallenge _ _ messages := row976Point K (prefixRound messages)

def row976AcceptedRun (K : Type*) [Field K] : AcceptedRun (row976Schedule K) where
  preEta := ⟨(), ()⟩
  eta := 0
  messages := 0
  point := row976Point K
  eta_eq := rfl
  point_eq := by
    funext round
    change row976Point K round =
      row976Point K
        (prefixRound
          (List.ofFn fun earlier : Fin ((round : ℕ) + 1) ↦
            (0 : Degree27RoundMessage K)))
    congr 1
    apply Fin.ext
    simp only [prefixRound, List.length_ofFn]
    have hround := round.isLt
    simp only [AspisV5SumcheckCommitment.roundCount] at hround
    omega

/-- The counterexample uses Component A's existing concrete injective q18
schedule, rather than an independently sampled diagnostic schedule. -/
def row976SampleQueriesApplicableSchedule (K : Type*) [Field K] :
    ApplicableSchedule (row976Schedule K) where
  run := row976AcceptedRun K
  fibres := AspisV5ComponentARankCompletion.sampleQueries
  withoutReplacement :=
    AspisV5ComponentARankCompletion.sampleQueries_injective

@[simp] theorem row976SampleQueriesApplicableSchedule_point
    {K : Type*} [Field K] :
    (row976SampleQueriesApplicableSchedule K).run.point = row976Point K := rfl

theorem row976SampleQueriesApplicableSchedule_distinct
    {K : Type*} [Field K] :
    Function.Injective (row976SampleQueriesApplicableSchedule K).fibres :=
  (row976SampleQueriesApplicableSchedule K).withoutReplacement

/-- Import-ready cross-gate endpoint: once Component A identifies an
accepted execution with this point and these `sampleQueries`, exact runtime
point-to-MLE correspondence reduces its B residual map to `row976MLE`, whose
rank is at most 73. -/
theorem row976_sampleQueries_point_to_mle_rank76_counterexample
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (rawForSchedule :
      ApplicableSchedule (row976Schedule K) →
        Message K →ₗ[K] (RawCoordinate → K))
    (mleForSchedule :
      ApplicableSchedule (row976Schedule K) →
        Message K →ₗ[K] (MLECoordinate → K))
    (hpointToMLE :
      mleForSchedule (row976SampleQueriesApplicableSchedule K) = row976MLE K) :
    Module.finrank K
      (LinearMap.range
        (completeResidualMap inactive
          (rawForSchedule (row976SampleQueriesApplicableSchedule K))
          (mleForSchedule (row976SampleQueriesApplicableSchedule K)))) ≤ 73 := by
  rw [hpointToMLE]
  exact row976_completeResidualMap_rank_le_73 inactive _

/-- A rank-76 theorem quantified over every applicable transcript schedule
is therefore impossible without an additional point-rejection predicate.
The counterexample uses distinct fibres; it is not a q18 collision. -/
theorem applicable_schedule_universal_rank76_is_false
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (rawForSchedule :
      ApplicableSchedule (zeroSchedule K) →
        Message K →ₗ[K] (RawCoordinate → K))
    (mleForSchedule :
      ApplicableSchedule (zeroSchedule K) →
        Message K →ₗ[K] (MLECoordinate → K))
    (hzero : mleForSchedule (zeroApplicableSchedule K) = degenerateMLE K) :
    ¬ (∀ schedule : ApplicableSchedule (zeroSchedule K),
      Function.Surjective
        (completeResidualMap inactive (rawForSchedule schedule)
          (mleForSchedule schedule))) := by
  intro huniversal
  have hsurjective := huniversal (zeroApplicableSchedule K)
  rw [hzero] at hsurjective
  exact
    (degenerate_completeResidualMap_not_surjective inactive
      (rawForSchedule (zeroApplicableSchedule K))) hsurjective

/-! ## Exact serializer ordinals retained as executable seams -/

/-- B is helper lane one of C2; its four 16-byte values begin at byte 64 of
the 192-byte C2 leaf, in slot order. -/
def c2BSlotByteStart (slot : FibreSlot) : Fin 192 :=
  ⟨64 + 16 * (slot : ℕ), by omega⟩

theorem c2BSlotByteStart_values :
    List.ofFn (fun slot : FibreSlot => (c2BSlotByteStart slot : ℕ)) =
      [64, 80, 96, 112] := by
  decide

/-- Four point-major relation rows, 19 lanes per point, B at lane 17, based
at real-prefix byte 4583. -/
def bRelationClaimByteStart (point : Fin 4) : Fin 6423 :=
  ⟨4583 + 16 * (19 * (point : ℕ) + 17), by omega⟩

theorem bRelationClaimByteStart_values :
    List.ofFn (fun point : Fin 4 => (bRelationClaimByteStart point : ℕ)) =
      [4855, 5159, 5463, 5767] := by
  decide

theorem terminal_and_inactive_wire_offsets :
    4583 + 4 * 19 * 16 = 5799 ∧
      5799 + 3 * 16 = 5847 ∧
      5847 + 16 = 5863 := by
  norm_num

/-- Exact Rust encoder equality remains a code-model premise, not a theorem
derived from the transcribed constants. -/
def ExactRustStructuredEncoderCorrespondence {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (rustEncode : PadSample K → Message K) : Prop :=
  rustEncode = padPlusPivotEncoder inactive

/-- Exact parser order remains a code-model premise. -/
def ExactRustResidualSerializationCorrespondence
    (rustRawOrdinal : RawCoordinate → Fin 72)
    (rustC2BSlotStart : FibreSlot → Fin 192)
    (rustBClaimStart : Fin 4 → Fin 6423) : Prop :=
  rustRawOrdinal = rawWireOrdinal ∧
    rustC2BSlotStart = c2BSlotByteStart ∧
    rustBClaimStart = bRelationClaimByteStart

/-- Exact transcript extraction of the terminal point remains a code-model
premise. -/
def ExactRustTranscriptPointCorrespondence
    {Public Root K : Type*} [Field K]
    {scheme : FiatShamirSchedule Public Root K}
    (schedule : ApplicableSchedule scheme)
    (rustPoint : Round → K) : Prop :=
  rustPoint = schedule.run.point

/-! ## Required teeth retained around the negative result -/

/-- Removing pad coordinate `i` destroys coverage of its actual physical pad
row.  This is a basis-level structural tooth, not a claim that the already
false 76-coordinate map has a minimal 255-column basis. -/
theorem removing_one_pad_direction_breaks_physical_row_coverage
    {K : Type*} [Field K] (coordinate : PadCoordinate) :
    ¬ Function.Surjective
      (((LinearMap.proj (structuredPadRow coordinate) :
          Message K →ₗ[K] K).comp (structuredPadMessage K)).comp
        (LinearMap.ker
          (LinearMap.proj coordinate : PadVector K →ₗ[K] K)).subtype) := by
  intro hsurjective
  obtain ⟨pads, hpads⟩ := hsurjective 1
  have hzero : (pads : PadVector K) coordinate = 0 := by
    exact LinearMap.mem_ker.mp pads.property
  change structuredPadMessage K (pads : PadVector K)
      (structuredPadRow coordinate) = 1 at hpads
  rw [structuredPadMessage_at] at hpads
  rw [hzero] at hpads
  exact zero_ne_one hpads

/-- Using coefficient zero instead of the inverse pivot coefficient breaks
the carried invariant in the existing finite beyond-freshness model. -/
def wrongCoefficientCorrectedReleased
    (coefficient : AspisV5DeployedCarriedInvariant.egK)
    (message : AspisV5DeployedCarriedInvariant.egM) :
    AspisV5DeployedCarriedInvariant.egK :=
  AspisV5DeployedCarriedInvariant.egReleased message -
    (coefficient * AspisV5DeployedCarriedInvariant.egInactive message) •
      AspisV5DeployedCarriedInvariant.egReleased
        AspisV5DeployedCarriedInvariant.egPivot

theorem wrong_pivot_coefficient_breaks_carried_invariant :
    wrongCoefficientCorrectedReleased 0 0 ≠
      wrongCoefficientCorrectedReleased 0
        (AspisV5DeployedCarriedInvariant.egGens 1) := by
  decide

/-- Pivot freshness is not necessary: the existing finite certificate covers
the correlated legal-difference space while the released map reads the
pivot. -/
theorem pivot_freshness_can_fail_while_correlated_coverage_holds :
    AspisV5DeployedCarriedInvariant.egReleased
        AspisV5DeployedCarriedInvariant.egPivot ≠ 0 ∧
      AspisV5DeployedCarriedInvariant.CarriedCertificate
        AspisV5DeployedCarriedInvariant.egInactive
        AspisV5DeployedCarriedInvariant.egReleased
        AspisV5DeployedCarriedInvariant.egPivot
        AspisV5DeployedCarriedInvariant.egGens
        AspisV5DeployedCarriedInvariant.egΔB :=
  ⟨AspisV5DeployedCarriedInvariant.egBeyondFresh.1,
    AspisV5DeployedCarriedInvariant.egCertificate⟩

/-- Preserve the prior authentication teeth: uniqueness at a wrong root or
wrong point does not authenticate the pre-eta state at its derived point. -/
theorem wrong_terminal_point_or_root_does_not_authenticate_state :
    (AspisV5FreezeBTranscriptAuthentication.rootEchoAuthentication true () true ∧
      ¬ AspisV5FreezeBTranscriptAuthentication.rootEchoAuthentication
        false () true) ∧
    (AspisV5FreezeBTranscriptAuthentication.pointEchoAuthentication () true true ∧
      ¬ AspisV5FreezeBTranscriptAuthentication.pointEchoAuthentication
        () false true) := by
  constructor
  · exact
      ⟨AspisV5FreezeBTranscriptAuthentication.wrong_root_authentication_does_not_bind_preEta_root.2.2.1,
        AspisV5FreezeBTranscriptAuthentication.wrong_root_authentication_does_not_bind_preEta_root.2.2.2⟩
  · exact
      ⟨AspisV5FreezeBTranscriptAuthentication.wrong_point_authentication_does_not_bind_derived_point.2.2.1,
        AspisV5FreezeBTranscriptAuthentication.wrong_point_authentication_does_not_bind_derived_point.2.2.2⟩

end AspisV5ComponentBCorrelatedResidualCoverage

#print axioms AspisV5ComponentBCorrelatedResidualCoverage.exact_coordinate_counts
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.stateWireOrdinal_initial
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.stateWireOrdinal_tail_val
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.stateWireOrdinal_injective
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.rowMessage_recovers_state
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.structuredPadRow_val
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.structuredPadRow_injective
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.structuredPadRow_ne_pivot
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.structuredPadRow_ne_stateRow
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.structuredPadMessage_at
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.padPlusPivotEncoder_apply
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.inactive_padPlusPivotEncoder
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.padPlusPivotEncoder_mem_legalDifferenceSpace
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.rawWireOrdinal_val
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.degenerateMLERow_below_pads
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.degenerateMLE_apply
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_relation_points_to_mle_rows_exact
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976MLE_apply
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976MLERow_above_pads
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976MLERow_below_pivot
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.completeResidualMap_apply
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.degenerateMLE_padPlusPivot_zero
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976MLE_padPlusPivot_zero
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_completeResidualMap_eq_factored
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_completeResidualMap_rank_le_73
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.degenerate_completeResidualMap_not_surjective
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.degenerate_CurrentPadsPlusPivotMapHasRank76_fails
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_completeResidualMap_not_surjective
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_CurrentPadsPlusPivotMapHasRank76_fails
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.zeroApplicableSchedule_point
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976SampleQueriesApplicableSchedule_point
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976SampleQueriesApplicableSchedule_distinct
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.row976_sampleQueries_point_to_mle_rank76_counterexample
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.applicable_schedule_universal_rank76_is_false
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.c2BSlotByteStart_values
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.bRelationClaimByteStart_values
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.terminal_and_inactive_wire_offsets
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.removing_one_pad_direction_breaks_physical_row_coverage
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.wrong_pivot_coefficient_breaks_carried_invariant
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.pivot_freshness_can_fail_while_correlated_coverage_holds
#print axioms AspisV5ComponentBCorrelatedResidualCoverage.wrong_terminal_point_or_root_does_not_authenticate_state
