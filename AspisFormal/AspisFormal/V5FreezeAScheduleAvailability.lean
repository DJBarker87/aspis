import AspisFormal.V5AtomicComponentACorrespondence
import AspisFormal.V5ComponentARankCompletion

/-!
# Hostile freeze audit: Component-A schedule availability

This file separates the part of Component A that is closed in the Lean model
from the terminal-coverage condition that is not enforced by the candidate
wire.

The successful q18 sampler in the host and verifier uses sampling without
replacement from the `2^17` layer-zero fibres.  Its exact mathematical output
is represented by `AcceptedQ18Schedule`: eighteen fibre indices together with
the injectivity fact supplied by successful sampling.  For every such schedule,
the deployed M31 representative coordinates are nonzero.  If the Rust
row-896 encoder weight has the already-modelled three-twiddle shape, it too is
nonzero.  The existing kernel-checked theorem then gives rank 72 and
surjectivity after restriction to the atomic coefficient-sum-zero hyperplane.

That is not the complete A gate.  The remaining three eq-side MLE reads can be
the zero map on every Component-A difference.  At the all-zero ten-coordinate
point, the three Boolean points used by the wire select message rows `0`, `1`,
and `12`; Component A changes only rows `896..991`.  The theorem
`degenerate_eq_side_does_not_cover` proves that this induced terminal triple
cannot satisfy `EqTerminalTripleCoversDeployedKernel`.  The runtime samples
the ten round challenges with the ordinary `challenge_qm31` sampler, and no
existing public predicate rejects this point before the claims are used.

Consequently this file intentionally contains no freeze capstone for all of
Component A.  The layer-zero theorem is conditional only on exact executable
correspondence; the terminal gate has a mathematical counterexample unless an
already-existing rejection predicate can be exhibited.  None is present in
the inspected candidate host or verifier.  The repository's production-v4
`GoodSpend` is not such a predicate: its pinned definition uses the retired
H/G/D and H1 Schur maps, and the v5 candidate does not invoke it.
-/

open Matrix

namespace AspisV5FreezeAScheduleAvailability

open AspisCircleDiscreteAvailability
open AspisCircleRectangularMasking
open AspisCircleTensorBinding
open AspisV5AtomicComponentA
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentARankCompletion

/-! ## 1. Exact successful-q18 schedule hypotheses -/

/-- Mathematical data returned by a successful runtime q18 sampler.  The Rust
host and verifier obtain `withoutReplacement` by accepting only the successful
result of `challenge_queries_without_replacement(18, 2^17, ...)`.  Equality of
this structure's `queries` with those concrete output words is an executable-
correspondence obligation, not asserted by this definition. -/
structure AcceptedQ18Schedule where
  queries : Fin queryCount → Fin fibreCount
  withoutReplacement : Function.Injective queries

/-- The exact successful schedule expands to 72 distinct layer-zero codeword
positions. -/
theorem accepted_q18_has_72_distinct_positions (schedule : AcceptedQ18Schedule) :
    Function.Injective (expandedPosition schedule.queries) :=
  spend_opened_positions_injective schedule.queries schedule.withoutReplacement

/-- Cardinality plus injectivity in one statement: successful q18 exposes
exactly `18 * 4 = 72` pairwise-distinct layer-zero positions. -/
theorem accepted_q18_exactly_72_distinct_positions (schedule : AcceptedQ18Schedule) :
    Fintype.card (Fin queryCount × Fin fibreSlots) = 72 ∧
      Function.Injective (expandedPosition schedule.queries) := by
  exact ⟨by norm_num [queryCount, fibreSlots],
    accepted_q18_has_72_distinct_positions schedule⟩

/-- Both deployed representative coordinates are nonzero at every accepted
fibre.  These are facts about the concrete M31 generator and exponents, not a
generic-schedule premise. -/
theorem accepted_q18_representatives_nonzero (schedule : AcceptedQ18Schedule) :
    ∀ i, representativeX (schedule.queries i) ≠ 0 ∧
      representativeY (schedule.queries i) ≠ 0 := by
  intro i
  exact ⟨representative_x_ne_zero _, representative_y_ne_zero _⟩

/-! ## 2. The modelled row-896 weight and the layer-zero rank gate -/

/-- The three line-layer indices and output signs that instantiate the
row-896 factor family.  Proving that Rust bit reversal and butterfly routing
produce this data at each physical codeword position is deliberately kept as
an executable-correspondence premise. -/
structure Row896Routing where
  i6 : FibreIndex → Fin (2 ^ 11)
  i7 : FibreIndex → Fin (2 ^ 10)
  i8 : FibreIndex → Fin (2 ^ 9)
  s6 : FibreIndex → Bool
  s7 : FibreIndex → Bool
  s8 : FibreIndex → Bool

/-- The aligned weight obtained from a routed product of the three nonzero
line-twiddle layers selected by binary row 896. -/
def modelledRow896Weight (routing : Row896Routing) : FibreIndex → DeployedField :=
  fun row ↦ row896Factor (routing.i6 row) (routing.i7 row) (routing.i8 row)
    (routing.s6 row) (routing.s7 row) (routing.s8 row)

theorem modelledRow896Weight_ne_zero (routing : Row896Routing) :
    ∀ row, modelledRow896Weight routing row ≠ 0 := by
  intro row
  exact row896Factor_ne_zero _ _ _ _ _ _

/-- Minimal code/model edge for the aligned weight.  It says only that the
actual encoder row equals one member of the already-proved row-896 factor
family; it does not assume injectivity of a hash or any cryptographic fact. -/
def RustRow896WeightMatchesModel (weight : FibreIndex → DeployedField) : Prop :=
  ∃ routing : Row896Routing, weight = modelledRow896Weight routing

theorem rustRow896Weight_ne_zero
    (weight : FibreIndex → DeployedField)
    (hweight : RustRow896WeightMatchesModel weight) : ∀ row, weight row ≠ 0 := by
  obtain ⟨routing, rfl⟩ := hweight
  exact modelledRow896Weight_ne_zero routing

/-- Strongest closed layer-zero statement for the actual accepted-schedule
hypotheses.  It packages distinct physical positions, concrete nonzero x/y
coordinates, full rank of the 72-by-96 evaluation map, and surjectivity on the
atomic-v3 `∑ c = 0` hyperplane.  Its one residual premise is the exact
Rust encoder/bit-reversal/slot-layout identification of the aligned weight. -/
theorem accepted_q18_layerZero_gate
    (schedule : AcceptedQ18Schedule)
    (weight : FibreIndex → DeployedField)
    (hweightModel : RustRow896WeightMatchesModel weight) :
    Function.Injective (expandedPosition schedule.queries) ∧
      (∀ i, representativeX (schedule.queries i) ≠ 0 ∧
        representativeY (schedule.queries i) ≠ 0) ∧
      (deployedFibreRectangularEval schedule.queries weight).rank = openedWidth ∧
      ∀ w : FibreIndex → DeployedField,
        ∃ c : Fin originalWidth → DeployedField,
          coefficientSum c = 0 ∧
            (deployedFibreRectangularEval schedule.queries weight).mulVec c = w := by
  have hweight := rustRow896Weight_ne_zero weight hweightModel
  exact ⟨accepted_q18_has_72_distinct_positions schedule,
    accepted_q18_representatives_nonzero schedule,
    deployedFibreRectangularEval_rank_eq_openedWidth
      schedule.queries schedule.withoutReplacement weight hweight,
    deployedAtomicV3ComponentA_surjective
      schedule.queries schedule.withoutReplacement weight hweight⟩

/-! ## 3. Teeth for schedule, factor, and layout mistakes -/

/-- Repeating a fibre index repeats every corresponding slot position.  Thus
without-replacement is load-bearing, even though the current successful runtime
sampler supplies it. -/
theorem repeated_fibre_breaks_position_injectivity
    (queries : Fin queryCount → Fin fibreCount) {left right : Fin queryCount}
    (hne : left ≠ right) (hrepeat : queries left = queries right) :
    ¬ Function.Injective (expandedPosition queries) := by
  intro hinjective
  let slot : Fin fibreSlots := ⟨0, by norm_num [fibreSlots]⟩
  have heq : expandedPosition queries (left, slot) =
      expandedPosition queries (right, slot) := by
    apply Fin.ext
    simp only [expandedPosition, fibrePosition]
    rw [hrepeat]
  have hp := hinjective heq
  exact hne (congrArg Prod.fst hp)

/-- A zero aligned factor makes its complete evaluation row zero. -/
theorem zero_aligned_factor_zeroes_row
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) (row : FibreIndex)
    (hzero : weight row = 0) (column : Fin originalWidth) :
    deployedFibreRectangularEval queries weight row column = 0 := by
  simp [deployedFibreRectangularEval, hzero]

/-- Therefore a zero aligned factor destroys surjectivity, independently of
the coefficient-sum constraint. -/
theorem zero_aligned_factor_blocks_surjectivity
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) (row : FibreIndex)
    (hzero : weight row = 0) :
    ¬ Function.Surjective (deployedFibreRectangularEval queries weight).mulVec := by
  intro hsurjective
  let target : FibreIndex → DeployedField := fun r ↦ if r = row then 1 else 0
  obtain ⟨c, hc⟩ := hsurjective target
  have hrow := congrFun hc row
  have hleft : (deployedFibreRectangularEval queries weight).mulVec c row = 0 := by
    simp [Matrix.mulVec, dotProduct, zero_aligned_factor_zeroes_row queries weight row hzero]
  have hright : target row = 1 := by simp [target]
  rw [hleft, hright] at hrow
  exact zero_ne_one hrow

/-- Fibre-major and slot-major flattening are not the same physical order.
At query zero, slot one, the runtime fibre-major ordinal is `1`, whereas a
transposed slot-major implementation would use `18`.  A row permutation does
not by itself change rank, but treating the two layouts as entrywise equal is
false and must not be hidden inside the correspondence premise. -/
theorem fibreMajor_slotMajor_order_tooth :
    fibreSlots * 0 + 1 = 1 ∧ queryCount * 1 + 0 = 18 ∧
      fibreSlots * 0 + 1 ≠ queryCount * 1 + 0 := by
  norm_num [fibreSlots, queryCount]

/-! ## 4. Exact degenerate eq-side counterexample -/

/-- Message differences produced by Component A are supported exactly inside
the aligned reserve.  This property is stated on messages so it can be used
without pretending that the Rust ordinary-to-natural conversion has already
been identified with a Lean matrix. -/
def SupportedOnAlignedReserve {K : Type*} [Zero K]
    (message : Fin traceRows → K) : Prop :=
  ∀ row : Fin traceRows,
    (row : ℕ) < reserveStart ∨ reserveStart + reserveWidth ≤ (row : ℕ) →
    message row = 0

/-- At the all-zero ten-coordinate point, the wire's three Boolean MLE points
`z`, `successor(z)`, and `xor12(z)` select rows 0, 1, and 12 respectively under
the big-endian row convention. -/
def degenerateEqRows : Fin 3 → Fin traceRows :=
  ![⟨0, by norm_num [traceRows]⟩,
    ⟨1, by norm_num [traceRows]⟩,
    ⟨12, by norm_num [traceRows]⟩]

theorem degenerateEqRows_below_reserve (i : Fin 3) :
    (degenerateEqRows i : ℕ) < reserveStart := by
  fin_cases i <;> norm_num [degenerateEqRows, reserveStart]

/-- The exact three Boolean row reads as a linear map on message tables. -/
def degenerateBooleanEqTriple (K : Type*) [Field K] :
    (Fin traceRows → K) →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i ↦ LinearMap.proj (degenerateEqRows i)

@[simp] theorem degenerateBooleanEqTriple_apply {K : Type*} [Field K]
    (message : Fin traceRows → K) (i : Fin 3) :
    degenerateBooleanEqTriple K message i = message (degenerateEqRows i) := rfl

/-- Every aligned-reserve difference is invisible to the degenerate terminal
triple.  This is the kernel-checked algebraic content of the rank-zero Rust
counterexample. -/
theorem degenerateBooleanEqTriple_zero_of_supported
    {K : Type*} [Field K] (message : Fin traceRows → K)
    (hsupport : SupportedOnAlignedReserve message) :
    degenerateBooleanEqTriple K message = 0 := by
  funext i
  rw [degenerateBooleanEqTriple_apply, Pi.zero_apply]
  exact hsupport (degenerateEqRows i)
    (Or.inl (degenerateEqRows_below_reserve i))

/-- Exact reserve-support condition on a candidate executable encoder. -/
def EncoderOutputsAlignedReserve {K : Type*} [Field K]
    (encode : (Fin originalWidth → K) →ₗ[K] (Fin traceRows → K)) : Prop :=
  ∀ c, SupportedOnAlignedReserve (encode c)

/-- Canonical interleaved placement at Rust rows `896+2k` and `897+2k`.
Writing it as a sum makes the construction linear without choosing an inverse
for the physical layout. -/
noncomputable def alignedReserveEmbed (K : Type*) [Field K] :
    (Fin originalWidth → K) →ₗ[K] (Fin traceRows → K) where
  toFun c row := ∑ i, if layoutRow i = (row : ℕ) then c i else 0
  map_add' c d := by
    funext row
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : layoutRow i = (row : ℕ) <;> simp [h]
  map_smul' a c := by
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : layoutRow i = (row : ℕ) <;> simp [h]

/-- The canonical layout has no support outside rows 896..991. -/
theorem alignedReserveEmbed_supported {K : Type*} [Field K] :
    EncoderOutputsAlignedReserve (alignedReserveEmbed K) := by
  intro c row houtside
  change (∑ i, if layoutRow i = (row : ℕ) then c i else 0) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro heq
  have hbounds := layoutRow_mem_reserved i
  rw [heq] at hbounds
  rcases houtside with hlow | hhigh
  · norm_num [reservedStart, reserveStart, maskB, reserveWidth] at hbounds hlow
    omega
  · norm_num [reservedStart, reserveStart, maskB, reserveWidth] at hbounds hhigh
    omega

/-- Any coefficient conversion performed before the same physical placement
preserves reserve-only support.  Thus the counterexample does not depend on
the entries or orientation of the ordinary-to-natural conversion matrix. -/
theorem alignedReserveEmbed_comp_supported {K : Type*} [Field K]
    (conversion : (Fin originalWidth → K) →ₗ[K] (Fin originalWidth → K)) :
    EncoderOutputsAlignedReserve ((alignedReserveEmbed K).comp conversion) := by
  intro c
  exact alignedReserveEmbed_supported (conversion c)

/-- The terminal triple induced on coefficient vectors at the degenerate
point. -/
def inducedDegenerateEqTriple {K : Type*} [Field K]
    (encode : (Fin originalWidth → K) →ₗ[K] (Fin traceRows → K)) :
    (Fin originalWidth → K) →ₗ[K] (Fin 3 → K) :=
  (degenerateBooleanEqTriple K).comp encode

theorem inducedDegenerateEqTriple_zero
    {K : Type*} [Field K]
    (encode : (Fin originalWidth → K) →ₗ[K] (Fin traceRows → K))
    (hreserve : EncoderOutputsAlignedReserve encode)
    (c : Fin originalWidth → K) :
    inducedDegenerateEqTriple encode c = 0 := by
  exact degenerateBooleanEqTriple_zero_of_supported (encode c) (hreserve c)

/-- **Terminal blocker.**  For any encoder whose Component-A differences stay
inside rows 896..991, the all-zero challenge point makes the actual three
Boolean eq-side reads incapable of covering even the target vector `(1,0,0)`.
Hence the Schur premise used by the conditional rank-12 completion is false at
this point, for every query schedule and every aligned layer-zero weight. -/
theorem degenerate_eq_side_does_not_cover
    {L : Type*} [Field L] [Algebra DeployedField L]
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (encode : (Fin originalWidth → L) →ₗ[L] (Fin traceRows → L))
    (hreserve : EncoderOutputsAlignedReserve encode) :
    ¬ EqTerminalTripleCoversDeployedKernel queries weight
      (inducedDegenerateEqTriple encode) := by
  intro hcoverage
  let target : Fin 3 → L := fun i ↦ if i = 0 then 1 else 0
  obtain ⟨c, _, _, hterminal⟩ := hcoverage target
  have hzero := inducedDegenerateEqTriple_zero encode hreserve c
  have hcoordinate := congrFun hterminal (0 : Fin 3)
  have hleft : inducedDegenerateEqTriple encode c (0 : Fin 3) = 0 :=
    congrFun hzero 0
  have hright : target (0 : Fin 3) = 1 := by simp [target]
  rw [hleft, hright] at hcoordinate
  exact zero_ne_one hcoordinate

/-- Concrete layout counterexample, robust under every preceding linear
coefficient conversion: the interleaved reserve placement itself forces the
all-zero-point terminal triple to vanish. -/
theorem degenerate_eq_side_counterexample_for_any_reserved_conversion
    {L : Type*} [Field L] [Algebra DeployedField L]
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (conversion : (Fin originalWidth → L) →ₗ[L] (Fin originalWidth → L)) :
    ¬ EqTerminalTripleCoversDeployedKernel queries weight
      (inducedDegenerateEqTriple ((alignedReserveEmbed L).comp conversion)) :=
  degenerate_eq_side_does_not_cover queries weight _
    (alignedReserveEmbed_comp_supported conversion)

/-! ## Proof-dependency audit -/

#print axioms accepted_q18_has_72_distinct_positions
#print axioms accepted_q18_exactly_72_distinct_positions
#print axioms accepted_q18_representatives_nonzero
#print axioms modelledRow896Weight_ne_zero
#print axioms rustRow896Weight_ne_zero
#print axioms accepted_q18_layerZero_gate
#print axioms repeated_fibre_breaks_position_injectivity
#print axioms zero_aligned_factor_zeroes_row
#print axioms zero_aligned_factor_blocks_surjectivity
#print axioms fibreMajor_slotMajor_order_tooth
#print axioms degenerateEqRows_below_reserve
#print axioms degenerateBooleanEqTriple_apply
#print axioms degenerateBooleanEqTriple_zero_of_supported
#print axioms alignedReserveEmbed_supported
#print axioms alignedReserveEmbed_comp_supported
#print axioms inducedDegenerateEqTriple_zero
#print axioms degenerate_eq_side_does_not_cover
#print axioms degenerate_eq_side_counterexample_for_any_reserved_conversion

end AspisV5FreezeAScheduleAvailability
