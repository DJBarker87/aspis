import AspisFormal.V5ComponentBLegalWitnessDifference
import AspisFormal.V5ComponentATerminalRankPredicate
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Component B: schedule-specific coverage of Spend differences

The deployed Rust prover does not expose a mathematical function from an
accepted `SpendWitness` to the 271 coefficients of its *real* degree-27
sumcheck transcript.  It builds an atomic oracle and interpolates each round
after the preceding transcript challenges.  Consequently this file does not
pretend that an arbitrary state vector, the range of the mask encoder, or the
row-976 obstruction direction is the actual legal Spend-difference image.

What can be closed exactly is the schedule-specific residual algebra.  The
public residual map has a 72-coordinate raw base and a four-coordinate tail
(`inactive ||` the point-major MLE triple).  A public Schur
certificate consists of

* a right inverse for the 72-coordinate raw map;
* four directions in the kernel of that raw map; and
* a nonzero determinant for their 4-by-4 inactive/MLE matrix.

The certificate implies surjectivity of the exact 76-coordinate deployed
pad-plus-dependent-pivot map.  Hence it covers every legal Spend residual
difference, whatever the still-unformalised legal image is.  The exact
surjectivity predicate remains the reference `ExactGoodB`; the Schur
predicate is only proved sufficient, not equivalent.  The existing row-976
and all-zero counterexamples are retained: both reject `ExactGoodB` and every
Schur certificate.

A concrete linear lift on the actual 255-pad-plus-pivot row layout proves that
arbitrary values on aligned rows 256 through 383 and a caller-owned inactive
scalar are genuinely available.  The canonical 56 q18-kernel directions and
the fixed first-four tail minor give an executable public `CanonicalFixedMinorGoodB`
predicate.  A literal finite-field matrix and a kernel-checked inverse below
retain one public probe as regression evidence.  Equality between that matrix
and the exact model remains an explicit open premise: this file therefore does
not claim a concrete accepted runtime schedule.  Its synthetic schedule also
has `raw := 0`, so even that equality would establish determinant-predicate
nonvacuity only, not the separate raw-map commuting square or deployed
coverage.  Exact Rust circle
encoding, transcript-to-map extraction,
Spend-to-271-state extraction, field serialization, and verifier enforcement
remain explicitly named interfaces.  Computational Merkle/PCS properties and
hash/random-oracle assumptions remain outside this algebraic file.
-/

namespace AspisV5ComponentBSpendDifferenceCoverage

open Matrix
open AspisV5CompactTerminal
open AspisV5ComponentBCorrelatedResidualCoverage
open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability
open AspisCircleTensorBinding
open AspisCircleGroupOrder
open Polynomial

abbrev Message (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.Message K
abbrev StateSample (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.StateSample K
abbrev PadSample (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.PadSample K
abbrev PadCoordinate :=
  AspisV5ComponentBCorrelatedResidualCoverage.PadCoordinate
abbrev PadVector (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.PadVector K
abbrev RawCoordinate :=
  AspisV5ComponentBCorrelatedResidualCoverage.RawCoordinate
abbrev MLECoordinate :=
  AspisV5ComponentBCorrelatedResidualCoverage.MLECoordinate
abbrev ResidualCoordinate :=
  AspisV5ComponentBCorrelatedResidualCoverage.ResidualCoordinate
abbrev ResidualView (K : Type*) :=
  AspisV5ComponentBCorrelatedResidualCoverage.ResidualView K
abbrev RawView (K : Type*) := RawCoordinate → K
abbrev FinalCoordinate := Fin 4
abbrev FinalView (K : Type*) := FinalCoordinate → K

/-! ## Exact residual order -/

/-- Negation flags in the accepted fixed-circle codeword order.  `false`
means the base coordinate and `true` its negation.  In particular codeword
slot two is `(-x, -y)` and slot three is `(-x, y)`.  The diagnostic
`v5_mask::fibre_positions` helper swaps those last two slots and therefore is
not used as the runtime-order authority. -/
def runtimeFibreNegations : Fin 4 → Bool × Bool :=
  ![(false, false), (false, true), (true, true), (true, false)]

theorem runtimeFibreNegations_values :
    List.ofFn runtimeFibreNegations =
      [(false, false), (false, true), (true, true), (true, false)] := by
  decide

/-- The same runtime order in the discrete four-sign index used by the circle
minor. -/
def runtimeSlotToFibreSign : Fin 4 → FibreSign :=
  ![(0, 0), (0, 1), (1, 1), (1, 0)]

/-- Inverse map from a signed circle point to its accepted codeword slot. -/
def runtimeFibreSignToSlot (sign : FibreSign) : Fin 4 :=
  if hx : (sign.1 : ℕ) = 0 then
    ⟨(sign.2 : ℕ), by have hy := sign.2.isLt; omega⟩
  else
    ⟨3 - (sign.2 : ℕ), by have hy := sign.2.isLt; omega⟩

theorem runtimeSlot_sign_roundtrip (slot : Fin 4) :
    runtimeFibreSignToSlot (runtimeSlotToFibreSign slot) = slot := by
  fin_cases slot <;> rfl

theorem runtimeSign_slot_roundtrip (sign : FibreSign) :
    runtimeSlotToFibreSign (runtimeFibreSignToSlot sign) = sign := by
  rcases sign with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> rfl

def rawToFibreIndex (raw : RawCoordinate) : FibreIndex :=
  (raw.1, runtimeSlotToFibreSign raw.2)

theorem rawToFibreIndex_bijective : Function.Bijective rawToFibreIndex := by
  constructor
  · rintro ⟨leftQuery, leftSlot⟩ ⟨rightQuery, rightSlot⟩ equal
    apply Prod.ext
    · exact congrArg (fun row : FibreIndex ↦ row.1) equal
    · apply Function.LeftInverse.injective
        (fun slot ↦ runtimeSlot_sign_roundtrip slot)
      exact congrArg (fun row : FibreIndex ↦ row.2) equal
  · rintro ⟨query, sign⟩
    refine ⟨(query, runtimeFibreSignToSlot sign), ?_⟩
    apply Prod.ext
    · rfl
    · exact runtimeSign_slot_roundtrip sign

/-- Exact query-major/runtime-slot permutation as an equivalence. -/
noncomputable def rawFibreOrder : RawCoordinate ≃ FibreIndex :=
  Equiv.ofBijective rawToFibreIndex rawToFibreIndex_bijective

/-- A concrete public injective q18 schedule, used only to show that the raw
applicability premise is inhabited.  It does not assert the four-coordinate
terminal Schur condition. -/
def canonicalInjectiveQ18 (query : Fin queryCount) : Fin fibreCount :=
  ⟨query, by
    have hquery := query.isLt
    norm_num [queryCount, fibreCount] at hquery ⊢
    omega⟩

theorem canonicalInjectiveQ18_injective :
    Function.Injective canonicalInjectiveQ18 := by
  intro left right equal
  apply Fin.ext
  simpa [canonicalInjectiveQ18] using congrArg Fin.val equal

/-- Exact public normalization of a stored 17-bit Merkle fibre index into
natural representative order. -/
def normalizeStoredFibreIndex
    (stored : Fin fibreCount) : Fin fibreCount :=
  ⟨(BitVec.ofNat 17 stored).reverse.toNat, by
    change (BitVec.ofNat 17 stored).reverse.toNat < 2 ^ 17
    exact (BitVec.ofNat 17 stored).reverse.isLt⟩

theorem normalizeStoredFibreIndex_involutive :
    Function.Involutive normalizeStoredFibreIndex := by
  intro stored
  apply Fin.ext
  change (BitVec.ofNat 17
      (BitVec.ofNat 17 stored).reverse.toNat).reverse.toNat = stored
  rw [show BitVec.ofNat 17 (BitVec.ofNat 17 stored).reverse.toNat =
      (BitVec.ofNat 17 stored).reverse by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
  simp

theorem normalizeStoredFibreIndex_injective :
    Function.Injective normalizeStoredFibreIndex :=
  normalizeStoredFibreIndex_involutive.injective

/-- Public equality between stored q18 and the natural representative q18. -/
def StoredQ18Normalizes
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  representativeQueries = normalizeStoredFibreIndex ∘ storedQueries

theorem storedQ18Normalizes_injective
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (hnormalizes : StoredQ18Normalizes storedQueries representativeQueries)
    (hstored : Function.Injective storedQueries) :
    Function.Injective representativeQueries := by
  rw [hnormalizes]
  exact normalizeStoredFibreIndex_injective.comp hstored

/-- Exact fixed-circle codeword position `4 * fibre + slot`. -/
def row256CodewordPosition
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) :
    Fin (2 ^ 19) :=
  ⟨4 * (queries row.1 : ℕ) + (runtimeFibreSignToSlot row.2 : ℕ), by
    have hquery := (queries row.1).isLt
    have hslot := (runtimeFibreSignToSlot row.2).isLt
    norm_num [fibreCount] at hquery ⊢
    omega⟩

@[simp] theorem row256CodewordPosition_val
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) :
    (row256CodewordPosition queries row : ℕ) =
      4 * (queries row.1 : ℕ) + (runtimeFibreSignToSlot row.2 : ℕ) :=
  rfl

/-- Exact logical order of the independent B residual:
inactive first, then query-major/fibre-slot raw values, then point-major MLE
values. -/
def residualWireOrdinal : ResidualCoordinate → Fin 76
  | .inl _ => ⟨0, by omega⟩
  | .inr (.inl raw) => ⟨1 + (rawWireOrdinal raw : ℕ), by omega⟩
  | .inr (.inr point) => ⟨73 + (point : ℕ), by omega⟩

@[simp] theorem residualWireOrdinal_inactive :
    residualWireOrdinal (.inl ()) = 0 := rfl

@[simp] theorem residualWireOrdinal_raw_val (raw : RawCoordinate) :
    (residualWireOrdinal (.inr (.inl raw)) : ℕ) =
      1 + 4 * (raw.1 : ℕ) + (raw.2 : ℕ) := by
  change 1 + (rawWireOrdinal raw : ℕ) = _
  rw [rawWireOrdinal_val]
  omega

@[simp] theorem residualWireOrdinal_mle_val (point : MLECoordinate) :
    (residualWireOrdinal (.inr (.inr point)) : ℕ) =
      73 + (point : ℕ) := rfl

theorem rawWireOrdinal_injective : Function.Injective rawWireOrdinal := by
  rintro ⟨leftQuery, leftSlot⟩ ⟨rightQuery, rightSlot⟩ equal
  have hval : 4 * (leftQuery : ℕ) + (leftSlot : ℕ) =
      4 * (rightQuery : ℕ) + (rightSlot : ℕ) := by
    simpa only [rawWireOrdinal] using congrArg Fin.val equal
  have hls := leftSlot.isLt
  have hrs := rightSlot.isLt
  apply Prod.ext
  · apply Fin.ext
    change (leftQuery : ℕ) = (rightQuery : ℕ)
    omega
  · apply Fin.ext
    change (leftSlot : ℕ) = (rightSlot : ℕ)
    omega

theorem residualWireOrdinal_injective :
    Function.Injective residualWireOrdinal := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right => simp
      | inr right =>
          exfalso
          cases right with
          | inl raw =>
              have hval := congrArg Fin.val equal
              simp only [residualWireOrdinal] at hval
              omega
          | inr point =>
              have hval := congrArg Fin.val equal
              simp only [residualWireOrdinal] at hval
              omega
  | inr left =>
      cases right with
      | inl right =>
          exfalso
          cases left with
          | inl raw =>
              have hval := congrArg Fin.val equal
              simp only [residualWireOrdinal] at hval
              omega
          | inr point =>
              have hval := congrArg Fin.val equal
              simp only [residualWireOrdinal] at hval
              omega
      | inr right =>
          cases left with
          | inl leftRaw =>
              cases right with
              | inl rightRaw =>
                  have hordinal : rawWireOrdinal leftRaw =
                      rawWireOrdinal rightRaw := by
                    apply Fin.ext
                    have hval := congrArg Fin.val equal
                    change 1 + (rawWireOrdinal leftRaw : ℕ) =
                      1 + (rawWireOrdinal rightRaw : ℕ) at hval
                    omega
                  rw [rawWireOrdinal_injective hordinal]
              | inr rightPoint =>
                  exfalso
                  have hval := congrArg Fin.val equal
                  simp only [residualWireOrdinal] at hval
                  have hraw := (rawWireOrdinal leftRaw).isLt
                  omega
          | inr leftPoint =>
              cases right with
              | inl rightRaw =>
                  exfalso
                  have hval := congrArg Fin.val equal
                  simp only [residualWireOrdinal] at hval
                  have hraw := (rawWireOrdinal rightRaw).isLt
                  omega
              | inr rightPoint =>
                  congr 2
                  apply Fin.ext
                  have hval := congrArg Fin.val equal
                  simp only [residualWireOrdinal] at hval
                  omega

/-! ## The exact aligned row-256 pad block -/

/-- The full aligned natural-tensor block `256..383` is contained in the
deployed pad rows `224..478`; logical pad coordinates are `32..159`. -/
def row256PadCoordinate (index : Fin 128) : PadCoordinate :=
  ⟨32 + (index : ℕ), by omega⟩

def row256MessageRow (index : Fin 128) : Row :=
  structuredPadRow (row256PadCoordinate index)

@[simp] theorem row256PadCoordinate_val (index : Fin 128) :
    (row256PadCoordinate index : ℕ) = 32 + (index : ℕ) := rfl

@[simp] theorem row256MessageRow_val (index : Fin 128) :
    (row256MessageRow index : ℕ) = 256 + (index : ℕ) := by
  change 224 + (32 + (index : ℕ)) = 256 + (index : ℕ)
  omega

theorem row256MessageRow_injective : Function.Injective row256MessageRow := by
  intro left right equal
  apply Fin.ext
  have hval := congrArg Fin.val equal
  simp only [row256MessageRow_val] at hval
  omega

/-- Exact coordinate readback for every physical pad row.  It is independent
of the inactive functional because the dependent write is at row 993. -/
theorem padPlusPivotEncoder_at_structuredPad
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (sample : PadSample K)
    (coordinate : PadCoordinate) :
    padPlusPivotEncoder inactive sample (structuredPadRow coordinate) =
      sample.1 coordinate := by
  rw [padPlusPivotEncoder_apply, Pi.add_apply, structuredPadMessage_at]
  rw [basis, if_neg (structuredPadRow_ne_pivot coordinate)]
  exact add_zero _

/-- Embed arbitrary values in the exact aligned pad coordinates 32 through
159 and zero every other pad coordinate. -/
def row256PadVector {K : Type*} [Field K]
    (values : Fin 128 → K) : PadVector K :=
  fun coordinate ↦
    if h : 32 ≤ (coordinate : ℕ) ∧ (coordinate : ℕ) < 160 then
      values ⟨(coordinate : ℕ) - 32, by omega⟩
    else 0

@[simp] theorem row256PadVector_at
    {K : Type*} [Field K] (values : Fin 128 → K) (index : Fin 128) :
    row256PadVector values (row256PadCoordinate index) = values index := by
  simp only [row256PadVector, row256PadCoordinate_val]
  rw [dif_pos]
  · congr 1
    apply Fin.ext
    simp
  · have hindex := index.isLt
    omega

/-- Ordinary coefficient block order is `p[0..64] || q[0..64]`. -/
def row256OrdinaryP {K : Type*} [Field K] :
    (Fin 128 → K) →ₗ[K] (Fin 64 → K) :=
  LinearMap.pi fun index ↦ LinearMap.proj ⟨index, by omega⟩

/-- The second ordinary coefficient block. -/
def row256OrdinaryQ {K : Type*} [Field K] :
    (Fin 128 → K) →ₗ[K] (Fin 64 → K) :=
  LinearMap.pi fun index ↦ LinearMap.proj ⟨64 + (index : ℕ), by omega⟩

/-- Physical aligned-row offset of natural `p[index]`. -/
def row256PhysicalP (index : Fin 64) : Fin 128 :=
  ⟨2 * (index : ℕ), by omega⟩

/-- Physical aligned-row offset of natural `q[index]`. -/
def row256PhysicalQ (index : Fin 64) : Fin 128 :=
  ⟨2 * (index : ℕ) + 1, by omega⟩

@[simp] theorem row256PhysicalP_val (index : Fin 64) :
    (row256PhysicalP index : ℕ) = 2 * (index : ℕ) := rfl

@[simp] theorem row256PhysicalQ_val (index : Fin 64) :
    (row256PhysicalQ index : ℕ) = 2 * (index : ℕ) + 1 := rfl

/-- Permanent ordering tooth: physical offset one is natural `q[0]`, whereas
ordinary flat coordinate one is `p[1]`. -/
theorem row256_q0_is_physical_one_and_p1_is_physical_two :
    row256PhysicalQ 0 = 1 ∧ row256PhysicalP 1 = 2 := by
  decide

/-- Canonical width-64 ordinary-to-natural conversion followed by Rust's
interleaved physical layout.  Even offsets hold natural `p`; odd offsets hold
natural `q`. -/
noncomputable def row256OrdinaryToInterleavedNatural
    (K : Type*) [Field K] :
    (Fin 128 → K) →ₗ[K] (Fin 128 → K) :=
  LinearMap.pi fun physical ↦
    if heven : (physical : ℕ) % 2 = 0 then
      (LinearMap.proj ⟨(physical : ℕ) / 2, by
        have hphysical := physical.isLt
        omega⟩).comp
        ((monomialToNatural K 64).mulVecLin.comp row256OrdinaryP)
    else
      (LinearMap.proj ⟨(physical : ℕ) / 2, by
        have hphysical := physical.isLt
        omega⟩).comp
        ((monomialToNatural K 64).mulVecLin.comp row256OrdinaryQ)

@[simp] theorem row256OrdinaryToInterleavedNatural_at_p
    {K : Type*} [Field K] (ordinary : Fin 128 → K) (index : Fin 64) :
    row256OrdinaryToInterleavedNatural K ordinary (row256PhysicalP index) =
      (monomialToNatural K 64).mulVec (row256OrdinaryP ordinary) index := by
  simp [row256OrdinaryToInterleavedNatural, row256PhysicalP]

@[simp] theorem row256OrdinaryToInterleavedNatural_at_q
    {K : Type*} [Field K] (ordinary : Fin 128 → K) (index : Fin 64) :
    row256OrdinaryToInterleavedNatural K ordinary (row256PhysicalQ index) =
      (monomialToNatural K 64).mulVec (row256OrdinaryQ ordinary) index := by
  simp [row256OrdinaryToInterleavedNatural, row256PhysicalQ]
  congr 2
  omega

/-- Choosing the caller-owned inactive scalar to equal the inactive value of
the aligned pad block makes the dependent row-993 coefficient exactly zero.
This is the block-only message used by the raw-matrix correspondence; choosing
the scalar `0` would generally add a nonzero row-993 correction. -/
theorem padPlusPivotEncoder_row256Block
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (values : Fin 128 → K) :
    padPlusPivotEncoder inactive
        (row256PadVector values,
          inactive (structuredPadMessage K (row256PadVector values))) =
      structuredPadMessage K (row256PadVector values) := by
  rw [padPlusPivotEncoder_apply]
  apply add_eq_left.mpr
  funext row
  simp [AspisV5CompactTerminal.basis]

/-- Linear form of the aligned physical-pad embedding. -/
def row256PadEmbedding {K : Type*} [Field K] :
    (Fin 128 → K) →ₗ[K] PadVector K where
  toFun := row256PadVector
  map_add' left right := by
    funext coordinate
    simp only [Pi.add_apply, row256PadVector]
    split <;> simp
  map_smul' scalar values := by
    funext coordinate
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      row256PadVector]
    split <;> simp

/-- Linear lift of a physical row-256 block whose desired inactive scalar is
its own inactive value.  The dependent row-993 write therefore vanishes. -/
noncomputable def row256PureBlockPadLift
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K) :
    (Fin 128 → K) →ₗ[K] PadSample K where
  toFun values :=
    let pads := row256PadEmbedding values
    (pads, inactive (structuredPadMessage K pads))
  map_add' left right := by
    apply Prod.ext
    · exact map_add row256PadEmbedding left right
    · change inactive
          (structuredPadMessage K (row256PadEmbedding (left + right))) =
        inactive (structuredPadMessage K (row256PadEmbedding left)) +
          inactive (structuredPadMessage K (row256PadEmbedding right))
      simp only [map_add]
  map_smul' scalar values := by
    apply Prod.ext
    · exact map_smul row256PadEmbedding scalar values
    · change inactive
          (structuredPadMessage K (row256PadEmbedding (scalar • values))) =
        scalar • inactive
          (structuredPadMessage K (row256PadEmbedding values))
      simp only [map_smul]

/-- Complete ordinary p||q to converted/interleaved physical pad lift. -/
noncomputable def row256OrdinaryPadLift
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K) :
    (Fin 128 → K) →ₗ[K] PadSample K :=
  (row256PureBlockPadLift inactive).comp
    (row256OrdinaryToInterleavedNatural K)

theorem padPlusPivotEncoder_row256OrdinaryPadLift
    {K : Type*} [Field K] (inactive : Message K →ₗ[K] K)
    (ordinary : Fin 128 → K) :
    padPlusPivotEncoder inactive (row256OrdinaryPadLift inactive ordinary) =
      structuredPadMessage K
        (row256PadVector
          (row256OrdinaryToInterleavedNatural K ordinary)) := by
  exact padPlusPivotEncoder_row256Block inactive _

/-! ## Universal raw rank in the row-256 algebraic model -/

abbrev DeployedField := AspisCircleRectangularMasking.DeployedField
abbrev FibreIndex := AspisCircleRectangularMasking.FibreIndex

/-- The sole line-twiddle factor selected by binary message rows 256 through
383: bit eight is set and bits nine and above are clear.  Rust source equality
still has to identify its bit-reversed layer index and output sign. -/
def row256Factor (index : Fin (2 ^ 10)) (negative : Bool) : DeployedField :=
  signed negative (X (g ^ lineTwiddleExp 7 index))

/-- Every factor in the row-256 family is nonzero.  This is derived from the
public three-factor row-896 theorem, so it does not rely on the private
`lineTwiddle7_ne_zero` helper. -/
theorem row256Factor_ne_zero
    (index : Fin (2 ^ 10)) (negative : Bool) :
    row256Factor index negative ≠ 0 := by
  intro hzero
  have h896 := row896Factor_ne_zero
    (⟨0, by norm_num⟩ : Fin (2 ^ 11)) index
    (⟨0, by norm_num⟩ : Fin (2 ^ 9)) false negative false
  apply h896
  change
    signed false (X (g ^ lineTwiddleExp 6 (0 : Fin (2 ^ 11)))) *
      row256Factor index negative *
        signed false (X (g ^ lineTwiddleExp 8 (0 : Fin (2 ^ 9)))) = 0
  rw [hzero]
  simp

/-- Layer-seven table index selected by the exact codeword position. -/
def row256Layer7Index
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) :
    Fin (2 ^ 10) :=
  ⟨(row256CodewordPosition queries row : ℕ) / (2 ^ 9), by
    have hposition := (row256CodewordPosition queries row).isLt
    norm_num at hposition ⊢
    omega⟩

/-- The line-twiddle table is stored in 10-bit bit-reversed order.  The
algebraic exponent model therefore consumes the natural index obtained by
reversing the stored table index selected from the codeword position. -/
def normalizeStoredRow256LayerIndex
  (stored : Fin (2 ^ 10)) : Fin (2 ^ 10) :=
  ⟨(BitVec.ofNat 10 stored).reverse.toNat, by
    exact (BitVec.ofNat 10 stored).reverse.isLt⟩

/-- Natural line-layer index used by `lineTwiddleExp`. -/
def row256Layer7NaturalIndex
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) :
    Fin (2 ^ 10) :=
  normalizeStoredRow256LayerIndex (row256Layer7Index queries row)

/-- Concrete storage-order tooth.  Stored fibre 128, slot zero selects table
index 1, whose natural exponent index is 512.  Omitting the reversal therefore
does not describe the deployed constructor. -/
theorem row256_stored128_requires_layer_bit_reversal :
    let queries : Fin queryCount → Fin fibreCount :=
      fun _ ↦ ⟨128, by norm_num [fibreCount]⟩
    let row : FibreIndex :=
      (⟨0, by norm_num [queryCount]⟩,
        (⟨0, by norm_num⟩, ⟨0, by norm_num⟩))
    row256Layer7Index queries row = 1 ∧
      row256Layer7NaturalIndex queries row = 512 := by
  decide

/-- Output sign selected by bit eight of the exact codeword position. -/
def row256Layer7Negative
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) : Bool :=
  (row256CodewordPosition queries row : ℕ).testBit 8

/-- Algebraic row-256 weight indexed by the accepted codeword position.  A
Rust correspondence still has to identify the realised line-layer table with
this generator model; nonvanishing itself is unconditional. -/
def row256ModelWeight
    (queries : Fin queryCount → Fin fibreCount) :
    FibreIndex → DeployedField :=
  fun row ↦
    row256Factor (row256Layer7NaturalIndex queries row)
      (row256Layer7Negative queries row)

theorem row256ModelWeight_ne_zero
    (queries : Fin queryCount → Fin fibreCount) (row : FibreIndex) :
    row256ModelWeight queries row ≠ 0 :=
  row256Factor_ne_zero _ _

/-! ## Canonical 56-dimensional raw-kernel family -/

/-- Block-major index for the two families `K(X) * X^i`, `0 ≤ i < 28`. -/
abbrev CanonicalKernelDirection := Fin 2 × Fin 28

/-- Public ordinal: first the 28 pure-x directions, then the 28 y-block
directions. -/
def canonicalKernelOrdinal (direction : CanonicalKernelDirection) : Fin 56 :=
  ⟨28 * (direction.1 : ℕ) + (direction.2 : ℕ), by omega⟩

theorem canonicalKernelOrdinal_injective :
    Function.Injective canonicalKernelOrdinal := by
  rintro ⟨leftBlock, leftShift⟩ ⟨rightBlock, rightShift⟩ equal
  have hval := congrArg Fin.val equal
  simp only [canonicalKernelOrdinal] at hval
  apply Prod.ext
  · apply Fin.ext
    change (leftBlock : ℕ) = (rightBlock : ℕ)
    have hlb := leftBlock.isLt
    have hrb := rightBlock.isLt
    have hls := leftShift.isLt
    have hrs := rightShift.isLt
    omega
  · apply Fin.ext
    change (leftShift : ℕ) = (rightShift : ℕ)
    have hlb := leftBlock.isLt
    have hrb := rightBlock.isLt
    have hls := leftShift.isLt
    have hrs := rightShift.isLt
    omega

/-- Degree-`36+i` polynomial vanishing at all 36 signed q18 x-nodes. -/
noncomputable def row256KernelPolynomial
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (shift : Fin 28) : DeployedField[X] :=
  AspisV5AtomicComponentA.kernelPoly representativeQueries *
    Polynomial.X ^ (shift : ℕ)

theorem row256KernelPolynomial_natDegree_lt_64
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (shift : Fin 28) :
    (row256KernelPolynomial representativeQueries shift).natDegree < 64 := by
  rw [row256KernelPolynomial,
    Polynomial.Monic.natDegree_mul
      (AspisV5ComponentARankCompletion.kernelPoly_monic representativeQueries)
      (monic_X_pow (shift : ℕ)),
    AspisV5ComponentARankCompletion.kernelPoly_natDegree,
    natDegree_X_pow]
  have hshift := shift.isLt
  omega

theorem row256KernelPolynomial_eval_node_zero
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (shift : Fin 28) (query : Fin queryCount) (sign : Fin 2) :
    (row256KernelPolynomial representativeQueries shift).eval
        (signedCoordinate sign
          (representativeX (representativeQueries query))) = 0 := by
  rw [row256KernelPolynomial, eval_mul,
    AspisV5AtomicComponentA.kernelPoly_eval_node_zero]
  exact zero_mul _

/-- Ordinary p-block coefficient vector for one degree-<64 polynomial. -/
def row256PPolynomialVector (polynomial : DeployedField[X]) :
    Fin 128 → DeployedField :=
  fun column ↦
    if (column : ℕ) < 64 then polynomial.coeff (column : ℕ) else 0

/-- Ordinary q-block coefficient vector for one degree-<64 polynomial. -/
def row256QPolynomialVector (polynomial : DeployedField[X]) :
    Fin 128 → DeployedField :=
  fun column ↦
    if (column : ℕ) < 64 then 0
    else polynomial.coeff ((column : ℕ) - 64)

/-- The exact block-major family of 56 ordinary directions. -/
noncomputable def row256CanonicalKernelOrdinary
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (direction : CanonicalKernelDirection) : Fin 128 → DeployedField :=
  if direction.1 = 0 then
    row256PPolynomialVector
      (row256KernelPolynomial representativeQueries direction.2)
  else
    row256QPolynomialVector
      (row256KernelPolynomial representativeQueries direction.2)

/-- The 72-by-128 ordinary-monomial point-evaluation model for the aligned
block.  The first 64 columns are pure-x and the last 64 are y-weighted.
Equality with Rust's natural tensor basis is deliberately not asserted. -/
def row256FibreEval
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix FibreIndex (Fin 128) DeployedField :=
  fun row column ↦
    weight row *
      if (column : ℕ) < 64 then
        signedCoordinate row.2.1 (representativeX (queries row.1)) ^
          (column : ℕ)
      else
        signedCoordinate row.2.2 (representativeY (queries row.1)) *
          signedCoordinate row.2.1 (representativeX (queries row.1)) ^
            ((column : ℕ) - 64)

private theorem row256PRowEval
    (weight x y : DeployedField) (polynomial : DeployedField[X])
    (hdegree : polynomial.natDegree < 64) :
    (∑ column : Fin 128,
      (weight * (if (column : ℕ) < 64 then x ^ (column : ℕ)
        else y * x ^ ((column : ℕ) - 64))) *
        (if (column : ℕ) < 64 then
          polynomial.coeff (column : ℕ) else 0)) =
      weight * polynomial.eval x := by
  classical
  let term : ℕ → DeployedField := fun n ↦
    (weight * (if n < 64 then x ^ n else y * x ^ (n - 64))) *
      (if n < 64 then polynomial.coeff n else 0)
  change (∑ column : Fin 128, term column) = _
  rw [Fin.sum_univ_eq_sum_range term 128]
  have hsubset : Finset.range 64 ⊆ Finset.range 128 := by
    intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  have htail : ∀ n ∈ Finset.range 128, n ∉ Finset.range 64 →
      term n = 0 := by
    intro n _ hn
    rw [Finset.mem_range] at hn
    simp [term, hn]
  rw [← Finset.sum_subset hsubset htail]
  have hcongr : ∀ n ∈ Finset.range 64,
      term n =
      weight * (polynomial.coeff n * x ^ n) := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [term, if_pos hn]
    ring
  rw [Finset.sum_congr rfl hcongr,
    ← Finset.mul_sum (Finset.range 64)
      (fun n ↦ polynomial.coeff n * x ^ n) weight,
    eval_eq_sum_range' hdegree x]

private theorem row256QRowEval
    (weight x y : DeployedField) (polynomial : DeployedField[X])
    (hdegree : polynomial.natDegree < 64) :
    (∑ column : Fin 128,
      (weight * (if (column : ℕ) < 64 then x ^ (column : ℕ)
        else y * x ^ ((column : ℕ) - 64))) *
        (if (column : ℕ) < 64 then 0
          else polynomial.coeff ((column : ℕ) - 64))) =
      weight * y * polynomial.eval x := by
  classical
  let term : ℕ → DeployedField := fun n ↦
    (weight * (if n < 64 then x ^ n else y * x ^ (n - 64))) *
      (if n < 64 then 0 else polynomial.coeff (n - 64))
  change (∑ column : Fin 128, term column) = _
  rw [Fin.sum_univ_eq_sum_range term 128,
    show 128 = 64 + 64 by omega, Finset.sum_range_add]
  have hfirst :
      (∑ n ∈ Finset.range 64, term n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_range] at hn
    simp [term, hn]
  rw [hfirst, zero_add]
  have hcongr : ∀ n ∈ Finset.range 64,
      term (64 + n) =
        (weight * y) * (polynomial.coeff n * x ^ n) := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [term, show ¬ 64 + n < 64 by omega, if_false,
      Nat.add_sub_cancel_left]
    ring
  rw [Finset.sum_congr rfl hcongr,
    ← Finset.mul_sum (Finset.range 64)
      (fun n ↦ polynomial.coeff n * x ^ n) (weight * y),
    eval_eq_sum_range' hdegree x]

private theorem row256_mulVec_pPolynomial
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (polynomial : DeployedField[X]) (hdegree : polynomial.natDegree < 64)
    (row : FibreIndex) :
    (row256FibreEval queries weight).mulVec
        (row256PPolynomialVector polynomial) row =
      weight row * polynomial.eval
        (signedCoordinate row.2.1
          (representativeX (queries row.1))) := by
  change (∑ column : Fin 128,
      row256FibreEval queries weight row column *
        row256PPolynomialVector polynomial column) = _
  simp only [row256FibreEval, row256PPolynomialVector]
  exact row256PRowEval _ _ _ polynomial hdegree

private theorem row256_mulVec_qPolynomial
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (polynomial : DeployedField[X]) (hdegree : polynomial.natDegree < 64)
    (row : FibreIndex) :
    (row256FibreEval queries weight).mulVec
        (row256QPolynomialVector polynomial) row =
      weight row *
        signedCoordinate row.2.2 (representativeY (queries row.1)) *
          polynomial.eval
            (signedCoordinate row.2.1
              (representativeX (queries row.1))) := by
  change (∑ column : Fin 128,
      row256FibreEval queries weight row column *
        row256QPolynomialVector polynomial column) = _
  simp only [row256FibreEval, row256QPolynomialVector]
  exact row256QRowEval _ _ _ polynomial hdegree

/-- All 56 public polynomial directions lie in the raw kernel, for every row
weight and every q18 schedule. -/
theorem row256CanonicalKernelOrdinary_mulVec_zero
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (direction : CanonicalKernelDirection) :
    (row256FibreEval representativeQueries weight).mulVec
      (row256CanonicalKernelOrdinary representativeQueries direction) = 0 := by
  funext row
  rcases direction with ⟨block, shift⟩
  by_cases hblock : block = 0
  · rw [row256CanonicalKernelOrdinary, if_pos hblock,
      row256_mulVec_pPolynomial _ _ _
        (row256KernelPolynomial_natDegree_lt_64 representativeQueries shift),
      row256KernelPolynomial_eval_node_zero]
    exact mul_zero _
  · rw [row256CanonicalKernelOrdinary, if_neg hblock,
      row256_mulVec_qPolynomial _ _ _
        (row256KernelPolynomial_natDegree_lt_64 representativeQueries shift),
      row256KernelPolynomial_eval_node_zero]
    simp

/-- Embed the existing 72-column four-sign minor: pure degrees 0..35 and
y-weighted degrees 0..35 inside the two width-64 blocks. -/
def row256SelectedFibreColumn (column : FibreIndex) : Fin 128 :=
  if h : column.2.2 = 0 then
    ⟨fibreXDegree column, by
      have hdegree := fibreXDegree_lt_rectangularHalf column
      norm_num [rectangularHalf] at hdegree ⊢
      omega⟩
  else
    ⟨64 + fibreXDegree column, by
      have hdegree := fibreXDegree_lt_rectangularHalf column
      norm_num [rectangularHalf] at hdegree ⊢
      omega⟩

theorem row256_selected_minor_eq
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    (row256FibreEval queries weight).submatrix id
        row256SelectedFibreColumn =
      Matrix.diagonal weight *
        fibreEvaluationMinor
          (fun index ↦ representativeX (queries index))
          (fun index ↦ representativeY (queries index)) := by
  ext row column
  rcases row with ⟨query, sign⟩
  rcases column with ⟨degree, character⟩
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_mul,
    row256FibreEval]
  rw [fibreEvaluationMinor_is_block_eval]
  congr 1
  have hsmall : fibreXDegree (degree, character) < 64 := by
    have hdegree := fibreXDegree_lt_rectangularHalf (degree, character)
    norm_num [rectangularHalf] at hdegree ⊢
    omega
  have hcharacter : character.2 = 0 ∨ character.2 = 1 := by omega
  have hlt : 2 * (degree : ℕ) + (character.1 : ℕ) < 64 := by
    simpa [fibreXDegree] using hsmall
  rcases hcharacter with hcharacter | hcharacter
  · simp [row256SelectedFibreColumn, fibreXDegree, hcharacter, hlt,
      queryCount, pow_add]
  · simp [row256SelectedFibreColumn, fibreXDegree, hcharacter,
      queryCount, pow_add]
    ring

theorem row256_selected_minor_det_ne_zero
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    ((row256FibreEval queries weight).submatrix id
      row256SelectedFibreColumn).det ≠ 0 := by
  rw [row256_selected_minor_eq, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun row _ ↦ hweight row))
    (spend_fibre_minor_det_ne_zero queries hqueries)

/-- Sparse embedding of the 72 selected minor columns into the full
128-coordinate ordinary block. -/
def row256SelectedEmbedding :
    Matrix (Fin 128) FibreIndex DeployedField :=
  fun column selected ↦
    if column = row256SelectedFibreColumn selected then 1 else 0

theorem row256_mul_selectedEmbedding
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    row256FibreEval queries weight * row256SelectedEmbedding =
      (row256FibreEval queries weight).submatrix id
        row256SelectedFibreColumn := by
  ext row selected
  simp [Matrix.mul_apply, row256SelectedEmbedding]

/-- An explicit public right-inverse matrix obtained from the inverse of the
fixed 72-column minor.  Unlike an arbitrary choice of a preimage, this is a
deterministic algebraic function of q18 and its row weights. -/
noncomputable def row256RawRightInverse
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix (Fin 128) FibreIndex DeployedField :=
  row256SelectedEmbedding *
    ((row256FibreEval queries weight).submatrix id
      row256SelectedFibreColumn)⁻¹

theorem row256RawRightInverse_is_right_inverse
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    row256FibreEval queries weight *
        row256RawRightInverse queries weight = 1 := by
  rw [row256RawRightInverse, ← Matrix.mul_assoc,
    row256_mul_selectedEmbedding]
  apply Matrix.mul_nonsing_inv
  exact isUnit_iff_ne_zero.mpr
    (row256_selected_minor_det_ne_zero queries hqueries weight hweight)

/-- The explicit minor inverse is a q18-derived linear raw lift. -/
noncomputable def row256RawRightInverseLin
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    (FibreIndex → DeployedField) →ₗ[DeployedField]
      (Fin 128 → DeployedField) :=
  (row256RawRightInverse queries weight).mulVecLin

theorem row256RawRightInverseLin_recovers
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0)
    (target : FibreIndex → DeployedField) :
    (row256FibreEval queries weight).mulVecLin
        (row256RawRightInverseLin queries weight target) = target := by
  rw [row256RawRightInverseLin, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    row256RawRightInverse_is_right_inverse queries hqueries weight hweight,
    Matrix.one_mulVec]

theorem row256FibreEval_rank_eq_72
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    (row256FibreEval queries weight).rank = 72 := by
  have hdet :=
    row256_selected_minor_det_ne_zero queries hqueries weight hweight
  let minor : Matrix FibreIndex FibreIndex DeployedField :=
    (row256FibreEval queries weight).submatrix id
      row256SelectedFibreColumn
  have hdetMinor : minor.det ≠ 0 := by simpa [minor] using hdet
  have hminorRank : minor.rank = Fintype.card FibreIndex :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hdetMinor).rank_matrix
  have hlower : Fintype.card FibreIndex ≤
      (row256FibreEval queries weight).rank := by
    rw [← hminorRank]
    change ((row256FibreEval queries weight).submatrix id
      row256SelectedFibreColumn).rank ≤ _
    exact Matrix.rank_submatrix_le
      (row256FibreEval queries weight) id row256SelectedFibreColumn
  have hupper := Matrix.rank_le_card_height (row256FibreEval queries weight)
  have hcard : Fintype.card FibreIndex = 72 := by
    norm_num [FibreIndex, FibreSign, queryCount]
  omega

theorem row256FibreEval_mulVec_surjective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective (row256FibreEval queries weight).mulVec := by
  change Function.Surjective ⇑(row256FibreEval queries weight).mulVecLin
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change (row256FibreEval queries weight).rank =
    Module.finrank DeployedField (FibreIndex → DeployedField)
  rw [row256FibreEval_rank_eq_72 queries hqueries weight hweight,
    Module.finrank_pi]
  norm_num [FibreIndex, FibreSign, queryCount]

/-- The raw kernel has the advertised dimension `128 - 72 = 56`.  This does
not select the four directions needed by the final Schur determinant. -/
theorem row256FibreEval_kernel_finrank_eq_56
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Module.finrank DeployedField
      (LinearMap.ker (row256FibreEval queries weight).mulVecLin) = 56 := by
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (row256FibreEval queries weight).mulVecLin
  change (row256FibreEval queries weight).rank +
      Module.finrank DeployedField
        (LinearMap.ker (row256FibreEval queries weight).mulVecLin) =
      Module.finrank DeployedField (Fin 128 → DeployedField) at hrankNullity
  rw [row256FibreEval_rank_eq_72 queries hqueries weight hweight,
    Module.finrank_pi] at hrankNullity
  norm_num at hrankNullity ⊢
  omega

/-- For the exact accepted codeword geometry, injective q18 alone supplies
the nonzero-weight hypothesis in the algebraic row-256 model. -/
theorem row256ModelFibreEval_rank_eq_72
    (storedQueries representativeQueries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries) :
    (row256FibreEval representativeQueries
      (row256ModelWeight storedQueries)).rank = 72 :=
  row256FibreEval_rank_eq_72 representativeQueries hqueries _
    (row256ModelWeight_ne_zero storedQueries)

theorem row256ModelFibreEval_kernel_finrank_eq_56
    (storedQueries representativeQueries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries) :
    Module.finrank DeployedField
      (LinearMap.ker
        (row256FibreEval representativeQueries
          (row256ModelWeight storedQueries)).mulVecLin) = 56 :=
  row256FibreEval_kernel_finrank_eq_56 representativeQueries hqueries _
    (row256ModelWeight_ne_zero storedQueries)

theorem row256ModelRawRightInverse_is_right_inverse
    (storedQueries representativeQueries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries) :
    row256FibreEval representativeQueries (row256ModelWeight storedQueries) *
        row256RawRightInverse representativeQueries
          (row256ModelWeight storedQueries) = 1 :=
  row256RawRightInverse_is_right_inverse representativeQueries hqueries _
    (row256ModelWeight_ne_zero storedQueries)

section Tower

variable {L : Type*} [CommRing L] [Algebra DeployedField L]

/-- Scalar extension of the row-256 raw matrix.  Instantiation with deployed
QM31 remains a separate field/coder correspondence. -/
def extendedRow256FibreEval
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix FibreIndex (Fin 128) L :=
  (row256FibreEval queries weight).map (algebraMap DeployedField L)

/-- The same scalar-extended matrix in exact query-major/runtime-slot order. -/
def wireOrderedExtendedRow256FibreEval
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix RawCoordinate (Fin 128) L :=
  fun raw column ↦
    extendedRow256FibreEval (L := L) queries weight
      (rawToFibreIndex raw) column

/-- Scalar extension of one canonical raw-kernel direction. -/
noncomputable def extendedRow256CanonicalKernelOrdinary
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (direction : CanonicalKernelDirection) : Fin 128 → L :=
  fun column ↦ algebraMap DeployedField L
    (row256CanonicalKernelOrdinary representativeQueries direction column)

theorem extendedRow256CanonicalKernelOrdinary_mulVec_zero
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (direction : CanonicalKernelDirection) :
    (extendedRow256FibreEval (L := L) representativeQueries weight).mulVec
      (extendedRow256CanonicalKernelOrdinary
        representativeQueries direction) = 0 := by
  funext row
  have mapped := RingHom.map_mulVec (algebraMap DeployedField L)
    (row256FibreEval representativeQueries weight)
    (row256CanonicalKernelOrdinary representativeQueries direction) row
  rw [row256CanonicalKernelOrdinary_mulVec_zero] at mapped
  simp only [Pi.zero_apply, map_zero] at mapped
  exact mapped.symm

theorem wireOrderedExtendedRow256CanonicalKernel_mulVec_zero
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (direction : CanonicalKernelDirection) :
    (wireOrderedExtendedRow256FibreEval (L := L)
      representativeQueries weight).mulVec
        (extendedRow256CanonicalKernelOrdinary
          representativeQueries direction) = 0 := by
  funext raw
  exact congrFun
    (extendedRow256CanonicalKernelOrdinary_mulVec_zero
      (L := L) representativeQueries weight direction)
    (rawToFibreIndex raw)

/-- Scalar extension of the explicit selected-minor right inverse. -/
noncomputable def extendedRow256RawRightInverse
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix (Fin 128) FibreIndex L :=
  (row256RawRightInverse representativeQueries weight).map
    (algebraMap DeployedField L)

theorem extendedRow256RawRightInverse_is_right_inverse
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    extendedRow256FibreEval (L := L) representativeQueries weight *
        extendedRow256RawRightInverse (L := L)
          representativeQueries weight = 1 := by
  rw [extendedRow256FibreEval, extendedRow256RawRightInverse,
    ← Matrix.map_mul,
    row256RawRightInverse_is_right_inverse
      representativeQueries hqueries weight hweight]
  exact Matrix.map_one (algebraMap DeployedField L)
    (map_zero (algebraMap DeployedField L))
    (map_one (algebraMap DeployedField L))

/-- Reindex a query-major/runtime-slot raw target into signed-fibre order. -/
noncomputable def rawTargetToFibre :
    RawView L →ₗ[L] (FibreIndex → L) :=
  LinearMap.pi fun row ↦ LinearMap.proj (rawFibreOrder.symm row)

/-- Explicit q18-derived ordinary-coefficient lift in runtime raw order. -/
noncomputable def wireOrderedRow256RawRightInverseLin
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    RawView L →ₗ[L] (Fin 128 → L) :=
  (extendedRow256RawRightInverse (L := L)
    representativeQueries weight).mulVecLin.comp rawTargetToFibre

theorem wireOrderedRow256RawRightInverseLin_recovers
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0)
    (target : RawView L) :
    (wireOrderedExtendedRow256FibreEval (L := L)
      representativeQueries weight).mulVec
        (wireOrderedRow256RawRightInverseLin
          representativeQueries weight target) = target := by
  funext raw
  change (extendedRow256FibreEval (L := L)
      representativeQueries weight).mulVec
    ((extendedRow256RawRightInverse (L := L)
      representativeQueries weight).mulVec
        (rawTargetToFibre target)) (rawFibreOrder raw) = target raw
  rw [Matrix.mulVec_mulVec,
    extendedRow256RawRightInverse_is_right_inverse
      representativeQueries hqueries weight hweight,
    Matrix.one_mulVec]
  simp [rawTargetToFibre, rawFibreOrder]

theorem extendedRow256FibreEval_mulVec_surjective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective
      (extendedRow256FibreEval (L := L) queries weight).mulVec :=
  AspisV5ComponentARankCompletion.mulVec_map_surjective
    (algebraMap DeployedField L) _
      (row256FibreEval_mulVec_surjective queries hqueries weight hweight)

theorem wireOrderedExtendedRow256FibreEval_mulVec_surjective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective
      (wireOrderedExtendedRow256FibreEval (L := L) queries weight).mulVec := by
  let order : RawCoordinate ≃ FibreIndex :=
    Equiv.ofBijective rawToFibreIndex rawToFibreIndex_bijective
  intro target
  let fibreTarget : FibreIndex → L := fun row ↦ target (order.symm row)
  obtain ⟨coefficients, hcoefficients⟩ :=
    extendedRow256FibreEval_mulVec_surjective
      (L := L) queries hqueries weight hweight fibreTarget
  refine ⟨coefficients, ?_⟩
  funext raw
  change (extendedRow256FibreEval (L := L) queries weight).mulVec
      coefficients (order raw) = target raw
  rw [hcoefficients]
  simp [fibreTarget, order]

end Tower

/-! ## Public schedule-specific GoodB -/

/-- The exact schedule-derived maps needed by Component B.  Both fields are
public functions of q18 and the ten-round transcript point; no witness is a
field of this structure. -/
structure PublicResidualSchedule (K : Type*) [Field K] where
  raw : Message K →ₗ[K] (RawCoordinate → K)
  mle : Message K →ₗ[K] (MLECoordinate → K)

/-- The exact reference predicate: the deployed 255 pads plus dependent pivot
cover all 76 independent residual coordinates for this public schedule. -/
def ExactGoodB {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K) : Prop :=
  Function.Surjective
    (completeResidualMap inactive schedule.raw schedule.mle)

/-- The 72 raw values of the pad-plus-pivot message. -/
noncomputable def rawResidualMap {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K) :
    PadSample K →ₗ[K] RawView K :=
  schedule.raw.comp (padPlusPivotEncoder inactive)

/-- Final four coordinates in the order `inactive || 3 point-major MLE`.
Using `Fin.cases` makes coordinate zero the inactive claim and coordinates
one through three the MLE points zero through two. -/
noncomputable def finalResidualMap {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K) :
    PadSample K →ₗ[K] FinalView K :=
  LinearMap.pi fun coordinate ↦
    Fin.cases
      (inactive.comp (padPlusPivotEncoder inactive))
      (fun point ↦
        (LinearMap.proj point).comp
          (schedule.mle.comp (padPlusPivotEncoder inactive)))
      coordinate

/-- Pack a residual target into the final-coordinate order used by the
4-by-4 Schur block. -/
def packFinal {K : Type*} [Field K] (target : ResidualView K) : FinalView K :=
  Fin.cases target.1 target.2.2

/-- Public block data checked by the Schur predicate. -/
structure PublicSchurData (K : Type*) [Field K] where
  rawLift : RawView K →ₗ[K] PadSample K
  kernelDirection : FinalCoordinate → PadSample K

/-- The final 4-by-4 matrix after restricting to four supplied raw-kernel
directions.  Row zero is inactive; rows one through three are point-major MLE
outputs. -/
noncomputable def schurMatrix {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K)
    (data : PublicSchurData K) : Matrix FinalCoordinate FinalCoordinate K :=
  fun output direction =>
    finalResidualMap inactive schedule (data.kernelDirection direction) output

/-- Checkable sufficient predicate: the raw lift is a right inverse, the four
directions preserve all 72 raw outputs, and the final determinant is nonzero. -/
def SchurGoodB {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K)
    (data : PublicSchurData K) : Prop :=
  (rawResidualMap inactive schedule).comp data.rawLift = LinearMap.id
    ∧ (∀ direction,
      rawResidualMap inactive schedule (data.kernelDirection direction) = 0)
    ∧ (schurMatrix inactive schedule data).det ≠ 0

/-- The 72+4 block/Schur certificate proves exact ambient residual coverage.
Every conjunct is used: the raw right inverse fixes the first 72 outputs,
the kernel condition prevents the final correction from disturbing them, and
the determinant solves inactive plus the final three MLE coordinates. -/
theorem schurGoodB_implies_exactGoodB
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K)
    (data : PublicSchurData K) (hgood : SchurGoodB inactive schedule data) :
    ExactGoodB inactive schedule := by
  intro target
  let rawTarget : RawView K := target.2.1
  let rawSample : PadSample K := data.rawLift rawTarget
  let finalTarget : FinalView K :=
    packFinal target - finalResidualMap inactive schedule rawSample
  have hmatrixSurjective :
      Function.Surjective (schurMatrix inactive schedule data).mulVec := by
    rw [Matrix.mulVec_surjective_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hgood.2.2
  obtain ⟨coefficients, hcoefficients⟩ := hmatrixSurjective finalTarget
  let correction : PadSample K :=
    ∑ direction, coefficients direction • data.kernelDirection direction
  have hrawSample :
      rawResidualMap inactive schedule rawSample = rawTarget := by
    have happ := LinearMap.congr_fun hgood.1 rawTarget
    simpa [rawSample] using happ
  have hrawCorrection :
      rawResidualMap inactive schedule correction = 0 := by
    simp only [correction, map_sum, map_smul, hgood.2.1, smul_zero,
      Finset.sum_const_zero]
  have hfinalCorrection :
      finalResidualMap inactive schedule correction =
        (schurMatrix inactive schedule data).mulVec coefficients := by
    funext point
    simp only [correction, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      schurMatrix]
    apply Finset.sum_congr rfl
    intro direction _
    rw [mul_comm]
  refine ⟨rawSample + correction, ?_⟩
  have hraw :
      rawResidualMap inactive schedule (rawSample + correction) =
        rawTarget := by
    rw [map_add, hrawSample, hrawCorrection, add_zero]
  have hfinal :
      finalResidualMap inactive schedule (rawSample + correction) =
        packFinal target := by
    rw [map_add, hfinalCorrection, hcoefficients]
    simp [finalTarget]
  apply Prod.ext
  · exact congrFun hfinal 0
  · apply Prod.ext
    · exact hraw
    · funext point
      exact congrFun hfinal point.succ

/-! ## Canonical fixed-minor GoodB -/

/-- Fixed columns zero through three of the block-major 56-direction family. -/
def fixedCanonicalKernelDirection
    (column : FinalCoordinate) : CanonicalKernelDirection :=
  (0, ⟨column, by omega⟩)

@[simp] theorem fixedCanonicalKernelDirection_ordinal
    (column : FinalCoordinate) :
    canonicalKernelOrdinal (fixedCanonicalKernelDirection column) =
      ⟨column, by omega⟩ := by
  apply Fin.ext
  simp [fixedCanonicalKernelDirection, canonicalKernelOrdinal]

section CanonicalGood

variable {K : Type*} [Field K] [Algebra DeployedField K]

/-- One canonical ordinary kernel direction, scalar-extended, converted to
natural coefficients, interleaved, and embedded in the exact physical pad
rows. -/
noncomputable def canonicalKernelPadDirection
    (inactive : Message K →ₗ[K] K)
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (direction : CanonicalKernelDirection) : PadSample K :=
  row256OrdinaryPadLift inactive
    (extendedRow256CanonicalKernelOrdinary representativeQueries direction)

/-- Exact public 4-by-56 tail matrix: inactive first, followed by the three
point-major MLE outputs. -/
noncomputable def canonicalKernelTailMatrix
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (representativeQueries : Fin queryCount → Fin fibreCount) :
    Matrix FinalCoordinate CanonicalKernelDirection K :=
  fun output direction ↦
    finalResidualMap inactive schedule
      (canonicalKernelPadDirection inactive representativeQueries direction)
      output

/-- The fixed columns-zero-through-three 4-by-4 minor. -/
noncomputable def canonicalFixedTailMinor
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (representativeQueries : Fin queryCount → Fin fibreCount) :
    Matrix FinalCoordinate FinalCoordinate K :=
  (canonicalKernelTailMatrix inactive schedule representativeQueries).submatrix
    id fixedCanonicalKernelDirection

/-- Exact model/code commuting square needed to use the row-256 algebra for a
public residual schedule.  Stored q18 selects codeword weights; natural q18
selects `representativeX/Y`. -/
def Row256RawMapCommutes
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  (rawResidualMap inactive schedule).comp
      (row256OrdinaryPadLift inactive) =
    (wireOrderedExtendedRow256FibreEval (L := K) representativeQueries
      (row256ModelWeight storedQueries)).mulVecLin

/-- Fully explicit public raw lift: selected-minor inverse, runtime row
permutation, two width-64 conversions, interleaving, and physical pad embed. -/
noncomputable def canonicalRow256RawPadLift
    (inactive : Message K →ₗ[K] K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    RawView K →ₗ[K] PadSample K :=
  (row256OrdinaryPadLift inactive).comp
    (wireOrderedRow256RawRightInverseLin representativeQueries
      (row256ModelWeight storedQueries))

theorem canonicalRow256RawPadLift_recovers
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective representativeQueries)
    (hcommutes : Row256RawMapCommutes inactive schedule
      storedQueries representativeQueries) :
    (rawResidualMap inactive schedule).comp
      (canonicalRow256RawPadLift inactive
        storedQueries representativeQueries) = LinearMap.id := by
  apply LinearMap.ext
  intro target
  funext raw
  have happ := LinearMap.congr_fun hcommutes
    (wireOrderedRow256RawRightInverseLin representativeQueries
      (row256ModelWeight storedQueries) target)
  have hrecover := wireOrderedRow256RawRightInverseLin_recovers
    (L := K) representativeQueries hqueries
    (row256ModelWeight storedQueries)
    (row256ModelWeight_ne_zero storedQueries) target
  exact (congrFun happ raw).trans (congrFun hrecover raw)

theorem canonicalKernelPadDirection_raw_zero
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (hcommutes : Row256RawMapCommutes inactive schedule
      storedQueries representativeQueries)
    (direction : CanonicalKernelDirection) :
    rawResidualMap inactive schedule
      (canonicalKernelPadDirection inactive representativeQueries direction) = 0 := by
  have happ := LinearMap.congr_fun hcommutes
    (extendedRow256CanonicalKernelOrdinary representativeQueries direction)
  have hzero := wireOrderedExtendedRow256CanonicalKernel_mulVec_zero
    (L := K) representativeQueries (row256ModelWeight storedQueries) direction
  simpa [canonicalKernelPadDirection] using happ.trans hzero

/-- The canonical Schur data use the explicit raw lift and fixed kernel
columns zero through three. -/
noncomputable def canonicalFixedSchurData
    (inactive : Message K →ₗ[K] K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : PublicSchurData K where
  rawLift := canonicalRow256RawPadLift inactive
    storedQueries representativeQueries
  kernelDirection := fun column ↦
    canonicalKernelPadDirection inactive representativeQueries
      (fixedCanonicalKernelDirection column)

theorem canonicalFixedSchurMatrix_eq
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    schurMatrix inactive schedule
        (canonicalFixedSchurData inactive
          storedQueries representativeQueries) =
      canonicalFixedTailMinor inactive schedule representativeQueries := by
  rfl

/-- Exact executable public schedule predicate.  It checks 17-bit
stored-to-natural normalization, distinct stored q18 indices, and the nonzero
determinant of fixed tail columns 0..3.  The global Rust/model commuting square
is deliberately not part of this runtime predicate. -/
def CanonicalFixedMinorGoodB
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  StoredQ18Normalizes storedQueries representativeQueries ∧
    Function.Injective storedQueries ∧
    (canonicalFixedTailMinor inactive schedule representativeQueries).det ≠ 0

/-- Fixed-minor GoodB closes the full 76-coordinate residual map.  Raw rank
72 is supplied by the explicit selected-minor inverse; the four fixed
canonical kernel directions solve inactive plus the three MLE outputs. -/
theorem canonicalFixedMinorGoodB_implies_exactGoodB
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (hgood : CanonicalFixedMinorGoodB inactive schedule
      storedQueries representativeQueries)
    (hcommutes : Row256RawMapCommutes inactive schedule
      storedQueries representativeQueries) :
    ExactGoodB inactive schedule := by
  let data := canonicalFixedSchurData inactive
    storedQueries representativeQueries
  apply schurGoodB_implies_exactGoodB inactive schedule data
  refine ⟨?_, ?_, ?_⟩
  · exact canonicalRow256RawPadLift_recovers inactive schedule
      storedQueries representativeQueries
      (storedQ18Normalizes_injective storedQueries representativeQueries
        hgood.1 hgood.2.1)
      hcommutes
  · intro column
    exact canonicalKernelPadDirection_raw_zero inactive schedule
      storedQueries representativeQueries hcommutes
      (fixedCanonicalKernelDirection column)
  · rw [canonicalFixedSchurMatrix_eq]
    exact hgood.2.2

end CanonicalGood

/-! ## Kernel-checked concrete public determinant witness -/

namespace ConcreteProbeWitness

open AspisV5ComponentATerminalRankPredicate
open AspisV5ComponentCQM31TowerExact

abbrev Tower := QM31Exact

/-- Literal four-limb constructor in Rust `(c0.a,c0.b,c1.a,c1.b)` order. -/
def ofLimbs (c0a c0b c1a c1b : DeployedField) : Tower :=
  ⟨⟨c0a, c0b⟩, ⟨c1a, c1b⟩⟩

/-- Total constructor used for public constants because `fibreCount` is an
opaque public definition.  Every constant below is independently below
`fibreCount`; the modulo is therefore extensionally inert and remains
computable by the kernel. -/
def fibreLiteral (value : ℕ) : Fin fibreCount :=
  ⟨value % fibreCount, Nat.mod_lt value (by norm_num [fibreCount])⟩

/-- Stored Merkle-fibre q18 printed by the one-sample public probe. -/
def storedQ18 : Fin queryCount → Fin fibreCount :=
  ![fibreLiteral 43207, fibreLiteral 120206, fibreLiteral 17043,
    fibreLiteral 67247, fibreLiteral 16605, fibreLiteral 67412,
    fibreLiteral 38305, fibreLiteral 76973, fibreLiteral 90471,
    fibreLiteral 31210, fibreLiteral 56578, fibreLiteral 46239,
    fibreLiteral 30047, fibreLiteral 20052, fibreLiteral 52222,
    fibreLiteral 18382, fibreLiteral 78787, fibreLiteral 55365]

/-- Natural representative q18 from the same printout. -/
def representativeQ18 : Fin queryCount → Fin fibreCount :=
  ![fibreLiteral 116266, fibreLiteral 58199, fibreLiteral 103044,
    fibreLiteral 125633, fibreLiteral 95748, fibreLiteral 21953,
    fibreLiteral 68434, fibreLiteral 92777, fibreLiteral 118029,
    fibreLiteral 44860, fibreLiteral 33142, fibreLiteral 127578,
    fibreLiteral 128348, fibreLiteral 21732, fibreLiteral 65446,
    fibreLiteral 59332, fibreLiteral 100249, fibreLiteral 82998]

theorem q18_normalizes : StoredQ18Normalizes storedQ18 representativeQ18 := by
  unfold StoredQ18Normalizes
  funext query
  fin_cases query <;> decide

theorem storedQ18_injective : Function.Injective storedQ18 := by
  decide

/-- Ten exact public QM31 challenges printed by the same probe, in deployed
limb order. -/
def probePoint : TranscriptPoint Tower :=
  ![ofLimbs 1172386436 1161809346 231311125 1657641968,
    ofLimbs 1828458268 1578712149 1608902830 1579510721,
    ofLimbs 1721750008 1239567766 1983367437 433579121,
    ofLimbs 1859334625 1600271129 393240979 2047715878,
    ofLimbs 1186730067 841460075 889431940 1172222237,
    ofLimbs 1279578245 1795858616 895492659 1258840036,
    ofLimbs 316244094 522365714 1407831697 1254039847,
    ofLimbs 49763791 1922224494 1451015114 308541941,
    ofLimbs 521754014 1074986457 1597297686 1674524242,
    ofLimbs 1580574897 638595193 1370469754 1299880623]

/-- Big-endian row bit used by the runtime MLE fold. -/
def probeBigEndianBit (row : Fin traceRows) (coordinate : Fin 10) : Bool :=
  Nat.testBit (row : ℕ) (9 - (coordinate : ℕ))

/-- Equality-polynomial weight of one physical row. -/
def probeMLERowWeight (point : TranscriptPoint Tower)
    (row : Fin traceRows) : Tower :=
  ∏ coordinate, if probeBigEndianBit row coordinate then point coordinate
    else 1 - point coordinate

/-- Literal big-endian multilinear evaluation used for the public probe. -/
noncomputable def probeMultilinearEvalAt (point : TranscriptPoint Tower) :
    Message Tower →ₗ[Tower] Tower where
  toFun message := ∑ row, message row * probeMLERowWeight point row
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar message := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      Finset.mul_sum]

/-- Carry entering one public challenge coordinate. -/
def probeSuccessorCarry (point : TranscriptPoint Tower)
    (coordinate : Fin 10) : Tower :=
  ∏ later ∈ Finset.univ.filter (fun later : Fin 10 ↦ coordinate < later),
    point later

/-- Exact polynomial binary increment used by the host and verifier. -/
def probeSuccessorPoint (point : TranscriptPoint Tower) : TranscriptPoint Tower :=
  fun coordinate ↦
    let carry := probeSuccessorCarry point coordinate
    let product := point coordinate * carry
    point coordinate + carry - (product + product)

/-- Exact toggle of row-index bits two and three. -/
def probeXor12Point (point : TranscriptPoint Tower) : TranscriptPoint Tower :=
  fun coordinate ↦ if coordinate = 6 ∨ coordinate = 7 then
    1 - point coordinate else point coordinate

def probeRelationPoint (point : TranscriptPoint Tower) (which : Fin 3) :
    TranscriptPoint Tower :=
  ![point, probeSuccessorPoint point, probeXor12Point point] which

/-- Three point-major MLE values on one physical message. -/
noncomputable def probeMessageTerminal (point : TranscriptPoint Tower) :
    Message Tower →ₗ[Tower] (Fin 3 → Tower) :=
  LinearMap.pi fun which ↦
    probeMultilinearEvalAt (probeRelationPoint point which)

/-- Offsets in physical rows 256..383 that the generated copy registry marks
active.  The deployed inactive covector has coefficient zero exactly here and
one on every other offset in this block. -/
def activeRow256Offsets : List ℕ :=
  [0, 11, 12, 16, 27, 28, 32, 43, 44, 48, 59, 60, 64, 75, 76, 80,
    91, 92, 96, 107, 108, 112, 124]

def row256OffsetIsActive (offset : Fin 128) : Bool :=
  activeRow256Offsets.contains (offset : ℕ)

/-- Exact restriction of the binary copy-inactive covector to the aligned
block, plus its deployed unit pivot coefficient.  Other rows are irrelevant
to all canonical directions and are set to zero here. -/
noncomputable def inactiveRestriction : Message Tower →ₗ[Tower] Tower :=
  LinearMap.proj AspisV5InactiveClaimJointHiding.pivotRow +
    ∑ offset, if row256OffsetIsActive offset then 0
      else LinearMap.proj (row256MessageRow offset)

/-- Public schedule used only for the tail determinant.  Its raw field is
zero because public GoodB does not inspect the Rust/model commuting square;
that square is a separate deployment premise. -/
noncomputable def residualSchedule : PublicResidualSchedule Tower where
  raw := 0
  mle := probeMessageTerminal probePoint

/-- The fixed first-four B tail matrix printed by the probe. -/
def printedTailMatrix : Matrix FinalCoordinate FinalCoordinate Tower :=
  ![![ofLimbs 1215679962 0 0 0,
      ofLimbs 1367066067 0 0 0,
      ofLimbs 455586062 0 0 0,
      ofLimbs 1367066067 0 0 0],
    ![ofLimbs 715562970 446616633 1306624865 2072429146,
      ofLimbs 984666751 2135235014 1859225722 816872679,
      ofLimbs 1191631822 702646951 322421219 473911766,
      ofLimbs 976270115 1312115273 380313394 308769311],
    ![ofLimbs 1080607331 1162139045 1414381201 873184652,
      ofLimbs 170285435 1536138300 964973478 175149571,
      ofLimbs 394423277 712390563 583913832 1685919859,
      ofLimbs 967659928 11429260 809513558 35769401],
    ![ofLimbs 264933096 1317941924 1742420533 342472955,
      ofLimbs 391195103 2074949225 455255892 1271485767,
      ofLimbs 1962642976 456546086 839869917 1748299793,
      ofLimbs 1339065538 1849720420 2054327149 139287558]]

/-- The corresponding printed inverse. -/
def printedTailInverse : Matrix FinalCoordinate FinalCoordinate Tower :=
  ![![ofLimbs 689857327 280928523 492035589 219746675,
      ofLimbs 2018559895 83181110 2016136199 144765888,
      ofLimbs 1871005807 1296599873 1064481803 1323939585,
      ofLimbs 1890446344 1031599869 567111844 1153747741],
    ![ofLimbs 996041580 835275630 1513636094 68818553,
      ofLimbs 281338620 1130376085 570197621 576760956,
      ofLimbs 35084472 1648288070 1648741507 1119348157,
      ofLimbs 272093966 853688899 344265040 1683092629],
    ![ofLimbs 1663243723 132476480 813250525 1138440,
      ofLimbs 2136602981 690559158 764473328 932665775,
      ofLimbs 2145853378 117609484 1594130097 1173774633,
      ofLimbs 1047331724 1809721709 99136970 1993620859],
    ![ofLimbs 912813468 226666682 1693686678 1175173760,
      ofLimbs 464811331 342995330 83804966 413167077,
      ofLimbs 70466498 2099986886 962285205 454926541,
      ofLimbs 67139602 1193343356 1966994168 1143460231]]

/-- Exact finite equality still required to turn the printed regression
matrix into a concrete mathematical acceptance certificate.  It is a named
premise, not an axiom and not inferred from the Rust probe. -/
def ConcreteProbeTailMatrixEquality : Prop :=
    canonicalFixedTailMinor inactiveRestriction residualSchedule
      representativeQ18 = printedTailMatrix

/-- Independent kernel check of the printed inverse. -/
theorem printedTailMatrix_mul_inverse :
    printedTailMatrix * printedTailInverse = 1 := by
  decide

theorem printedTailMatrix_det_ne_zero : printedTailMatrix.det ≠ 0 := by
  have hunit : IsUnit printedTailMatrix :=
    IsUnit.of_mul_eq_one printedTailInverse printedTailMatrix_mul_inverse
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det printedTailMatrix).mp hunit)

/-- The exact finite matrix equality would prove concrete nonvacuity of the
public determinant predicate.  The theorem does not assert the separate raw
commuting square. -/
theorem concreteProbe_goodB_of_tail_matrix_equality
    (hequality : ConcreteProbeTailMatrixEquality) :
    CanonicalFixedMinorGoodB inactiveRestriction residualSchedule
      storedQ18 representativeQ18 := by
  refine ⟨q18_normalizes, storedQ18_injective, ?_⟩
  rw [hequality]
  exact printedTailMatrix_det_ne_zero

end ConcreteProbeWitness

theorem exactGoodB_iff_range_eq_top
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K) :
    ExactGoodB inactive schedule ↔
      LinearMap.range
        (completeResidualMap inactive schedule.raw schedule.mle) = ⊤ := by
  exact LinearMap.range_eq_top.symm

/-! ## Permanent bad-schedule teeth -/

def row976ResidualSchedule {K : Type*} [Field K]
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    PublicResidualSchedule K where
  raw := raw
  mle := row976MLE K

def allZeroResidualSchedule {K : Type*} [Field K]
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    PublicResidualSchedule K where
  raw := raw
  mle := degenerateMLE K

theorem row976_exactGoodB_rejected
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ ExactGoodB inactive (row976ResidualSchedule raw) :=
  row976_completeResidualMap_not_surjective inactive raw

theorem row976_schurGoodB_rejected
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (data : PublicSchurData K) :
    ¬ SchurGoodB inactive (row976ResidualSchedule raw) data := by
  intro hgood
  exact row976_exactGoodB_rejected inactive raw
    (schurGoodB_implies_exactGoodB inactive _ data hgood)

theorem row976_canonicalFixedTailMinor_det_eq_zero
    {K : Type*} [Field K] [Algebra DeployedField K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (representativeQueries : Fin queryCount → Fin fibreCount) :
    (canonicalFixedTailMinor inactive (row976ResidualSchedule raw)
      representativeQueries).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero 1
  intro column
  change row976MLE K
    (padPlusPivotEncoder inactive
      (canonicalKernelPadDirection inactive representativeQueries
        (fixedCanonicalKernelDirection column))) 0 = 0
  rw [row976MLE_padPlusPivot_zero]
  rfl

theorem row976_canonicalFixedMinorGoodB_rejected
    {K : Type*} [Field K] [Algebra DeployedField K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    ¬ CanonicalFixedMinorGoodB inactive (row976ResidualSchedule raw)
      storedQueries representativeQueries := by
  intro hgood
  exact hgood.2.2
    (row976_canonicalFixedTailMinor_det_eq_zero inactive raw
      representativeQueries)

theorem allZero_exactGoodB_rejected
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K)) :
    ¬ ExactGoodB inactive (allZeroResidualSchedule raw) :=
  degenerate_completeResidualMap_not_surjective inactive raw

theorem allZero_schurGoodB_rejected
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (data : PublicSchurData K) :
    ¬ SchurGoodB inactive (allZeroResidualSchedule raw) data := by
  intro hgood
  exact allZero_exactGoodB_rejected inactive raw
    (schurGoodB_implies_exactGoodB inactive _ data hgood)

theorem allZero_canonicalFixedTailMinor_det_eq_zero
    {K : Type*} [Field K] [Algebra DeployedField K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (representativeQueries : Fin queryCount → Fin fibreCount) :
    (canonicalFixedTailMinor inactive (allZeroResidualSchedule raw)
      representativeQueries).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero 1
  intro column
  change degenerateMLE K
    (padPlusPivotEncoder inactive
      (canonicalKernelPadDirection inactive representativeQueries
        (fixedCanonicalKernelDirection column))) 0 = 0
  rw [degenerateMLE_padPlusPivot_zero]
  rfl

theorem allZero_canonicalFixedMinorGoodB_rejected
    {K : Type*} [Field K] [Algebra DeployedField K]
    (inactive : Message K →ₗ[K] K)
    (raw : Message K →ₗ[K] (RawCoordinate → K))
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    ¬ CanonicalFixedMinorGoodB inactive (allZeroResidualSchedule raw)
      storedQueries representativeQueries := by
  intro hgood
  exact hgood.2.2
    (allZero_canonicalFixedTailMinor_det_eq_zero inactive raw
      representativeQueries)

/-! ## The strongest exact legal-image statement currently available -/

/-- A schedule-indexed semantic source.  This is the precise data missing
from the Rust-to-Lean surface: which Spend pairs are legal and which 271 real
sumcheck-state coordinates the prover assigns to each witness. -/
structure SpendStateSource
    (Schedule Witness K : Type*) [Field K] where
  legalPairs : Schedule → Set (Witness × Witness)
  realState : Schedule → Witness → StateSample K

/-- Exact, non-linear legal state-difference image.  It is a set, not a
submodule and not an encoder range. -/
def legalStateDifferenceImage
    {Schedule Witness K : Type*} [Field K]
    (source : SpendStateSource Schedule Witness K) (schedule : Schedule) :
    Set (StateSample K) :=
  {difference | ∃ pair ∈ source.legalPairs schedule,
    difference = source.realState schedule pair.2 -
      source.realState schedule pair.1}

/-- The exact residual contribution, in order
`inactive || 72 raw || 3 MLE`, of one 271-state direction. -/
def stateResidualContribution
    {K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K) (schedule : PublicResidualSchedule K)
    (state : StateSample K) : ResidualView K :=
  let message := rowMessage state.1 state.2
  (inactive message, schedule.raw message, schedule.mle message)

/-- Exact correction targets after multiplying a legal real-state difference
by the public nonzero mixing challenge.  The minus sign is the pad translation
needed to cancel that contribution. -/
def legalSpendResidualTargets
    {Schedule Witness K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (publicSchedule : PublicResidualSchedule K)
    (source : SpendStateSource Schedule Witness K) (schedule : Schedule)
    (eta : K) : Set (ResidualView K) :=
  {target | ∃ difference ∈ legalStateDifferenceImage source schedule,
    target =
      -(eta • stateResidualContribution inactive publicSchedule difference)}

/-- Exact ambient GoodB covers the complete actual legal target set supplied
by any semantic source.  The proof intentionally needs no enlargement of that
set: ambient surjectivity is stronger than every possible legal image. -/
theorem exactGoodB_covers_legalSpendResidualTargets
    {Schedule Witness K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (publicSchedule : PublicResidualSchedule K)
    (source : SpendStateSource Schedule Witness K) (schedule : Schedule)
    (eta : K) (hgood : ExactGoodB inactive publicSchedule) :
    legalSpendResidualTargets inactive publicSchedule source schedule eta ⊆
      LinearMap.range
        (completeResidualMap inactive publicSchedule.raw publicSchedule.mle) := by
  intro target _
  exact hgood target

theorem schurGoodB_covers_legalSpendResidualTargets
    {Schedule Witness K : Type*} [Field K]
    (inactive : Message K →ₗ[K] K)
    (publicSchedule : PublicResidualSchedule K)
    (data : PublicSchurData K)
    (source : SpendStateSource Schedule Witness K) (schedule : Schedule)
    (eta : K) (hgood : SchurGoodB inactive publicSchedule data) :
    legalSpendResidualTargets inactive publicSchedule source schedule eta ⊆
      LinearMap.range
        (completeResidualMap inactive publicSchedule.raw publicSchedule.mle) :=
  exactGoodB_covers_legalSpendResidualTargets inactive publicSchedule source
    schedule eta
      (schurGoodB_implies_exactGoodB inactive publicSchedule data hgood)

/-! ## Explicit executable interfaces -/

namespace UnmetDeployment

/-- Missing source theorem: the Rust legal-pair predicate and the real
sumcheck interpolation produce exactly the supplied schedule-indexed
271-coordinate semantic source. -/
def ExactRustSpendStateSourceCorrespondence
    {Schedule Witness K : Type*} [Field K]
    (rustLegalPairs : Schedule → Set (Witness × Witness))
    (rustInitial : Schedule → Witness → K)
    (rustTails : Schedule → Witness → Round → TailDegree → K)
    (source : SpendStateSource Schedule Witness K) : Prop :=
  source.legalPairs = rustLegalPairs ∧
    ∀ schedule witness,
      source.realState schedule witness =
        (rustInitial schedule witness, rustTails schedule witness)

/-- Missing schedule-map theorem: Rust q18, circle encoding, relation points,
and field decoding equal the public linear maps used by `ExactGoodB`. -/
def ExactRustPublicResidualScheduleCorrespondence
    {K : Type*} [Field K]
    (rustRaw : Message K → RawCoordinate → K)
    (rustMLE : Message K → MLECoordinate → K)
    (publicSchedule : PublicResidualSchedule K) : Prop :=
  rustRaw = publicSchedule.raw ∧ rustMLE = publicSchedule.mle

/-- Missing stored-index bridge.  Runtime q18 contains bit-reversed Merkle
fibre indices, whereas `representativeX/Y` are indexed in natural exponent
order.  This interface prevents silently feeding stored q18 directly to the
algebraic evaluation matrix.  Equality of `rustBitReverse17` with the core
17-bit executable is itself part of the Rust-semantics side of the premise. -/
def ExactRustStoredQ18RepresentativeCorrespondence
    (rustBitReverse17 : Fin fibreCount → Fin fibreCount)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  rustBitReverse17 = normalizeStoredFibreIndex ∧
    StoredQ18Normalizes storedQueries representativeQueries

/-- Missing source theorem that the accepted fixed-circle codeword slots have
the order modelled by `runtimeFibreNegations`. -/
def ExactRustFibreSlotOrder
    (rustSlotNegations : Fin 4 → Bool × Bool) : Prop :=
  rustSlotNegations = runtimeFibreNegations

/-- Missing source equality for the public inactive/MLE tail computation used
by the determinant gate. -/
def ExactRustCanonicalTailMatrixCorrespondence
    {K : Type*} [Field K] [Algebra DeployedField K]
    (rustTailMatrix : Matrix FinalCoordinate FinalCoordinate K)
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K)
    (representativeQueries : Fin queryCount → Fin fibreCount) : Prop :=
  rustTailMatrix =
    canonicalFixedTailMinor inactive schedule representativeQueries

/-- Missing aligned-block theorem.  It separately requires Rust's two
width-64 conversions plus interleaving to equal the canonical conversion in
this file, then requires C1 evaluation of that physical block to equal the
ordinary 72-by-128 model with its aligned `B256` row weights.  The caller-owned
inactive scalar is the inactive value of the block, so the dependent row-993
coefficient is zero.  Stored q18 selects weights/codeword positions while the
separately supplied natural representative q18 selects `representativeX/Y`;
slot order is the separate `ExactRustFibreSlotOrder` interface above. -/
def ExactRustRow256RawMatrixCorrespondence
    {K : Type*} [Field K] [Algebra DeployedField K]
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (inactive : Message K →ₗ[K] K)
    (rustOrdinaryToNatural : (Fin 128 → K) →ₗ[K] (Fin 128 → K))
    (rustRaw : Message K → RawCoordinate → K) : Prop :=
  rustOrdinaryToNatural = row256OrdinaryToInterleavedNatural K
    ∧ (∀ ordinary : Fin 128 → K,
      let physical := rustOrdinaryToNatural ordinary
      rustRaw
          (padPlusPivotEncoder inactive
            (row256PadVector physical,
              inactive (structuredPadMessage K (row256PadVector physical)))) =
        fun raw ↦
          (extendedRow256FibreEval (L := K) representativeQueries
            (row256ModelWeight storedQueries)).mulVec ordinary
            (rawToFibreIndex raw))

/-- The two exact pointwise Rust correspondences imply the global linear-map
commuting square used by the mathematical coverage theorem. -/
theorem row256RawMapCommutes_of_correspondence
    {K : Type*} [Field K] [Algebra DeployedField K]
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (inactive : Message K →ₗ[K] K)
    (rustOrdinaryToNatural : (Fin 128 → K) →ₗ[K] (Fin 128 → K))
    (rustRaw : Message K → RawCoordinate → K)
    (rustMLE : Message K → MLECoordinate → K)
    (schedule : PublicResidualSchedule K)
    (hschedule : ExactRustPublicResidualScheduleCorrespondence
      rustRaw rustMLE schedule)
    (hrow : ExactRustRow256RawMatrixCorrespondence
      storedQueries representativeQueries inactive
      rustOrdinaryToNatural rustRaw) :
    Row256RawMapCommutes inactive schedule
      storedQueries representativeQueries := by
  apply LinearMap.ext
  intro ordinary
  funext raw
  have hpointwise := congrFun (hrow.2 ordinary) raw
  rw [hrow.1, padPlusPivotEncoder_row256Block] at hpointwise
  change schedule.raw
    (padPlusPivotEncoder inactive
      (row256OrdinaryPadLift inactive ordinary)) raw = _
  rw [← hschedule.1, padPlusPivotEncoder_row256OrdinaryPadLift]
  exact hpointwise

/-- Missing implementation theorem: the verifier recomputes normalization,
stored-q18 distinctness, and the exact fixed 4-by-4 determinant, accepting
exactly the public GoodB branch. -/
def VerifierEnforcesCanonicalFixedMinorGoodB
    {Run K : Type*} [Field K] [Algebra DeployedField K]
    (inactive : Message K →ₗ[K] K)
    (publicSchedule : Run → PublicResidualSchedule K)
    (storedQueries representativeQueries :
      Run → Fin queryCount → Fin fibreCount)
    (verifierAccepts : Run → Prop) : Prop :=
  ∀ run, verifierAccepts run ↔
    CanonicalFixedMinorGoodB inactive (publicSchedule run)
      (storedQueries run) (representativeQueries run)

end UnmetDeployment

end AspisV5ComponentBSpendDifferenceCoverage

#print axioms AspisV5ComponentBSpendDifferenceCoverage.residualWireOrdinal_inactive
#print axioms AspisV5ComponentBSpendDifferenceCoverage.runtimeFibreNegations_values
#print axioms AspisV5ComponentBSpendDifferenceCoverage.runtimeSlot_sign_roundtrip
#print axioms AspisV5ComponentBSpendDifferenceCoverage.runtimeSign_slot_roundtrip
#print axioms AspisV5ComponentBSpendDifferenceCoverage.rawToFibreIndex_bijective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalInjectiveQ18_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256CodewordPosition_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.residualWireOrdinal_raw_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.residualWireOrdinal_mle_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.rawWireOrdinal_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.residualWireOrdinal_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256PadCoordinate_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256MessageRow_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256MessageRow_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.padPlusPivotEncoder_at_structuredPad
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256PadVector_at
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256PhysicalP_val
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256PhysicalQ_val
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.row256_q0_is_physical_one_and_p1_is_physical_two
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256OrdinaryToInterleavedNatural_at_p
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256OrdinaryToInterleavedNatural_at_q
#print axioms AspisV5ComponentBSpendDifferenceCoverage.padPlusPivotEncoder_row256Block
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256Factor_ne_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_stored128_requires_layer_bit_reversal
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256ModelWeight_ne_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256PRowEval
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256QRowEval
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_mulVec_pPolynomial
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_mulVec_qPolynomial
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_selected_minor_eq
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_selected_minor_det_ne_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256_mul_selectedEmbedding
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256RawRightInverse_is_right_inverse
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256RawRightInverseLin_recovers
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256FibreEval_rank_eq_72
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256FibreEval_mulVec_surjective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256FibreEval_kernel_finrank_eq_56
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256ModelFibreEval_rank_eq_72
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256ModelFibreEval_kernel_finrank_eq_56
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256ModelRawRightInverse_is_right_inverse
#print axioms AspisV5ComponentBSpendDifferenceCoverage.extendedRow256FibreEval_mulVec_surjective
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.wireOrderedExtendedRow256FibreEval_mulVec_surjective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.schurGoodB_implies_exactGoodB
#print axioms AspisV5ComponentBSpendDifferenceCoverage.exactGoodB_iff_range_eq_top
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row976_exactGoodB_rejected
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row976_schurGoodB_rejected
#print axioms AspisV5ComponentBSpendDifferenceCoverage.allZero_exactGoodB_rejected
#print axioms AspisV5ComponentBSpendDifferenceCoverage.allZero_schurGoodB_rejected
#print axioms AspisV5ComponentBSpendDifferenceCoverage.exactGoodB_covers_legalSpendResidualTargets
#print axioms AspisV5ComponentBSpendDifferenceCoverage.schurGoodB_covers_legalSpendResidualTargets
#print axioms AspisV5ComponentBSpendDifferenceCoverage.normalizeStoredFibreIndex_involutive
#print axioms AspisV5ComponentBSpendDifferenceCoverage.normalizeStoredFibreIndex_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.storedQ18Normalizes_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.padPlusPivotEncoder_row256OrdinaryPadLift
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalKernelOrdinal_injective
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256KernelPolynomial_natDegree_lt_64
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256KernelPolynomial_eval_node_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row256CanonicalKernelOrdinary_mulVec_zero
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.extendedRow256CanonicalKernelOrdinary_mulVec_zero
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.wireOrderedExtendedRow256CanonicalKernel_mulVec_zero
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.extendedRow256RawRightInverse_is_right_inverse
#print axioms AspisV5ComponentBSpendDifferenceCoverage.wireOrderedRow256RawRightInverseLin_recovers
#print axioms AspisV5ComponentBSpendDifferenceCoverage.fixedCanonicalKernelDirection_ordinal
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalRow256RawPadLift_recovers
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalKernelPadDirection_raw_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalFixedSchurMatrix_eq
#print axioms AspisV5ComponentBSpendDifferenceCoverage.canonicalFixedMinorGoodB_implies_exactGoodB
#print axioms AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness.q18_normalizes
#print axioms AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness.storedQ18_injective
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness.printedTailMatrix_mul_inverse
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness.printedTailMatrix_det_ne_zero
namespace AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness
#print axioms concreteProbe_goodB_of_tail_matrix_equality
end AspisV5ComponentBSpendDifferenceCoverage.ConcreteProbeWitness
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row976_canonicalFixedTailMinor_det_eq_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.row976_canonicalFixedMinorGoodB_rejected
#print axioms AspisV5ComponentBSpendDifferenceCoverage.allZero_canonicalFixedTailMinor_det_eq_zero
#print axioms AspisV5ComponentBSpendDifferenceCoverage.allZero_canonicalFixedMinorGoodB_rejected
#print axioms
  AspisV5ComponentBSpendDifferenceCoverage.UnmetDeployment.row256RawMapCommutes_of_correspondence
