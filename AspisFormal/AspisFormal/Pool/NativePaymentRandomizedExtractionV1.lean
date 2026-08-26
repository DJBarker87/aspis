import AspisFormal.Pool.NativePaymentTerminalBridgeV1
import AspisFormal.V5TowerPackedResidualExtraction

/-!
# Native Pool V1 randomized-terminal extraction

This module moves the native payment checkpoint one exact layer upward.  It
models the production 29-lane theta batch (four packed Poseidon lanes,
twenty-four packed semantic lanes and one extension-field Copy LogUp lane),
the ten-coordinate Boolean zerocheck evaluation, and the strengthened
degree-two mu aggregate.

An accepted aggregate yields every raw Boolean-row residual outside three
separate events: mu coefficient cancellation, zerocheck evaluation collision,
and theta lane cancellation.  Exact LogUp endpoint equations are then combined
with the local conservation rows to produce the copy premises consumed by
`NativePaymentTerminalBridgeV1`.

The remaining Rust boundary is explicit in `PrivateTransferResidualRefinement`
and `WithdrawalResidualRefinement`: it must identify the production native
semantic/Poseidon evaluator with the typed decoded row facts.  No theorem here
assumes the final `ValidPrivateTransfer` or `ValidWithdrawal` conclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.NativePaymentRandomizedExtractionV1

open Module Polynomial
open AspisPool.NativePaymentTerminalBridgeV1
open AspisPool.PaymentRelationV1
open AspisV5FriConcreteEncoderApplicability
open AspisV5TowerPackedResidualExtraction

/-! ## Exact 29-lane production layout -/

def nativeThetaWidth : Nat := 29
def nativePoseidonPackedLanes : Nat := 4
def nativeSemanticPackedLanes : Nat := 24
def nativeSourceSemanticResiduals : Nat := 94
def nativeSemanticTailPadding : Nat := 2
def nativeCopyLanes : Nat := 1
def nativeThetaDegree : Nat := 28
def nativeZerocheckCoordinates : Nat := 10
def nativeBooleanRows : Nat := 1024
def nativeMuDegree : Nat := 2

theorem native_randomized_layout_pinned :
    nativeThetaWidth = 29 ∧ nativePoseidonPackedLanes = 4 ∧
    nativeSemanticPackedLanes = 24 ∧ nativeCopyLanes = 1 ∧
    nativeSourceSemanticResiduals = 94 ∧ nativeSemanticTailPadding = 2 ∧
    4 * nativeSemanticPackedLanes =
      nativeSourceSemanticResiduals + nativeSemanticTailPadding ∧
    nativeThetaWidth = nativePoseidonPackedLanes +
      nativeSemanticPackedLanes + nativeCopyLanes ∧
    nativeThetaDegree = 28 ∧ nativeZerocheckCoordinates = 10 ∧
    nativeBooleanRows = 1024 ∧ nativeMuDegree = 2 := by
  decide

/-- Raw Boolean-row residuals before tower packing.  At Boolean rows the four
coordinates of every Poseidon/semantic pack are base-field values.  The copy
lane is already an extension-field LogUp residual. -/
structure NativeConstraintRowResiduals
    (F K : Type*) [Field F] [Field K] [Algebra F K] where
  poseidon : Fin 4 → Fin 4 → F
  semantic : Fin 24 → Fin 4 → F
  copy : K

def poseidonLaneIndex (group : Fin 4) : Fin 29 :=
  ⟨group.val, by omega⟩

def semanticLaneIndex (group : Fin 24) : Fin 29 :=
  ⟨group.val + 4, by omega⟩

def copyLaneIndex : Fin 29 := ⟨28, by omega⟩

/-- Literal final coefficient order of the two reverse Horner loops in the
native payment terminal. -/
noncomputable def NativeConstraintRowResiduals.laneVector
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (row : NativeConstraintRowResiduals F K) : Fin 29 → K := fun lane =>
  if hposeidon : lane.val < 4 then
    towerPack basis (row.poseidon ⟨lane.val, hposeidon⟩)
  else if hsemantic : lane.val < 28 then
    towerPack basis (row.semantic ⟨lane.val - 4, by omega⟩)
  else
    row.copy

@[simp] theorem laneVector_poseidon
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K) (row : NativeConstraintRowResiduals F K)
    (group : Fin 4) :
    row.laneVector basis (poseidonLaneIndex group) =
      towerPack basis (row.poseidon group) := by
  simp [NativeConstraintRowResiduals.laneVector, poseidonLaneIndex,
    group.isLt]

@[simp] theorem laneVector_semantic
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K) (row : NativeConstraintRowResiduals F K)
    (group : Fin 24) :
    row.laneVector basis (semanticLaneIndex group) =
      towerPack basis (row.semantic group) := by
  simp [NativeConstraintRowResiduals.laneVector, semanticLaneIndex]

@[simp] theorem laneVector_copy
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K) (row : NativeConstraintRowResiduals F K) :
    row.laneVector basis copyLaneIndex = row.copy := by
  simp [NativeConstraintRowResiduals.laneVector, copyLaneIndex]

def nativeThetaBatch
    {K : Type*} [Field K] (lanes : Fin 29 → K) (theta : K) : K :=
  ∑ lane, lanes lane * theta ^ lane.val

@[simp] theorem eval_monomialPolynomial_nativeTheta
    {K : Type*} [Field K] (lanes : Fin 29 → K) (theta : K) :
    (monomialPolynomial lanes).eval theta = nativeThetaBatch lanes theta := by
  simp [monomialPolynomial, nativeThetaBatch, Polynomial.eval_finsetSum]

noncomputable def nativeRowConstraintPolynomial
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (row : NativeConstraintRowResiduals F K) : K[X] :=
  monomialPolynomial (row.laneVector basis)

theorem native_row_polynomial_natDegree_le_twenty_eight
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (row : NativeConstraintRowResiduals F K) :
    (nativeRowConstraintPolynomial basis row).natDegree ≤ 28 := by
  simpa [nativeRowConstraintPolynomial] using
    (monomialPolynomial_natDegree_le (K := K) (n := 29) (by decide)
      (row.laneVector basis))

/-- Identity of one native row polynomial exposes all 4*4 Poseidon, 24*4
semantic and one Copy LogUp residuals. -/
theorem all_native_row_residuals_zero_of_polynomial_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (row : NativeConstraintRowResiduals F K)
    (polynomialZero : nativeRowConstraintPolynomial basis row = 0) :
    (∀ group slot, row.poseidon group slot = 0) ∧
      (∀ group slot, row.semantic group slot = 0) ∧ row.copy = 0 := by
  have vectorZero : row.laneVector basis = 0 := by
    apply monomialPolynomial_injective
    simpa [nativeRowConstraintPolynomial, monomialPolynomial] using polynomialZero
  refine ⟨?_, ?_, ?_⟩
  · intro group slot
    have packedZero : towerPack basis (row.poseidon group) = 0 := by
      have atLane := congrFun vectorZero (poseidonLaneIndex group)
      simpa using atLane
    exact (towerPack_eq_zero_iff basis (row.poseidon group)).mp packedZero slot
  · intro group slot
    have packedZero : towerPack basis (row.semantic group) = 0 := by
      have atLane := congrFun vectorZero (semanticLaneIndex group)
      simpa using atLane
    exact (towerPack_eq_zero_iff basis (row.semantic group)).mp packedZero slot
  · have atLane := congrFun vectorZero copyLaneIndex
    simpa using atLane

/-! ## Exact Boolean zerocheck and collision events -/

def bigEndianRowBit (row : Fin 1024) (coordinate : Fin 10) : Bool :=
  row.val.testBit (9 - coordinate.val)

noncomputable def nativeMleRowWeight
    {K : Type*} [Field K] (point : Fin 10 → K) (row : Fin 1024) : K :=
  ∏ coordinate : Fin 10,
    if bigEndianRowBit row coordinate then point coordinate
    else 1 - point coordinate

noncomputable def nativeThetaConstraintTable
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) : Fin 1024 → K := fun row =>
  (nativeRowConstraintPolynomial basis (rows row)).eval theta

noncomputable def nativeConstraintMLE
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K) : K :=
  ∑ row : Fin 1024,
    nativeMleRowWeight point row * nativeThetaConstraintTable basis rows theta row

def NativeZerocheckEvaluationCollision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K) : Prop :=
  nativeThetaConstraintTable basis rows theta ≠ 0 ∧
    nativeConstraintMLE basis rows theta point = 0

noncomputable def selectedNonzeroNativeRow
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K) : Fin 1024 := by
  classical
  exact if existsNonzero : ∃ row,
      nativeRowConstraintPolynomial basis (rows row) ≠ 0 then
    Classical.choose existsNonzero
  else 0

theorem selectedNonzeroNativeRow_spec
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (existsNonzero : ∃ row,
      nativeRowConstraintPolynomial basis (rows row) ≠ 0) :
    nativeRowConstraintPolynomial basis
      (rows (selectedNonzeroNativeRow basis rows)) ≠ 0 := by
  rw [selectedNonzeroNativeRow, dif_pos existsNonzero]
  exact Classical.choose_spec existsNonzero

def NativeThetaLaneCollision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) : Prop :=
  nativeRowConstraintPolynomial basis
      (rows (selectedNonzeroNativeRow basis rows)) ≠ 0 ∧
    (nativeRowConstraintPolynomial basis
      (rows (selectedNonzeroNativeRow basis rows))).eval theta = 0

structure NativeConstraintRowsVanish
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rows : Fin 1024 → NativeConstraintRowResiduals F K) : Prop where
  poseidon : ∀ row group slot, (rows row).poseidon group slot = 0
  semantic : ∀ row group slot, (rows row).semantic group slot = 0
  copy : ∀ row, (rows row).copy = 0

theorem native_theta_table_zero_outside_zerocheck_collision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K)
    (mleZero : nativeConstraintMLE basis rows theta point = 0)
    (outside : ¬ NativeZerocheckEvaluationCollision basis rows theta point) :
    nativeThetaConstraintTable basis rows theta = 0 := by
  by_contra tableNonzero
  exact outside ⟨tableNonzero, mleZero⟩

theorem native_row_polynomials_zero_outside_theta_collision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K)
    (tableZero : nativeThetaConstraintTable basis rows theta = 0)
    (outside : ¬ NativeThetaLaneCollision basis rows theta) :
    ∀ row, nativeRowConstraintPolynomial basis (rows row) = 0 := by
  intro row
  by_contra polynomialNonzero
  apply outside
  have existsNonzero : ∃ row,
      nativeRowConstraintPolynomial basis (rows row) ≠ 0 :=
    ⟨row, polynomialNonzero⟩
  refine ⟨selectedNonzeroNativeRow_spec basis rows existsNonzero, ?_⟩
  have selectedZero := congrFun tableZero
    (selectedNonzeroNativeRow basis rows)
  exact selectedZero

theorem native_rows_vanish_of_mle_zero_outside_collisions
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K)
    (mleZero : nativeConstraintMLE basis rows theta point = 0)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta) :
    NativeConstraintRowsVanish rows := by
  have tableZero := native_theta_table_zero_outside_zerocheck_collision
    basis rows theta point mleZero noZerocheck
  have polynomialZero := native_row_polynomials_zero_outside_theta_collision
    basis rows theta tableZero noTheta
  refine ⟨?_, ?_, ?_⟩
  · intro row group slot
    exact (all_native_row_residuals_zero_of_polynomial_zero basis (rows row)
      (polynomialZero row)).1 group slot
  · intro row group slot
    exact (all_native_row_residuals_zero_of_polynomial_zero basis (rows row)
      (polynomialZero row)).2.1 group slot
  · intro row
    exact (all_native_row_residuals_zero_of_polynomial_zero basis (rows row)
      (polynomialZero row)).2.2

/-! ## Exact degree-two mu aggregate -/

def NativeAcceptedRandomizedTerminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K) : Prop :=
  nativeConstraintMLE basis rows theta point + mu * totalHelper +
    mu ^ 2 * inactiveHelper = 0

def NativeMuAggregateCollision
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper mu : K) : Prop :=
  ¬ (constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0) ∧
    constraintValue + mu * totalHelper + mu ^ 2 * inactiveHelper = 0

theorem native_mu_coefficients_zero_outside_collision
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper mu : K)
    (aggregateZero : constraintValue + mu * totalHelper +
      mu ^ 2 * inactiveHelper = 0)
    (outside : ¬ NativeMuAggregateCollision constraintValue totalHelper
      inactiveHelper mu) :
    constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0 := by
  by_contra coefficientsNonzero
  exact outside ⟨coefficientsNonzero, aggregateZero⟩

theorem native_rows_vanish_of_accepted_randomized_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta) :
    NativeConstraintRowsVanish rows ∧ totalHelper = 0 ∧ inactiveHelper = 0 := by
  have coefficients := native_mu_coefficients_zero_outside_collision
    (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu
    accepted noMu
  exact ⟨native_rows_vanish_of_mle_zero_outside_collisions basis rows theta
    point coefficients.1 noZerocheck noTheta, coefficients.2.1,
    coefficients.2.2⟩

/-! ## Fixed-vector bad-event cardinalities -/

section FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable def nativeThetaCollisionSet (lanes : Fin 29 → K) : Finset K :=
  Finset.univ.filter fun theta => nativeThetaBatch lanes theta = 0

theorem native_theta_collision_card_le_twenty_eight
    (lanes : Fin 29 → K) (nonzero : lanes ≠ 0) :
    (nativeThetaCollisionSet lanes).card ≤ 28 := by
  let polynomial := monomialPolynomial lanes
  have polynomialNonzero : polynomial ≠ 0 := by
    intro polynomialZero
    apply nonzero
    apply monomialPolynomial_injective
    simpa [polynomial, monomialPolynomial] using polynomialZero
  have subsetRoots : (nativeThetaCollisionSet lanes).val ⊆ polynomial.roots := by
    intro theta member
    have batchZero := (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots polynomialNonzero]
    simpa [Polynomial.IsRoot, polynomial] using batchZero
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    (by simpa [polynomial] using
      (monomialPolynomial_natDegree_le (K := K) (n := 29) (by decide) lanes))

noncomputable def nativeMuCollisionSet
    (constraintValue totalHelper inactiveHelper : K) : Finset K :=
  Finset.univ.filter fun mu =>
    constraintValue + mu * totalHelper + mu ^ 2 * inactiveHelper = 0

theorem native_mu_collision_card_le_two
    (constraintValue totalHelper inactiveHelper : K)
    (nonzero : ¬ (constraintValue = 0 ∧ totalHelper = 0 ∧
      inactiveHelper = 0)) :
    (nativeMuCollisionSet constraintValue totalHelper inactiveHelper).card ≤ 2 := by
  let coefficients : Fin 3 → K :=
    ![constraintValue, totalHelper, inactiveHelper]
  let polynomial := monomialPolynomial coefficients
  have coefficientsNonzero : coefficients ≠ 0 := by
    intro coefficientsZero
    apply nonzero
    have c0 := congrFun coefficientsZero (0 : Fin 3)
    have c1 := congrFun coefficientsZero (1 : Fin 3)
    have c2 := congrFun coefficientsZero (2 : Fin 3)
    exact ⟨by simpa [coefficients] using c0,
      by simpa [coefficients] using c1,
      by simpa [coefficients] using c2⟩
  have polynomialNonzero : polynomial ≠ 0 := by
    intro polynomialZero
    apply coefficientsNonzero
    apply monomialPolynomial_injective
    simpa [polynomial, monomialPolynomial] using polynomialZero
  have subsetRoots :
      (nativeMuCollisionSet constraintValue totalHelper inactiveHelper).val ⊆
        polynomial.roots := by
    intro mu member
    have aggregateZero := (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots polynomialNonzero]
    simp only [Polynomial.IsRoot]
    rw [show polynomial.eval mu =
        constraintValue + mu * totalHelper + mu ^ 2 * inactiveHelper by
      simp [polynomial, coefficients, monomialPolynomial, Fin.sum_univ_succ]
      ring]
    exact aggregateZero
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    (by simpa [polynomial] using
      (monomialPolynomial_natDegree_le (K := K) (n := 3) (by decide)
        coefficients))

end FiniteField

/-! ## Exact native LogUp endpoint equations -/

structure CommonLogUpEndpointEquations
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  inputSource : sourceValue trace 0 = auxiliaryValue trace 0
  changeSource : sourceValue trace 2 = auxiliaryValue trace 2
  conservationInput : auxiliaryValue trace 0 =
    trace.natCell conservationInputCell
  conservationRecipientOrAmount : auxiliaryValue trace 1 =
    trace.natCell conservationRecipientOrAmountCell
  conservationChange : auxiliaryValue trace 2 =
    trace.natCell conservationChangeCell
  conservationPartial : trace.natCell conservationPartialCell =
    trace.natCell conservationCarriedPartialCell

structure PrivateTransferLogUpEndpointEquations
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  common : CommonLogUpEndpointEquations trace
  recipientSource : sourceValue trace 1 = auxiliaryValue trace 1

structure ConservationSemanticRowEquations
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  first : trace.natCell conservationInputCell =
    trace.natCell conservationRecipientOrAmountCell +
      trace.natCell conservationPartialCell
  second : trace.natCell conservationCarriedPartialCell =
    trace.natCell conservationChangeCell

theorem common_value_copy_and_conservation_of_endpoints
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (endpoints : CommonLogUpEndpointEquations trace)
    (conservation : ConservationSemanticRowEquations trace) :
    CommonValueCopyAndConservation trace := by
  exact ⟨endpoints.inputSource, endpoints.changeSource,
    endpoints.conservationInput, endpoints.conservationRecipientOrAmount,
    endpoints.conservationChange, conservation.first,
    endpoints.conservationPartial, conservation.second⟩

theorem private_transfer_value_copy_of_endpoint
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (endpoints : PrivateTransferLogUpEndpointEquations trace) :
    PrivateTransferValueCopy trace :=
  endpoints.recipientSource

/-! ## Residual-to-decoded-row refinement and capstones -/

structure PrivateTransferDecodedSemanticRows
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  values : ValueRowsAccepted trace
  conservation : ConservationSemanticRowEquations trace
  commonHashes : CommonHashRowsAccepted primitives statement.common trace
  outputHashes : PrivateTransferOutputHashRowsAccepted primitives statement trace

structure WithdrawalDecodedSemanticRows
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  values : ValueRowsAccepted trace
  conservation : ConservationSemanticRowEquations trace
  amount : WithdrawalAmountBinding statement trace
  commonHashes : CommonHashRowsAccepted primitives statement.common trace
  outputHashes : WithdrawalOutputHashRowsAccepted primitives statement trace

/-- Explicit source-refinement boundary: zero native production residuals
decode to the granular transfer row equations. -/
structure PrivateTransferResidualRefinement
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  decode : NativeConstraintRowsVanish rows →
    PrivateTransferDecodedSemanticRows primitives statement trace

/-- Explicit source-refinement boundary for withdrawal. -/
structure WithdrawalResidualRefinement
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  decode : NativeConstraintRowsVanish rows →
    WithdrawalDecodedSemanticRows primitives statement trace

structure PrivateTransferBridgePremises
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  valueRows : ValueRowsAccepted trace
  valueCopies : CommonValueCopyAndConservation trace
  transferCopy : PrivateTransferValueCopy trace
  commonHashes : CommonHashRowsAccepted primitives statement.common trace
  outputHashes : PrivateTransferOutputHashRowsAccepted primitives statement trace

structure WithdrawalBridgePremises
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop where
  valueRows : ValueRowsAccepted trace
  valueCopies : CommonValueCopyAndConservation trace
  amount : WithdrawalAmountBinding statement trace
  commonHashes : CommonHashRowsAccepted primitives statement.common trace
  outputHashes : WithdrawalOutputHashRowsAccepted primitives statement trace

theorem native_private_transfer_premises_of_accepted_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta)
    (refinement : PrivateTransferResidualRefinement rows primitives statement trace)
    (endpoints : PrivateTransferLogUpEndpointEquations trace) :
    PrivateTransferBridgePremises primitives statement trace := by
  have vanished := (native_rows_vanish_of_accepted_randomized_terminal basis
    rows theta point mu totalHelper inactiveHelper accepted noMu noZerocheck
    noTheta).1
  have decoded := refinement.decode vanished
  exact {
    valueRows := decoded.values
    valueCopies := common_value_copy_and_conservation_of_endpoints trace
      endpoints.common decoded.conservation
    transferCopy := private_transfer_value_copy_of_endpoint trace endpoints
    commonHashes := decoded.commonHashes
    outputHashes := decoded.outputHashes
  }

theorem native_withdrawal_premises_of_accepted_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta)
    (refinement : WithdrawalResidualRefinement rows primitives statement trace)
    (endpoints : CommonLogUpEndpointEquations trace) :
    WithdrawalBridgePremises primitives statement trace := by
  have vanished := (native_rows_vanish_of_accepted_randomized_terminal basis
    rows theta point mu totalHelper inactiveHelper accepted noMu noZerocheck
    noTheta).1
  have decoded := refinement.decode vanished
  exact {
    valueRows := decoded.values
    valueCopies := common_value_copy_and_conservation_of_endpoints trace
      endpoints decoded.conservation
    amount := decoded.amount
    commonHashes := decoded.commonHashes
    outputHashes := decoded.outputHashes
  }

theorem native_private_transfer_valid_of_accepted_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta)
    (refinement : PrivateTransferResidualRefinement rows primitives statement trace)
    (endpoints : PrivateTransferLogUpEndpointEquations trace) :
    ValidPrivateTransfer primitives statement (privateTransferWitnessOfTrace trace) := by
  have premises := native_private_transfer_premises_of_accepted_terminal basis
    rows primitives statement trace theta point mu totalHelper inactiveHelper
    accepted noMu noZerocheck noTheta refinement endpoints
  exact native_private_transfer_semantic_rows_imply_valid primitives statement
    trace premises.valueRows premises.valueCopies premises.transferCopy
    premises.commonHashes premises.outputHashes

theorem native_withdrawal_valid_of_accepted_terminal
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (noMu : ¬ NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu)
    (noZerocheck : ¬ NativeZerocheckEvaluationCollision basis rows theta point)
    (noTheta : ¬ NativeThetaLaneCollision basis rows theta)
    (refinement : WithdrawalResidualRefinement rows primitives statement trace)
    (endpoints : CommonLogUpEndpointEquations trace) :
    ValidWithdrawal primitives statement (withdrawalWitnessOfTrace trace) := by
  have premises := native_withdrawal_premises_of_accepted_terminal basis rows
    primitives statement trace theta point mu totalHelper inactiveHelper
    accepted noMu noZerocheck noTheta refinement endpoints
  exact native_withdrawal_semantic_rows_imply_valid primitives statement trace
    premises.valueRows premises.valueCopies premises.amount
    premises.commonHashes premises.outputHashes

/-- Collision-explicit transfer form: the three algebraic events remain
separate disjuncts, rather than being folded into a generic failure premise. -/
theorem native_private_transfer_premises_or_collision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (refinement : PrivateTransferResidualRefinement rows primitives statement trace)
    (endpoints : PrivateTransferLogUpEndpointEquations trace) :
    NativeMuAggregateCollision
        (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu ∨
      NativeZerocheckEvaluationCollision basis rows theta point ∨
      NativeThetaLaneCollision basis rows theta ∨
      PrivateTransferBridgePremises primitives statement trace := by
  by_cases muCollision : NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu
  · exact Or.inl muCollision
  by_cases zerocheckCollision :
      NativeZerocheckEvaluationCollision basis rows theta point
  · exact Or.inr (Or.inl zerocheckCollision)
  by_cases thetaCollision : NativeThetaLaneCollision basis rows theta
  · exact Or.inr (Or.inr (Or.inl thetaCollision))
  exact Or.inr (Or.inr (Or.inr
    (native_private_transfer_premises_of_accepted_terminal basis rows
      primitives statement trace theta point mu totalHelper inactiveHelper
      accepted muCollision zerocheckCollision thetaCollision refinement endpoints)))

theorem native_withdrawal_premises_or_collision
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (theta : K) (point : Fin 10 → K) (mu totalHelper inactiveHelper : K)
    (accepted : NativeAcceptedRandomizedTerminal basis rows theta point mu
      totalHelper inactiveHelper)
    (refinement : WithdrawalResidualRefinement rows primitives statement trace)
    (endpoints : CommonLogUpEndpointEquations trace) :
    NativeMuAggregateCollision
        (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu ∨
      NativeZerocheckEvaluationCollision basis rows theta point ∨
      NativeThetaLaneCollision basis rows theta ∨
      WithdrawalBridgePremises primitives statement trace := by
  by_cases muCollision : NativeMuAggregateCollision
      (nativeConstraintMLE basis rows theta point) totalHelper inactiveHelper mu
  · exact Or.inl muCollision
  by_cases zerocheckCollision :
      NativeZerocheckEvaluationCollision basis rows theta point
  · exact Or.inr (Or.inl zerocheckCollision)
  by_cases thetaCollision : NativeThetaLaneCollision basis rows theta
  · exact Or.inr (Or.inr (Or.inl thetaCollision))
  exact Or.inr (Or.inr (Or.inr
    (native_withdrawal_premises_of_accepted_terminal basis rows primitives
      statement trace theta point mu totalHelper inactiveHelper accepted
      muCollision zerocheckCollision thetaCollision refinement endpoints)))

#print axioms all_native_row_residuals_zero_of_polynomial_zero
#print axioms native_theta_table_zero_outside_zerocheck_collision
#print axioms native_row_polynomials_zero_outside_theta_collision
#print axioms native_rows_vanish_of_accepted_randomized_terminal
#print axioms native_theta_collision_card_le_twenty_eight
#print axioms native_mu_collision_card_le_two
#print axioms common_value_copy_and_conservation_of_endpoints
#print axioms native_private_transfer_premises_of_accepted_terminal
#print axioms native_withdrawal_premises_of_accepted_terminal
#print axioms native_private_transfer_valid_of_accepted_terminal
#print axioms native_withdrawal_valid_of_accepted_terminal
#print axioms native_private_transfer_premises_or_collision
#print axioms native_withdrawal_premises_or_collision

end AspisPool.NativePaymentRandomizedExtractionV1
