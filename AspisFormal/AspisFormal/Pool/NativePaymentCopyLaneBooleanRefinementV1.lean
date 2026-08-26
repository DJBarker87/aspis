import AspisFormal.Pool.NativePaymentCompiledCopyLogUpV1

/-!
# Native Pool V1 compiled Copy-lane Boolean refinement

This leaf models the source dataflow of `pattern_values`, the two endpoint
accumulation loops, `copy_residual`, and `copy_lane`.  At a Boolean row point,
it proves that the source-shaped evaluator is exactly
`nativeCompiledCopyLane`, provided the authenticated C1 openings are the
selected trace row.  The already-proved executable `Selectors` refinement is
used for both `Selectors::row` and `Selectors::copy_active`.

The final source-equality predicate names, but does not assume inside the
kernel proof, the remaining Charon/Aeneas generated-root correspondence.  No
PCS or hash behavior is modeled by this pure evaluator leaf.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisPool.NativePaymentCopyLaneBooleanRefinementV1

open AspisPool.NativePaymentCompiledActiveExecutableV1
open AspisPool.NativePaymentCompiledActiveMaskV1
open AspisPool.NativePaymentCompiledCopyLogUpV1
open AspisPool.NativePaymentRandomizedExtractionV1
open AspisV5ProductionRowSelector

/-! ## Source-shaped selectors and pattern compression -/

/-- Exact `selectors.high[row >> 4] * selectors.low[row & 15]` read after
the source expansion loops. -/
def rustCopyRowSelectorAtPoint
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (row : Fin 1024) : K :=
  rustExpandedHighWeight point (rowBlock row) *
    rustExpandedLowWeight point (rowLocal row)

theorem rowOfBlockLocal_rowBlock_rowLocal (row : Fin 1024) :
    rowOfBlockLocal (rowBlock row) (rowLocal row) = row := by
  apply Fin.ext
  simp [rowBlock, rowLocal]
  omega

theorem rustCopyRowSelectorAtPoint_eq_factored
    {K : Type*} [CommRing K]
    (point : TerminalPoint K) (row : Fin 1024) :
    rustCopyRowSelectorAtPoint point row =
      factoredSourceRowSelector point row := by
  rw [rustCopyRowSelectorAtPoint, rustExpandedHighWeight_eq_compiled,
    rustExpandedLowWeight_eq_compiled]
  rw [← factoredSourceRowSelector_rowOfBlockLocal]
  rw [rowOfBlockLocal_rowBlock_rowLocal]

theorem rustCopyRowSelectorAtBooleanPoint
    {K : Type*} [CommRing K]
    (selected row : Fin 1024) :
    rustCopyRowSelectorAtPoint (booleanPointOfRow (F := K) selected) row =
      if row = selected then 1 else 0 := by
  rw [rustCopyRowSelectorAtPoint_eq_factored,
    factoredSourceRowSelector_at_booleanPoint]

/-- The source `pattern_values` result for one generated pattern.  The
checked-in `nativePatternLimb` table already pins all thirteen generated
kind/column/scale/offset arrays, including the nonzero pattern-eight offset. -/
noncomputable def rustCompiledPatternValue
    {K : Type*} [Field K]
    (openings : Fin 16 → K) (lambda : K) (pattern : Fin 13) : K :=
  ∑ limb : Fin 16, lambda ^ (limb.val + 1) *
    nativePatternLimb (fun _ => openings) 0 pattern limb

noncomputable def rustCompiledEndpointValue
    {K : Type*} [Field K]
    (openings : Fin 16 → K) (lambda : K) (tag : Nat)
    (endpoint : NativeCompiledCopyEndpoint) : K :=
  (tag : K) + rustCompiledPatternValue openings lambda endpoint.pattern

/-- The external PCS/opening boundary needed to identify the single C1
opening vector consumed by `copy_lane` with a physical trace row. -/
def AuthenticatedC1BooleanOpenings
    {K : Type*}
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K) : Prop :=
  ∀ column, openings column = trace selected column

set_option linter.flexible false in
private theorem nativePatternLimb_openings_eq_selected
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected openings)
    (pattern : Fin 13) (limb : Fin 16) :
    nativePatternLimb (fun _ => openings) 0 pattern limb =
      nativePatternLimb trace selected pattern limb := by
  fin_cases pattern <;> fin_cases limb <;>
    simp [nativePatternLimb] <;>
    change openings _ = trace selected _ <;>
    exact openingsExact _

theorem rustCompiledEndpointValue_eq_native_at_selected
    {K : Type*} [Field K]
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected openings)
    (lambda : K) (tag : Nat) (endpoint : NativeCompiledCopyEndpoint)
    (endpointRow : endpoint.row = selected) :
    rustCompiledEndpointValue openings lambda tag endpoint =
      nativeCompressTuple lambda (nativeEndpointTuple trace tag endpoint) := by
  unfold rustCompiledEndpointValue rustCompiledPatternValue nativeCompressTuple
    nativeEndpointTuple
  simp only
  congr 1
  apply Finset.sum_congr rfl
  intro limb _
  congr 1
  rw [endpointRow]
  exact nativePatternLimb_openings_eq_selected trace selected openings
    openingsExact endpoint.pattern limb

/-! ## The two source endpoint loops -/

noncomputable def rustEndpointSlotValueAtPoint
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (endpoint : NativeCopyIndex variant → NativeCompiledCopyEndpoint)
    (openings : Fin 16 → K) (point : TerminalPoint K) (lambda : K)
    (slot : Fin 2) : K :=
  ∑ index : NativeCopyIndex variant,
    if (endpoint index).slot = slot then
      rustCopyRowSelectorAtPoint point (endpoint index).row *
        rustCompiledEndpointValue openings lambda
          (nativeCopyTag variant index) (endpoint index)
    else 0

noncomputable def rustEndpointSlotWeightAtPoint
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (endpoint : NativeCopyIndex variant → NativeCompiledCopyEndpoint)
    (point : TerminalPoint K) (slot : Fin 2) : K :=
  ∑ index : NativeCopyIndex variant,
    if (endpoint index).slot = slot then
      rustCopyRowSelectorAtPoint point (endpoint index).row
    else 0

theorem rustEndpointSlotValueAtBooleanPoint_eq_native
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (endpoint : NativeCopyIndex variant → NativeCompiledCopyEndpoint)
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected openings)
    (lambda : K) (slot : Fin 2) :
    rustEndpointSlotValueAtPoint endpoint openings
        (booleanPointOfRow (F := K) selected) lambda slot =
      nativeSlotValue (fun index => ((endpoint index).row, (endpoint index).slot))
        (fun index => nativeCompressTuple lambda
          (nativeEndpointTuple trace (nativeCopyTag variant index)
            (endpoint index))) (selected, slot) := by
  classical
  unfold rustEndpointSlotValueAtPoint nativeSlotValue
  apply Finset.sum_congr rfl
  intro index _
  rw [rustCopyRowSelectorAtBooleanPoint]
  by_cases rowExact : (endpoint index).row = selected
  · by_cases slotExact : (endpoint index).slot = slot
    · simp only [rowExact, slotExact, if_pos, one_mul]
      exact rustCompiledEndpointValue_eq_native_at_selected trace selected
        openings openingsExact lambda (nativeCopyTag variant index)
          (endpoint index) rowExact
    · simp [rowExact, slotExact]
  · have placementDifferent :
        ((endpoint index).row, (endpoint index).slot) ≠ (selected, slot) := by
      intro equal
      exact rowExact (congrArg Prod.fst equal)
    simp [rowExact, placementDifferent]

private theorem nativeSlotValue_one_eq_weight
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (placement : NativeCopyIndex variant → NativeCopyRowSlot)
    (injective : Function.Injective placement) (target : NativeCopyRowSlot) :
    nativeSlotValue placement (fun _ => (1 : K)) target =
      nativeSlotWeight (K := K) placement target := by
  classical
  by_cases occupied : ∃ index, placement index = target
  · obtain ⟨index, placed⟩ := occupied
    rw [← placed, nativeSlotValue_eq_of_placed placement injective]
    simp [nativeSlotWeight]
  · have empty : ∀ index, placement index ≠ target := by
      intro index equal
      exact occupied ⟨index, equal⟩
    rw [nativeSlotValue_eq_zero_of_unoccupied placement (fun _ => 1) target empty]
    simp [nativeSlotWeight, occupied]

theorem rustEndpointSlotWeightAtBooleanPoint_eq_native
    {K : Type*} [Field K]
    {variant : NativePaymentVariantV1}
    (endpoint : NativeCopyIndex variant → NativeCompiledCopyEndpoint)
    (placementInjective : Function.Injective
      (fun index => ((endpoint index).row, (endpoint index).slot)))
    (selected : Fin 1024) (slot : Fin 2) :
    rustEndpointSlotWeightAtPoint endpoint
        (booleanPointOfRow (F := K) selected) slot =
      nativeSlotWeight (K := K)
        (fun index => ((endpoint index).row, (endpoint index).slot))
        (selected, slot) := by
  classical
  rw [← nativeSlotValue_one_eq_weight _ placementInjective]
  unfold rustEndpointSlotWeightAtPoint nativeSlotValue
  apply Finset.sum_congr rfl
  intro index _
  rw [rustCopyRowSelectorAtBooleanPoint]
  by_cases rowExact : (endpoint index).row = selected
  · by_cases slotExact : (endpoint index).slot = slot
    · simp [rowExact, slotExact]
    · simp [rowExact, slotExact]
  · have placementDifferent :
        ((endpoint index).row, (endpoint index).slot) ≠ (selected, slot) := by
      intro equal
      exact rowExact (congrArg Prod.fst equal)
    simp [rowExact, placementDifferent]

noncomputable def rustCompiledCopyRowsAtPoint
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (openings : Fin 16 → K)
    (point : TerminalPoint K) (lambda : K) :
    NativeCompiledCopyRow K where
  producerValue := fun slot => rustEndpointSlotValueAtPoint
    (fun index => (nativeCompiledCopyLink variant index).producer)
    openings point lambda slot
  producerWeight := fun slot => rustEndpointSlotWeightAtPoint
    (fun index => (nativeCompiledCopyLink variant index).producer)
    point slot
  consumerValue := fun slot => rustEndpointSlotValueAtPoint
    (fun index => (nativeCompiledCopyLink variant index).consumer)
    openings point lambda slot
  consumerWeight := fun slot => rustEndpointSlotWeightAtPoint
    (fun index => (nativeCompiledCopyLink variant index).consumer)
    point slot

private theorem nativeCompiledCopyRow_ext
    {K : Type*} [Field K] {left right : NativeCompiledCopyRow K}
    (producerValue : left.producerValue = right.producerValue)
    (producerWeight : left.producerWeight = right.producerWeight)
    (consumerValue : left.consumerValue = right.consumerValue)
    (consumerWeight : left.consumerWeight = right.consumerWeight) :
    left = right := by
  cases left
  cases right
  simp_all

theorem rustCompiledCopyRowsAtBooleanPoint_eq_native
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected openings)
    (lambda : K) :
    rustCompiledCopyRowsAtPoint variant openings
        (booleanPointOfRow (F := K) selected) lambda =
      nativeCompiledCopyRows variant trace lambda selected := by
  apply nativeCompiledCopyRow_ext
  · funext slot
    exact rustEndpointSlotValueAtBooleanPoint_eq_native
      (fun index => (nativeCompiledCopyLink variant index).producer)
      trace selected openings openingsExact lambda slot
  · funext slot
    exact rustEndpointSlotWeightAtBooleanPoint_eq_native
      (fun index => (nativeCompiledCopyLink variant index).producer)
      (nativeProducerRowSlot_injective variant) selected slot
  · funext slot
    exact rustEndpointSlotValueAtBooleanPoint_eq_native
      (fun index => (nativeCompiledCopyLink variant index).consumer)
      trace selected openings openingsExact lambda slot
  · funext slot
    exact rustEndpointSlotWeightAtBooleanPoint_eq_native
      (fun index => (nativeCompiledCopyLink variant index).consumer)
      (nativeConsumerRowSlot_injective variant) selected slot

/-! ## Source `copy_residual` and `copy_lane` -/

/-- Operation order of Rust `copy_residual`, before field-ring normalization. -/
def rustCopyResidual
    {K : Type*} [Field K]
    (row : NativeCompiledCopyRow K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  let producerDenominator := p0 * p1
  let consumerDenominator := c0 * c1
  let producerNumerator := row.producerWeight 0 * p1 +
    row.producerWeight 1 * p0
  let consumerNumerator := row.consumerWeight 0 * c1 +
    row.consumerWeight 1 * c0
  producerDenominator * (helper * consumerDenominator + consumerNumerator) -
    consumerDenominator * producerNumerator

theorem rustCopyResidual_eq_native
    {K : Type*} [Field K]
    (row : NativeCompiledCopyRow K) (helper chi : K) :
    rustCopyResidual row helper chi = nativeCopyLocalResidual row helper chi := by
  unfold rustCopyResidual nativeCopyLocalResidual
  dsimp only
  ring

/-- Source-shaped output pair of `copy_lane`.  Its inputs match the private
Rust root after selecting one of the two generated registries. -/
noncomputable def rustCompiledCopyLaneAtPoint
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1) (openings : Fin 16 → K)
    (point : TerminalPoint K) (h1 lambda chi : K) : K × K :=
  let compiledRow := rustCompiledCopyRowsAtPoint variant openings point lambda
  let active := rustCopyActiveAtPoint variant point
  (active * rustCopyResidual compiledRow h1 chi, active)

/-- The production Boolean `copy_lane` evaluator is the exact lane consumed
by `native_copy_rational_balance_zero_of_accepted_terminal`. -/
theorem rustCompiledCopyLaneAtBooleanPoint_eq_native
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → K)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected openings)
    (helper : Fin 1024 → K) (lambda chi : K) :
    rustCompiledCopyLaneAtPoint variant openings
        (booleanPointOfRow (F := K) selected) (helper selected) lambda chi =
      (nativeCompiledCopyLane variant trace lambda chi helper selected,
        compiledCopyActiveField variant selected) := by
  unfold rustCompiledCopyLaneAtPoint
  rw [rustCompiledCopyRowsAtBooleanPoint_eq_native variant trace selected
      openings openingsExact lambda,
    rustCopyActiveAtBooleanPoint_eq_compiled_bit]
  dsimp only
  rw [rustCopyResidual_eq_native]
  by_cases active : compiledCopyRowActive variant selected <;>
    simp [nativeCompiledCopyLane, compiledCopyActiveField, active]

/-- Directly discharges the prior checkpoint's `copyExact` premise for any
row table populated by successful Boolean evaluations. -/
theorem native_copyExact_of_rust_boolean_copy_lane
    {K : Type*} [Field K]
    (variant : NativePaymentVariantV1)
    (rows : Fin 1024 → NativeConstraintRowResiduals K K)
    (trace : Fin 1024 → Fin 16 → K)
    (openings : Fin 1024 → Fin 16 → K) (helper : Fin 1024 → K)
    (lambda chi : K)
    (openingsExact : ∀ row,
      AuthenticatedC1BooleanOpenings trace row (openings row))
    (sourceExact : ∀ row,
      (rows row).copy =
        (rustCompiledCopyLaneAtPoint variant (openings row)
          (booleanPointOfRow (F := K) row) (helper row) lambda chi).1) :
    ∀ row,
      (rows row).copy = nativeCompiledCopyLane variant trace lambda chi helper row := by
  intro row
  rw [sourceExact row]
  exact congrArg Prod.fst
    (rustCompiledCopyLaneAtBooleanPoint_eq_native variant trace row
      (openings row) (openingsExact row) helper lambda chi)

/-! ## Explicit generated-root/source boundary and identity pins -/

/-- Raw-field interface expected from the Charon/Aeneas extraction wrapper
around the private Rust `copy_lane` root.  The wrapper accepts exactly the
variant and selected Boolean row rather than a second implementation of
`Selectors::expand`. -/
structure ExtractedRustBooleanCopyLane (R : Type*) where
  evaluate : NativePaymentVariantV1 → Fin 1024 → (Fin 16 → R) →
    R → R → R → Option (R × R)

/-- The only generated-root premise: a successful extracted evaluation
returns the pure source-shaped result above.  It neither asserts PCS opening
validity nor any terminal acceptance conclusion. -/
def AeneasBooleanCopyLaneSourceEquality
    {R K : Type*} [Field K] (valid : R → Prop) (view : R → K)
    (rust : ExtractedRustBooleanCopyLane R) : Prop :=
  ∀ variant selected openings h1 lambda chi output,
    (∀ column, valid (openings column)) →
    valid h1 → valid lambda → valid chi →
    rust.evaluate variant selected openings h1 lambda chi = some output →
      (view output.1, view output.2) = rustCompiledCopyLaneAtPoint
        variant (fun column => view (openings column))
          (booleanPointOfRow (F := K) selected)
          (view h1) (view lambda) (view chi)

theorem extractedRustBooleanCopyLane_eq_native
    {R K : Type*} [Field K]
    (valid : R → Prop) (view : R → K)
    (rust : ExtractedRustBooleanCopyLane R)
    (sourceEquality : AeneasBooleanCopyLaneSourceEquality valid view rust)
    (variant : NativePaymentVariantV1)
    (trace : Fin 1024 → Fin 16 → K) (selected : Fin 1024)
    (openings : Fin 16 → R) (h1 lambda chi : R)
    (openingsValid : ∀ column, valid (openings column))
    (h1Valid : valid h1) (lambdaValid : valid lambda) (chiValid : valid chi)
    (openingsExact : AuthenticatedC1BooleanOpenings trace selected
      (fun column => view (openings column)))
    (helper : Fin 1024 → K) (helperExact : view h1 = helper selected)
    (output : R × R)
    (success : rust.evaluate variant selected openings h1 lambda chi =
      some output) :
    (view output.1, view output.2) =
      (nativeCompiledCopyLane variant trace (view lambda) (view chi)
        helper selected,
      compiledCopyActiveField variant selected) := by
  rw [sourceEquality variant selected openings h1 lambda chi output
    openingsValid h1Valid lambdaValid chiValid success, helperExact]
  exact rustCompiledCopyLaneAtBooleanPoint_eq_native variant trace selected
    (fun column => view (openings column)) openingsExact helper
      (view lambda) (view chi)

def auditedRustSourceRevision : String :=
  "65a46367387d3985dd8cf52929df2629c2be15c9"

def auditedRustSourceTree : String :=
  "d8887822d0a0dda089e51ed2dba2c8fbce702b72"

/-- SHA-256 pins of the evaluator, generated tables, and their generator at
the audited committed revision. -/
def auditedRustSourcePins : List (String × String) :=
  [("crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs",
      "77e63ade4699b4805dd061aac6d42517c96f842274c713b98d1e48282baa0594"),
    ("crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs",
      "8e042b07ed259f8b408d097453dff1a9f946b0e21423e0f746f84806bd3898d7"),
    ("crates/aspis-statement/examples/generate_pool_v1_payment_terminal_constants.rs",
      "9f121ae21e9ce7d7db8300b794f12374a182d06a36da9412e0081078cf0240ed")]

def auditedRustSourceRanges : List (String × Nat × Nat) :=
  [("crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs", 197, 247),
    ("crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs", 258, 352),
    ("crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs", 9, 180)]

def auditedRegistryFingerprints : List (String × String) :=
  [("private-transfer-registry", "e3f3ce154db0f662"),
    ("private-transfer-active", "e858c4c0d4e22b94"),
    ("withdrawal-registry", "fb77daf4328c134e"),
    ("withdrawal-active", "e9de6f8fae7f1793")]

theorem auditedRustIdentityPins_nonempty :
    auditedRustSourceRevision.length = 40 ∧
      auditedRustSourceTree.length = 40 ∧
      auditedRustSourcePins.length = 3 ∧
      auditedRustSourceRanges.length = 3 ∧
      auditedRegistryFingerprints.length = 4 := by
  decide

#print axioms rustCopyRowSelectorAtBooleanPoint
#print axioms rustCompiledEndpointValue_eq_native_at_selected
#print axioms rustCompiledCopyRowsAtBooleanPoint_eq_native
#print axioms rustCopyResidual_eq_native
#print axioms rustCompiledCopyLaneAtBooleanPoint_eq_native
#print axioms native_copyExact_of_rust_boolean_copy_lane
#print axioms extractedRustBooleanCopyLane_eq_native
#print axioms auditedRustIdentityPins_nonempty

end AspisPool.NativePaymentCopyLaneBooleanRefinementV1
