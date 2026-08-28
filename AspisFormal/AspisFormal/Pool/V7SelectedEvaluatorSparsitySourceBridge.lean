import AspisFormal.Pool.V7SelectedEvaluatorSparsityEquivalence

/-!
# Source-shaped bridge for the selected V7 evaluator sparsity features

This file is the ordinary-kernel endpoint of the Rust/Charon/Aeneas bridge at
production revision `cee5947cbd5929a2be96d8f7ec29728afec2d3dd`.

The accompanying extraction bundle pins the Rust definitions, Cargo feature
edges, generated tables and loop bodies.  Here those source-shaped schedules
are fed to the generic identities in
`V7SelectedEvaluatorSparsityEquivalence`: the result is equality of every
piece consumed by the unchanged terminal evaluator.  No relation, challenge,
transcript event or field operation is removed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace AspisPool.V7SelectedEvaluatorSparsitySourceBridge

open V7SelectedEvaluatorSparsityEquivalence

/-! ## Pinned selected build and literal source schedules -/

/-- Exact commit archived before Charon extraction. -/
def productionRevision : String :=
  "cee5947cbd5929a2be96d8f7ec29728afec2d3dd"

/-- The exact selected verifier features from the locked build manifest.
Dependencies of the tensor features are recorded by Cargo and checked by the
extraction replay script. -/
def selectedVerifierFeatures : List String :=
  [ "v7-pair-forest-fixed-canonical-exact-once-audit"
  , "v7-pair-forest-lane-invariant-audit"
  , "v7-pair-forest-packed-digest-selector-tensor-audit"
  , "v7-pair-forest-binary-copy-weights-audit"
  , "v7-pair-forest-endpoint-selector-cache-audit"
  , "v7-pair-forest-semantic-factor-audit"
  , "v7-pair-forest-pattern-window-audit"
  , "v7-pair-forest-copy-tag-dot-basis-audit"
  , "v7-pair-forest-copy-finish-dot-basis-audit"
  , "v7-pair-forest-packed-range-audit"
  , "v7-pair-forest-active-mask-basis-audit"
  , "v7-gamma-four-slot-block-audit" ]

theorem selectedVerifierFeatures_count : selectedVerifierFeatures.length = 12 := by
  rfl

/-- `add_preweighted_shared_selector` starts at semantic lane 49, consumes
exactly 33 residuals, and therefore touches the nine base-four groups 12..20. -/
def packedRangeSourceTerm {K : Type*} [Zero K]
    (residual : Fin 33 → K) (group : Fin 9) (slot : Fin 4) : K :=
  let source := 4 * (12 + group.val) + slot.val
  if h : 49 ≤ source ∧ source < 82 then
    residual ⟨source - 49, by omega⟩
  else
    0

theorem packedRange_exact_source_interval :
    49 / 4 = 12 ∧ (49 + 33 - 1) / 4 = 20 := by
  decide

/-- The public-digest grammar binds only a block and one of the sixteen low
selector coordinates. -/
structure DigestBinding where
  block : Fin 64
  localCoordinate : Fin 16
deriving DecidableEq, Fintype

/-- Dynamic control values read by `public_digest_packed_selector_tensor`.
`sourceBit` is `((next_pair_index >> level) & 1) != 0`; `carry` is
`min(next_pair_index.trailing_ones(), 20)`. -/
structure DigestControl where
  hasRecipient : Bool
  sourceBit : Fin 20 → Bool
  carry : Fin 21

/-- Exact row schedule of `public_digest_packed_selector_tensor`: anchor,
nullifier, optional recipient, change, twenty frontier/empty-root bindings,
next root, and optional next-frontier carry. -/
def digestBindingSchedule (control : DigestControl) : List DigestBinding :=
  [{ block := 56, localCoordinate := 11 },
    { block := 26, localCoordinate := 11 }] ++
  (if control.hasRecipient then
    [{ block := 29, localCoordinate := 11 }]
  else []) ++
  [{ block := 32, localCoordinate := 11 }] ++
  List.ofFn (fun level : Fin 20 =>
    if control.sourceBit level then
      { block := ⟨34 + level.val, by omega⟩, localCoordinate := 12 }
    else
      { block := ⟨34 + level.val, by omega⟩, localCoordinate := 0 }) ++
  [{ block := 53, localCoordinate := 11 }] ++
  if h : control.carry.val < 20 then
    [{ block := ⟨33 + control.carry.val, by omega⟩, localCoordinate := 11 }]
  else
    []

/-- A source event is one of the distinct bindings in the exact frozen
production schedule.  The current grammar has no duplicate binding value; a
future grammar with duplicate occurrences would require an occurrence index
instead of silently identifying them here. -/
abbrev ProductionDigestEvent (control : DigestControl) :=
  { binding : DigestBinding // binding ∈ digestBindingSchedule control }

theorem digestBindingSchedule_uses_exact_locals
    (control : DigestControl) (binding : DigestBinding)
    (member : binding ∈ digestBindingSchedule control) :
    binding.localCoordinate = 0 ∨ binding.localCoordinate = 11 ∨
      binding.localCoordinate = 12 := by
  unfold digestBindingSchedule at member
  split at member <;> split at member <;>
    simp_all <;> aesop

/-- Exact seven-way classification of the 64 generated active-row masks. -/
def activeMaskCoordinate : Fin 64 → Fin 7 := ![
  0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 3, 1, 4, 3, 1,
  4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5, 5, 5, 5, 6]

/-- Exact `constants::ACTIVE_ROW_MASKS`. -/
def activeRowMask : Fin 64 → Fin 65536 := ![
  6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
  2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
  6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145,
  4097, 26214, 26214, 26214, 26214, 26214, 26214, 1749]

theorem activeRowMask_eq_basis (block : Fin 64) :
    activeRowMask block = copyActiveMask (activeMaskCoordinate block) := by
  decide +revert

/-- Exact generated nonzero `(group, local)` support used by the Copy tensor. -/
def copyGroupLocalGroup : Fin 30 → Fin 4 := ![
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3]

def copyGroupLocalLocal : Fin 30 → Fin 16 := ![
  0, 1, 2, 4, 6, 10, 11, 12, 14,
  2, 6, 10, 11, 12, 14,
  0, 1, 2, 4, 5, 6, 7, 9, 10, 12, 13,
  6, 7, 9, 12]

/-- Exact generated nonzero `(group, pattern, local)` support.  The last
array is the 26-coordinate output map consumed by `finish_pattern_basis_values`. -/
def copyPatternLocalGroup : Fin 43 → Fin 4 := ![
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3, 3]

def copyPatternLocalPattern : Fin 43 → Fin 14 := ![
  0, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6, 7, 7, 7, 9, 10, 11,
  1, 6, 13, 13, 13, 13,
  0, 1, 3, 6, 7, 7, 7, 8, 10, 11, 11, 12, 12, 12, 12,
  1, 5, 6, 7, 8]

def copyPatternLocalLocal : Fin 43 → Fin 16 := ![
  11, 2, 6, 10, 11, 12, 14, 12, 12, 1, 12, 0, 2, 4, 6, 0, 10,
  11, 12, 2, 6, 10, 14,
  0, 12, 12, 6, 0, 2, 4, 7, 0, 9, 10, 1, 5, 9, 13,
  12, 12, 7, 9, 6]

def copyPatternLocalOutput : Fin 43 → Fin 26 := ![
  0, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5, 5, 5, 6, 7, 8,
  9, 10, 11, 11, 11, 11,
  12, 13, 14, 15, 16, 16, 16, 17, 18, 19, 19, 20, 20, 20, 20,
  21, 22, 23, 24, 25]

/-- Exact source offsets.  Their differences are the selected 9/6/11/4
finish-dot widths. -/
def copyFinishOffset : Fin 5 → Fin 31 := ![0, 9, 15, 26, 30]

theorem copyFinishWidths_exact :
    copyFinishOffset 1 - copyFinishOffset 0 = 9 ∧
    copyFinishOffset 2 - copyFinishOffset 1 = 6 ∧
    copyFinishOffset 3 - copyFinishOffset 2 = 11 ∧
    copyFinishOffset 4 - copyFinishOffset 3 = 4 := by
  decide

/-- Exact C1 schedule: six four-column blocks and the two-column tail. -/
def gammaChunkStart : Fin 7 → Fin 26 := ![0, 4, 8, 12, 16, 20, 24]

def gammaChunkWidth : Fin 7 → Fin 5 := ![4, 4, 4, 4, 4, 4, 2]

theorem gammaSchedule_exact :
    (∀ chunk : Fin 6, (gammaChunkStart chunk.castSucc).val = 4 * chunk.val ∧
      gammaChunkWidth chunk.castSucc = 4) ∧
    gammaChunkStart 6 = 24 ∧ gammaChunkWidth 6 = 2 := by
  decide +revert

/-- The generated table has 136 links and contributes its producer and
consumer endpoint exactly once to the tag/tensor schedule. -/
theorem copyEndpointSchedule_count : 136 * 2 = 272 := by
  decide

/-! ## Source-shaped selected and literal evaluator pieces -/

variable {K : Type*} [CommRing K]

def rangeSelected
    (selector : K) (residual : Fin 33 → K) : Fin 9 → K :=
  fun group => selector * ∑ slot, packedRangeSourceTerm residual group slot

def rangeLiteral
    (selector : K) (residual : Fin 33 → K) : Fin 9 → K :=
  fun group => ∑ slot, selector * packedRangeSourceTerm residual group slot

theorem rangeSelected_eq_literal
    (selector : K) (residual : Fin 33 → K) :
    rangeSelected selector residual = rangeLiteral selector residual := by
  funext group
  simp only [rangeSelected, rangeLiteral, Fin.sum_univ_four]
  exact selector_mul_four_sum (K := K) _ _ _ _ _

def digestSelected
    (control : DigestControl)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (residual : Fin 2 → ProductionDigestEvent control → K) : Fin 2 → K :=
  fun packedGroup => groupedSelectorTensor
    (fun event => event.val.block) (fun event => event.val.localCoordinate)
    high low (residual packedGroup)

def digestLiteral
    (control : DigestControl)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (residual : Fin 2 → ProductionDigestEvent control → K) : Fin 2 → K :=
  fun packedGroup => literalSelectorTensor
    (fun event => event.val.block) (fun event => event.val.localCoordinate)
    high low (residual packedGroup)

theorem digestSelected_eq_literal
    (control : DigestControl)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (residual : Fin 2 → ProductionDigestEvent control → K) :
    digestSelected control high low residual =
      digestLiteral control high low residual := by
  funext packedGroup
  exact packedDigestSelectorTensor_eq_literal (K := K) _ _ _ _ _

def activeSelected (high : Fin 64 → K) (lowMask : Fin 65536 → K) : K :=
  ∑ coordinate : Fin 7, lowMask (copyActiveMask coordinate) *
    ∑ block : Fin 64,
      if activeMaskCoordinate block = coordinate then high block else 0

def activeLiteral (high : Fin 64 → K) (lowMask : Fin 65536 → K) : K :=
  ∑ block : Fin 64, high block * lowMask (activeRowMask block)

theorem activeSelected_eq_literal
    (high : Fin 64 → K) (lowMask : Fin 65536 → K) :
    activeSelected high lowMask = activeLiteral high lowMask := by
  rw [activeSelected, activeLiteral]
  simpa only [activeRowMask_eq_basis] using
    (activeMaskBasis_eq_literal
      (K := K) (Block := Fin 64) (Mask := Fin 7)
      activeMaskCoordinate high (fun coordinate =>
        lowMask (copyActiveMask coordinate)))

/-- The exact selected build has 136 Copy links and therefore 272 endpoint
events.  Charon pins `blockOf`, `localOf`, `groupOf`, tags and patterns to the
generated `COPY_LINKS` traversal; the theorem is universal over their values. -/
def copySelected
    (blockOf : Fin 272 → Fin 64) (localOf : Fin 272 → Fin 16)
    (groupOf : Fin 272 → Fin 4)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (tag pattern : Fin 272 → K) : Fin 4 → K :=
  fun group =>
    groupedSelectorTensor blockOf localOf high low (fun event =>
      if groupOf event = group then tag event else 0) +
    groupedSelectorTensor blockOf localOf high low (fun event =>
      if groupOf event = group then pattern event else 0)

def copyLiteral
    (blockOf : Fin 272 → Fin 64) (localOf : Fin 272 → Fin 16)
    (groupOf : Fin 272 → Fin 4)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (tag pattern : Fin 272 → K) : Fin 4 → K :=
  fun group => ∑ event : Fin 272,
    if groupOf event = group then
      high (blockOf event) * low (localOf event) * (tag event + pattern event)
    else 0

theorem copySelected_eq_literal
    (blockOf : Fin 272 → Fin 64) (localOf : Fin 272 → Fin 16)
    (groupOf : Fin 272 → Fin 4)
    (high : Fin 64 → K) (low : Fin 16 → K)
    (tag pattern : Fin 272 → K) :
    copySelected blockOf localOf groupOf high low tag pattern =
      copyLiteral blockOf localOf groupOf high low tag pattern := by
  funext group
  simp only [copySelected, copyLiteral,
    groupedSelectorTensor_eq_literal, literalSelectorTensor]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro event _
  split <;> simp_all [mul_add, mul_assoc]

/-- Source-facing name for the exact lazy tag-dot safety bound. -/
theorem copyTagFourProductDot_lt_u64 :
    4 * (AspisV5ComponentCQM31TowerExact.P - 1) ^ 2 < 2 ^ 64 :=
  copy_tag_four_max_products_lt_u64

/-- Source-facing exactness theorem for one translated four-product tag
chunk.  The Charon loop uses `min(index + 4, end)`, hence every nonempty
chunk instantiates this theorem (short final chunks are zero padded). -/
theorem copyTagFourProductDot_reduce_exact
    (left right : Fin 4 → Nat)
    (hleft : ∀ index, left index < AspisV5ComponentCQM31TowerExact.P)
    (hright : ∀ index, right index < AspisV5ComponentCQM31TowerExact.P) :
    ((AspisV5M31RawMulReduction.rawReduceU64 (copyTagRaw4 left right) : Nat) :
        AspisV5ComponentCQM31TowerExact.M31Exact) =
      ∑ index : Fin 4,
        (left index : AspisV5ComponentCQM31TowerExact.M31Exact) *
          (right index : AspisV5ComponentCQM31TowerExact.M31Exact) :=
  copyTagRaw4_reduce_exact left right hleft hright

def gammaSelected (chunkTerm : Fin 4 → Fin 7 → K) : Fin 4 → K :=
  gammaBlockMajor chunkTerm

def gammaLiteral (chunkTerm : Fin 4 → Fin 7 → K) : Fin 4 → K :=
  gammaSlotMajor chunkTerm

theorem gammaSelected_eq_literal (chunkTerm : Fin 4 → Fin 7 → K) :
    gammaSelected chunkTerm = gammaLiteral chunkTerm :=
  gammaBlockMajor_eq_slotMajor chunkTerm

def finishSelected
    (term9 : Fin 9 → K) (term6 : Fin 6 → K)
    (term11 : Fin 11 → K) (term4 : Fin 4 → K) : Fin 4 → K :=
  ![finishDot9 term9, finishDot6 term6, finishDot11 term11, finishDot4 term4]

def finishLiteral
    (term9 : Fin 9 → K) (term6 : Fin 6 → K)
    (term11 : Fin 11 → K) (term4 : Fin 4 → K) : Fin 4 → K :=
  ![∑ index, term9 index, ∑ index, term6 index,
    ∑ index, term11 index, ∑ index, term4 index]

theorem finishSelected_eq_literal
    (term9 : Fin 9 → K) (term6 : Fin 6 → K)
    (term11 : Fin 11 → K) (term4 : Fin 4 → K) :
    finishSelected term9 term6 term11 term4 =
      finishLiteral term9 term6 term11 term4 := by
  funext group
  fin_cases group <;>
    simp [finishSelected, finishLiteral, finishDot9_eq_sum,
      finishDot6_eq_sum, finishDot11_eq_sum, finishDot4_eq_sum]

/-- All values handed from the selected kernels to the unchanged evaluator.
Equality of this structure is deliberately stronger than equality after one
particular challenge-weighted assembly. -/
@[ext] structure EvaluatorPieces (K : Type*) where
  range : Fin 9 → K
  digest : Fin 2 → K
  active : K
  copy : Fin 4 → K
  gamma : Fin 4 → K
  finish : Fin 4 → K

def selectedPieces
    (control : DigestControl)
    (rangeSelector : K) (rangeResidual : Fin 33 → K)
    (digestHigh : Fin 64 → K) (digestLow : Fin 16 → K)
    (digestResidual : Fin 2 → ProductionDigestEvent control → K)
    (activeHigh : Fin 64 → K) (activeLowMask : Fin 65536 → K)
    (copyBlock : Fin 272 → Fin 64) (copyLocal : Fin 272 → Fin 16)
    (copyGroup : Fin 272 → Fin 4)
    (copyHigh : Fin 64 → K) (copyLow : Fin 16 → K)
    (copyTag copyPattern : Fin 272 → K)
    (gammaTerm : Fin 4 → Fin 7 → K)
    (finish9 : Fin 9 → K) (finish6 : Fin 6 → K)
    (finish11 : Fin 11 → K) (finish4 : Fin 4 → K) : EvaluatorPieces K :=
  { range := rangeSelected rangeSelector rangeResidual
  , digest := digestSelected control digestHigh digestLow digestResidual
  , active := activeSelected activeHigh activeLowMask
  , copy := copySelected copyBlock copyLocal copyGroup copyHigh copyLow copyTag copyPattern
  , gamma := gammaSelected gammaTerm
  , finish := finishSelected finish9 finish6 finish11 finish4 }

def literalPieces
    (control : DigestControl)
    (rangeSelector : K) (rangeResidual : Fin 33 → K)
    (digestHigh : Fin 64 → K) (digestLow : Fin 16 → K)
    (digestResidual : Fin 2 → ProductionDigestEvent control → K)
    (activeHigh : Fin 64 → K) (activeLowMask : Fin 65536 → K)
    (copyBlock : Fin 272 → Fin 64) (copyLocal : Fin 272 → Fin 16)
    (copyGroup : Fin 272 → Fin 4)
    (copyHigh : Fin 64 → K) (copyLow : Fin 16 → K)
    (copyTag copyPattern : Fin 272 → K)
    (gammaTerm : Fin 4 → Fin 7 → K)
    (finish9 : Fin 9 → K) (finish6 : Fin 6 → K)
    (finish11 : Fin 11 → K) (finish4 : Fin 4 → K) : EvaluatorPieces K :=
  { range := rangeLiteral rangeSelector rangeResidual
  , digest := digestLiteral control digestHigh digestLow digestResidual
  , active := activeLiteral activeHigh activeLowMask
  , copy := copyLiteral copyBlock copyLocal copyGroup copyHigh copyLow copyTag copyPattern
  , gamma := gammaLiteral gammaTerm
  , finish := finishLiteral finish9 finish6 finish11 finish4 }

/-- Strongest capstone: the exact source-shaped selected schedules preserve
every component of the literal evaluator input.  Consequently any unchanged
downstream evaluator, including the production terminal residual assembly,
returns the identical result. -/
theorem selectedPieces_eq_literalPieces
    (control : DigestControl)
    (rangeSelector : K) (rangeResidual : Fin 33 → K)
    (digestHigh : Fin 64 → K) (digestLow : Fin 16 → K)
    (digestResidual : Fin 2 → ProductionDigestEvent control → K)
    (activeHigh : Fin 64 → K) (activeLowMask : Fin 65536 → K)
    (copyBlock : Fin 272 → Fin 64) (copyLocal : Fin 272 → Fin 16)
    (copyGroup : Fin 272 → Fin 4)
    (copyHigh : Fin 64 → K) (copyLow : Fin 16 → K)
    (copyTag copyPattern : Fin 272 → K)
    (gammaTerm : Fin 4 → Fin 7 → K)
    (finish9 : Fin 9 → K) (finish6 : Fin 6 → K)
    (finish11 : Fin 11 → K) (finish4 : Fin 4 → K) :
    selectedPieces control rangeSelector rangeResidual digestHigh digestLow
        digestResidual activeHigh activeLowMask copyBlock copyLocal copyGroup
        copyHigh copyLow copyTag copyPattern gammaTerm finish9 finish6 finish11 finish4 =
      literalPieces control rangeSelector rangeResidual digestHigh digestLow
        digestResidual activeHigh activeLowMask copyBlock copyLocal copyGroup
        copyHigh copyLow copyTag copyPattern gammaTerm finish9 finish6 finish11 finish4 := by
  apply EvaluatorPieces.ext
  · exact rangeSelected_eq_literal _ _
  · exact digestSelected_eq_literal _ _ _ _
  · exact activeSelected_eq_literal _ _
  · exact copySelected_eq_literal _ _ _ _ _ _ _
  · exact gammaSelected_eq_literal _
  · exact finishSelected_eq_literal _ _ _ _

theorem selected_preserves_literal_evaluator_result
    {Result : Type*} (evaluate : EvaluatorPieces K → Result)
    (control : DigestControl)
    (rangeSelector : K) (rangeResidual : Fin 33 → K)
    (digestHigh : Fin 64 → K) (digestLow : Fin 16 → K)
    (digestResidual : Fin 2 → ProductionDigestEvent control → K)
    (activeHigh : Fin 64 → K) (activeLowMask : Fin 65536 → K)
    (copyBlock : Fin 272 → Fin 64) (copyLocal : Fin 272 → Fin 16)
    (copyGroup : Fin 272 → Fin 4)
    (copyHigh : Fin 64 → K) (copyLow : Fin 16 → K)
    (copyTag copyPattern : Fin 272 → K)
    (gammaTerm : Fin 4 → Fin 7 → K)
    (finish9 : Fin 9 → K) (finish6 : Fin 6 → K)
    (finish11 : Fin 11 → K) (finish4 : Fin 4 → K) :
    evaluate (selectedPieces control rangeSelector rangeResidual digestHigh digestLow
        digestResidual activeHigh activeLowMask copyBlock copyLocal copyGroup
        copyHigh copyLow copyTag copyPattern gammaTerm finish9 finish6 finish11 finish4) =
      evaluate (literalPieces control rangeSelector rangeResidual digestHigh digestLow
        digestResidual activeHigh activeLowMask copyBlock copyLocal copyGroup
        copyHigh copyLow copyTag copyPattern gammaTerm finish9 finish6 finish11 finish4) := by
  rw [selectedPieces_eq_literalPieces]

#print axioms selectedVerifierFeatures_count
#print axioms packedRange_exact_source_interval
#print axioms digestBindingSchedule_uses_exact_locals
#print axioms activeRowMask_eq_basis
#print axioms copyFinishWidths_exact
#print axioms gammaSchedule_exact
#print axioms copyEndpointSchedule_count
#print axioms copyTagFourProductDot_lt_u64
#print axioms copyTagFourProductDot_reduce_exact
#print axioms selectedPieces_eq_literalPieces
#print axioms selected_preserves_literal_evaluator_result

end AspisPool.V7SelectedEvaluatorSparsitySourceBridge
