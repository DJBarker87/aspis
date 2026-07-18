import AspisFormal.V5ComponentCConcreteDownstream

/-!
# v5 Component C: deployed pre-C projection layout

This leaf pins the mathematical layout immediately before Component C:

* total lanes `0..15` are semantic, lane `16` is Hcopy, lane `17` is
  Component B, and lane `18` is Component C;
* the pre-C word uses powers `gamma^0 .. gamma^17` and excludes lane `18`;
* the released pre-C view is one already-combined inactive scalar plus
  eighteen lane-major 76-coordinate views;
* each 76-coordinate view is 72 authenticated layer-zero values followed by
  the four point-major relation claims; and
* the physical 58-field relation tail is decoded to its witness-dependent
  36 rows using the exact non-contiguous order proved in
  `V5ComponentCConcreteDownstream`.

The universal commutation theorem below is mathematical.  Equality with the
actual Rust parser/evaluator is deliberately represented by the single named
`RustPreCProjectionFunctionCorresponds` premise.  No KAT, frozen schedule, or
same-language test discharges that code/model edge here.
-/

namespace AspisV5ComponentCPreProjectionDeployed

open AspisV5ComponentCPreCProjection
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCRelationRowLinearity

abbrev LogicalRelationIndex :=
  AspisV5ComponentCConcreteFoldLinearity.RelationIndex

def semanticLaneCount : Nat := 16
def preCLaneCount : Nat := 18
def totalLaneCount : Nat := 19
def layerZeroViewRows : Nat := 72
def pointClaimRows : Nat := 4

abbrev PreCLane := Fin preCLaneCount
abbrev TotalLane := Fin totalLaneCount
abbrev LayerZeroViewRow := Fin layerZeroViewRows
abbrev PointClaimRow := Fin pointClaimRows

theorem deployed_dimension_teeth :
    semanticLaneCount = 16 ∧ preCLaneCount = 18 ∧ totalLaneCount = 19 ∧
      layerZeroViewRows + pointClaimRows = 76 ∧
      physicalRelationTailFieldCount = 58 ∧
      Fintype.card LogicalRelationIndex = 36 := by
  decide

/-- Canonical total-lane embedding of the eighteen pre-C lanes. -/
def preCLaneToTotal (lane : PreCLane) : TotalLane :=
  ⟨lane.val, by
    simpa only [preCLaneCount, totalLaneCount] using lane.isLt.trans (by decide)⟩

/-- Canonical pre-C embedding of a semantic lane. -/
def semanticLaneToPreC (lane : SemanticLane) : PreCLane :=
  ⟨lane.val, by
    simpa only [preCLaneCount] using lane.isLt.trans (by decide)⟩

def hcopyPreCLane : PreCLane := ⟨16, by decide⟩
def componentBPreCLane : PreCLane := ⟨17, by decide⟩
def componentCTotalLane : TotalLane := ⟨18, by decide⟩

@[simp] theorem preCLaneToTotal_val (lane : PreCLane) :
    (preCLaneToTotal lane).val = lane.val := rfl

@[simp] theorem semanticLaneToPreC_val (lane : SemanticLane) :
    (semanticLaneToPreC lane).val = lane.val := rfl

theorem deployed_lane_numbering :
    hcopyPreCLane.val = 16 ∧ componentBPreCLane.val = 17 ∧
      componentCTotalLane.val = 18 := by
  decide

/-- The exact row split `72 + 4 = 76`: layer-zero rows first, then the four
point-major claim rows. -/
def conditionedRowLayout :
    (LayerZeroViewRow ⊕ PointClaimRow) ≃ ConditionedRow :=
  finSumFinEquiv

/-- Within the 72 authenticated layer-zero coordinates, Rust uses
`4 * fibreOrdinal + slot`. -/
def layerZeroFibreMajorLayout :
    (Fin 18 × Fin 4) ≃ LayerZeroViewRow :=
  finProdFinEquiv

@[simp] theorem layerZeroFibreMajorLayout_val
    (fibreOrdinal : Fin 18) (slot : Fin 4) :
    (layerZeroFibreMajorLayout (fibreOrdinal, slot)).val =
      4 * fibreOrdinal.val + slot.val := by
  change slot.val + 4 * fibreOrdinal.val = 4 * fibreOrdinal.val + slot.val
  omega

/-- The serialized four-by-nineteen claim table uses
`19 * point + lane`. -/
def pointMajorClaimLayout :
    (PointClaimRow × TotalLane) ≃ Fin 76 :=
  finProdFinEquiv

@[simp] theorem pointMajorClaimLayout_val
    (point : PointClaimRow) (lane : TotalLane) :
    (pointMajorClaimLayout (point, lane)).val =
      19 * point.val + lane.val := by
  change lane.val + 19 * point.val = 19 * point.val + lane.val
  omega

/-- Mathematical field-level image of the deployed authenticated data.

`pointMajorClaims` is the flat 76-field Rust table.  Every access below goes
through `pointMajorClaimLayout`, so `point * 19 + lane` is part of the decoder
rather than hidden inside the executable-correspondence premise.  The
Component-C lane is present in that table but intentionally ignored by the
pre-C decoder. -/
structure PhysicalVisible (K : Type*) where
  publishedInactive : K
  layerZeroFibreMajor : PreCLane → Fin 18 → Fin 4 → K
  pointMajorClaims : Fin 76 → K
  relationTail : Fin physicalRelationTailFieldCount → K

/-- Decode one pre-C lane's 76 coordinates from the exact `72 + 4` physical
partition. -/
def decodeLaneView {K : Type*} (visible : PhysicalVisible K)
    (lane : PreCLane) : ConditionedView K :=
  fun row =>
    match conditionedRowLayout.symm row with
    | .inl layerRow =>
        let fibreSlot := layerZeroFibreMajorLayout.symm layerRow
        visible.layerZeroFibreMajor lane fibreSlot.1 fibreSlot.2
    | .inr claim =>
        visible.pointMajorClaims
          (pointMajorClaimLayout (claim, preCLaneToTotal lane))

/-- Decode all eighteen pre-C views into the semantic/Hcopy/B partition used
by the hiding theorem. -/
def decodeConditionedRows {K : Type*} (visible : PhysicalVisible K) :
    PreCConditionedRows (ConditionedView K) where
  semantic lane := decodeLaneView visible (semanticLaneToPreC lane)
  hcopy := decodeLaneView visible hcopyPreCLane
  componentB := decodeLaneView visible componentBPreCLane

theorem preCConditionedRows_ext {U : Type*}
    {left right : PreCConditionedRows U}
    (hsemantic : left.semantic = right.semantic)
    (hhcopy : left.hcopy = right.hcopy)
    (hcomponentB : left.componentB = right.componentB) : left = right := by
  cases left with
  | mk leftSemantic leftHcopy leftB =>
    cases right with
    | mk rightSemantic rightHcopy rightB =>
      simp only at hsemantic hhcopy hcomponentB
      subst rightSemantic
      subst rightHcopy
      subst rightB
      rfl

/-- Decode only the witness-dependent `2 + 7` fields per relation round from
the physical 58-field tail. -/
def decodeLogicalRelationRows {K : Type*} (visible : PhysicalVisible K) :
    LogicalRelationIndex → K :=
  reorderPhysicalRelationTail visible.relationTail

@[simp] theorem decodeLaneView_layerZero {K : Type*}
    (visible : PhysicalVisible K) (lane : PreCLane)
    (fibreOrdinal : Fin 18) (slot : Fin 4) :
    decodeLaneView visible lane
        (conditionedRowLayout
          (.inl (layerZeroFibreMajorLayout (fibreOrdinal, slot)))) =
      visible.layerZeroFibreMajor lane fibreOrdinal slot := by
  simp [decodeLaneView, conditionedRowLayout]

@[simp] theorem decodeLaneView_pointClaim {K : Type*}
    (visible : PhysicalVisible K) (lane : PreCLane)
    (claim : PointClaimRow) :
    decodeLaneView visible lane (conditionedRowLayout (.inr claim)) =
      visible.pointMajorClaims
        (pointMajorClaimLayout (claim, preCLaneToTotal lane)) := by
  simp [decodeLaneView, conditionedRowLayout]

theorem decodeLogicalRelationRows_ood {K : Type*}
    (visible : PhysicalVisible K) (round : Fin 4) (sample : Fin 2) :
    decodeLogicalRelationRows visible
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
      visible.relationTail (physicalRelationIndex (round, .inl sample)) := by
  exact reorderPhysicalRelationTail_ood visible.relationTail round sample

theorem decodeLogicalRelationRows_polynomial {K : Type*}
    (visible : PhysicalVisible K) (round : Fin 4) (degree : Fin 7) :
    decodeLogicalRelationRows visible
        (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
      visible.relationTail (physicalRelationIndex (round, .inr degree)) := by
  exact reorderPhysicalRelationTail_polynomial visible.relationTail round degree

/-! ### A structured mathematical producer for the physical 58-field tail -/

/-- The exact field inventory written by
`V5RealHostArtifact::encode_relation_tail`: public point coordinates, public
line points, witness-dependent OOD values, public OOD mixes,
witness-dependent polynomial coefficients, and final coefficients. -/
structure PhysicalRelationFields (K : Type*) where
  circlePointCoordinates : Fin 4 → K
  linePoints : Fin 6 → K
  oodValues : Fin 4 → Fin 2 → K
  oodMixes : Fin 4 → Fin 2 → K
  polynomialCoefficients : Fin 4 → Fin 7 → K
  finalCoefficients : Fin 4 → K

/-- Flatten the structured physical relation fields into their exact 58-field
Rust order. -/
def encodePhysicalRelationTail {K : Type*} (fields : PhysicalRelationFields K) :
    Fin physicalRelationTailFieldCount → K :=
  fun index =>
    if hCircle : index.val < 4 then
      fields.circlePointCoordinates ⟨index.val, hCircle⟩
    else if hLine : index.val < physicalOodStart then
      fields.linePoints ⟨index.val - 4, by
        simp only [physicalOodStart] at hLine
        omega⟩
    else if hOod : index.val < physicalMixStart then
      let flat : Fin 8 := ⟨index.val - physicalOodStart, by
        simp only [physicalOodStart, physicalMixStart] at hLine hOod ⊢
        omega⟩
      let tagged : Fin 4 × Fin 2 := finProdFinEquiv.symm flat
      fields.oodValues tagged.1 tagged.2
    else if hMix : index.val < physicalPolynomialStart then
      let flat : Fin 8 := ⟨index.val - physicalMixStart, by
        simp only [physicalMixStart, physicalPolynomialStart] at hOod hMix ⊢
        omega⟩
      let tagged : Fin 4 × Fin 2 := finProdFinEquiv.symm flat
      fields.oodMixes tagged.1 tagged.2
    else if hPolynomial : index.val < physicalFinalStart then
      let flat : Fin 28 := ⟨index.val - physicalPolynomialStart, by
        simp only [physicalPolynomialStart, physicalFinalStart] at hMix hPolynomial ⊢
        omega⟩
      let tagged : Fin 4 × Fin 7 := finProdFinEquiv.symm flat
      fields.polynomialCoefficients tagged.1 tagged.2
    else
      fields.finalCoefficients ⟨index.val - physicalFinalStart, by
        have hlt := index.isLt
        simp only [physicalRelationTailFieldCount, physicalFinalStart] at hlt ⊢
        omega⟩

/-- The logical witness-dependent rows represented by the structured physical
tail. -/
def logicalRelationRowsOfFields {K : Type*} (fields : PhysicalRelationFields K) :
    LogicalRelationIndex → K :=
  fun logical =>
    let tagged := relationTaggedIndexEquiv.symm logical
    match tagged.2 with
    | .inl sample => fields.oodValues tagged.1 sample
    | .inr degree => fields.polynomialCoefficients tagged.1 degree

@[simp] theorem encodePhysicalRelationTail_ood {K : Type*}
    (fields : PhysicalRelationFields K) (round : Fin 4) (sample : Fin 2) :
    encodePhysicalRelationTail fields
        (physicalRelationIndex (round, .inl sample)) =
      fields.oodValues round sample := by
  have hCircle : ¬(10 + 2 * round.val + sample.val < 4) := by omega
  have hLine : ¬(10 + 2 * round.val + sample.val < 10) := by omega
  have hOod : 10 + 2 * round.val + sample.val < 18 := by omega
  have htagged :
      finProdFinEquiv.symm
          (⟨10 + 2 * round.val + sample.val - 10, by omega⟩ : Fin 8) =
        (round, sample) := by
    apply finProdFinEquiv.injective
    rw [finProdFinEquiv.apply_symm_apply]
    apply Fin.ext
    change 10 + 2 * round.val + sample.val - 10 =
      sample.val + 2 * round.val
    omega
  simp [encodePhysicalRelationTail, physicalRelationIndex,
    physicalOodStart, physicalMixStart, hCircle, hLine, hOod, htagged]

@[simp] theorem encodePhysicalRelationTail_polynomial {K : Type*}
    (fields : PhysicalRelationFields K) (round : Fin 4) (degree : Fin 7) :
    encodePhysicalRelationTail fields
        (physicalRelationIndex (round, .inr degree)) =
      fields.polynomialCoefficients round degree := by
  have hCircle : ¬(26 + 7 * round.val + degree.val < 4) := by omega
  have hLine : ¬(26 + 7 * round.val + degree.val < 10) := by omega
  have hOod : ¬(26 + 7 * round.val + degree.val < 18) := by omega
  have hMix : ¬(26 + 7 * round.val + degree.val < 26) := by omega
  have hPolynomial : 26 + 7 * round.val + degree.val < 54 := by omega
  have htagged :
      finProdFinEquiv.symm
          (⟨26 + 7 * round.val + degree.val - 26, by omega⟩ : Fin 28) =
        (round, degree) := by
    apply finProdFinEquiv.injective
    rw [finProdFinEquiv.apply_symm_apply]
    apply Fin.ext
    change 26 + 7 * round.val + degree.val - 26 =
      degree.val + 7 * round.val
    omega
  simp [encodePhysicalRelationTail, physicalRelationIndex,
    physicalOodStart, physicalMixStart, physicalPolynomialStart,
    physicalFinalStart, hCircle, hLine, hOod, hMix, hPolynomial,
    htagged]

/-- Exact universal `58 -> 36` theorem: encoding the structured Rust-order
tail and applying the non-contiguous decoder recovers precisely the two OOD
and seven polynomial rows of each round. -/
theorem decode_encode_physical_relation_tail {K : Type*}
    (fields : PhysicalRelationFields K) :
    reorderPhysicalRelationTail (encodePhysicalRelationTail fields) =
      logicalRelationRowsOfFields fields := by
  funext logical
  obtain ⟨⟨round, row⟩, rfl⟩ := relationTaggedIndexEquiv.surjective logical
  cases row with
  | inl sample =>
      have hindex : relationTaggedIndexEquiv.symm
          (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
          (round, .inl sample) := by
        unfold relationTaggedIndexEquiv
        apply Prod.ext
        · rfl
        · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
      change reorderPhysicalRelationTail (encodePhysicalRelationTail fields)
          (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
        logicalRelationRowsOfFields fields
          (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))
      rw [reorderPhysicalRelationTail_ood, encodePhysicalRelationTail_ood]
      simp only [logicalRelationRowsOfFields, hindex]
  | inr degree =>
      have hindex : relationTaggedIndexEquiv.symm
          (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
          (round, .inr degree) := by
        unfold relationTaggedIndexEquiv
        apply Prod.ext
        · rfl
        · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
      change reorderPhysicalRelationTail (encodePhysicalRelationTail fields)
          (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
        logicalRelationRowsOfFields fields
          (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))
      rw [reorderPhysicalRelationTail_polynomial,
        encodePhysicalRelationTail_polynomial]
      simp only [logicalRelationRowsOfFields, hindex]

section Model

variable {K M : Type*} [Field K]
variable [AddCommGroup M] [Module K M]

abbrev LaneWords := TotalLane → M

def semanticWords (words : LaneWords (M := M)) : SemanticLane → M :=
  fun lane => words (preCLaneToTotal (semanticLaneToPreC lane))

def hcopyWord (words : LaneWords (M := M)) : M :=
  words (preCLaneToTotal hcopyPreCLane)

def componentBWord (words : LaneWords (M := M)) : M :=
  words (preCLaneToTotal componentBPreCLane)

/-- The exact word before `gamma^18 * C`: powers `0..15`, then Hcopy at 16
and B at 17.  Total lane 18 is not read. -/
def deployedPreCWord (gamma : K) (words : LaneWords (M := M)) : M :=
  preCWord gamma (semanticWords words) (hcopyWord words) (componentBWord words)

/-- Build the mathematical physical view from all nineteen lane words.  The
Component-C word contributes to its own four point-major entries, but never
to the eighteen decoded pre-C views or the combined inactive scalar. -/
def modelVisible (ell : M →ₗ[K] K)
    (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : LaneWords (M := M))
    (tail : Fin physicalRelationTailFieldCount → K) : PhysicalVisible K where
  publishedInactive := ell (deployedPreCWord gamma words)
  layerZeroFibreMajor lane fibreOrdinal slot :=
    E (words (preCLaneToTotal lane))
      (conditionedRowLayout
        (.inl (layerZeroFibreMajorLayout (fibreOrdinal, slot))))
  pointMajorClaims flatIndex :=
    let claimLane := pointMajorClaimLayout.symm flatIndex
    E (words claimLane.2) (conditionedRowLayout (.inr claimLane.1))
  relationTail := tail

/-- The complete mathematical visible object, including the exact structured
producer of the physical 58-field relation tail. -/
def modelVisibleFromFields (ell : M →ₗ[K] K)
    (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : LaneWords (M := M)) (fields : PhysicalRelationFields K) :
    PhysicalVisible K :=
  modelVisible ell E gamma words (encodePhysicalRelationTail fields)

theorem deployedPreCWord_explicit (gamma : K)
    (words : LaneWords (M := M)) :
    deployedPreCWord gamma words =
      (∑ lane : SemanticLane,
          gamma ^ lane.val • words (preCLaneToTotal (semanticLaneToPreC lane)))
        + gamma ^ 16 • words (preCLaneToTotal hcopyPreCLane)
        + gamma ^ 17 • words (preCLaneToTotal componentBPreCLane) := by
  rfl

theorem decodeLaneView_modelVisible (ell : M →ₗ[K] K)
    (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : LaneWords (M := M))
    (tail : Fin physicalRelationTailFieldCount → K) (lane : PreCLane) :
    decodeLaneView (modelVisible ell E gamma words tail) lane =
      E (words (preCLaneToTotal lane)) := by
  funext row
  obtain ⟨layerRow | claim, rfl⟩ := conditionedRowLayout.surjective row
  · obtain ⟨⟨fibreOrdinal, slot⟩, rfl⟩ :=
      layerZeroFibreMajorLayout.surjective layerRow
    simp [modelVisible]
  · simp [modelVisible]

theorem decodeConditionedRows_modelVisible (ell : M →ₗ[K] K)
    (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : LaneWords (M := M))
    (tail : Fin physicalRelationTailFieldCount → K) :
    decodeConditionedRows (modelVisible ell E gamma words tail) =
      preCConditionedRows E (semanticWords words)
        (hcopyWord words) (componentBWord words) := by
  apply preCConditionedRows_ext
  · funext lane
    exact decodeLaneView_modelVisible ell E gamma words tail
      (semanticLaneToPreC lane)
  · exact decodeLaneView_modelVisible ell E gamma words tail hcopyPreCLane
  · exact decodeLaneView_modelVisible ell E gamma words tail componentBPreCLane

/-- Universal mathematical commutation of the deployed field layout with the
pre-C projection model.  This is not a claim about Rust bytes. -/
theorem modelVisible_deployedProjectionCorrespondence
    (ell : M →ₗ[K] K) (E : M →ₗ[K] ConditionedView K) (gamma : K) :
    DeployedProjectionCorrespondence
      (fun input : LaneWords (M := M) ×
          (Fin physicalRelationTailFieldCount → K) =>
        modelVisible ell E gamma input.1 input.2)
      PhysicalVisible.publishedInactive decodeConditionedRows
      ell E gamma
      (fun input lane => semanticWords input.1 lane)
      (fun input => hcopyWord input.1)
      (fun input => componentBWord input.1) := by
  constructor
  · intro input
    rfl
  · intro input
    exact decodeConditionedRows_modelVisible ell E gamma input.1 input.2

/-- The decoded gamma projection of the eighteen 76-row views is literally
`E(preCWord)`. -/
theorem projectedConditionedRows_modelVisible
    (ell : M →ₗ[K] K) (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : LaneWords (M := M))
    (tail : Fin physicalRelationTailFieldCount → K) :
    projectedConditionedRows gamma
        (decodeConditionedRows (modelVisible ell E gamma words tail)) =
      E (deployedPreCWord gamma words) := by
  rw [decodeConditionedRows_modelVisible]
  exact (E_preCWord_conditioned_rows E gamma
    (semanticWords words) (hcopyWord words) (componentBWord words)).symm

end Model

/-! ## The one honest Rust code/model seam -/

namespace UnmetDeployment

variable {K M S Bytes : Type*} [Field K]
variable [AddCommGroup M] [Module K M]

/-- The single executable correspondence premise.  It covers canonical byte
decoding, split C1/C2 opening addressing, point-major claim parsing, the
combined inactive field, and the physical 58-field relation-tail parser.
It deliberately does not follow from a frozen KAT. -/
def RustPreCProjectionFunctionCorresponds
    (rustVisibleBytes : S → Bytes)
    (decodeRustVisible : Bytes → PhysicalVisible K)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : S → LaneWords (M := M))
    (relationFields : S → PhysicalRelationFields K) : Prop :=
  ∀ sample, decodeRustVisible (rustVisibleBytes sample) =
    modelVisibleFromFields ell E gamma (words sample) (relationFields sample)

end UnmetDeployment

/-- Transfer the universal mathematical decoder theorem across the one named
Rust code/model equality.  The second conjunct pins the 58-to-36 physical
selection at the same time. -/
theorem deployedProjection_and_relation_of_rust_correspondence
    {K M S Bytes : Type*} [Field K]
    [AddCommGroup M] [Module K M]
    (rustVisibleBytes : S → Bytes)
    (decodeRustVisible : Bytes → PhysicalVisible K)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] ConditionedView K) (gamma : K)
    (words : S → LaneWords (M := M))
    (relationFields : S → PhysicalRelationFields K)
    (hRust : UnmetDeployment.RustPreCProjectionFunctionCorresponds
      rustVisibleBytes decodeRustVisible ell E gamma words relationFields) :
    DeployedProjectionCorrespondence
        rustVisibleBytes
        (fun bytes => (decodeRustVisible bytes).publishedInactive)
        (fun bytes => decodeConditionedRows (decodeRustVisible bytes))
        ell E gamma
        (fun sample lane => semanticWords (words sample) lane)
        (fun sample => hcopyWord (words sample))
        (fun sample => componentBWord (words sample))
      ∧
    ∀ sample, decodeLogicalRelationRows
        (decodeRustVisible (rustVisibleBytes sample)) =
      logicalRelationRowsOfFields (relationFields sample) := by
  constructor
  · constructor
    · intro sample
      change ell (deployedPreCWord gamma (words sample)) =
        (decodeRustVisible (rustVisibleBytes sample)).publishedInactive
      rw [hRust sample]
      rfl
    · intro sample
      change decodeConditionedRows (decodeRustVisible (rustVisibleBytes sample)) =
        preCConditionedRows E (semanticWords (words sample))
          (hcopyWord (words sample)) (componentBWord (words sample))
      rw [hRust sample]
      exact decodeConditionedRows_modelVisible ell E gamma
        (words sample) (encodePhysicalRelationTail (relationFields sample))
  · intro sample
    rw [hRust sample]
    change reorderPhysicalRelationTail
      (encodePhysicalRelationTail (relationFields sample)) = _
    exact decode_encode_physical_relation_tail (relationFields sample)

/-! ## Non-vacuity and mutation teeth -/

namespace Teeth

private instance aspisFactPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

abbrev K5 := ZMod 5

theorem rust_correspondence_nonvacuous
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] ConditionedView K) (gamma : K) :
    UnmetDeployment.RustPreCProjectionFunctionCorresponds
      (fun input : LaneWords (M := M) ×
          PhysicalRelationFields K => input)
      (fun input => modelVisibleFromFields ell E gamma input.1 input.2)
      ell E gamma
      Prod.fst Prod.snd := by
  intro input
  rfl

/-- Wrongly assigning B the Hcopy power `gamma^16` changes the projection at
the deployed exponents; this is a concrete algebraic tooth. -/
theorem componentB_power17_is_loadBearing :
    (2 : K5) ^ 17 ≠ (2 : K5) ^ 16 := by
  decide

def onlyComponentBRows : PreCConditionedRows K5 where
  semantic _ := 0
  hcopy := 0
  componentB := 1

def wrongPower16Projection (gamma : K5) (rows : PreCConditionedRows K5) : K5 :=
  (∑ lane : SemanticLane, gamma ^ lane.val * rows.semantic lane)
    + gamma ^ 16 * rows.hcopy
    + gamma ^ 16 * rows.componentB

/-- The exponent tooth reaches the actual projection formula: on a view with
only the B coordinate nonzero, replacing B's `gamma^17` by `gamma^16`
changes the released projection. -/
theorem wrong_componentB_power_changes_projection :
    projectedConditionedRows (2 : K5) onlyComponentBRows ≠
      wrongPower16Projection 2 onlyComponentBRows := by
  decide

def oneAtPhysicalOodZero : Fin physicalRelationTailFieldCount → K5 :=
  fun index => if index.val = physicalOodStart then 1 else 0

/-- A decoder that takes the first polynomial field (26) where the first OOD
field (10) belongs changes the logical relation view. -/
theorem physical_relation_order_is_loadBearing :
    oneAtPhysicalOodZero
        (physicalRelationIndex ((0 : Fin 4), .inl (0 : Fin 2))) ≠
      oneAtPhysicalOodZero
        (physicalRelationIndex ((0 : Fin 4), .inr (0 : Fin 7))) := by
  decide

end Teeth

#print axioms deployed_dimension_teeth
#print axioms preCLaneToTotal_val
#print axioms semanticLaneToPreC_val
#print axioms deployed_lane_numbering
#print axioms layerZeroFibreMajorLayout_val
#print axioms pointMajorClaimLayout_val
#print axioms preCConditionedRows_ext
#print axioms decodeLaneView_layerZero
#print axioms decodeLaneView_pointClaim
#print axioms decodeLogicalRelationRows_ood
#print axioms decodeLogicalRelationRows_polynomial
#print axioms encodePhysicalRelationTail_ood
#print axioms encodePhysicalRelationTail_polynomial
#print axioms decode_encode_physical_relation_tail
#print axioms deployedPreCWord_explicit
#print axioms decodeLaneView_modelVisible
#print axioms decodeConditionedRows_modelVisible
#print axioms modelVisible_deployedProjectionCorrespondence
#print axioms projectedConditionedRows_modelVisible
#print axioms UnmetDeployment.RustPreCProjectionFunctionCorresponds
#print axioms deployedProjection_and_relation_of_rust_correspondence
#print axioms Teeth.rust_correspondence_nonvacuous
#print axioms Teeth.componentB_power17_is_loadBearing
#print axioms Teeth.wrong_componentB_power_changes_projection
#print axioms Teeth.physical_relation_order_is_loadBearing

end AspisV5ComponentCPreProjectionDeployed
