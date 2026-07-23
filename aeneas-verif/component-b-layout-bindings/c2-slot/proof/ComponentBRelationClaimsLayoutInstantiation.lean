import ComponentBC2SlotProof
import ComponentBRelationClaimsTerminalBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBRelationClaimsLayoutInstantiation

open AspisV5CompactTerminal

abbrev LayoutQM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev RelationQM31 := aspis_prover.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBRealEvaluatorProof.ExactQM31
abbrev RelationExactQM31 := aspis_prover.MultilinearEvalProofs.ExactQM31
abbrev Lane :=
  ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane

local instance : Inhabited LayoutQM31 :=
  ⟨ComponentBGenerated.aspis_core.field.QM31.ZERO⟩

local instance : Inhabited RelationQM31 :=
  ⟨aspis_prover.aspis_core.field.QM31.ZERO⟩

/-- Coordinate-preserving adapter between two independent Aeneas
extractions of the same Rust `QM31` structure. -/
def toRelationQM31 (value : LayoutQM31) : RelationQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

/-- Coordinatewise transport between the exact quadratic towers used by the
two independent extraction bundles. -/
def relationExactToLayout (value : RelationExactQM31) : ExactQM31 :=
  ⟨value.re, value.im⟩

/-- Inverse coordinate transport, used to discharge relation-claim equalities
without identifying the two independently extracted exact-tower constants. -/
def layoutExactToRelation (value : ExactQM31) : RelationExactQM31 :=
  ⟨value.re, value.im⟩

@[simp] theorem relationExactToLayout_layoutExactToRelation
    (value : ExactQM31) :
    relationExactToLayout (layoutExactToRelation value) = value := by
  rfl

@[simp] theorem layoutExactToRelation_relationExactToLayout
    (value : RelationExactQM31) :
    layoutExactToRelation (relationExactToLayout value) = value := by
  rfl

theorem relationExactToLayout_injective :
    Function.Injective relationExactToLayout := by
  intro left right equal
  have := congrArg layoutExactToRelation equal
  simpa using this

@[simp] theorem relationExactToLayout_zero :
    relationExactToLayout (0 : RelationExactQM31) = (0 : ExactQM31) := by
  rfl

@[simp] theorem relationExactToLayout_one :
    relationExactToLayout (1 : RelationExactQM31) = (1 : ExactQM31) := by
  rfl

@[simp] theorem relationExactToLayout_add (left right : RelationExactQM31) :
    relationExactToLayout (left + right) =
      relationExactToLayout left + relationExactToLayout right := by
  rfl

@[simp] theorem relationExactToLayout_neg (value : RelationExactQM31) :
    relationExactToLayout (-value) = -relationExactToLayout value := by
  rfl

@[simp] theorem relationExactToLayout_mul (left right : RelationExactQM31) :
    relationExactToLayout (left * right) =
      relationExactToLayout left * relationExactToLayout right := by
  rfl

/-- The coordinate transport is the exact field embedding between the two
independent extraction bundles. -/
def relationExactToLayoutHom : RelationExactQM31 →+* ExactQM31 where
  toFun := relationExactToLayout
  map_one' := relationExactToLayout_one
  map_mul' := relationExactToLayout_mul
  map_zero' := relationExactToLayout_zero
  map_add' := relationExactToLayout_add

@[simp] theorem relationExactToLayoutHom_apply (value : RelationExactQM31) :
    relationExactToLayoutHom value = relationExactToLayout value := by
  rfl

@[simp] theorem relationExactToLayout_half :
    relationExactToLayout
        (AspisV5SumcheckCommitment.half : RelationExactQM31) =
      (AspisV5SumcheckCommitment.half : ExactQM31) := by
  change relationExactToLayoutHom
      ((2 : RelationExactQM31)⁻¹) = (2 : ExactQM31)⁻¹
  rw [map_inv₀ relationExactToLayoutHom]
  congr 1

@[simp] theorem relationExactToLayout_pow (value : RelationExactQM31)
    (exponent : Nat) :
    relationExactToLayout (value ^ exponent) =
      relationExactToLayout value ^ exponent := by
  induction exponent with
  | zero => simp only [pow_zero, relationExactToLayout_one]
  | succ exponent ih =>
      rw [pow_succ, pow_succ, relationExactToLayout_mul, ih]

theorem relationExactToLayout_finsetSum {ι : Type*} (set : Finset ι)
    (values : ι → RelationExactQM31) :
    relationExactToLayout (∑ index ∈ set, values index) =
      ∑ index ∈ set, relationExactToLayout (values index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, relationExactToLayout_zero]
  | @insert index set absent inductionHypothesis =>
      simp only [Finset.sum_insert absent, relationExactToLayout_add,
        inductionHypothesis]

theorem relationExactToLayout_fintypeSum {ι : Type*} [Fintype ι]
    (values : ι → RelationExactQM31) :
    relationExactToLayout (∑ index, values index) =
      ∑ index, relationExactToLayout (values index) := by
  exact relationExactToLayout_finsetSum Finset.univ values

theorem relationExactToLayout_storedCoefficient
    (tails : Round → TailDegree → RelationExactQM31)
    (index : CoefficientIndex) :
    relationExactToLayout (storedCoefficient tails index) =
      storedCoefficient
        (fun round degree => relationExactToLayout (tails round degree)) index := by
  rcases index with ⟨round, degree⟩
  refine Fin.cases ?_ (fun tailDegree => ?_) degree
  · rw [storedCoefficient_zero, storedCoefficient_zero,
      relationExactToLayout_mul, relationExactToLayout_neg,
      relationExactToLayout_half]
    congr 2
  · rfl

theorem relationExactToLayout_basis (location : Row)
    (value : RelationExactQM31) (row : Row) :
    relationExactToLayout (basis location value row) =
      basis location (relationExactToLayout value) row := by
  unfold basis
  split <;> rfl

theorem relationExactToLayout_rowMessage
    (initial : RelationExactQM31)
    (tails : Round → TailDegree → RelationExactQM31) (row : Row) :
    relationExactToLayout (rowMessage initial tails row) =
      rowMessage (relationExactToLayout initial)
        (fun round degree => relationExactToLayout (tails round degree)) row := by
  unfold rowMessage
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [relationExactToLayout_add]
  apply congrArg₂ (· + ·)
  · exact relationExactToLayout_basis initialRow initial row
  · rw [relationExactToLayout_fintypeSum]
    apply Finset.sum_congr rfl
    intro index _
    rw [relationExactToLayout_basis,
      relationExactToLayout_storedCoefficient]

theorem relationExactToLayout_terminalWeights
    (point : Round → RelationExactQM31) (row : Row) :
    relationExactToLayout (terminalWeights point 1 row) =
      terminalWeights
        (fun round => relationExactToLayout (point round)) 1 row := by
  unfold terminalWeights
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [relationExactToLayout_add]
  apply congrArg₂ (· + ·)
  · rw [relationExactToLayout_basis, relationExactToLayout_mul,
      relationExactToLayout_one, relationExactToLayout_pow,
      relationExactToLayout_half]
  · rw [relationExactToLayout_fintypeSum]
    apply Finset.sum_congr rfl
    intro index _
    rw [relationExactToLayout_basis, relationExactToLayout_mul,
      relationExactToLayout_mul, relationExactToLayout_one,
      relationExactToLayout_pow, relationExactToLayout_pow,
      relationExactToLayout_half]

/-- The adapter preserves the exact maintained field element definitionally. -/
theorem toRelationQM31_exact (value : LayoutQM31) :
    relationExactToLayout
        (aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
          (toRelationQM31 value)) =
      ComponentBRealEvaluatorProof.generatedQm31ToExact value := by
  rfl

/-- The exact relation-field transcript point obtained from the authentic
layout extraction. -/
def relationPoint (point : Array LayoutQM31 10#usize) :
    Round → RelationExactQM31 :=
  fun round =>
    aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
      (toRelationQM31 point.val[round.val]!)

/-- The exact relation-field initial claim from the authentic mask. -/
def relationMaskInitial (mask : ComponentBEncodedMessageBindingProof.Mask) :
    RelationExactQM31 :=
  aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
    (toRelationQM31 mask.initial_claim)

/-- The exact relation-field nonconstant coefficient tail from the authentic
mask. -/
def relationMaskTails (mask : ComponentBEncodedMessageBindingProof.Mask) :
    Round → TailDegree → RelationExactQM31 :=
  fun round degree =>
    aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
      (toRelationQM31
        mask.zero_boundary_rounds.val[round.val]!.val[degree.val + 1]!)

@[simp] theorem relationPoint_toLayout
    (point : Array LayoutQM31 10#usize) (round : Round) :
    relationExactToLayout (relationPoint point round) =
      ComponentBRealEvaluatorProof.generatedQm31ToExact
        point.val[round.val]! := by
  exact toRelationQM31_exact _

@[simp] theorem relationMaskInitial_toLayout
    (mask : ComponentBEncodedMessageBindingProof.Mask) :
    relationExactToLayout (relationMaskInitial mask) =
      ComponentBEncodedMessageBindingProof.maskInitial mask := by
  exact toRelationQM31_exact _

@[simp] theorem relationMaskTails_toLayout
    (mask : ComponentBEncodedMessageBindingProof.Mask)
    (round : Round) (degree : TailDegree) :
    relationExactToLayout (relationMaskTails mask round degree) =
      ComponentBEncodedMessageBindingProof.maskTails mask round degree := by
  exact toRelationQM31_exact _

/-- Coordinatewise adapter for an extracted Rust vector. -/
def toRelationVec (values : alloc.vec.Vec LayoutQM31) :
    alloc.vec.Vec RelationQM31 :=
  ⟨values.val.map toRelationQM31, by simpa using values.property⟩

theorem toRelationVec_get_bang
    (values : alloc.vec.Vec LayoutQM31) (index : Nat)
    (hindex : index < values.val.length) :
    (toRelationVec values).val[index]! =
      toRelationQM31 values.val[index]! := by
  unfold toRelationVec
  rw [List.getElem!_of_getElem?]
  simp [hindex]

/-- The relation-claim extraction's representation of the exact source C2
array assembled by `assemble_v5_c2_messages`. -/
def relationC2Messages
    (hcopy componentB componentC : alloc.vec.Vec LayoutQM31) :
    Array (alloc.vec.Vec RelationQM31) 3#usize :=
  Array.make 3#usize
    [toRelationVec hcopy, toRelationVec componentB,
      toRelationVec componentC]

theorem relationC2Messages_slot_one
    (hcopy componentB componentC : alloc.vec.Vec LayoutQM31) :
    aspis_prover.ComponentBRelationClaimsProof.generatedComponentBMessage
        (relationC2Messages hcopy componentB componentC) =
      toRelationVec componentB := by
  rfl

/-- The authentic generated terminal-covector constructor discharges the
relation consumer's exact row-identification premise after coordinate
transport. -/
theorem extracted_component_b_relation_claims_covectorRows
    (point : Array LayoutQM31 10#usize)
    (hpointCanonical : ComponentBLayoutBindingsProof.CanonicalArray point) :
    ∃ covector,
      ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
          point = ok covector ∧
      covector.length = 1024 ∧
      ComponentBLayoutBindingsProof.CanonicalVec covector ∧
      ∀ row : Row,
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)) row =
          terminalWeights (relationPoint point) 1 row := by
  obtain ⟨covector, covectorRun, covectorLength, covectorCanonical,
      covectorRows⟩ :=
    ComponentBLayoutBindingsProof.extracted_terminal_covector_rows_eq_terminalWeights
      point hpointCanonical
  refine ⟨covector, covectorRun, covectorLength, covectorCanonical, ?_⟩
  intro row
  apply relationExactToLayout_injective
  rw [relationExactToLayout_terminalWeights]
  have hlength : covector.val.length = 1024 := by
    simpa [alloc.vec.Vec.length] using covectorLength
  change relationExactToLayout
      (aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
        (toRelationVec covector).val[row.val]!) = _
  rw [toRelationVec_get_bang covector row.val (by
    rw [hlength]
    exact row.isLt), toRelationQM31_exact]
  have mappedPoint :
      (fun round => relationExactToLayout (relationPoint point round)) =
        fun round =>
          ComponentBRealEvaluatorProof.generatedQm31ToExact
            point.val[round.val]! := by
    funext round
    exact relationPoint_toLayout point round
  rw [mappedPoint]
  exact covectorRows row

/-- The source-authentic C2 copy and lane-order constructor identify every
committed Component-B row selected by the relation-claims consumer with the
same physical row of the authentic encoded lane. -/
theorem extracted_component_b_committed_rows_eq_encoded_lane
    (componentB : Lane) (hcopy componentC : alloc.vec.Vec LayoutQM31) :
    ∃ copied assembled,
      ComponentBC2SlotGenerated.component_b_message_values componentB =
        ok copied ∧
      ComponentBC2SlotGenerated.assemble_v5_c2_messages
          hcopy copied componentC = ok assembled ∧
      assembled = Array.make 3#usize [hcopy, copied, componentC] ∧
      ∀ row : Fin 1024,
        relationExactToLayout
            (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
              (relationC2Messages hcopy copied componentC) row) =
          ComponentBLayoutBindingsProof.exactArrayAt
            componentB.values row.val := by
  obtain ⟨copied, copiedRun, copiedRows⟩ := Aeneas.Std.WP.spec_imp_exists
    (ComponentBC2SlotProof.extracted_component_b_message_values_exact componentB)
  let assembled := Array.make 3#usize [hcopy, copied, componentC]
  refine ⟨copied, assembled, copiedRun, rfl, rfl, ?_⟩
  intro row
  rw [aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows,
    relationC2Messages_slot_one]
  have hlength : copied.val.length = 1024 := by
    rw [copiedRows, Array.length_eq componentB.values]
    norm_num
  rw [toRelationVec_get_bang copied row.val (by
    rw [hlength]
    exact row.isLt), toRelationQM31_exact, copiedRows]
  rfl

/-- The exact `weightedMessageRows` fact required by the source-authentic
relation-claims consumer.  The proof composes the generated encoder, generated
1,024-row copy, generated C2 lane-one constructor, and the maintained sparse
message theorem.  It deliberately asserts nothing about pad or pivot rows
before multiplication by the terminal covector. -/
theorem extracted_component_b_relation_claims_layoutWeightedMessageRows
    (point : Round → ExactQM31)
    (mask : ComponentBEncodedMessageBindingProof.Mask)
    (pads : Array LayoutQM31 255#usize) (pivotPad : LayoutQM31)
    (componentB : Lane)
    (hmask : ComponentBEncodedMessageBindingProof.CanonicalMask mask)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok componentB))
    (hcopy componentC : alloc.vec.Vec LayoutQM31) :
    ∃ copied assembled,
      ComponentBC2SlotGenerated.component_b_message_values componentB =
        ok copied ∧
      ComponentBC2SlotGenerated.assemble_v5_c2_messages
          hcopy copied componentC = ok assembled ∧
      assembled = Array.make 3#usize [hcopy, copied, componentC] ∧
      ∀ row : Row,
        terminalWeights point 1 row *
            relationExactToLayout
              (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
                (relationC2Messages hcopy copied componentC) row) =
          terminalWeights point 1 row *
            rowMessage
              (ComponentBEncodedMessageBindingProof.maskInitial mask)
              (ComponentBEncodedMessageBindingProof.maskTails mask) row := by
  obtain ⟨copied, assembled, copiedRun, assembledRun, assembledExact,
      committedRows⟩ :=
    extracted_component_b_committed_rows_eq_encoded_lane
      componentB hcopy componentC
  refine ⟨copied, assembled, copiedRun, assembledRun, assembledExact, ?_⟩
  intro row
  have hencoded :=
    ComponentBEncodedMessageBindingProof.extracted_component_b_encode_weighted_rowMessage
      point mask pads pivotPad componentB hmask encodeRun row
  rw [committedRows row]
  rw [hencoded]

/-- The actual relation-field `weightedMessageRows` premise is discharged by
the authentic encoder, authentic 1,024-row copy, and authentic C2 slot-one
constructor.  Only the weighted equality is claimed; the pad and pivot rows
remain deliberately unconstrained before multiplication. -/
theorem extracted_component_b_relation_claims_weightedMessageRows
    (point : Array LayoutQM31 10#usize)
    (mask : ComponentBEncodedMessageBindingProof.Mask)
    (pads : Array LayoutQM31 255#usize) (pivotPad : LayoutQM31)
    (componentB : Lane)
    (hmask : ComponentBEncodedMessageBindingProof.CanonicalMask mask)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok componentB))
    (hcopy componentC : alloc.vec.Vec LayoutQM31) :
    ∃ copied assembled,
      ComponentBC2SlotGenerated.component_b_message_values componentB =
        ok copied ∧
      ComponentBC2SlotGenerated.assemble_v5_c2_messages
          hcopy copied componentC = ok assembled ∧
      assembled = Array.make 3#usize [hcopy, copied, componentC] ∧
      ∀ row : Row,
        terminalWeights (relationPoint point) 1 row *
            aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
              (relationC2Messages hcopy copied componentC) row =
          terminalWeights (relationPoint point) 1 row *
            rowMessage (relationMaskInitial mask) (relationMaskTails mask) row := by
  let layoutPoint : Round → ExactQM31 := fun round =>
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      point.val[round.val]!
  obtain ⟨copied, assembled, copiedRun, assembledRun, assembledExact,
      layoutRows⟩ :=
    extracted_component_b_relation_claims_layoutWeightedMessageRows
      layoutPoint mask pads pivotPad componentB hmask encodeRun hcopy componentC
  refine ⟨copied, assembled, copiedRun, assembledRun, assembledExact, ?_⟩
  intro row
  apply relationExactToLayout_injective
  rw [relationExactToLayout_mul, relationExactToLayout_mul,
    relationExactToLayout_terminalWeights, relationExactToLayout_rowMessage,
    relationMaskInitial_toLayout]
  have mappedPoint :
      (fun round => relationExactToLayout (relationPoint point round)) =
        layoutPoint := by
    funext round
    exact relationPoint_toLayout point round
  have mappedTails :
      (fun round degree =>
        relationExactToLayout (relationMaskTails mask round degree)) =
        ComponentBEncodedMessageBindingProof.maskTails mask := by
    funext round degree
    exact relationMaskTails_toLayout mask round degree
  rw [mappedPoint, mappedTails]
  rw [layoutRows row]

/-- Capstone for the two former relation-claims layout premises.  The
terminal covector, full 1,024-row Component-B copy, and C2 slot constructor
are all executed by their generated functions.  The sole executable premise
is the authentic encoder run; canonicality hypotheses are the exact field
representation preconditions already required by the generated arithmetic.

The conclusion includes both the pointwise weighted relation and the actual
Nat-indexed 1,024-row sum consumed by the source relation-claims loop. -/
theorem extracted_component_b_relation_claims_layout_equalities
    (point : Array LayoutQM31 10#usize)
    (mask : ComponentBEncodedMessageBindingProof.Mask)
    (pads : Array LayoutQM31 255#usize) (pivotPad : LayoutQM31)
    (componentB : Lane)
    (hpointCanonical : ComponentBLayoutBindingsProof.CanonicalArray point)
    (hmask : ComponentBEncodedMessageBindingProof.CanonicalMask mask)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok componentB))
    (hcopy componentC : alloc.vec.Vec LayoutQM31) :
    ∃ covector copied assembled,
      ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
          point = ok covector ∧
      ComponentBC2SlotGenerated.component_b_message_values componentB =
        ok copied ∧
      ComponentBC2SlotGenerated.assemble_v5_c2_messages
          hcopy copied componentC = ok assembled ∧
      assembled = Array.make 3#usize [hcopy, copied, componentC] ∧
      covector.length = 1024 ∧
      ComponentBLayoutBindingsProof.CanonicalVec covector ∧
      (∀ row : Row,
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)) row =
          terminalWeights (relationPoint point) 1 row) ∧
      (∀ row : Row,
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
              (alloc.vec.Vec.deref (toRelationVec covector)) row *
            aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
              (relationC2Messages hcopy copied componentC) row =
          aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
              (alloc.vec.Vec.deref (toRelationVec covector)) row *
            rowMessage (relationMaskInitial mask) (relationMaskTails mask) row) ∧
      dot
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)))
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
            (relationC2Messages hcopy copied componentC)) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (relationMaskInitial mask) (relationMaskTails mask)
          (relationPoint point) ∧
      (∑ row ∈ Finset.Ico 0 1024,
          aspis_prover.ComponentBRelationClaimsProof.exactSliceEntry
              (alloc.vec.Vec.deref (toRelationVec covector)) row *
            aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
              (aspis_prover.ComponentBRelationClaimsProof.generatedComponentBMessage
                (relationC2Messages hcopy copied componentC)).val[row]!) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (relationMaskInitial mask) (relationMaskTails mask)
          (relationPoint point) := by
  obtain ⟨covector, covectorRun, covectorLength, covectorCanonical,
      covectorRows⟩ :=
    extracted_component_b_relation_claims_covectorRows point hpointCanonical
  obtain ⟨copied, assembled, copiedRun, assembledRun, assembledExact,
      terminalWeightedRows⟩ :=
    extracted_component_b_relation_claims_weightedMessageRows point mask pads
      pivotPad componentB hmask encodeRun hcopy componentC
  have weightedRows : ∀ row : Row,
      aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)) row *
          aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
            (relationC2Messages hcopy copied componentC) row =
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)) row *
          rowMessage (relationMaskInitial mask) (relationMaskTails mask) row := by
    intro row
    rw [covectorRows row]
    exact terminalWeightedRows row
  have weightedDot :
      dot
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)))
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
            (relationC2Messages hcopy copied componentC)) =
        dot
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)))
          (rowMessage (relationMaskInitial mask) (relationMaskTails mask)) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro row _
    rw [weightedRows row]
  have covectorEq :
      aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
          (alloc.vec.Vec.deref (toRelationVec covector)) =
        terminalWeights (relationPoint point) 1 :=
    funext covectorRows
  have dotExact :
      dot
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref (toRelationVec covector)))
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
            (relationC2Messages hcopy copied componentC)) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (relationMaskInitial mask) (relationMaskTails mask)
          (relationPoint point) := by
    rw [weightedDot, covectorEq,
      dot_terminalWeights_rowMessage_eq_tenRoundTerminal, one_mul]
  have sourceSumExact :
      (∑ row ∈ Finset.Ico 0 1024,
          aspis_prover.ComponentBRelationClaimsProof.exactSliceEntry
              (alloc.vec.Vec.deref (toRelationVec covector)) row *
            aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
              (aspis_prover.ComponentBRelationClaimsProof.generatedComponentBMessage
                (relationC2Messages hcopy copied componentC)).val[row]!) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (relationMaskInitial mask) (relationMaskTails mask)
          (relationPoint point) := by
    rw [aspis_prover.ComponentBRelationClaimsTerminalBridge.extracted_terminal_sum_eq_maintained_dot]
    exact dotExact
  exact ⟨covector, copied, assembled, covectorRun, copiedRun, assembledRun,
    assembledExact, covectorLength, covectorCanonical, covectorRows,
    weightedRows, dotExact, sourceSumExact⟩

#print axioms extracted_component_b_relation_claims_covectorRows
#print axioms extracted_component_b_relation_claims_weightedMessageRows
#print axioms extracted_component_b_relation_claims_layout_equalities

end ComponentBRelationClaimsLayoutInstantiation
