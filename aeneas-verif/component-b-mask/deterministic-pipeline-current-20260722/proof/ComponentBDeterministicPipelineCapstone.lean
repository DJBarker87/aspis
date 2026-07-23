import ComponentBSamplerUnifiedCapstone
import ComponentBRelationClaimsLayoutInstantiation

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBDeterministicPipelineCapstone

open AspisV5CompactTerminal

noncomputable local instance :
    Field ComponentBRealEvaluatorProof.ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

local instance : Inhabited ComponentBGenerated.aspis_core.field.QM31 :=
  ⟨ComponentBGenerated.aspis_core.field.QM31.ZERO⟩

local instance : Inhabited aspis_prover.aspis_core.field.QM31 :=
  ⟨aspis_prover.aspis_core.field.QM31.ZERO⟩

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (hindex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hindex]

/-- The `Fin`-indexed canonical point predicate used by the extracted
evaluator supplies the `Nat`-indexed predicate used by the extracted terminal
covector builder. -/
theorem point_canonical_for_layout
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (canonical : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        point.val[round.val]) :
    ComponentBLayoutBindingsProof.CanonicalArray point := by
  intro round hround
  have h := canonical ⟨round, hround⟩
  rw [← list_get_eq_getElemBang point.val round (by
    simpa [point.property] using hround)]
  exact h

/-- Successful execution of the real sampler supplies the canonical mask
predicate required by the source-authentic Component-B lane encoder. -/
theorem sampled_mask_canonical_for_encoder
    {S : Type} (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource)) :
    ComponentBEncodedMessageBindingProof.CanonicalMask mask := by
  obtain ⟨initialCanonical, rounds⟩ :=
    ComponentBSamplerMaintainedPredicatesBridge.sample_success_supplies_maintained_predicates
      sourceInst nextWordTotal source finalSource mask sampleRun
  refine ⟨initialCanonical, ?_⟩
  intro round hround coefficient hcoefficient
  have h := (rounds ⟨round, hround⟩).1
    ⟨coefficient, hcoefficient⟩
  have hroundLength : round < mask.zero_boundary_rounds.val.length := by
    rw [mask.zero_boundary_rounds.property]
    exact hround
  have hroundIndex :
      mask.zero_boundary_rounds.val[round]'hroundLength =
        mask.zero_boundary_rounds.val[round]! :=
    list_get_eq_getElemBang _ _ hroundLength
  have hcoefficientLength : coefficient <
      (mask.zero_boundary_rounds.val[round]'hroundLength).val.length := by
    rw [(mask.zero_boundary_rounds.val[round]'hroundLength).property]
    exact hcoefficient
  have hcoefficientIndex :
      (mask.zero_boundary_rounds.val[round]'hroundLength).val[coefficient]'hcoefficientLength =
        (mask.zero_boundary_rounds.val[round]'hroundLength).val[coefficient]! :=
    list_get_eq_getElemBang _ _ hcoefficientLength
  change ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
    (mask.zero_boundary_rounds.val[round]!.val[coefficient]!)
  rw [← hroundIndex, ← hcoefficientIndex]
  simpa [ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask,
    ComponentBMaintainedTerminalBridge.storedRound,
    ComponentBRealEvaluatorProof.CanonicalArray,
    ComponentBRealEvaluatorProof.coefficientAt] using h

/-- Both authentic bundles select coefficient `degree + 1` from the same
stored source round.  The apparent difference is only bounded versus
bang-index spelling. -/
theorem exactTail_eq_layoutMaskTails
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (round : Fin 10) (degree : Fin 27) :
    ComponentBMaintainedTerminalBridge.exactTail
        (ComponentBMaintainedTerminalBridge.storedRound mask round) degree =
      ComponentBEncodedMessageBindingProof.maskTails mask round degree := by
  have hroundLength :
      round.val < mask.zero_boundary_rounds.val.length := by
    rw [mask.zero_boundary_rounds.property]
    exact round.isLt
  have hroundIndex :
      mask.zero_boundary_rounds.val[round.val]'hroundLength =
        mask.zero_boundary_rounds.val[round.val]! :=
    list_get_eq_getElemBang _ _ hroundLength
  have hdegreeLength : degree.val + 1 <
      (mask.zero_boundary_rounds.val[round.val]'hroundLength).val.length := by
    rw [(mask.zero_boundary_rounds.val[round.val]'hroundLength).property]
    simpa using Nat.succ_lt_succ degree.isLt
  have hdegreeIndex :
      (mask.zero_boundary_rounds.val[round.val]'hroundLength).val[degree.val + 1]'hdegreeLength =
        (mask.zero_boundary_rounds.val[round.val]'hroundLength).val[degree.val + 1]! :=
    list_get_eq_getElemBang _ _ hdegreeLength
  unfold ComponentBMaintainedTerminalBridge.exactTail
    ComponentBMaintainedTerminalBridge.storedRound
    ComponentBRealEvaluatorProof.coefficientAt
    ComponentBEncodedMessageBindingProof.maskTails
  rw [← hroundIndex, ← hdegreeIndex]

/-- Exact coordinate transport commutes with one maintained tail evaluation. -/
theorem relationExactToLayout_tailEvaluation
    (tail : Fin 27 →
      ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31)
    (x : ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31) :
    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (AspisV5SumcheckCommitment.tailEvaluation tail x) =
      AspisV5SumcheckCommitment.tailEvaluation
        (fun degree =>
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (tail degree))
        (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x) := by
  unfold AspisV5SumcheckCommitment.tailEvaluation
  rw [ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_fintypeSum]
  apply Finset.sum_congr rfl
  intro degree _
  have hsub :
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (x ^ (degree.val + 1) - AspisV5SumcheckCommitment.half) =
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
            (degree.val + 1) - AspisV5SumcheckCommitment.half := by
    calc
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (x ^ (degree.val + 1) - AspisV5SumcheckCommitment.half) =
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (x ^ (degree.val + 1) + -AspisV5SumcheckCommitment.half) :=
            congrArg _ (sub_eq_add_neg _ _)
      _ = ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (x ^ (degree.val + 1)) +
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (-AspisV5SumcheckCommitment.half) :=
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_add _ _
      _ = ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
            (degree.val + 1) +
          -(ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            AspisV5SumcheckCommitment.half) :=
              congrArg₂ (· + ·)
                (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_pow
                  x (degree.val + 1))
                (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_neg
                  AspisV5SumcheckCommitment.half)
      _ = ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
            (degree.val + 1) + -AspisV5SumcheckCommitment.half :=
              congrArg
                (fun value =>
                  ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
                      (degree.val + 1) + -value)
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_half
      _ = ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
            (degree.val + 1) - AspisV5SumcheckCommitment.half :=
              (sub_eq_add_neg _ _).symm
  calc
    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (tail degree *
          (x ^ (degree.val + 1) - AspisV5SumcheckCommitment.half)) =
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout (tail degree) *
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (x ^ (degree.val + 1) - AspisV5SumcheckCommitment.half) :=
            ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_mul _ _
    _ = ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout (tail degree) *
        (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout x ^
          (degree.val + 1) - AspisV5SumcheckCommitment.half) :=
            congrArg _ hsub

/-- Exact coordinate transport commutes with every affine recurrence step. -/
theorem relationExactToLayout_chainContributions
    (initial : ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31)
    (contributions : List
      ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31) :
    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (AspisV5SumcheckCommitment.chainContributions initial contributions) =
      AspisV5SumcheckCommitment.chainContributions
        (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial)
        (contributions.map
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout) := by
  unfold AspisV5SumcheckCommitment.chainContributions
  induction contributions generalizing initial with
  | nil => rfl
  | cons contribution remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      have hstep :
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
              (AspisV5SumcheckCommitment.half * initial + contribution) =
            AspisV5SumcheckCommitment.half *
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial +
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution := by
        calc
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
              (AspisV5SumcheckCommitment.half * initial + contribution) =
            ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
                (AspisV5SumcheckCommitment.half * initial) +
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution :=
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_add _ _
          _ = (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
                  AspisV5SumcheckCommitment.half) *
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial +
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution :=
                congrArg
                  (fun value => value +
                    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution)
                  (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_mul _ _)
          _ = AspisV5SumcheckCommitment.half *
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial +
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution :=
                congrArg
                  (fun value => value *
                      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial +
                    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution)
                  ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout_half
      calc
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (List.foldl
              (fun state contribution =>
                AspisV5SumcheckCommitment.half * state + contribution)
              (AspisV5SumcheckCommitment.half * initial + contribution)
              remaining) =
          List.foldl
            (fun state contribution =>
              AspisV5SumcheckCommitment.half * state + contribution)
            (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
              (AspisV5SumcheckCommitment.half * initial + contribution))
            (remaining.map
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout) :=
                inductionHypothesis _
        _ = List.foldl
            (fun state contribution =>
              AspisV5SumcheckCommitment.half * state + contribution)
            (AspisV5SumcheckCommitment.half *
                ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial +
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout contribution)
            (remaining.map
              ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout) := by
              exact congrArg (fun start => List.foldl
                (fun state contribution =>
                  AspisV5SumcheckCommitment.half * state + contribution)
                start
                (remaining.map
                  ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout)) hstep

/-- Exact coordinate transport commutes with the maintained ten-round
recurrence.  This proof follows the actual fold structure instead of
expanding the terminal into a large closed sum. -/
theorem relationExactToLayout_tenRoundTerminal
    (initial : ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31)
    (tails : Fin 10 → Fin 27 →
      ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31)
    (point : Fin 10 →
      ComponentBRelationClaimsLayoutInstantiation.RelationExactQM31) :
    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (AspisV5SumcheckCommitment.tenRoundTerminal initial tails point) =
      AspisV5SumcheckCommitment.tenRoundTerminal
        (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial)
        (fun round degree =>
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (tails round degree))
        (fun round =>
          ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
            (point round)) := by
  unfold AspisV5SumcheckCommitment.tenRoundTerminal
  rw [relationExactToLayout_chainContributions]
  apply congrArg
    (AspisV5SumcheckCommitment.chainContributions
      (ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout initial))
  unfold AspisV5SumcheckCommitment.tenContributions
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext (fun round =>
    relationExactToLayout_tailEvaluation (tails round) (point round)))

/-- The maintained relation-field ten-round recurrence is exactly the
terminal returned by the source-extracted evaluator, after the explicit
coordinate transport between the two authenticated exact towers. -/
theorem relation_tenRoundTerminal_to_generated_terminalCovector
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask) :
    ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
        (AspisV5SumcheckCommitment.tenRoundTerminal
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationPoint point)) =
      AspisV5SumcheckCommitment.terminalCovector
        (fun round : Fin 10 =>
          ComponentBRealEvaluatorProof.generatedQm31ToExact
            point.val[round.val])
        (ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim)
        (fun round => ComponentBMaintainedTerminalBridge.exactTail
          (ComponentBMaintainedTerminalBridge.storedRound mask round)) := by
  rw [relationExactToLayout_tenRoundTerminal]
  rw [AspisV5SumcheckCommitment.tenRoundTerminal_eq_terminalCovector]
  congr 1
  · funext round
    rw [ComponentBRelationClaimsLayoutInstantiation.relationPoint_toLayout]
    exact congrArg ComponentBRealEvaluatorProof.generatedQm31ToExact
      (list_get_eq_getElemBang point.val round.val (by
        have hround : round.val < 10 := by
          have h := round.isLt
          change round.val < 10 at h
          exact h
        rw [point.property]
        exact hround)).symm
  · funext round degree
    rw [ComponentBRelationClaimsLayoutInstantiation.relationMaskTails_toLayout]
    exact (exactTail_eq_layoutMaskTails mask round degree).symm

/-- Source-authentic deterministic Component-B pipeline.

A successful execution of the actual generic sampler produces the same mask
consumed by the actual mixing/evaluation helper and by the actual structured
lane encoder.  The generated terminal-covector builder, the actual 1,024-row
Component-B copy, and the generated C2 constructor are then composed with the
maintained weighted relation and ten-round recurrence.  The final two fields
identify the exact generated evaluator result with both maintained relation
sums through the explicit exact-tower coordinate transport.

The pointwise message equality is intentionally weight-multiplied: pad and
pivot rows are not claimed equal away from terminal support. -/
theorem sampled_mask_to_c2_relation_and_tenRoundTerminal
    {S : Type} (sourceInst : ComponentBGenerated.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S)
    (mask : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask)
    (sampleRun :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.sample
          sourceInst source = .ok (.Ok mask, finalSource))
    (selectedRound : Fin 10)
    (totalClaim eta : ComponentBGenerated.aspis_core.field.QM31)
    (real : Array ComponentBGenerated.aspis_core.field.QM31 28#usize)
    (point : Array ComponentBGenerated.aspis_core.field.QM31 10#usize)
    (hpoint : ∀ round : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        point.val[round.val])
    (htotal : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 totalClaim)
    (heta : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 eta)
    (hreal : ComponentBRealEvaluatorProof.CanonicalArray real)
    (pads : Array ComponentBGenerated.aspis_core.field.QM31 255#usize)
    (pivotPad : ComponentBGenerated.aspis_core.field.QM31)
    (componentB : ComponentBRelationClaimsLayoutInstantiation.Lane)
    (encodeRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = .ok (.Ok componentB))
    (hcopy componentC :
      alloc.vec.Vec ComponentBGenerated.aspis_core.field.QM31) :
    ∃ mixed terminal covector copied assembled,
      ComponentBGenerated.v5_sumcheck_mask.v5_sumcheck_mask_mixing_evaluate_correspondence
          mask (ComponentBMaintainedTerminalBridge.roundUsize selectedRound)
          totalClaim eta real point = .ok (.some mixed, terminal) ∧
      ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
          mixed = .ok totalClaim ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 terminal ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact terminal =
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (AspisV5SumcheckCommitment.tenRoundTerminal
            (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
            (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
            (ComponentBRelationClaimsLayoutInstantiation.relationPoint point)) ∧
      ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
          point = .ok covector ∧
      ComponentBC2SlotGenerated.component_b_message_values componentB =
        .ok copied ∧
      ComponentBC2SlotGenerated.assemble_v5_c2_messages
          hcopy copied componentC = .ok assembled ∧
      assembled = Array.make 3#usize [hcopy, copied, componentC] ∧
      covector.length = 1024 ∧
      ComponentBLayoutBindingsProof.CanonicalVec covector ∧
      (∀ row : Row,
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref
              (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)) row =
          terminalWeights
            (ComponentBRelationClaimsLayoutInstantiation.relationPoint point) 1 row) ∧
      (∀ row : Row,
        aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
              (alloc.vec.Vec.deref
                (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)) row *
            aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
              (ComponentBRelationClaimsLayoutInstantiation.relationC2Messages
                hcopy copied componentC) row =
          aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
              (alloc.vec.Vec.deref
                (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)) row *
            rowMessage
              (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
              (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask) row) ∧
      dot
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
            (alloc.vec.Vec.deref
              (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)))
          (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
            (ComponentBRelationClaimsLayoutInstantiation.relationC2Messages
              hcopy copied componentC)) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationPoint point) ∧
      (∑ row ∈ Finset.Ico 0 1024,
          aspis_prover.ComponentBRelationClaimsProof.exactSliceEntry
              (alloc.vec.Vec.deref
                (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)) row *
            aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
              (aspis_prover.ComponentBRelationClaimsProof.generatedComponentBMessage
                (ComponentBRelationClaimsLayoutInstantiation.relationC2Messages
                  hcopy copied componentC)).val[row]!) =
        AspisV5SumcheckCommitment.tenRoundTerminal
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
          (ComponentBRelationClaimsLayoutInstantiation.relationPoint point) ∧
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (dot
            (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactTerminalCovectorRows
              (alloc.vec.Vec.deref
                (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)))
            (aspis_prover.ComponentBRelationClaimsTerminalBridge.exactCommittedBMessageRows
              (ComponentBRelationClaimsLayoutInstantiation.relationC2Messages
                hcopy copied componentC))) =
        ComponentBRealEvaluatorProof.generatedQm31ToExact terminal ∧
      ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (∑ row ∈ Finset.Ico 0 1024,
            aspis_prover.ComponentBRelationClaimsProof.exactSliceEntry
                (alloc.vec.Vec.deref
                  (ComponentBRelationClaimsLayoutInstantiation.toRelationVec covector)) row *
              aspis_prover.MultilinearEvalProofs.generatedQm31ToExact
                (aspis_prover.ComponentBRelationClaimsProof.generatedComponentBMessage
                  (ComponentBRelationClaimsLayoutInstantiation.relationC2Messages
                    hcopy copied componentC)).val[row]!) =
        ComponentBRealEvaluatorProof.generatedQm31ToExact terminal := by
  have hpointLayout := point_canonical_for_layout point hpoint
  have hmask := sampled_mask_canonical_for_encoder sourceInst nextWordTotal
    source finalSource mask sampleRun
  obtain ⟨mixed, terminal, helperRun, boundary, terminalCanonical,
      terminalCovector⟩ :=
    ComponentBSamplerUnifiedCapstone.sampled_helper_mixing_and_terminal_covector
      sourceInst nextWordTotal source finalSource mask sampleRun selectedRound
      totalClaim eta real point hpoint htotal heta hreal
  obtain ⟨covector, copied, assembled, covectorRun, copiedRun, assembledRun,
      assembledExact, covectorLength, covectorCanonical, covectorRows,
      weightedRows, dotExact, sourceSumExact⟩ :=
    ComponentBRelationClaimsLayoutInstantiation.extracted_component_b_relation_claims_layout_equalities
      point mask pads pivotPad componentB hpointLayout hmask encodeRun hcopy componentC
  have terminalBridge :=
    relation_tenRoundTerminal_to_generated_terminalCovector point mask
  have terminalRelation :
      ComponentBRealEvaluatorProof.generatedQm31ToExact terminal =
        ComponentBRelationClaimsLayoutInstantiation.relationExactToLayout
          (AspisV5SumcheckCommitment.tenRoundTerminal
            (ComponentBRelationClaimsLayoutInstantiation.relationMaskInitial mask)
            (ComponentBRelationClaimsLayoutInstantiation.relationMaskTails mask)
            (ComponentBRelationClaimsLayoutInstantiation.relationPoint point)) :=
    terminalCovector.trans terminalBridge.symm
  refine ⟨mixed, terminal, covector, copied, assembled, helperRun, boundary,
    terminalCanonical, terminalRelation, covectorRun, copiedRun, assembledRun,
    assembledExact, covectorLength, covectorCanonical, covectorRows,
    weightedRows, dotExact, sourceSumExact, ?_, ?_⟩
  · rw [dotExact]
    exact terminalRelation.symm
  · rw [sourceSumExact]
    exact terminalRelation.symm

#print axioms point_canonical_for_layout
#print axioms sampled_mask_canonical_for_encoder
#print axioms exactTail_eq_layoutMaskTails
#print axioms relationExactToLayout_tailEvaluation
#print axioms relationExactToLayout_chainContributions
#print axioms relationExactToLayout_tenRoundTerminal
#print axioms relation_tenRoundTerminal_to_generated_terminalCovector
#print axioms sampled_mask_to_c2_relation_and_tenRoundTerminal

end ComponentBDeterministicPipelineCapstone
