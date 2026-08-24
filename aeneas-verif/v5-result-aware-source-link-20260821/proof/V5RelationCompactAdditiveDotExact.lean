import V5RelationTerminalDotCanonical
import V5RelationGeneratedFieldProjection
import V5RelationLinkedFoldArithmetic

/-!
# Exact semantics of the production compact additive dot

The accepted relation verifier obtains four terminal weights from the compact
additive state and computes an ordinary four-term dot product.  This file
connects that exact translated Rust call to the maintained QM31 field.  It
also retains canonicality of the returned representation for the following
terminal equality check.
-/

namespace AspisV5RelationCompactAdditiveDotExact

open Aeneas Aeneas.Std Result
open AspisV5RelationGeneratedFieldProjection
open AspisV5RelationLinkedFoldArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev FinalQM31 := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev FinalBlock :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev FinalState :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights
abbrev CallerState :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- Public spelling of the structural conversion used inside the generated
caller before invoking the separately extracted final-weight helper. -/
def finalToRaw (value : FinalQM31) : RawQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def rawToFinal (value : RawQM31) : FinalQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerBlockToFinal
    (block : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalBlock) :
    FinalBlock :=
  { scale := rawToFinal block.scale
    power_lo := rawToFinal block.power_lo
    power_hi := rawToFinal block.power_hi
    selector := block.selector }

/-- Public spelling of the state conversion used by the generated caller.
All four field records have the same limb order, so this is structural. -/
def callerStateToFinal (state : CallerState) : FinalState :=
  { blocks := ⟨state.blocks.val.map callerBlockToFinal,
      by simpa using state.blocks.property⟩
    delta_scale := rawToFinal state.delta_scale
    folds := state.folds }

def finalWeightAt
    (weights : Array FinalQM31 4#usize) (index : Fin 4) : RawQM31 :=
  finalToRaw weights.val[index.val]!

def finalValueAt
    (values : Array RawQM31 4#usize) (index : Fin 4) : RawQM31 :=
  values.val[index.val]!

def CanonicalFinalWeights (weights : Array FinalQM31 4#usize) : Prop :=
  ∀ index : Fin 4, CanonicalQM31 (finalWeightAt weights index)

def CanonicalFinalValues (values : Array RawQM31 4#usize) : Prop :=
  ∀ index : Fin 4, CanonicalQM31 (finalValueAt values index)

/-- The maintained-field value of the four-term terminal dot, with the same
left-associated addition order as the production Rust. -/
def exactFourTermDot
    (weights : Array FinalQM31 4#usize)
    (values : Array RawQM31 4#usize) : ExactQM31 :=
  ((toMaintainedExact (finalWeightAt weights 0) *
        toMaintainedExact (finalValueAt values 0) +
      toMaintainedExact (finalWeightAt weights 1) *
        toMaintainedExact (finalValueAt values 1)) +
    toMaintainedExact (finalWeightAt weights 2) *
      toMaintainedExact (finalValueAt values 2)) +
  toMaintainedExact (finalWeightAt weights 3) *
    toMaintainedExact (finalValueAt values 3)

/-- The four reads, four products, and four additions made after the compact
state has produced its terminal weights. -/
def fourTermDotProgram
    (weights : Array FinalQM31 4#usize)
    (values : Array RawQM31 4#usize) : Result RawQM31 := do
  let w0 ← Array.index_usize weights 0#usize
  let w1 ← Array.index_usize weights 1#usize
  let w2 ← Array.index_usize weights 2#usize
  let w3 ← Array.index_usize weights 3#usize
  let v0 ← Array.index_usize values 0#usize
  let v1 ← Array.index_usize values 1#usize
  let v2 ← Array.index_usize values 2#usize
  let v3 ← Array.index_usize values 3#usize
  let p0 ← V5RelationFullGenerated.aspis_core.field.QM31.mul
    (finalToRaw w0) v0
  let s0 ← V5RelationFullGenerated.aspis_core.field.QM31.add
    V5RelationFullGenerated.aspis_core.field.QM31.ZERO p0
  let p1 ← V5RelationFullGenerated.aspis_core.field.QM31.mul
    (finalToRaw w1) v1
  let s1 ← V5RelationFullGenerated.aspis_core.field.QM31.add s0 p1
  let p2 ← V5RelationFullGenerated.aspis_core.field.QM31.mul
    (finalToRaw w2) v2
  let s2 ← V5RelationFullGenerated.aspis_core.field.QM31.add s1 p2
  let p3 ← V5RelationFullGenerated.aspis_core.field.QM31.mul
    (finalToRaw w3) v3
  V5RelationFullGenerated.aspis_core.field.QM31.add s2 p3

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (hindex : index.val < count.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have getExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp
  simpa [valueExact, getExact] using run

private theorem zero_exact :
    toMaintainedExact V5RelationFullGenerated.aspis_core.field.QM31.ZERO = 0 := by
  norm_num [toMaintainedExact,
    V5RelationFullGenerated.aspis_core.field.QM31.ZERO]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp
  · apply QuadraticAlgebra.ext <;> simp

@[simp] private theorem generated_oldQm31ToMaintained_toExact
    (value : RawQM31) :
    oldQm31ToMaintained
        (AspisV5RelationGeneratedFieldProjection.toExact value) =
      toMaintainedExact value := by
  rfl

/-- Exact field semantics of the fixed four-term program once its weights and
values have canonical raw representatives. -/
theorem fourTermDotProgram_success_exact
    (weights : Array FinalQM31 4#usize)
    (values : Array RawQM31 4#usize) (out : RawQM31)
    (hweights : CanonicalFinalWeights weights)
    (hvalues : CanonicalFinalValues values)
    (run : fourTermDotProgram weights values = .ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out = exactFourTermDot weights values := by
  unfold fourTermDotProgram at run
  rw [array_index_run weights 0#usize (by decide),
    array_index_run weights 1#usize (by decide),
    array_index_run weights 2#usize (by decide),
    array_index_run weights 3#usize (by decide),
    array_index_run values 0#usize (by decide),
    array_index_run values 1#usize (by decide),
    array_index_run values 2#usize (by decide),
    array_index_run values 3#usize (by decide)] at run
  simp only [bind_tc_ok] at run
  generalize hp0 :
      V5RelationFullGenerated.aspis_core.field.QM31.mul
        (finalToRaw weights.val[(0#usize).val]!)
        values.val[(0#usize).val]! = p0Result at run
  cases p0Result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok p0 =>
    simp only [bind_tc_ok] at run
    have p0Exact := generated_qm31_mul_run_corresponds _ _ p0
      (hweights 0) (hvalues 0) hp0
    generalize hs0 :
        V5RelationFullGenerated.aspis_core.field.QM31.add
          V5RelationFullGenerated.aspis_core.field.QM31.ZERO p0 = s0Result at run
    cases s0Result with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok s0 =>
      simp only [bind_tc_ok] at run
      have s0Exact := generated_qm31_add_run_corresponds _ _ s0
        AspisV5RelationUnconditionalCanonical.generated_qm31_zero_canonical
        p0Exact.1 hs0
      generalize hp1 :
          V5RelationFullGenerated.aspis_core.field.QM31.mul
            (finalToRaw weights.val[(1#usize).val]!)
            values.val[(1#usize).val]! = p1Result at run
      cases p1Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok p1 =>
        simp only [bind_tc_ok] at run
        have p1Exact := generated_qm31_mul_run_corresponds _ _ p1
          (hweights 1) (hvalues 1) hp1
        generalize hs1 :
            V5RelationFullGenerated.aspis_core.field.QM31.add s0 p1 =
              s1Result at run
        cases s1Result with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok s1 =>
          simp only [bind_tc_ok] at run
          have s1Exact := generated_qm31_add_run_corresponds _ _ s1
            s0Exact.1 p1Exact.1 hs1
          generalize hp2 :
              V5RelationFullGenerated.aspis_core.field.QM31.mul
                (finalToRaw weights.val[(2#usize).val]!)
                values.val[(2#usize).val]! = p2Result at run
          cases p2Result with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok p2 =>
            simp only [bind_tc_ok] at run
            have p2Exact := generated_qm31_mul_run_corresponds _ _ p2
              (hweights 2) (hvalues 2) hp2
            generalize hs2 :
                V5RelationFullGenerated.aspis_core.field.QM31.add s1 p2 =
                  s2Result at run
            cases s2Result with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok s2 =>
              simp only [bind_tc_ok] at run
              have s2Exact := generated_qm31_add_run_corresponds _ _ s2
                s1Exact.1 p2Exact.1 hs2
              generalize hp3 :
                  V5RelationFullGenerated.aspis_core.field.QM31.mul
                    (finalToRaw weights.val[(3#usize).val]!)
                    values.val[(3#usize).val]! = p3Result at run
              cases p3Result with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok p3 =>
                simp only [bind_tc_ok] at run
                have p3Exact := generated_qm31_mul_run_corresponds _ _ p3
                  (hweights 3) (hvalues 3) hp3
                have s3Exact := generated_qm31_add_run_corresponds _ _ out
                  s2Exact.1 p3Exact.1 run
                refine ⟨s3Exact.1, ?_⟩
                have p0Maintained := congrArg oldQm31ToMaintained p0Exact.2
                have s0Maintained := congrArg oldQm31ToMaintained s0Exact.2
                have p1Maintained := congrArg oldQm31ToMaintained p1Exact.2
                have s1Maintained := congrArg oldQm31ToMaintained s1Exact.2
                have p2Maintained := congrArg oldQm31ToMaintained p2Exact.2
                have s2Maintained := congrArg oldQm31ToMaintained s2Exact.2
                have p3Maintained := congrArg oldQm31ToMaintained p3Exact.2
                have s3Maintained := congrArg oldQm31ToMaintained s3Exact.2
                simp only [generated_oldQm31ToMaintained_toExact,
                  oldQm31ToMaintained_add, oldQm31ToMaintained_mul] at p0Maintained s0Maintained p1Maintained s1Maintained p2Maintained s2Maintained p3Maintained s3Maintained
                rw [s3Maintained, s2Maintained, s1Maintained, s0Maintained,
                  p0Maintained, p1Maintained, p2Maintained, p3Maintained,
                  zero_exact]
                simp [exactFourTermDot]

/-- A successful call to the exact translated production method is the
maintained four-term dot of the very terminal-weight array returned in that
same call. -/
theorem production_compact_additive_dot_success_exact
    (state : CallerState) (values : Array RawQM31 4#usize)
    (weights : Array FinalQM31 4#usize) (out : RawQM31)
    (weightsRun :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        (callerStateToFinal state) = .ok weights)
    (hweights : CanonicalFinalWeights weights)
    (hvalues : CanonicalFinalValues values)
    (run :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
        state values = .ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out = exactFourTermDot weights values := by
  apply fourTermDotProgram_success_exact weights values out hweights hvalues
  unfold
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
    at run
  change
    (do
      let terminalWeights ←
        V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
          (callerStateToFinal state)
      fourTermDotProgram terminalWeights values) = .ok out at run
  simpa [weightsRun] using run

#print axioms fourTermDotProgram_success_exact
#print axioms production_compact_additive_dot_success_exact

end AspisV5RelationCompactAdditiveDotExact
