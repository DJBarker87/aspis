import V5NonzeroKappa.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5NonzeroKappaGenerated

namespace V5NonzeroKappaGeneratedProof

private def successIsNonzero
    (result : core.result.Result field.QM31
      transcript.ChallengeSampleExhausted × transcript.Transcript) : Prop :=
  match result.1 with
  | .Ok value => value ≠ field.QM31.ZERO
  | .Err _ => True

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

/-- The exact Aeneas translation of the production three-attempt wrapper can
only return a successful value after its comparison against `QM31::ZERO` has
succeeded.  No property of the opaque lower-level sampler is used. -/
theorem generated_success_is_nonzero
    (source finalSource : transcript.Transcript) (value : field.QM31)
    (run : transcript.Transcript.challenge_nonzero_qm31 source =
      .ok (.Ok value, finalSource)) :
    value ≠ field.QM31.ZERO := by
  have hSpec :
      transcript.Transcript.challenge_nonzero_qm31 source
        ⦃ result => successIsNonzero result ⦄ := by
    simp only [transcript.Transcript.challenge_nonzero_qm31,
      transcript.Transcript.challenge_nonzero_qm31_loop]
    apply loop.spec_decr_nat
      (fun state => state.1.«end».val - state.1.start.val)
      (fun state => state.1.start.val ≤ state.1.«end».val)
      successIsNonzero
    · rintro ⟨iter, currentSource⟩ hRange
      change iter.start.val ≤ iter.end.val at hRange
      by_cases hactive : iter.start.val < iter.end.val
      · have hendMaxGeneric :
            iter.end.val ≤ UScalar.max .U32 := by
          rw [← UScalar.rMax_eq_max]
          exact iter.end.hrBounds
        have hendMax : iter.end.val ≤ Std.U32.max := by
          simpa using hendMaxGeneric
        have hMaxDefs : UScalar.max .U32 = Std.U32.max :=
          UScalar.max_UScalarTy_U32_eq
        have hmaxGeneric : iter.start.val < UScalar.max .U32 :=
          lt_of_lt_of_le hactive hendMaxGeneric
        have hmax : iter.start.val < Std.U32.max :=
          lt_of_lt_of_le hactive hendMax
        cases hsample : transcript.Transcript.challenge_qm31 currentSource with
        | ok sampled =>
            rcases sampled with ⟨sampleResult, nextSource⟩
            cases sampleResult with
            | Err sampleError =>
                simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
                  core.iter.range.IteratorRange.next,
                  core.iter.range.StepU32, core.iter.range.UScalarStep,
                  core.iter.range.UScalarStep.forward_checked,
                  core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
                  core.clone.CloneU32, core.clone.impls.CloneU32.clone,
                  UScalar.ofNatCore_val_eq, successIsNonzero,
                  hactive, hmax, hMaxDefs, hsample]
            | Ok sampledValue =>
                rcases sampledValue with ⟨⟨a, b⟩, ⟨c, d⟩⟩
                by_cases ha : a = 0#u32 <;>
                by_cases hb : b = 0#u32 <;>
                by_cases hc : c = 0#u32 <;>
                by_cases hd : d = 0#u32 <;>
                simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
                  core.iter.range.IteratorRange.next,
                  core.iter.range.StepU32, core.iter.range.UScalarStep,
                  core.iter.range.UScalarStep.forward_checked,
                  core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
                  core.clone.CloneU32, core.clone.impls.CloneU32.clone,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default,
                  field.QM31.Insts.CoreCmpPartialEqQM31.eq,
                  field.CM31.Insts.CoreCmpPartialEqCM31.eq,
                  field.M31.Insts.CoreCmpPartialEqM31.eq,
                  field.QM31.ZERO, UScalar.ofNatCore_val_eq,
                  successIsNonzero, hactive, hmax, hMaxDefs, hsample,
                  ha, hb, hc, hd]
                all_goals omega
        | fail sampleError =>
            cases currentSource with
            | nil => simp [transcript.Transcript.challenge_qm31] at hsample
            | cons head tail =>
                cases head <;>
                  simp [transcript.Transcript.challenge_qm31] at hsample
        | div =>
            cases currentSource with
            | nil => simp [transcript.Transcript.challenge_qm31] at hsample
            | cons head tail =>
                cases head <;>
                  simp [transcript.Transcript.challenge_qm31] at hsample
      · simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
          core.iter.range.IteratorRange.next,
          core.iter.range.StepU32, core.iter.range.UScalarStep,
          core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
          successIsNonzero, hactive]
    · norm_num [transcript.NONZERO_QM31_RETRY_LIMIT]
  simp [run, successIsNonzero, Aeneas.Std.WP.spec,
    Aeneas.Std.WP.theta] at hSpec
  exact hSpec

def rawZero : transcript.RawChallenge :=
  .value 0#u32 0#u32 0#u32 0#u32

/-- A terminating reference function for the extracted wrapper.  Its input is
the arbitrary stream of outcomes supplied by the opaque lower-level sampler;
it records both the returned result and the exact unconsumed suffix. -/
def wrapperModel : Nat → transcript.Transcript →
    core.result.Result field.QM31 transcript.ChallengeSampleExhausted ×
      transcript.Transcript
  | 0, source => (.Err (), source)
  | _ + 1, [] => (.Err (), [])
  | _ + 1, .exhausted :: tail => (.Err (), tail)
  | attempts + 1, .value a b c d :: tail =>
      let value := field.QM31.ofRaw a b c d
      if a = 0#u32 ∧ b = 0#u32 ∧ c = 0#u32 ∧ d = 0#u32 then
        wrapperModel attempts tail
      else
        (.Ok value, tail)

/-- The exact generated wrapper agrees with `wrapperModel` for every possible
sequence of lower-level values and errors.  This proves the rejection and
state-transition behavior without assigning any distribution to that stream. -/
theorem generated_wrapper_eq_model (source : transcript.Transcript) :
    transcript.Transcript.challenge_nonzero_qm31 source =
      .ok (wrapperModel 3 source) := by
  have hSpec :
      transcript.Transcript.challenge_nonzero_qm31 source
        ⦃ result => result = wrapperModel 3 source ⦄ := by
    simp only [transcript.Transcript.challenge_nonzero_qm31,
      transcript.Transcript.challenge_nonzero_qm31_loop]
    apply loop.spec_decr_nat
      (fun state => state.1.«end».val - state.1.start.val)
      (fun state =>
        state.1.start.val ≤ state.1.«end».val ∧
          wrapperModel (state.1.«end».val - state.1.start.val) state.2 =
            wrapperModel 3 source)
      (fun result => result = wrapperModel 3 source)
    · rintro ⟨iter, currentSource⟩ ⟨hRange, hModel⟩
      change iter.start.val ≤ iter.end.val at hRange
      by_cases hactive : iter.start.val < iter.end.val
      · have hendMaxGeneric :
            iter.end.val ≤ UScalar.max .U32 := by
          rw [← UScalar.rMax_eq_max]
          exact iter.end.hrBounds
        have hendMax : iter.end.val ≤ Std.U32.max := by
          simpa using hendMaxGeneric
        have hMaxDefs : UScalar.max .U32 = Std.U32.max :=
          UScalar.max_UScalarTy_U32_eq
        have hmaxGeneric : iter.start.val < UScalar.max .U32 :=
          lt_of_lt_of_le hactive hendMaxGeneric
        have hmax : iter.start.val < Std.U32.max :=
          lt_of_lt_of_le hactive hendMax
        have hremaining : 0 < iter.end.val - iter.start.val :=
          Nat.sub_pos_iff_lt.mpr hactive
        cases hremainingEq : iter.end.val - iter.start.val with
        | zero => omega
        | succ remaining =>
          cases currentSource with
          | nil =>
              simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
                transcript.Transcript.challenge_qm31, wrapperModel,
                core.iter.range.IteratorRange.next,
                core.iter.range.StepU32, core.iter.range.UScalarStep,
                core.iter.range.UScalarStep.forward_checked,
                core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
                core.clone.CloneU32, core.clone.impls.CloneU32.clone,
                UScalar.ofNatCore_val_eq, hactive, hmax, hMaxDefs,
                hremainingEq] at hModel ⊢
              exact hModel
          | cons head tail =>
              cases head with
              | exhausted =>
                  simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
                    transcript.Transcript.challenge_qm31, wrapperModel,
                    core.iter.range.IteratorRange.next,
                    core.iter.range.StepU32, core.iter.range.UScalarStep,
                    core.iter.range.UScalarStep.forward_checked,
                    core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
                    core.clone.CloneU32, core.clone.impls.CloneU32.clone,
                    UScalar.ofNatCore_val_eq, hactive, hmax, hMaxDefs,
                    hremainingEq] at hModel ⊢
                  exact hModel
              | value a b c d =>
                  by_cases ha : a = 0#u32 <;>
                  by_cases hb : b = 0#u32 <;>
                  by_cases hc : c = 0#u32 <;>
                  by_cases hd : d = 0#u32 <;>
                  simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
                    transcript.Transcript.challenge_qm31, wrapperModel,
                    field.QM31.ofRaw, field.QM31.ZERO,
                    field.QM31.Insts.CoreCmpPartialEqQM31.eq,
                    field.CM31.Insts.CoreCmpPartialEqCM31.eq,
                    field.M31.Insts.CoreCmpPartialEqM31.eq,
                    core.cmp.PartialEq.ne.trait_default,
                    core.cmp.PartialEq.ne.default,
                    core.iter.range.IteratorRange.next,
                    core.iter.range.StepU32, core.iter.range.UScalarStep,
                    core.iter.range.UScalarStep.forward_checked,
                    core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
                    core.clone.CloneU32, core.clone.impls.CloneU32.clone,
                    UScalar.ofNatCore_val_eq, hactive, hmax, hMaxDefs,
                    hremainingEq, ha, hb, hc, hd] at hModel ⊢ <;>
                    try exact hModel
                  all_goals
                    constructor
                    · have hnextRemaining :
                          iter.end.val - (iter.start.val + 1) = remaining := by
                        omega
                      simpa [hnextRemaining] using hModel
                    · omega
      · simp [transcript.Transcript.challenge_nonzero_qm31_loop.body,
          core.iter.range.IteratorRange.next,
          core.iter.range.StepU32, core.iter.range.UScalarStep,
          core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.lt,
          hactive] at ⊢
        have heq : iter.start.val = iter.end.val :=
          Nat.le_antisymm hRange (Nat.le_of_not_gt hactive)
        simp [heq, wrapperModel] at hModel
        exact hModel
    · constructor
      · norm_num [transcript.NONZERO_QM31_RETRY_LIMIT]
      · norm_num [transcript.NONZERO_QM31_RETRY_LIMIT]
  generalize hrun : transcript.Transcript.challenge_nonzero_qm31 source = result at hSpec ⊢
  cases result with
  | ok value =>
      simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta] at hSpec
      simpa [hSpec]
  | fail error =>
      simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta] at hSpec
  | div =>
      simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta] at hSpec

/-- Three lower-level zero results consume exactly three transcript states and
return the production exhaustion error. -/
theorem generated_three_zeros_exhaust (tail : transcript.Transcript) :
    transcript.Transcript.challenge_nonzero_qm31
        (rawZero :: rawZero :: rawZero :: tail) =
      .ok (.Err (), tail) := by
  rw [generated_wrapper_eq_model]
  simp [wrapperModel, rawZero]

/-- A lower-level field-sampler exhaustion is returned immediately with the
state produced by that failed call; the wrapper does not retry it. -/
theorem generated_inner_exhaustion_is_immediate
    (tail : transcript.Transcript) :
    transcript.Transcript.challenge_nonzero_qm31
        (.exhausted :: tail) = .ok (.Err (), tail) := by
  rw [generated_wrapper_eq_model]
  rfl

/-- Rejecting a zero uses the next lower-level sampler result.  If that next
result has a nonzero first limb, it is returned and exactly two result-stream
entries have been consumed. -/
theorem generated_zero_then_nonzero
    (a b c d : Std.U32) (tail : transcript.Transcript)
    (ha : a ≠ 0#u32) :
    transcript.Transcript.challenge_nonzero_qm31
        (rawZero :: .value a b c d :: tail) =
      .ok (.Ok (field.QM31.ofRaw a b c d), tail) := by
  rw [generated_wrapper_eq_model]
  simp [wrapperModel, rawZero, field.QM31.ofRaw, ha]

#print axioms generated_success_is_nonzero
#print axioms generated_wrapper_eq_model
#print axioms generated_three_zeros_exhaust
#print axioms generated_inner_exhaustion_is_immediate
#print axioms generated_zero_then_nonzero

end V5NonzeroKappaGeneratedProof
