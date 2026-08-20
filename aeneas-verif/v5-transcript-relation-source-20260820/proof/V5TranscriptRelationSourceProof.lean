import V5TranscriptRelationHelper.Funs
import Aeneas.Tactic.Simp.SimpScalar

open Aeneas Aeneas.Std Result ControlFlow Error
open V5TranscriptRelationGenerated

set_option maxRecDepth 50000

namespace AspisV5TranscriptRelationSourceProof

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

def sampleEvents (round sample : Nat) : List RelationTranscriptEvent :=
  (if round = 0 then [.secureCirclePoint] else [.lineOodPoint]) ++
    [.absorbOod (if round = 0 then 16 else 17) round sample,
      .squeezeQm31]

def roundEvents (round nonce : Nat) : List RelationTranscriptEvent :=
  sampleEvents round 0 ++ sampleEvents round 1 ++
    [.relationSumcheck round, .foldWork round nonce, .squeezeQm31] ++
    if round < 3 then [.laterRoot round] else []

def roundTailEvents (round nonce : Nat) : List RelationTranscriptEvent :=
  [.relationSumcheck round, .foldWork round nonce, .squeezeQm31] ++
    if round < 3 then [.laterRoot round] else []

def fourRoundEvents (nonces : Fin 4 → Nat) : List RelationTranscriptEvent :=
  roundEvents 0 (nonces 0) ++ roundEvents 1 (nonces 1) ++
    roundEvents 2 (nonces 2) ++ roundEvents 3 (nonces 3)

private theorem usizeMulExact (x y z : Std.Usize)
    (hbound : x.val * y.val ≤ Std.Usize.max)
    (hval : z.val = x.val * y.val) :
    x * y = ok z := by
  have hspec := Std.Usize.mul_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeSubExact (x y z : Std.Usize)
    (hbound : y.val ≤ x.val)
    (hval : z.val = x.val - y.val) :
    x - y = ok z := by
  have hspec := Std.Usize.sub_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

syntax "usize_mul_fact " ident ", " term ", " term ", " term : command
syntax "usize_add_fact " ident ", " term ", " term ", " term : command
syntax "usize_sub_fact " ident ", " term ", " term ", " term : command

macro_rules
  | `(usize_mul_fact $name:ident, $x:term, $y:term, $z:term) =>
      `(@[local simp] private theorem $name :
          ($x * $y : Result Std.Usize) = .ok $z := by
        apply usizeMulExact <;> scalar_tac)
  | `(usize_add_fact $name:ident, $x:term, $y:term, $z:term) =>
      `(@[local simp] private theorem $name :
          ($x + $y : Result Std.Usize) = .ok $z := by
        apply usizeAddExact <;> scalar_tac)
  | `(usize_sub_fact $name:ident, $x:term, $y:term, $z:term) =>
      `(@[local simp] private theorem $name :
          ($x - $y : Result Std.Usize) = .ok $z := by
        apply usizeSubExact <;> scalar_tac)

usize_mul_fact mul_2_0, 2#usize, 0#usize, 0#usize
usize_mul_fact mul_0_16, 0#usize, 16#usize, 0#usize
usize_add_fact add_0_0, 0#usize, 0#usize, 0#usize
usize_mul_fact mul_2_1, 2#usize, 1#usize, 2#usize
usize_mul_fact mul_0_2, 0#usize, 2#usize, 0#usize
usize_mul_fact mul_1_2, 1#usize, 2#usize, 2#usize
usize_mul_fact mul_2_2, 2#usize, 2#usize, 4#usize
usize_mul_fact mul_3_2, 3#usize, 2#usize, 6#usize
usize_mul_fact mul_4_2, 4#usize, 2#usize, 8#usize
usize_mul_fact mul_6_2, 6#usize, 2#usize, 12#usize
usize_mul_fact mul_0_7, 0#usize, 7#usize, 0#usize
usize_mul_fact mul_1_7, 1#usize, 7#usize, 7#usize
usize_mul_fact mul_2_7, 2#usize, 7#usize, 14#usize
usize_mul_fact mul_3_7, 3#usize, 7#usize, 21#usize
usize_mul_fact mul_4_7, 4#usize, 7#usize, 28#usize
usize_mul_fact mul_1_16, 1#usize, 16#usize, 16#usize
usize_mul_fact mul_2_16, 2#usize, 16#usize, 32#usize
usize_mul_fact mul_3_16, 3#usize, 16#usize, 48#usize
usize_mul_fact mul_4_16_global, 4#usize, 16#usize, 64#usize
usize_mul_fact mul_5_16, 5#usize, 16#usize, 80#usize
usize_mul_fact mul_6_16_global, 6#usize, 16#usize, 96#usize
usize_mul_fact mul_7_16, 7#usize, 16#usize, 112#usize
usize_mul_fact mul_8_16_global, 8#usize, 16#usize, 128#usize
usize_mul_fact mul_14_16, 14#usize, 16#usize, 224#usize
usize_mul_fact mul_21_16, 21#usize, 16#usize, 336#usize
usize_mul_fact mul_28_16, 28#usize, 16#usize, 448#usize

usize_sub_fact sub_1_1, 1#usize, 1#usize, 0#usize
usize_sub_fact sub_2_1, 2#usize, 1#usize, 1#usize
usize_sub_fact sub_3_1, 3#usize, 1#usize, 2#usize
usize_sub_fact sub_4_1_global, 4#usize, 1#usize, 3#usize

usize_add_fact add_0_1_global, 0#usize, 1#usize, 1#usize
usize_add_fact add_1_1, 1#usize, 1#usize, 2#usize
usize_add_fact add_2_1, 2#usize, 1#usize, 3#usize
usize_add_fact add_3_1, 3#usize, 1#usize, 4#usize
usize_add_fact add_2_0, 2#usize, 0#usize, 2#usize
usize_add_fact add_4_0, 4#usize, 0#usize, 4#usize
usize_add_fact add_4_1, 4#usize, 1#usize, 5#usize
usize_add_fact add_6_0, 6#usize, 0#usize, 6#usize
usize_add_fact add_6_1, 6#usize, 1#usize, 7#usize
usize_add_fact add_0_16_global, 0#usize, 16#usize, 16#usize
usize_add_fact add_0_32, 0#usize, 32#usize, 32#usize
usize_add_fact add_32_16, 32#usize, 16#usize, 48#usize
usize_add_fact add_0_64_global, 0#usize, 64#usize, 64#usize
usize_add_fact add_64_0, 64#usize, 0#usize, 64#usize
usize_add_fact add_64_16, 64#usize, 16#usize, 80#usize
usize_add_fact add_64_32, 64#usize, 32#usize, 96#usize
usize_add_fact add_64_48, 64#usize, 48#usize, 112#usize
usize_add_fact add_64_64, 64#usize, 64#usize, 128#usize
usize_add_fact add_64_80, 64#usize, 80#usize, 144#usize
usize_add_fact add_64_96_global, 64#usize, 96#usize, 160#usize
usize_add_fact add_160_0, 160#usize, 0#usize, 160#usize
usize_add_fact add_160_16, 160#usize, 16#usize, 176#usize
usize_add_fact add_160_32, 160#usize, 32#usize, 192#usize
usize_add_fact add_160_48, 160#usize, 48#usize, 208#usize
usize_add_fact add_160_64, 160#usize, 64#usize, 224#usize
usize_add_fact add_160_80, 160#usize, 80#usize, 240#usize
usize_add_fact add_160_96, 160#usize, 96#usize, 256#usize
usize_add_fact add_160_112, 160#usize, 112#usize, 272#usize
usize_add_fact add_160_128_global, 160#usize, 128#usize, 288#usize
usize_add_fact add_288_0, 288#usize, 0#usize, 288#usize
usize_add_fact add_288_16, 288#usize, 16#usize, 304#usize
usize_add_fact add_288_32, 288#usize, 32#usize, 320#usize
usize_add_fact add_288_48, 288#usize, 48#usize, 336#usize
usize_add_fact add_288_64, 288#usize, 64#usize, 352#usize
usize_add_fact add_288_80, 288#usize, 80#usize, 368#usize
usize_add_fact add_288_96, 288#usize, 96#usize, 384#usize
usize_add_fact add_288_112, 288#usize, 112#usize, 400#usize
usize_add_fact add_288_128, 288#usize, 128#usize, 416#usize
usize_add_fact add_416_0, 416#usize, 0#usize, 416#usize
usize_add_fact add_416_112, 416#usize, 112#usize, 528#usize
usize_add_fact add_416_224, 416#usize, 224#usize, 640#usize
usize_add_fact add_416_336, 416#usize, 336#usize, 752#usize
usize_add_fact add_528_112, 528#usize, 112#usize, 640#usize
usize_add_fact add_640_112, 640#usize, 112#usize, 752#usize
usize_add_fact add_752_112, 752#usize, 112#usize, 864#usize
usize_add_fact add_416_448, 416#usize, 448#usize, 864#usize

private theorem inner_body_round0_sample0
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript) :
    v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
        parsed () nonces batch roots final selector 0#usize transcript 0#usize =
      .ok (.cont
        ({ events := transcript.events ++ sampleEvents 0 0 }, 1#usize)) := by
  have mul2_0 : 2#usize * 0#usize = ok 0#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul0_16 : 0#usize * 16#usize = ok 0#usize := by
    apply usizeMulExact <;> scalar_tac
  have add0_0 : 0#usize + 0#usize = ok 0#usize := by
    apply usizeAddExact <;> scalar_tac
  have add0_16 : 0#usize + 16#usize = ok 16#usize := by
    apply usizeAddExact <;> scalar_tac
  have mul0_2 : 0#usize * 2#usize = ok 0#usize := by
    apply usizeMulExact <;> scalar_tac
  have sub4_1 : 4#usize - 1#usize = ok 3#usize := by
    apply usizeSubExact <;> scalar_tac
  have mul3_2 : 3#usize * 2#usize = ok 6#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul6_16 : 6#usize * 16#usize = ok 96#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul2_2 : 2#usize * 2#usize = ok 4#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul4_16 : 4#usize * 16#usize = ok 64#usize := by
    apply usizeMulExact <;> scalar_tac
  have add0_64 : 0#usize + 64#usize = ok 64#usize := by
    apply usizeAddExact <;> scalar_tac
  have add64_96 : 64#usize + 96#usize = ok 160#usize := by
    apply usizeAddExact <;> scalar_tac
  have mul4_2 : 4#usize * 2#usize = ok 8#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul8_16 : 8#usize * 16#usize = ok 128#usize := by
    apply usizeMulExact <;> scalar_tac
  have add160_128 : 160#usize + 128#usize = ok 288#usize := by
    apply usizeAddExact <;> scalar_tac
  have add160_0 : 160#usize + 0#usize = ok 160#usize := by
    apply usizeAddExact <;> scalar_tac
  have add288_0 : 288#usize + 0#usize = ok 288#usize := by
    apply usizeAddExact <;> scalar_tac
  have add0_1 : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExact <;> scalar_tac
  simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body,
    sampleEvents, v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
    v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
    v5_relation_stress.CIRCLE_COORDINATES,
    v5_relation_stress.LINE_POINTS,
    v5_relation_stress.OOD_VALUES,
    v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
    v5_relation_stress.QM31_BYTES,
    v5_cu_probe.QM31_BYTES,
    aspis_core.transcript.label.M31_CIRCLE_OOD_VALUE,
    aspis_core.transcript.Transcript.challenge_secure_circle_point,
    aspis_core.transcript.Transcript.challenge_qm31,
    v5_cu_probe.stress_qm31,
    v5_cu_probe.absorb_real_v5_ood,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    core.result.Result.map_err, mul2_0, mul0_16, add0_0, add0_16,
    mul0_2, sub4_1, mul3_2, mul6_16, mul2_2, mul4_16, add0_64,
    add64_96, mul4_2, mul8_16, add160_128, add160_0, add288_0,
    add0_1]
  change
    ({ events := ((transcript.events ++ [.secureCirclePoint]) ++
      [.absorbOod 16 0 0]) ++ [.squeezeQm31] } :
      aspis_core.transcript.Transcript) = _
  simp [List.append_assoc]

#print axioms inner_body_round0_sample0

private theorem active_body_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript)
    (round sample : Std.Usize)
    (hround : round.val < 4)
    (hsample : sample.val < 2) :
    ∃ next : Std.Usize,
      next.val = sample.val + 1 ∧
      v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed () nonces batch roots final selector round transcript sample =
        .ok (.cont
          ({ events := transcript.events ++
              sampleEvents round.val sample.val }, next)) := by
  let next : Std.Usize :=
    Std.Usize.ofNatCore (sample.val + 1) (by scalar_tac)
  have hnextVal : next.val = sample.val + 1 := by simp [next]
  have hnext : sample + 1#usize = ok next := by
    apply usizeAddExact
    · scalar_tac
    · simpa [next]
  refine ⟨next, hnextVal, ?_⟩
  have hrange : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  have srange : sample.val = 0 ∨ sample.val = 1 := by omega
  rcases hrange with hr | hr | hr | hr <;>
    rcases srange with hs | hs
  all_goals
    first
    | have roundEq : round = 0#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 1#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 2#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 3#usize := UScalar.eq_of_val_eq hr
      subst round
    first
    | have sampleEq : sample = 0#usize := UScalar.eq_of_val_eq hs
      subst sample
    | have sampleEq : sample = 1#usize := UScalar.eq_of_val_eq hs
      subst sample
    simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body,
      sampleEvents, v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
      v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
      v5_relation_stress.CIRCLE_COORDINATES,
      v5_relation_stress.LINE_POINTS,
      v5_relation_stress.OOD_VALUES,
      v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
      v5_relation_stress.QM31_BYTES, v5_cu_probe.QM31_BYTES,
      aspis_core.transcript.label.M31_CIRCLE_OOD_VALUE,
      aspis_core.transcript.label.M31_LINE_OOD_VALUE,
      aspis_core.transcript.Transcript.challenge_secure_circle_point,
      aspis_core.transcript.Transcript.challenge_ood_qm31,
      aspis_core.transcript.Transcript.challenge_qm31,
      v5_cu_probe.stress_qm31, v5_cu_probe.absorb_real_v5_ood,
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      core.result.Result.map_err, hnext]
  all_goals
    change
      ({ events := ((transcript.events ++ [_]) ++ [_]) ++ [_] } :
        aspis_core.transcript.Transcript) = _
    simp [List.append_assoc, sampleEvents]

#print axioms active_body_exact

private theorem tail_body_round0
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript) :
    v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
        parsed () nonces batch roots final selector 0#usize transcript 2#usize =
      .ok (.done
        ({ events := transcript.events ++ roundTailEvents 0
            (nonces.val[0]!.val) }, 1#usize, 1#u32)) := by
  simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body,
    roundTailEvents, v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
    v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
    v5_relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
    v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
    v5_relation_stress.OOD_MIXES, v5_relation_stress.OOD_VALUES,
    v5_relation_stress.LINE_POINTS, v5_relation_stress.CIRCLE_COORDINATES,
    v5_relation_stress.QM31_BYTES, aspis_core.sumcheck.SUMCHECK_COEFFICIENTS,
    v5_cu_probe.QM31_BYTES,
    v5_cu_probe.absorb_real_v5_relation_sumcheck,
    v5_cu_probe.check_and_absorb_real_v5_fold_nonce,
    aspis_core.transcript.Transcript.challenge_qm31,
    v5_cu_probe.decode_qm31,
    v5_cu_probe.absorb_real_v5_later_root_for_round,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    core.result.Result.map_err,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    Array.to_slice, Array.index_usize, Array.getElem?_Usize_eq]
  change
    ({ events := (((transcript.events ++ [_]) ++ [_]) ++ [_]) ++ [_] } :
      aspis_core.transcript.Transcript) = _
  simp [List.append_assoc, roundTailEvents]

#print axioms tail_body_round0

private theorem tail_body_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript)
    (round : Std.Usize)
    (hround : round.val < 4) :
    ∃ next : Std.Usize,
      next.val = round.val + 1 ∧
      v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed () nonces batch roots final selector round transcript 2#usize =
        .ok (.done
          ({ events := transcript.events ++ roundTailEvents round.val
              (nonces.val[round.val]!.val) }, next, 1#u32)) := by
  let next : Std.Usize :=
    Std.Usize.ofNatCore (round.val + 1) (by scalar_tac)
  have hnextVal : next.val = round.val + 1 := by simp [next]
  have hnext : round + 1#usize = ok next := by
    apply usizeAddExact
    · scalar_tac
    · simpa [next]
  refine ⟨next, hnextVal, ?_⟩
  have hrange : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  rcases hrange with hr | hr | hr | hr
  all_goals
    first
    | have roundEq : round = 0#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 1#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 2#usize := UScalar.eq_of_val_eq hr
      subst round
    | have roundEq : round = 3#usize := UScalar.eq_of_val_eq hr
      subst round
    simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body,
      roundTailEvents, v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
      v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
      v5_relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
      v5_relation_stress.OOD_MIXES, v5_relation_stress.OOD_VALUES,
      v5_relation_stress.LINE_POINTS, v5_relation_stress.CIRCLE_COORDINATES,
      v5_relation_stress.QM31_BYTES,
      aspis_core.sumcheck.SUMCHECK_COEFFICIENTS, v5_cu_probe.QM31_BYTES,
      v5_cu_probe.absorb_real_v5_relation_sumcheck,
      v5_cu_probe.check_and_absorb_real_v5_fold_nonce,
      aspis_core.transcript.Transcript.challenge_qm31,
      v5_cu_probe.decode_qm31,
      v5_cu_probe.absorb_real_v5_later_root_for_round,
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default, core.result.Result.map_err,
      core.slice.index.SliceIndexRangeUsizeSlice.index,
      Array.to_slice, Array.index_usize, Array.getElem?_Usize_eq, hnext]
  all_goals
    first
    | change
        ({ events := (((transcript.events ++ [_]) ++ [_]) ++ [_]) ++ [_] } :
          aspis_core.transcript.Transcript) = _
      simp [List.append_assoc]
    | change
        ({ events := ((transcript.events ++ [_]) ++ [_]) ++ [_] } :
          aspis_core.transcript.Transcript) = _
      simp [List.append_assoc]

#print axioms tail_body_exact

theorem generated_inner_round_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript)
    (round : Std.Usize)
    (hround : round.val < 4) :
    ∃ next : Std.Usize,
      next.val = round.val + 1 ∧
      v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
          parsed transcript () nonces batch roots final selector round 0#usize =
        .ok
          ({ events := transcript.events ++ roundEvents round.val
              (nonces.val[round.val]!.val) }, next, 1#u32) := by
  obtain ⟨sample1, hsample1Val, hsample1⟩ :=
    active_body_exact parsed nonces batch final roots selector transcript
      round 0#usize hround (by simp)
  have hsample1Eq : sample1 = 1#usize :=
    UScalar.eq_of_val_eq (by simpa using hsample1Val)
  subst sample1
  let transcript1 : aspis_core.transcript.Transcript :=
    { events := transcript.events ++ sampleEvents round.val 0 }
  have hsample1' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed () nonces batch roots final selector round transcript 0#usize =
        .ok (.cont (transcript1, 1#usize)) := by
    simpa [transcript1] using hsample1
  obtain ⟨sample2, hsample2Val, hsample2⟩ :=
    active_body_exact parsed nonces batch final roots selector transcript1
      round 1#usize hround (by simp)
  have hsample2Eq : sample2 = 2#usize :=
    UScalar.eq_of_val_eq (by simpa using hsample2Val)
  subst sample2
  let transcript2 : aspis_core.transcript.Transcript :=
    { events := transcript1.events ++ sampleEvents round.val 1 }
  have hsample2' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0.body
          parsed () nonces batch roots final selector round transcript1 1#usize =
        .ok (.cont (transcript2, 2#usize)) := by
    simpa [transcript2] using hsample2
  obtain ⟨next, hnextVal, htail⟩ :=
    tail_body_exact parsed nonces batch final roots selector transcript2
      round hround
  refine ⟨next, hnextVal, ?_⟩
  unfold v5_cu_probe.replay_real_v5_relation_rounds_loop0_loop0
  rw [loop.eq_def]
  simp only
  rw [hsample1']
  simp only [bind_tc_ok]
  rw [loop.eq_def]
  simp only
  rw [hsample2']
  simp only [bind_tc_ok]
  rw [loop.eq_def]
  simp only
  rw [htail]
  simpa [transcript2, transcript1, roundEvents, roundTailEvents,
    List.append_assoc]

#print axioms generated_inner_round_exact

theorem generated_outer_body_active_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript)
    (round : Std.Usize)
    (hround : round.val < 4) :
    ∃ next : Std.Usize,
      next.val = round.val + 1 ∧
      v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed () nonces batch roots final selector transcript round =
        .ok (.cont
          ({ events := transcript.events ++ roundEvents round.val
              (nonces.val[round.val]!.val) }, next)) := by
  obtain ⟨next, hnextVal, hinner⟩ :=
    generated_inner_round_exact parsed nonces batch final roots selector
      transcript round hround
  refine ⟨next, hnextVal, ?_⟩
  have hactive : round < 4#usize := by scalar_tac
  simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0.body,
    v5_relation_stress.V5_RELATION_STRESS_ROUNDS, hactive, hinner]
  rfl

theorem generated_outer_body_done_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript) :
    v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
        parsed () nonces batch roots final selector transcript 4#usize =
      .ok (.done (some (.Ok transcript))) := by
  simp [v5_cu_probe.replay_real_v5_relation_rounds_loop0.body,
    v5_relation_stress.V5_RELATION_STRESS_ROUNDS]

#print axioms generated_outer_body_active_exact
#print axioms generated_outer_body_done_exact

theorem generated_four_round_loop_exact
    (parsed : v5_cu_probe.ParsedProbeData)
    (nonces : Array Std.U64 4#usize)
    (batch final : Std.U64)
    (roots : v5_cu_probe.private_openings.V5PrivateOpeningRoots)
    (selector : Std.U8)
    (transcript : aspis_core.transcript.Transcript) :
    v5_cu_probe.replay_real_v5_relation_rounds_loop0
        parsed transcript () nonces batch roots final selector 0#usize =
      .ok (some (.Ok
        { events := transcript.events ++ fourRoundEvents
            (fun index => nonces.val[index.val]!.val) })) := by
  let nonceAt : Fin 4 → Nat :=
    fun index => nonces.val[index.val]!.val
  obtain ⟨round1, hround1Val, hround0⟩ :=
    generated_outer_body_active_exact parsed nonces batch final roots selector
      transcript 0#usize (by simp)
  have hround1Eq : round1 = 1#usize :=
    UScalar.eq_of_val_eq (by simpa using hround1Val)
  subst round1
  let transcript1 : aspis_core.transcript.Transcript :=
    { events := transcript.events ++ roundEvents 0 (nonceAt 0) }
  have hround0' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed () nonces batch roots final selector transcript 0#usize =
        .ok (.cont (transcript1, 1#usize)) := by
    simpa [transcript1, nonceAt] using hround0

  obtain ⟨round2, hround2Val, hround1⟩ :=
    generated_outer_body_active_exact parsed nonces batch final roots selector
      transcript1 1#usize (by simp)
  have hround2Eq : round2 = 2#usize :=
    UScalar.eq_of_val_eq (by simpa using hround2Val)
  subst round2
  let transcript2 : aspis_core.transcript.Transcript :=
    { events := transcript1.events ++ roundEvents 1 (nonceAt 1) }
  have hround1' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed () nonces batch roots final selector transcript1 1#usize =
        .ok (.cont (transcript2, 2#usize)) := by
    simpa [transcript2, nonceAt] using hround1

  obtain ⟨round3, hround3Val, hround2⟩ :=
    generated_outer_body_active_exact parsed nonces batch final roots selector
      transcript2 2#usize (by simp)
  have hround3Eq : round3 = 3#usize :=
    UScalar.eq_of_val_eq (by simpa using hround3Val)
  subst round3
  let transcript3 : aspis_core.transcript.Transcript :=
    { events := transcript2.events ++ roundEvents 2 (nonceAt 2) }
  have hround2' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed () nonces batch roots final selector transcript2 2#usize =
        .ok (.cont (transcript3, 3#usize)) := by
    simpa [transcript3, nonceAt] using hround2

  obtain ⟨round4, hround4Val, hround3⟩ :=
    generated_outer_body_active_exact parsed nonces batch final roots selector
      transcript3 3#usize (by simp)
  have hround4Eq : round4 = 4#usize :=
    UScalar.eq_of_val_eq (by simpa using hround4Val)
  subst round4
  let transcript4 : aspis_core.transcript.Transcript :=
    { events := transcript3.events ++ roundEvents 3 (nonceAt 3) }
  have hround3' :
      v5_cu_probe.replay_real_v5_relation_rounds_loop0.body
          parsed () nonces batch roots final selector transcript3 3#usize =
        .ok (.cont (transcript4, 4#usize)) := by
    simpa [transcript4, nonceAt] using hround3
  have hdone := generated_outer_body_done_exact parsed nonces batch final roots
    selector transcript4

  unfold v5_cu_probe.replay_real_v5_relation_rounds_loop0
  rw [loop.eq_def]
  simp only
  rw [hround0']
  simp only
  rw [loop.eq_def]
  simp only
  rw [hround1']
  simp only
  rw [loop.eq_def]
  simp only
  rw [hround2']
  simp only
  rw [loop.eq_def]
  simp only
  rw [hround3']
  simp only
  rw [loop.eq_def]
  simp only
  rw [hdone]
  simpa [transcript4, transcript3, transcript2, transcript1, nonceAt,
    fourRoundEvents, List.append_assoc]

#print axioms generated_four_round_loop_exact

/-- Exact successful event trace of the Aeneas-translated production
`replay_real_v5_relation_rounds` helper.  The field values are intentionally
erased by the observation semantics; the theorem fixes every transcript call,
round/sample index, and fold nonce consumed by the source helper. -/
theorem generated_replay_relation_rounds_exact
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData) :
    v5_cu_probe.replay_real_v5_relation_rounds transcript parsed =
      .ok (.Ok
        { events := transcript.events ++ fourRoundEvents
            (fun index => parsed.v5_fold_nonces.val[index.val]!.val) }) := by
  have hloop := generated_four_round_loop_exact parsed parsed.v5_fold_nonces
    parsed.v5_batch_nonce parsed.v5_final_nonce parsed.v5_private_roots
    parsed.v5_query_selector transcript
  simp [v5_cu_probe.replay_real_v5_relation_rounds,
    v5_cu_probe.verify_v5_relation_final_zero_tail, hloop]

#print axioms generated_replay_relation_rounds_exact

end AspisV5TranscriptRelationSourceProof
