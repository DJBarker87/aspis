import ComponentBV5SamplerAuthenticatedConstants20260721.Funs
import QM31AddSubNegProof
import HalfProof
import Aeneas.Tactic.Step.StepStar

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBSamplerZeroBoundary

abbrev SamplerQM31 := aspis_prover.aspis_core.field.QM31
abbrev ExactQM31 := AspisAeneasQM31Additive.QM31Exact

def toAdditive (x : SamplerQM31) : AspisCoreAdditive.field.QM31 :=
  { c0 := { a := x.c0.a, b := x.c0.b },
    c1 := { a := x.c1.a, b := x.c1.b } }

def toHalf (x : SamplerQM31) : AspisCoreHalf.field.QM31 :=
  { c0 := { a := x.c0.a, b := x.c0.b },
    c1 := { a := x.c1.a, b := x.c1.b } }

def Canonical (x : SamplerQM31) : Prop :=
  AspisAeneasQM31Additive.CanonicalQM31 (toAdditive x)

def toExact (x : SamplerQM31) : ExactQM31 :=
  AspisAeneasQM31Additive.qm31ToExact (toAdditive x)

def mapAdditiveResult (result : Result SamplerQM31) :
    Result AspisCoreAdditive.field.QM31 :=
  match result with
  | .ok value => .ok (toAdditive value)
  | .fail error => .fail error
  | .div => .div

def mapHalfResult (result : Result SamplerQM31) :
    Result AspisCoreHalf.field.QM31 :=
  match result with
  | .ok value => .ok (toHalf value)
  | .fail error => .fail error
  | .div => .div

def CanonicalM31 (x : aspis_prover.aspis_core.field.M31) : Prop :=
  x.val < aspis_prover.aspis_core.field.P.val

private def canonicalM31Post {S : Type}
    (result : core.result.Result aspis_prover.aspis_core.field.M31
      aspis_prover.v5_mask.MaskSampleExhausted × S) : Prop :=
  match result.1 with
  | .Ok value => CanonicalM31 value
  | .Err _ => True

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from
  aspis_prover.aspis_core.field.CM31.new

/-- Every successful generated base-field rejection sample is canonical. -/
theorem sample_m31_success_canonical
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (value : aspis_prover.aspis_core.field.M31)
    (run : aspis_prover.v5_mask.sample_m31 sourceInst source =
      .ok (.Ok value, finalSource)) :
    CanonicalM31 value := by
  have hSpec :
      aspis_prover.v5_mask.sample_m31 sourceInst source ⦃ result =>
        canonicalM31Post result ⦄ := by
    simp only [aspis_prover.v5_mask.sample_m31,
      aspis_prover.v5_mask.sample_m31_loop]
    apply loop.spec_decr_nat
      (fun state => state.1.«end».val - state.1.start.val)
      (fun state =>
        state.1.«end».val =
            aspis_prover.v5_mask.V5_MASK_SAMPLE_RETRY_LIMIT.val ∧
        state.1.start.val ≤ state.1.«end».val)
      canonicalM31Post
    · rintro ⟨iter, currentSource⟩ ⟨hEnd, hStart⟩
      unfold aspis_prover.v5_mask.sample_m31_loop.body
      obtain ⟨word, nextSource, hWord⟩ := nextWordTotal currentSource
      step*
      all_goals simp_all [canonicalM31Post, CanonicalM31,
        aspis_prover.aspis_core.field.P]
      all_goals step*
    · simp [aspis_prover.v5_mask.V5_MASK_SAMPLE_RETRY_LIMIT]
  simp [run, canonicalM31Post, Aeneas.Std.WP.spec,
    Aeneas.Std.WP.theta] at hSpec
  exact hSpec

/-- The generated rejection sampler terminates for a total word source; its
only successful value branch is canonical. -/
theorem sample_m31_total
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) :
    ∃ result finalSource,
      aspis_prover.v5_mask.sample_m31 sourceInst source =
        .ok (result, finalSource) ∧
      match result with
      | .Ok value => CanonicalM31 value
      | .Err _ => True := by
  have hSpec :
      aspis_prover.v5_mask.sample_m31 sourceInst source ⦃ result =>
        canonicalM31Post result ⦄ := by
    simp only [aspis_prover.v5_mask.sample_m31,
      aspis_prover.v5_mask.sample_m31_loop]
    apply loop.spec_decr_nat
      (fun state => state.1.«end».val - state.1.start.val)
      (fun state =>
        state.1.«end».val =
            aspis_prover.v5_mask.V5_MASK_SAMPLE_RETRY_LIMIT.val ∧
        state.1.start.val ≤ state.1.«end».val)
      canonicalM31Post
    · rintro ⟨iter, currentSource⟩ ⟨hEnd, hStart⟩
      unfold aspis_prover.v5_mask.sample_m31_loop.body
      obtain ⟨word, nextSource, hWord⟩ := nextWordTotal currentSource
      step*
      all_goals simp_all [canonicalM31Post, CanonicalM31,
        aspis_prover.aspis_core.field.P]
      all_goals step*
    · simp [aspis_prover.v5_mask.V5_MASK_SAMPLE_RETRY_LIMIT]
  obtain ⟨result, hRun, hPost⟩ := Aeneas.Std.WP.spec_imp_exists hSpec
  exact ⟨result.1, result.2, hRun, hPost⟩

private def canonicalQM31Post {S : Type}
    (result : core.result.Result SamplerQM31
      aspis_prover.v5_mask.MaskSampleExhausted × S) : Prop :=
  match result.1 with
  | .Ok value => Canonical value
  | .Err _ => True

/-- Four successful authenticated base-field draws make every generated
QM31 limb canonical, in the exact source-threading order of Rust. -/
theorem sample_qm31_success_canonical
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (value : SamplerQM31)
    (run : aspis_prover.v5_mask.sample_qm31 sourceInst source =
      .ok (.Ok value, finalSource)) :
    Canonical value := by
  unfold aspis_prover.v5_mask.sample_qm31 at run
  cases h0 : aspis_prover.v5_mask.sample_m31 sourceInst source with
  | fail error => simp [h0] at run
  | div => simp [h0] at run
  | ok pair0 =>
    rcases pair0 with ⟨result0, source1⟩
    cases result0 with
    | Err error => simp [h0] at run
    | Ok value0 =>
      cases h1 : aspis_prover.v5_mask.sample_m31 sourceInst source1 with
      | fail error => simp [h0, h1] at run
      | div => simp [h0, h1] at run
      | ok pair1 =>
        rcases pair1 with ⟨result1, source2⟩
        cases result1 with
        | Err error => simp [h0, h1] at run
        | Ok value1 =>
          cases h2 : aspis_prover.v5_mask.sample_m31 sourceInst source2 with
          | fail error => simp [h0, h1, h2] at run
          | div => simp [h0, h1, h2] at run
          | ok pair2 =>
            rcases pair2 with ⟨result2, source3⟩
            cases result2 with
            | Err error => simp [h0, h1, h2] at run
            | Ok value2 =>
              cases h3 : aspis_prover.v5_mask.sample_m31 sourceInst source3 with
              | fail error => simp [h0, h1, h2, h3] at run
              | div => simp [h0, h1, h2, h3] at run
              | ok pair3 =>
                rcases pair3 with ⟨result3, source4⟩
                cases result3 with
                | Err error => simp [h0, h1, h2, h3] at run
                | Ok value3 =>
                  have hc0 := sample_m31_success_canonical sourceInst
                    nextWordTotal source source1 value0 h0
                  have hc1 := sample_m31_success_canonical sourceInst
                    nextWordTotal source1 source2 value1 h1
                  have hc2 := sample_m31_success_canonical sourceInst
                    nextWordTotal source2 source3 value2 h2
                  have hc3 := sample_m31_success_canonical sourceInst
                    nextWordTotal source3 source4 value3 h3
                  simp [h0, h1, h2, h3,
                    aspis_prover.aspis_core.field.CM31.new] at run
                  rcases run with ⟨rfl, rfl⟩
                  simpa [Canonical, CanonicalM31, toAdditive,
                    AspisAeneasQM31Additive.CanonicalQM31,
                    AspisAeneasQM31Additive.CanonicalCM31,
                    AspisAeneasQM31Additive.CanonicalRawM31,
                    AspisAeneasQM31Additive.m31Modulus,
                    aspis_prover.aspis_core.field.P] using
                      (⟨⟨hc0, hc1⟩, ⟨hc2, hc3⟩⟩ :
                        (CanonicalM31 value0 ∧ CanonicalM31 value1) ∧
                        (CanonicalM31 value2 ∧ CanonicalM31 value3))

/-- Total operational characterization of the authentic four-limb sampler. -/
theorem sample_qm31_total
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) :
    ∃ result finalSource,
      aspis_prover.v5_mask.sample_qm31 sourceInst source =
        .ok (result, finalSource) ∧
      match result with
      | .Ok value => Canonical value
      | .Err _ => True := by
  obtain ⟨result0, source1, h0, hc0⟩ :=
    sample_m31_total sourceInst nextWordTotal source
  cases result0 with
  | Err error =>
    refine ⟨.Err error, source1, ?_, trivial⟩
    simp [aspis_prover.v5_mask.sample_qm31, h0]
  | Ok value0 =>
    obtain ⟨result1, source2, h1, hc1⟩ :=
      sample_m31_total sourceInst nextWordTotal source1
    cases result1 with
    | Err error =>
      refine ⟨.Err error, source2, ?_, trivial⟩
      simp [aspis_prover.v5_mask.sample_qm31, h0, h1]
    | Ok value1 =>
      obtain ⟨result2, source3, h2, hc2⟩ :=
        sample_m31_total sourceInst nextWordTotal source2
      cases result2 with
      | Err error =>
        refine ⟨.Err error, source3, ?_, trivial⟩
        simp [aspis_prover.v5_mask.sample_qm31, h0, h1, h2]
      | Ok value2 =>
        obtain ⟨result3, source4, h3, hc3⟩ :=
          sample_m31_total sourceInst nextWordTotal source3
        cases result3 with
        | Err error =>
          refine ⟨.Err error, source4, ?_, trivial⟩
          simp [aspis_prover.v5_mask.sample_qm31, h0, h1, h2, h3]
        | Ok value3 =>
          let value : SamplerQM31 :=
            { c0 := { a := value0, b := value1 },
              c1 := { a := value2, b := value3 } }
          refine ⟨.Ok value, source4, ?_, ?_⟩
          · simp [aspis_prover.v5_mask.sample_qm31, h0, h1, h2, h3,
              value]
          · simpa [Canonical, CanonicalM31, toAdditive,
              AspisAeneasQM31Additive.CanonicalQM31,
              AspisAeneasQM31Additive.CanonicalCM31,
              AspisAeneasQM31Additive.CanonicalRawM31,
              AspisAeneasQM31Additive.m31Modulus,
              aspis_prover.aspis_core.field.P, value] using
                (⟨⟨hc0, hc1⟩, ⟨hc2, hc3⟩⟩ :
                  (CanonicalM31 value0 ∧ CanonicalM31 value1) ∧
                  (CanonicalM31 value2 ∧ CanonicalM31 value3))

@[step] theorem sample_qm31_spec
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) :
    aspis_prover.v5_mask.sample_qm31 sourceInst source ⦃ result =>
      canonicalQM31Post result ⦄ := by
  obtain ⟨result, finalSource, hRun, hPost⟩ :=
    sample_qm31_total sourceInst nextWordTotal source
  rw [hRun]
  cases result <;>
    simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta,
      Aeneas.Std.WP.wp_return, canonicalQM31Post] at hPost ⊢
  all_goals assumption

theorem zero_canonical :
    Canonical aspis_prover.aspis_core.field.QM31.ZERO := by
  norm_num [Canonical, toAdditive,
    AspisAeneasQM31Additive.CanonicalQM31,
    AspisAeneasQM31Additive.CanonicalCM31,
    AspisAeneasQM31Additive.CanonicalRawM31,
    AspisAeneasQM31Additive.m31Modulus,
    aspis_prover.aspis_core.field.QM31.ZERO]

theorem toExact_zero :
    toExact aspis_prover.aspis_core.field.QM31.ZERO = 0 := by
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
      simp [toExact, toAdditive,
        aspis_prover.aspis_core.field.QM31.ZERO,
        AspisAeneasQM31Additive.qm31ToExact,
        AspisAeneasQM31Additive.cm31ToExact]

theorem sampler_add_map (x y : SamplerQM31) :
    mapAdditiveResult (aspis_prover.aspis_core.field.QM31.add x y) =
      AspisCoreAdditive.field.QM31.add (toAdditive x) (toAdditive y) := by
  by_cases h00 : 2147483647 ≤ (x.c0.a.val + y.c0.a.val) % Std.U32.size
  all_goals by_cases h01 : 2147483647 ≤ (x.c0.b.val + y.c0.b.val) % Std.U32.size
  all_goals by_cases h10 : 2147483647 ≤ (x.c1.a.val + y.c1.a.val) % Std.U32.size
  all_goals by_cases h11 : 2147483647 ≤ (x.c1.b.val + y.c1.b.val) % Std.U32.size
  all_goals simp [aspis_prover.aspis_core.field.QM31.add,
    aspis_prover.aspis_core.field.CM31.add,
    aspis_prover.aspis_core.field.M31.add,
    aspis_prover.aspis_core.field.P,
    AspisCoreAdditive.field.QM31.add,
    AspisCoreAdditive.field.CM31.add,
    AspisCoreAdditive.field.M31.add,
    AspisCoreAdditive.field.P,
    mapAdditiveResult, toAdditive, lift, h00, h01, h10, h11]

theorem sampler_add_run_to_additive (x y out : SamplerQM31)
    (run : aspis_prover.aspis_core.field.QM31.add x y = .ok out) :
    AspisCoreAdditive.field.QM31.add (toAdditive x) (toAdditive y) =
      .ok (toAdditive out) := by
  rw [← sampler_add_map]
  simpa only [mapAdditiveResult] using congrArg mapAdditiveResult run

theorem sampler_add_exact (x y out : SamplerQM31)
    (hx : Canonical x) (hy : Canonical y)
    (run : aspis_prover.aspis_core.field.QM31.add x y = .ok out) :
    Canonical out ∧ toExact out = toExact x + toExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    AspisAeneasQM31Additive.extracted_qm31_add_corresponds
      (toAdditive x) (toAdditive y) hx hy
  have translated := sampler_add_run_to_additive x y out run
  have hout : toAdditive out = candidate :=
    Result.ok.inj (translated.symm.trans candidateRun)
  refine ⟨?_, ?_⟩
  · simpa [Canonical] using hout.symm ▸ candidateCanonical
  · simpa [toExact] using hout.symm ▸ candidateExact

theorem sampler_add_total (x y : SamplerQM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ out, aspis_prover.aspis_core.field.QM31.add x y = .ok out ∧
      Canonical out ∧ toExact out = toExact x + toExact y := by
  obtain ⟨candidate, candidateRun, _, _⟩ :=
    AspisAeneasQM31Additive.extracted_qm31_add_corresponds
      (toAdditive x) (toAdditive y) hx hy
  have hmap := sampler_add_map x y
  rw [candidateRun] at hmap
  cases hrun : aspis_prover.aspis_core.field.QM31.add x y with
  | fail error => simp [hrun, mapAdditiveResult] at hmap
  | div => simp [hrun, mapAdditiveResult] at hmap
  | ok out =>
    obtain ⟨hcanonical, hexact⟩ := sampler_add_exact x y out hx hy hrun
    exact ⟨out, rfl, hcanonical, hexact⟩

theorem sampler_neg_map (x : SamplerQM31) :
    mapAdditiveResult (aspis_prover.aspis_core.field.QM31.neg x) =
      AspisCoreAdditive.field.QM31.neg (toAdditive x) := by
  by_cases h00 : x.c0.a = 0#u32
  all_goals by_cases h01 : x.c0.b = 0#u32
  all_goals by_cases h10 : x.c1.a = 0#u32
  all_goals by_cases h11 : x.c1.b = 0#u32
  all_goals simp [aspis_prover.aspis_core.field.QM31.neg,
    aspis_prover.aspis_core.field.CM31.neg,
    aspis_prover.aspis_core.field.M31.neg,
    aspis_prover.aspis_core.field.P,
    AspisCoreAdditive.field.QM31.neg,
    AspisCoreAdditive.field.CM31.neg,
    AspisCoreAdditive.field.M31.neg,
    AspisCoreAdditive.field.P,
    mapAdditiveResult, toAdditive, lift, h00, h01, h10, h11]

theorem sampler_neg_run_to_additive (x out : SamplerQM31)
    (run : aspis_prover.aspis_core.field.QM31.neg x = .ok out) :
    AspisCoreAdditive.field.QM31.neg (toAdditive x) = .ok (toAdditive out) := by
  rw [← sampler_neg_map]
  simpa only [mapAdditiveResult] using congrArg mapAdditiveResult run

theorem sampler_neg_exact (x out : SamplerQM31)
    (hx : Canonical x)
    (run : aspis_prover.aspis_core.field.QM31.neg x = .ok out) :
    Canonical out ∧ toExact out = -toExact x := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    AspisAeneasQM31Additive.extracted_qm31_neg_corresponds
      (toAdditive x) hx
  have translated := sampler_neg_run_to_additive x out run
  have hout : toAdditive out = candidate :=
    Result.ok.inj (translated.symm.trans candidateRun)
  refine ⟨?_, ?_⟩
  · simpa [Canonical] using hout.symm ▸ candidateCanonical
  · simpa [toExact] using hout.symm ▸ candidateExact

theorem sampler_neg_total (x : SamplerQM31) (hx : Canonical x) :
    ∃ out, aspis_prover.aspis_core.field.QM31.neg x = .ok out ∧
      Canonical out ∧ toExact out = -toExact x := by
  obtain ⟨candidate, candidateRun, _, _⟩ :=
    AspisAeneasQM31Additive.extracted_qm31_neg_corresponds (toAdditive x) hx
  have hmap := sampler_neg_map x
  rw [candidateRun] at hmap
  cases hrun : aspis_prover.aspis_core.field.QM31.neg x with
  | fail error => simp [hrun, mapAdditiveResult] at hmap
  | div => simp [hrun, mapAdditiveResult] at hmap
  | ok out =>
    obtain ⟨hcanonical, hexact⟩ := sampler_neg_exact x out hx hrun
    exact ⟨out, rfl, hcanonical, hexact⟩

private theorem u32_one_eq_width_one :
    (1#u32 : Std.U32) = (1#32#uscalar : Std.U32) := by
  decide

theorem sampler_half_map (x : SamplerQM31) :
    mapHalfResult (aspis_prover.aspis_core.field.QM31.half x) =
      AspisCoreHalf.field.QM31.half (toHalf x) := by
  by_cases h00 : x.c0.a &&& 1#u32 = 0#u32
  all_goals by_cases h01 : x.c0.b &&& 1#u32 = 0#u32
  all_goals by_cases h10 : x.c1.a &&& 1#u32 = 0#u32
  all_goals by_cases h11 : x.c1.b &&& 1#u32 = 0#u32
  all_goals simp [aspis_prover.aspis_core.field.QM31.half,
    aspis_prover.aspis_core.field.CM31.half,
    aspis_prover.aspis_core.field.M31.half,
    aspis_prover.aspis_core.field.P,
    AspisCoreHalf.field.QM31.half,
    AspisCoreHalf.field.CM31.half,
    AspisCoreHalf.field.M31.half,
    AspisCoreHalf.field.P,
    mapHalfResult, toHalf, lift, h00, h01, h10, h11]
  all_goals simp only [u32_one_eq_width_one, true_and]

theorem sampler_half_run_to_authenticated (x out : SamplerQM31)
    (run : aspis_prover.aspis_core.field.QM31.half x = .ok out) :
    AspisCoreHalf.field.QM31.half (toHalf x) = .ok (toHalf out) := by
  rw [← sampler_half_map]
  simpa only [mapHalfResult] using congrArg mapHalfResult run

theorem sampler_half_exact (x out : SamplerQM31)
    (hx : Canonical x)
    (run : aspis_prover.aspis_core.field.QM31.half x = .ok out) :
    Canonical out ∧ toExact out + toExact out = toExact x := by
  have hx' : AspisAeneasHalf.CanonicalQM31 (toHalf x) := by
    simpa [Canonical, toAdditive, toHalf,
      AspisAeneasQM31Additive.CanonicalQM31,
      AspisAeneasQM31Additive.CanonicalCM31,
      AspisAeneasQM31Additive.CanonicalRawM31,
      AspisAeneasQM31Additive.m31Modulus,
      AspisAeneasHalf.CanonicalQM31,
      AspisAeneasHalf.CanonicalCM31,
      AspisAeneasHalf.CanonicalRawM31,
      AspisAeneasHalf.m31Modulus] using hx
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    AspisAeneasHalf.extracted_qm31_half_corresponds (toHalf x) hx'
  have translated := sampler_half_run_to_authenticated x out run
  have hout : toHalf out = candidate :=
    Result.ok.inj (translated.symm.trans candidateRun)
  rw [← hout] at candidateCanonical candidateExact
  refine ⟨?_, ?_⟩
  · simpa [Canonical, toAdditive, toHalf,
      AspisAeneasQM31Additive.CanonicalQM31,
      AspisAeneasQM31Additive.CanonicalCM31,
      AspisAeneasQM31Additive.CanonicalRawM31,
      AspisAeneasQM31Additive.m31Modulus,
      AspisAeneasHalf.CanonicalQM31,
      AspisAeneasHalf.CanonicalCM31,
      AspisAeneasHalf.CanonicalRawM31,
      AspisAeneasHalf.m31Modulus] using candidateCanonical
  · have h00 := congrArg
      (fun z : AspisAeneasHalf.QM31Exact => z.re.re) candidateExact.2
    have h01 := congrArg
      (fun z : AspisAeneasHalf.QM31Exact => z.re.im) candidateExact.2
    have h10 := congrArg
      (fun z : AspisAeneasHalf.QM31Exact => z.im.re) candidateExact.2
    have h11 := congrArg
      (fun z : AspisAeneasHalf.QM31Exact => z.im.im) candidateExact.2
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · simpa [toExact, toAdditive, toHalf,
          AspisAeneasQM31Additive.qm31ToExact,
          AspisAeneasQM31Additive.cm31ToExact,
          AspisAeneasHalf.qm31ToExact,
          AspisAeneasHalf.cm31ToExact] using h00
      · simpa [toExact, toAdditive, toHalf,
          AspisAeneasQM31Additive.qm31ToExact,
          AspisAeneasQM31Additive.cm31ToExact,
          AspisAeneasHalf.qm31ToExact,
          AspisAeneasHalf.cm31ToExact] using h01
    · apply QuadraticAlgebra.ext
      · simpa [toExact, toAdditive, toHalf,
          AspisAeneasQM31Additive.qm31ToExact,
          AspisAeneasQM31Additive.cm31ToExact,
          AspisAeneasHalf.qm31ToExact,
          AspisAeneasHalf.cm31ToExact] using h10
      · simpa [toExact, toAdditive, toHalf,
          AspisAeneasQM31Additive.qm31ToExact,
          AspisAeneasQM31Additive.cm31ToExact,
          AspisAeneasHalf.qm31ToExact,
          AspisAeneasHalf.cm31ToExact] using h11

theorem sampler_half_total (x : SamplerQM31) (hx : Canonical x) :
    ∃ out, aspis_prover.aspis_core.field.QM31.half x = .ok out ∧
      Canonical out ∧ toExact out + toExact out = toExact x := by
  have hx' : AspisAeneasHalf.CanonicalQM31 (toHalf x) := by
    simpa [Canonical, toAdditive, toHalf,
      AspisAeneasQM31Additive.CanonicalQM31,
      AspisAeneasQM31Additive.CanonicalCM31,
      AspisAeneasQM31Additive.CanonicalRawM31,
      AspisAeneasQM31Additive.m31Modulus,
      AspisAeneasHalf.CanonicalQM31,
      AspisAeneasHalf.CanonicalCM31,
      AspisAeneasHalf.CanonicalRawM31,
      AspisAeneasHalf.m31Modulus] using hx
  obtain ⟨candidate, candidateRun, _, _, _⟩ :=
    AspisAeneasHalf.extracted_qm31_half_corresponds (toHalf x) hx'
  have hmap := sampler_half_map x
  rw [candidateRun] at hmap
  cases hrun : aspis_prover.aspis_core.field.QM31.half x with
  | fail error => simp [hrun, mapHalfResult] at hmap
  | div => simp [hrun, mapHalfResult] at hmap
  | ok out =>
    obtain ⟨hcanonical, hexact⟩ := sampler_half_exact x out hx hrun
    exact ⟨out, rfl, hcanonical, hexact⟩

/-! ## Exact coefficient-array invariant -/

abbrev Polynomial := Array SamplerQM31 28#usize

local instance : Inhabited SamplerQM31 :=
  ⟨aspis_prover.aspis_core.field.QM31.ZERO⟩

def coefficientAt (polynomial : Polynomial) (coefficient : Nat) : SamplerQM31 :=
  polynomial[coefficient]!

def PolynomialCanonical (polynomial : Polynomial) : Prop :=
  ∀ coefficient : Nat, coefficient < 28 →
    Canonical (coefficientAt polynomial coefficient)

def exactPrefix (polynomial : Polynomial) (bound : Nat) : ExactQM31 :=
  ∑ coefficient ∈ Finset.Ico 1 bound,
    toExact (coefficientAt polynomial coefficient)

/-- Literal degree-27 boundary identity `2*c₀ + ∑ᵢ₌₁²⁷ cᵢ = 0`. -/
def ExactZeroBoundary (polynomial : Polynomial) : Prop :=
  toExact (coefficientAt polynomial 0) +
      toExact (coefficientAt polynomial 0) +
      exactPrefix polynomial 28 = 0

private theorem coefficientAt_set_eq
    (polynomial : Polynomial) (coefficient : Std.Usize) (value : SamplerQM31)
    (hbound : coefficient.val < 28) :
    coefficientAt (polynomial.set coefficient value) coefficient.val = value := by
  unfold coefficientAt
  rw [Array.getElem!_Nat_set_eq]
  exact ⟨rfl, by simpa using hbound⟩

private theorem coefficientAt_set_ne
    (polynomial : Polynomial) (coefficient : Std.Usize) (value : SamplerQM31)
    (index : Nat) (hne : coefficient.val ≠ index) :
    coefficientAt (polynomial.set coefficient value) index =
      coefficientAt polynomial index := by
  unfold coefficientAt
  exact Array.getElem!_Nat_set_ne polynomial coefficient index value hne

private theorem polynomialCanonical_set
    (polynomial : Polynomial) (coefficient : Std.Usize) (value : SamplerQM31)
    (hpolynomial : PolynomialCanonical polynomial)
    (hvalue : Canonical value) (hbound : coefficient.val < 28) :
    PolynomialCanonical (polynomial.set coefficient value) := by
  intro index hindex
  by_cases heq : coefficient.val = index
  · subst index
    rw [coefficientAt_set_eq polynomial coefficient value hbound]
    exact hvalue
  · rw [coefficientAt_set_ne polynomial coefficient value index heq]
    exact hpolynomial index hindex

private theorem exactPrefix_set_succ
    (polynomial : Polynomial) (coefficient : Std.Usize) (value : SamplerQM31)
    (hlower : 1 ≤ coefficient.val) (hbound : coefficient.val < 28) :
    exactPrefix (polynomial.set coefficient value) (coefficient.val + 1) =
      exactPrefix polynomial coefficient.val + toExact value := by
  unfold exactPrefix
  rw [Finset.sum_Ico_succ_top hlower]
  congr 1
  · apply Finset.sum_congr rfl
    intro index hindex
    rw [coefficientAt_set_ne]
    exact Nat.ne_of_gt (Finset.mem_Ico.mp hindex).2
  · rw [coefficientAt_set_eq polynomial coefficient value hbound]

private theorem exactPrefix_set_zero
    (polynomial : Polynomial) (value : SamplerQM31) :
    exactPrefix (polynomial.set 0#usize value) 28 =
      exactPrefix polynomial 28 := by
  unfold exactPrefix
  apply Finset.sum_congr rfl
  intro coefficient hcoefficient
  rw [coefficientAt_set_ne]
  have hpositive := (Finset.mem_Ico.mp hcoefficient).1
  have hzero : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [hzero]
  omega

private theorem repeatPolynomial_canonical :
    PolynomialCanonical
      (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO) := by
  intro coefficient hcoefficient
  unfold coefficientAt
  simp only [Array.getElem!_Nat_eq, Array.repeat_val]
  have h28 : (28#usize : Std.Usize).val = 28 := by scalar_tac
  rw [h28]
  rw [List.getElem!_replicate _ hcoefficient]
  exact zero_canonical

private theorem repeatPolynomial_prefix_one :
    exactPrefix
      (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO) 1 =
      toExact aspis_prover.aspis_core.field.QM31.ZERO := by
  simp [exactPrefix, toExact_zero]

private def roundInvariant {S : Type}
    (state : S × Polynomial × SamplerQM31 × Std.Usize) : Prop :=
  1 ≤ state.2.2.2.val ∧ state.2.2.2.val ≤ 28 ∧
    PolynomialCanonical state.2.1 ∧ Canonical state.2.2.1 ∧
    exactPrefix state.2.1 state.2.2.2.val = toExact state.2.2.1

private def zeroBoundaryRoundPost {S : Type}
    (result : core.result.Result Polynomial
      aspis_prover.v5_mask.MaskSampleExhausted × S) : Prop :=
  match result.1 with
  | .Ok polynomial => PolynomialCanonical polynomial ∧ ExactZeroBoundary polynomial
  | .Err _ => True

private theorem stateOnlySumcheckCoefficients_eq :
    aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS =
      .ok 28#usize := by
  have hspec := Usize.add_spec (x := 27#usize) (y := 1#usize) (by
    scalar_tac)
  obtain ⟨value, valueEquation, valueVal⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  have valueIs28 : value = 28#usize := by
    apply UScalar.eq_of_val_eq
    simpa using valueVal
  unfold aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS
    aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE
  rw [valueEquation, valueIs28]

/-- A successful authentic Rust round sampler returns a canonical degree-27
polynomial satisfying its exact zero-boundary identity. -/
theorem sample_zero_boundary_round_spec
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) :
    aspis_prover.v5_sumcheck_mask.sample_zero_boundary_round
      sourceInst source ⦃ result => zeroBoundaryRoundPost result ⦄ := by
  simp only [aspis_prover.v5_sumcheck_mask.sample_zero_boundary_round,
    aspis_prover.v5_sumcheck_mask.sample_zero_boundary_round_loop]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.2.2.val)
    roundInvariant zeroBoundaryRoundPost
  · rintro ⟨currentSource, polynomial, tailSum, coefficient⟩
      ⟨hlower, hupper, hpolynomial, htail, hprefix⟩
    simp only at hlower hupper hpolynomial htail hprefix
    unfold aspis_prover.v5_sumcheck_mask.sample_zero_boundary_round_loop.body
    by_cases hlt : coefficient.val < 28
    · obtain ⟨sampleResult, nextSource, hsample, hsamplePost⟩ :=
        sample_qm31_total sourceInst nextWordTotal currentSource
      cases sampleResult with
      | Err error =>
        simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS,
          aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE,
          stateOnlySumcheckCoefficients_eq, hlt, hsample, zeroBoundaryRoundPost]
      | Ok value =>
        obtain ⟨updated, hupdate, hupdated⟩ := Aeneas.Std.WP.spec_imp_exists
          (Array.update_spec polynomial coefficient value (by simpa using hlt))
        subst updated
        obtain ⟨tailSum1, hadd, htail1, hexact1⟩ :=
          sampler_add_total tailSum value htail hsamplePost
        let coefficient1 := Std.Usize.wrapping_add coefficient 1#usize
        have hcoefficient1 : coefficient1.val = coefficient.val + 1 := by
          unfold coefficient1
          rw [Usize.wrapping_add_val_eq]
          have hone : (1#usize : Std.Usize).val = 1 := by scalar_tac
          rw [hone]
          apply Nat.mod_eq_of_lt
          cases System.Platform.numBits_eq <;>
            simp [Usize.size, Usize.numBits, *] <;> omega
        have hcanonical1 := polynomialCanonical_set polynomial coefficient value
          hpolynomial hsamplePost hlt
        have hprefix1 := exactPrefix_set_succ polynomial coefficient value
          hlower hlt
        simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS,
          aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE,
          stateOnlySumcheckCoefficients_eq, hlt, hsample, hupdate, hadd, lift, coefficient1,
          roundInvariant, hcoefficient1, hcanonical1, htail1,
          hprefix1, hexact1, hprefix]
        omega
    · have heq : coefficient.val = 28 := by omega
      obtain ⟨q, hneg, hqCanonical, hqExact⟩ :=
        sampler_neg_total tailSum htail
      obtain ⟨q1, hhalf, hq1Canonical, hq1Double⟩ :=
        sampler_half_total q hqCanonical
      obtain ⟨updated, hupdate, hupdated⟩ := Aeneas.Std.WP.spec_imp_exists
        (Array.update_spec polynomial 0#usize q1 (by scalar_tac))
      subst updated
      have hcanonicalUpdated := polynomialCanonical_set polynomial 0#usize q1
        hpolynomial hq1Canonical (by scalar_tac)
      have hprefix28 : exactPrefix polynomial 28 = toExact tailSum := by
        simpa [heq] using hprefix
      simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS,
        aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE,
        stateOnlySumcheckCoefficients_eq, hlt, hneg, hhalf, hupdate, zeroBoundaryRoundPost]
      refine ⟨hcanonicalUpdated, ?_⟩
      unfold ExactZeroBoundary
      have hconstant := coefficientAt_set_eq polynomial 0#usize q1
        (by scalar_tac)
      have hzero : (0#usize : Std.Usize).val = 0 := by scalar_tac
      rw [hzero] at hconstant
      rw [hconstant, exactPrefix_set_zero]
      calc
        toExact q1 + toExact q1 + exactPrefix polynomial 28 =
            toExact q + exactPrefix polynomial 28 := by rw [hq1Double]
        _ = -toExact tailSum + exactPrefix polynomial 28 := by rw [hqExact]
        _ = -exactPrefix polynomial 28 + exactPrefix polynomial 28 := by
          rw [hprefix28]
        _ = 0 := neg_add_cancel _
  · change 1 ≤ (1#usize : Std.Usize).val ∧
      (1#usize : Std.Usize).val ≤ 28 ∧
      PolynomialCanonical
        (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO) ∧
      Canonical aspis_prover.aspis_core.field.QM31.ZERO ∧
      exactPrefix
          (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO)
          (1#usize : Std.Usize).val =
        toExact aspis_prover.aspis_core.field.QM31.ZERO
    refine ⟨by scalar_tac, by scalar_tac, repeatPolynomial_canonical,
      zero_canonical, ?_⟩
    have hone : (1#usize : Std.Usize).val = 1 := by scalar_tac
    rw [hone]
    exact repeatPolynomial_prefix_one

theorem sample_zero_boundary_round_success
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (polynomial : Polynomial)
    (run : aspis_prover.v5_sumcheck_mask.sample_zero_boundary_round
      sourceInst source = .ok (.Ok polynomial, finalSource)) :
    PolynomialCanonical polynomial ∧ ExactZeroBoundary polynomial := by
  have hSpec := sample_zero_boundary_round_spec sourceInst nextWordTotal source
  simp [run, zeroBoundaryRoundPost, Aeneas.Std.WP.spec,
    Aeneas.Std.WP.theta, Aeneas.Std.WP.wp_return] at hSpec
  exact hSpec

/-! ## Ten-round storage invariant -/

abbrev RoundArray := Array Polynomial 10#usize
abbrev Mask := aspis_prover.v5_sumcheck_mask.V5SumcheckMask

def storedRoundAt (rounds : RoundArray) (round : Nat) : Polynomial :=
  rounds[round]!

def StoredRoundsGood (rounds : RoundArray) (bound : Nat) : Prop :=
  ∀ round : Nat, round < bound →
    PolynomialCanonical (storedRoundAt rounds round) ∧
      ExactZeroBoundary (storedRoundAt rounds round)

private theorem storedRoundAt_set_eq
    (rounds : RoundArray) (round : Std.Usize) (polynomial : Polynomial)
    (hbound : round.val < 10) :
    storedRoundAt (rounds.set round polynomial) round.val = polynomial := by
  unfold storedRoundAt
  rw [Array.getElem!_Nat_set_eq]
  exact ⟨rfl, by simpa using hbound⟩

private theorem storedRoundAt_set_ne
    (rounds : RoundArray) (round : Std.Usize) (polynomial : Polynomial)
    (index : Nat) (hne : round.val ≠ index) :
    storedRoundAt (rounds.set round polynomial) index =
      storedRoundAt rounds index := by
  unfold storedRoundAt
  exact Array.getElem!_Nat_set_ne rounds round index polynomial hne

private theorem storedRoundsGood_set_succ
    (rounds : RoundArray) (round : Std.Usize) (polynomial : Polynomial)
    (hrounds : StoredRoundsGood rounds round.val)
    (hpolynomial : PolynomialCanonical polynomial ∧
      ExactZeroBoundary polynomial)
    (hbound : round.val < 10) :
    StoredRoundsGood (rounds.set round polynomial) (round.val + 1) := by
  intro index hindex
  by_cases heq : round.val = index
  · subst index
    rw [storedRoundAt_set_eq rounds round polynomial hbound]
    exact hpolynomial
  · rw [storedRoundAt_set_ne rounds round polynomial index heq]
    apply hrounds index
    omega

private def outerInvariant {S : Type}
    (state : S × RoundArray × Std.Usize) : Prop :=
  state.2.2.val ≤ 10 ∧ StoredRoundsGood state.2.1 state.2.2.val

private def completeMaskPost {S : Type}
    (result : core.result.Result Mask
      aspis_prover.v5_mask.MaskSampleExhausted × S) : Prop :=
  match result.1 with
  | .Ok mask =>
      Canonical mask.initial_claim ∧
        StoredRoundsGood mask.zero_boundary_rounds 10
  | .Err _ => True

private theorem usize_wrapping_add_one_val_of_lt_28
    (value : Std.Usize) (hvalue : value.val < 28) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Usize.wrapping_add_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by scalar_tac
  rw [hone]
  apply Nat.mod_eq_of_lt
  cases System.Platform.numBits_eq <;>
    simp [Usize.size, Usize.numBits, *] <;> omega

private theorem sample_loop_spec
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) (initialClaim : SamplerQM31)
    (hInitialClaim : Canonical initialClaim) :
    aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample_loop
      sourceInst source initialClaim
      (Array.repeat 10#usize
        (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO))
      0#usize ⦃ result => completeMaskPost result ⦄ := by
  simp only [aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample_loop]
  apply loop.spec_decr_nat
    (fun state => 10 - state.2.2.val)
    outerInvariant completeMaskPost
  · rintro ⟨currentSource, rounds, round⟩ ⟨hupper, hrounds⟩
    simp only at hupper hrounds
    unfold aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample_loop.body
    by_cases hlt : round.val < 10
    · obtain ⟨roundResultPair, hroundRun, hroundPost⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (sample_zero_boundary_round_spec sourceInst nextWordTotal currentSource)
      rcases roundResultPair with ⟨roundResult, nextSource⟩
      cases roundResult with
      | Err error =>
        simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
          hlt, hroundRun, completeMaskPost]
      | Ok polynomial =>
        change PolynomialCanonical polynomial ∧
          ExactZeroBoundary polynomial at hroundPost
        obtain ⟨updated, hupdate, hupdated⟩ := Aeneas.Std.WP.spec_imp_exists
          (Array.update_spec rounds round polynomial (by simpa using hlt))
        subst updated
        have hgood := storedRoundsGood_set_succ rounds round polynomial
          hrounds hroundPost hlt
        have hincrement :
            (Std.Usize.wrapping_add round 1#usize).val = round.val + 1 :=
          usize_wrapping_add_one_val_of_lt_28 round (by omega)
        simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
          hlt, hroundRun, hupdate, lift, outerInvariant, hgood, hincrement]
        omega
    · have heq : round.val = 10 := by omega
      simp [aspis_prover.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
        hlt, completeMaskPost, hInitialClaim]
      simpa [heq] using hrounds
  · change (0#usize : Std.Usize).val ≤ 10 ∧
      StoredRoundsGood
        (Array.repeat 10#usize
          (Array.repeat 28#usize aspis_prover.aspis_core.field.QM31.ZERO))
        (0#usize : Std.Usize).val
    constructor
    · scalar_tac
    · intro round hround
      have hzero : (0#usize : Std.Usize).val = 0 := by scalar_tac
      rw [hzero] at hround
      omega

/-- The exact authentic `V5SumcheckMask::sample` call returns a canonical
initial claim and ten canonical zero-boundary round polynomials. -/
theorem V5SumcheckMask_sample_spec
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source : S) :
    aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample sourceInst source
      ⦃ result => completeMaskPost result ⦄ := by
  obtain ⟨initialResult, nextSource, hinitialRun, hinitialPost⟩ :=
    sample_qm31_total sourceInst nextWordTotal source
  cases initialResult with
  | Err error =>
    simp [aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample,
      hinitialRun, completeMaskPost]
  | Ok initialClaim =>
    have hLoop := sample_loop_spec sourceInst nextWordTotal nextSource
      initialClaim hinitialPost
    simpa [aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample,
      hinitialRun] using hLoop

theorem V5SumcheckMask_sample_success
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (mask : Mask)
    (run : aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample
      sourceInst source = .ok (.Ok mask, finalSource)) :
    Canonical mask.initial_claim ∧
      ∀ round : Fin 10,
        PolynomialCanonical (storedRoundAt mask.zero_boundary_rounds round.val) ∧
          ExactZeroBoundary (storedRoundAt mask.zero_boundary_rounds round.val) := by
  have hSpec := V5SumcheckMask_sample_spec sourceInst nextWordTotal source
  simp [run, completeMaskPost, Aeneas.Std.WP.spec,
    Aeneas.Std.WP.theta, Aeneas.Std.WP.wp_return] at hSpec
  refine ⟨hSpec.1, ?_⟩
  intro round
  exact hSpec.2 round.val round.isLt

#print axioms sample_m31_success_canonical
#print axioms sample_m31_total
#print axioms sample_qm31_success_canonical
#print axioms sample_qm31_total
#print axioms sample_qm31_spec
#print axioms zero_canonical
#print axioms toExact_zero
#print axioms sampler_add_map
#print axioms sampler_add_run_to_additive
#print axioms sampler_add_exact
#print axioms sampler_add_total
#print axioms sampler_neg_map
#print axioms sampler_neg_run_to_additive
#print axioms sampler_neg_exact
#print axioms sampler_neg_total
#print axioms sampler_half_map
#print axioms sampler_half_run_to_authenticated
#print axioms sampler_half_exact
#print axioms sampler_half_total
#print axioms sample_zero_boundary_round_spec
#print axioms sample_zero_boundary_round_success
#print axioms V5SumcheckMask_sample_spec
#print axioms V5SumcheckMask_sample_success

end ComponentBSamplerZeroBoundary
