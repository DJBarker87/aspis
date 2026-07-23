-- Retained Component-B mixed-endpoint proof over the generated production graph.
import ComponentBMixingProof
import ComponentBEndpointProof
import ComponentBRoundMixingProof
import MultilinearEvalFormula

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.v5_sumcheck_mask

open ComponentBGenerated.MultilinearEvalProofs

private abbrev QM31 := aspis_core.field.QM31
private abbrev Polynomial := Array QM31 28#usize

private theorem boundaryCanonicalIffGenerated (x : QM31) :
    BoundaryCanonicalQM31 x ↔ GeneratedCanonicalQM31 x := by
  simp [BoundaryCanonicalQM31, GeneratedCanonicalQM31,
    GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem exactSumC0A (values : List QM31) :
    ((values.map generatedQm31ToExact).sum).re.re =
      (values.map (fun value =>
        ((value.c0.a.val : Nat) : ExactM31))).sum := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        inductionHypothesis]

private theorem exactSumC0B (values : List QM31) :
    ((values.map generatedQm31ToExact).sum).re.im =
      (values.map (fun value =>
        ((value.c0.b.val : Nat) : ExactM31))).sum := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        inductionHypothesis]

private theorem exactSumC1A (values : List QM31) :
    ((values.map generatedQm31ToExact).sum).im.re =
      (values.map (fun value =>
        ((value.c1.a.val : Nat) : ExactM31))).sum := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        inductionHypothesis]

private theorem exactSumC1B (values : List QM31) :
    ((values.map generatedQm31ToExact).sum).im.im =
      (values.map (fun value =>
        ((value.c1.b.val : Nat) : ExactM31))).sum := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [generatedQm31ToExact, generatedCm31ToExact,
        inductionHypothesis]

private theorem mapSumHeadTail {R : Type} [AddCommMonoid R]
    (polynomial : Polynomial) (f : QM31 → R) :
    (polynomial.val.map f).sum =
      f polynomial.val[0] + (polynomial.val.tail.map f).sum := by
  have hnonempty : polynomial.val ≠ [] := by
    intro hempty
    have hlength := polynomial.property
    rw [hempty] at hlength
    simp at hlength
  calc
    (polynomial.val.map f).sum =
        ((polynomial.val.head hnonempty :: polynomial.val.tail).map f).sum := by
      rw [List.cons_head_tail hnonempty]
    _ = f polynomial.val[0] + (polynomial.val.tail.map f).sum := by
      rw [List.head_eq_getElem hnonempty]
      rfl

def exactBoundary (polynomial : Polynomial) : ExactQM31 :=
  generatedQm31ToExact polynomial.val[0] +
    (polynomial.val.map generatedQm31ToExact).sum

theorem generatedBoundaryCorresponds (polynomial : Polynomial) :
    ∃ output,
      aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial =
        .ok output ∧
      GeneratedCanonicalQM31 output ∧
      generatedQm31ToExact output = exactBoundary polynomial := by
  obtain ⟨output, hcall, hcanonical, h00, h01, h10, h11⟩ :=
    generated_boundary_sum_exact polynomial
  refine ⟨output, hcall, (boundaryCanonicalIffGenerated output).mp hcanonical, ?_⟩
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · change
        (((output.c0.a.val : Nat) : ExactM31)) =
          (exactBoundary polynomial).re.re
      rw [h00]
      simp [exactBoundary, generatedQm31ToExact, generatedCm31ToExact,
        boundaryRawC0ASum, boundaryTail, exactSumC0A]
      rw [mapSumHeadTail polynomial]
      simp [Function.comp_def]
      ring
    · change
        (((output.c0.b.val : Nat) : ExactM31)) =
          (exactBoundary polynomial).re.im
      rw [h01]
      simp [exactBoundary, generatedQm31ToExact, generatedCm31ToExact,
        boundaryRawC0BSum, boundaryTail, exactSumC0B]
      rw [mapSumHeadTail polynomial]
      simp [Function.comp_def]
      ring
  · apply QuadraticAlgebra.ext
    · change
        (((output.c1.a.val : Nat) : ExactM31)) =
          (exactBoundary polynomial).im.re
      rw [h10]
      simp [exactBoundary, generatedQm31ToExact, generatedCm31ToExact,
        boundaryRawC1ASum, boundaryTail, exactSumC1A]
      rw [mapSumHeadTail polynomial]
      simp [Function.comp_def]
      ring
    · change
        (((output.c1.b.val : Nat) : ExactM31)) =
          (exactBoundary polynomial).im.im
      rw [h11]
      simp [exactBoundary, generatedQm31ToExact, generatedCm31ToExact,
        boundaryRawC1BSum, boundaryTail, exactSumC1B]
      rw [mapSumHeadTail polynomial]
      simp [Function.comp_def]
      ring

private theorem sumZipLinear
    (etaExact : ExactQM31) (base real : List ExactQM31)
    (sameLength : base.length = real.length) :
    (List.zipWith (fun x y => x + etaExact * y) base real).sum =
      base.sum + etaExact * real.sum := by
  induction base generalizing real with
  | nil =>
      have realEmpty : real = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using sameLength.symm)
      subst real
      simp
  | cons value base inductionHypothesis =>
      cases real with
      | nil => simp at sameLength
      | cons realValue real =>
          simp only [List.length_cons] at sameLength
          have tailsSame : base.length = real.length := by omega
          simp [inductionHypothesis real tailsSame]
          ring

private theorem exactMapEqZip
    (eta : QM31) (output base real : Polynomial)
    (pointwise : ∀ i : Fin 28,
      generatedQm31ToExact output.val[i.val] =
        generatedQm31ToExact base.val[i.val] +
          generatedQm31ToExact eta *
            generatedQm31ToExact real.val[i.val]) :
    output.val.map generatedQm31ToExact =
      List.zipWith
        (fun x y => x + generatedQm31ToExact eta * y)
        (base.val.map generatedQm31ToExact)
        (real.val.map generatedQm31ToExact) := by
  apply List.ext_getElem
  · simp [output.property, base.property, real.property]
  · intro index outputBound zipBound
    have indexBound : index < 28 := by
      simpa [output.property] using outputBound
    simpa using pointwise ⟨index, indexBound⟩

theorem exactBoundaryLinear
    (eta : QM31) (output base real : Polynomial)
    (pointwise : ∀ i : Fin 28,
      generatedQm31ToExact output.val[i.val] =
        generatedQm31ToExact base.val[i.val] +
          generatedQm31ToExact eta *
            generatedQm31ToExact real.val[i.val]) :
    exactBoundary output = exactBoundary base +
      generatedQm31ToExact eta * exactBoundary real := by
  have mapped := exactMapEqZip eta output base real pointwise
  have mappedSum := congrArg List.sum mapped
  have baseRealLength :
      (base.val.map generatedQm31ToExact).length =
        (real.val.map generatedQm31ToExact).length := by simp
  rw [sumZipLinear (generatedQm31ToExact eta) _ _ baseRealLength]
    at mappedSum
  have zeroPoint := pointwise ⟨0, by norm_num⟩
  unfold exactBoundary
  rw [mappedSum, zeroPoint]
  ring

private theorem generatedQm31AddOfRun
    (x y out : QM31)
    (hx : GeneratedCanonicalQM31 x) (hy : GeneratedCanonicalQM31 y)
    (run : aspis_core.field.QM31.add x y = .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generated_qm31_add_corresponds x y hx hy
  have outputEq : out = candidate :=
    Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

private theorem generatedQm31SubOfRun
    (x y out : QM31)
    (hx : GeneratedCanonicalQM31 x) (hy : GeneratedCanonicalQM31 y)
    (run : aspis_core.field.QM31.sub x y = .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x - generatedQm31ToExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generated_qm31_sub_corresponds x y hx hy
  have outputEq : out = candidate :=
    Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

private theorem generatedQm31MulOfRun
    (x y out : QM31)
    (hx : GeneratedCanonicalQM31 x) (hy : GeneratedCanonicalQM31 y)
    (run : aspis_core.field.QM31.mul x y = .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generated_qm31_mul_corresponds x y hx hy
  have outputEq : out = candidate :=
    Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

private theorem generatedBoundaryOfRun
    (polynomial : Polynomial) (out : QM31)
    (run :
      aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial =
        .ok out) :
    GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = exactBoundary polynomial := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    generatedBoundaryCorresponds polynomial
  have outputEq : out = candidate :=
    Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

private theorem canonicalM31ExactInjective
    (x y : Std.U32) (hx : x.val < 2147483647)
    (hy : y.val < 2147483647)
    (exactEq : (((x.val : Nat) : ExactM31)) =
      ((y.val : Nat) : ExactM31)) : x = y := by
  apply UScalar.eq_of_val_eq
  have valueEq := congrArg ZMod.val exactEq
  simpa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using valueEq

theorem generatedQm31ToExactInjective
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y)
    (exactEq : generatedQm31ToExact x = generatedQm31ToExact y) :
    x = y := by
  have exact00 := congrArg (fun value : ExactQM31 => value.re.re) exactEq
  have exact01 := congrArg (fun value : ExactQM31 => value.re.im) exactEq
  have exact10 := congrArg (fun value : ExactQM31 => value.im.re) exactEq
  have exact11 := congrArg (fun value : ExactQM31 => value.im.im) exactEq
  have boundX00 : x.c0.a.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hx.1.1
  have boundX01 : x.c0.b.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hx.1.2
  have boundX10 : x.c1.a.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hx.2.1
  have boundX11 : x.c1.b.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hx.2.2
  have boundY00 : y.c0.a.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hy.1.1
  have boundY01 : y.c0.b.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hy.1.2
  have boundY10 : y.c1.a.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hy.2.1
  have boundY11 : y.c1.b.val < 2147483647 := by
    simpa [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hy.2.2
  have limb00 : x.c0.a = y.c0.a := canonicalM31ExactInjective
    x.c0.a y.c0.a boundX00 boundY00 (by
      simpa [generatedQm31ToExact, generatedCm31ToExact] using exact00)
  have limb01 : x.c0.b = y.c0.b := canonicalM31ExactInjective
    x.c0.b y.c0.b boundX01 boundY01 (by
      simpa [generatedQm31ToExact, generatedCm31ToExact] using exact01)
  have limb10 : x.c1.a = y.c1.a := canonicalM31ExactInjective
    x.c1.a y.c1.a boundX10 boundY10 (by
      simpa [generatedQm31ToExact, generatedCm31ToExact] using exact10)
  have limb11 : x.c1.b = y.c1.b := canonicalM31ExactInjective
    x.c1.b y.c1.b boundX11 boundY11 (by
      simpa [generatedQm31ToExact, generatedCm31ToExact] using exact11)
  rcases x with ⟨⟨x00, x01⟩, ⟨x10, x11⟩⟩
  rcases y with ⟨⟨y00, y01⟩, ⟨y10, y11⟩⟩
  simp_all

private theorem setZeroAt
    (polynomial : Polynomial) (updated : QM31) (i : Fin 28) :
    ((polynomial.set 0#usize updated).val[i.val]) =
      if i.val = 0 then updated else polynomial.val[i.val] := by
  have outputBound :
      i.val < (polynomial.set 0#usize updated).val.length := by simp
  have optionalOutput :
      (polynomial.set 0#usize updated).val[i.val]? =
        some ((polynomial.set 0#usize updated).val[i.val]) := by
    exact List.getElem?_eq_getElem outputBound
  have optionalExact :
      (polynomial.set 0#usize updated).val[i.val]? =
        some (if i.val = 0 then updated else polynomial.val[i.val]) := by
    rw [Array.set_val_eq]
    by_cases indexZero : i.val = 0
    · simp [indexZero]
    · rw [List.getElem?_set_ne]
      · simp [indexZero]
      · exact Ne.symm indexZero
  rw [optionalOutput] at optionalExact
  exact Option.some.inj optionalExact

private theorem generatedRoundExactUpdatePublic
    (mask : V5SumcheckMask) (round : Std.Usize)
    (incoming half updated : QM31) (hround : round.val < 10)
    (halfCall : aspis_core.field.QM31.half incoming = .ok half)
    (updatedCall :
      aspis_core.field.QM31.add
          (roundStored mask round hround).val[0] half = .ok updated) :
    V5SumcheckMask.round_polynomial mask round incoming =
      .ok (some ((roundStored mask round hround).set 0#usize updated)) := by
  have hsome : mask.zero_boundary_rounds.val[round.val]? =
      some (roundStored mask round hround) := by
    simp [roundStored, hround]
  simp [V5SumcheckMask.round_polynomial, lift, Array.to_slice,
    core.slice.Slice.get, core.slice.index.Usize.get, hsome, halfCall,
    updatedCall, Array.index_usize, Array.update]
  apply Subtype.ext
  rfl

/-- The actual generated mixed-round wrapper has total-claim Boolean boundary.
    The premises are the explicit operational graph shared with the already
    proved actual round endpoint: the real boundary, claim multiplication and
    subtraction, round result, its boundary, and all 28 generated field calls.
    No boundary fact about the mixed output is assumed. -/
private theorem mixedRoundEndpointFromOperationalGraph
    (mask : V5SumcheckMask) (round : Std.Usize)
    (totalClaim eta realClaim claimProduct maskClaim : QM31)
    (real base : Polynomial) (products combined : Fin 28 → QM31)
    (totalCanonical : GeneratedCanonicalQM31 totalClaim)
    (etaCanonical : GeneratedCanonicalQM31 eta)
    (realCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31 real.val[i.val])
    (baseCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31 base.val[i.val])
    (hboundary :
      aspis_core.state_only_sumcheck.state_only_boundary_sum real =
        .ok realClaim)
    (hclaimMul :
      aspis_core.field.QM31.mul eta realClaim = .ok claimProduct)
    (hclaimSub :
      aspis_core.field.QM31.sub totalClaim claimProduct = .ok maskClaim)
    (hround :
      V5SumcheckMask.round_polynomial mask round maskClaim = .ok (some base))
    (hbaseBoundary :
      aspis_core.state_only_sumcheck.state_only_boundary_sum base =
        .ok maskClaim)
    (hmul : ∀ i : Fin 28,
      aspis_core.field.QM31.mul eta real.val[i.val] = .ok (products i))
    (hadd : ∀ i : Fin 28,
      aspis_core.field.QM31.add base.val[i.val] (products i) =
        .ok (combined i)) :
    ∃ output,
      V5SumcheckMask.mixed_round_polynomial
          mask round totalClaim eta real = .ok (some output) ∧
      aspis_core.state_only_sumcheck.state_only_boundary_sum output =
        .ok totalClaim := by
  have realBoundaryFacts := generatedBoundaryOfRun real realClaim hboundary
  have claimProductFacts := generatedQm31MulOfRun
    eta realClaim claimProduct etaCanonical realBoundaryFacts.1 hclaimMul
  have maskClaimFacts := generatedQm31SubOfRun
    totalClaim claimProduct maskClaim totalCanonical claimProductFacts.1
      hclaimSub
  have baseBoundaryFacts := generatedBoundaryOfRun
    base maskClaim hbaseBoundary
  have productFacts : ∀ i : Fin 28,
      GeneratedCanonicalQM31 (products i) ∧
      generatedQm31ToExact (products i) =
        generatedQm31ToExact eta *
          generatedQm31ToExact real.val[i.val] := by
    intro i
    exact generatedQm31MulOfRun eta real.val[i.val] (products i)
      etaCanonical (realCanonical i) (hmul i)
  have combinedFacts : ∀ i : Fin 28,
      GeneratedCanonicalQM31 (combined i) ∧
      generatedQm31ToExact (combined i) =
        generatedQm31ToExact base.val[i.val] +
          generatedQm31ToExact (products i) := by
    intro i
    exact generatedQm31AddOfRun base.val[i.val] (products i) (combined i)
      (baseCanonical i) (productFacts i).1 (hadd i)
  obtain ⟨output, mixedCall, outputPointwise⟩ :=
    generated_mixed_round_polynomial_composition
      mask round totalClaim eta realClaim claimProduct maskClaim
      real base products combined hboundary hclaimMul hclaimSub hround hmul hadd
  obtain ⟨outputBoundary, outputBoundaryCall,
      outputBoundaryCanonical, outputBoundaryExact⟩ :=
    generatedBoundaryCorresponds output
  have outputPointwiseExact : ∀ i : Fin 28,
      generatedQm31ToExact output.val[i.val] =
        generatedQm31ToExact base.val[i.val] +
          generatedQm31ToExact eta *
            generatedQm31ToExact real.val[i.val] := by
    intro i
    rw [outputPointwise i, (combinedFacts i).2, (productFacts i).2]
  have outputLinear :=
    exactBoundaryLinear eta output base real outputPointwiseExact
  have outputExactTotal :
      generatedQm31ToExact outputBoundary =
        generatedQm31ToExact totalClaim := by
    calc
      generatedQm31ToExact outputBoundary = exactBoundary output :=
        outputBoundaryExact
      _ = exactBoundary base +
          generatedQm31ToExact eta * exactBoundary real := outputLinear
      _ = generatedQm31ToExact maskClaim +
          generatedQm31ToExact eta * generatedQm31ToExact realClaim := by
        rw [baseBoundaryFacts.2, realBoundaryFacts.2]
      _ = (generatedQm31ToExact totalClaim -
            generatedQm31ToExact claimProduct) +
          generatedQm31ToExact eta * generatedQm31ToExact realClaim := by
        rw [maskClaimFacts.2]
      _ = (generatedQm31ToExact totalClaim -
            generatedQm31ToExact eta * generatedQm31ToExact realClaim) +
          generatedQm31ToExact eta * generatedQm31ToExact realClaim := by
        rw [claimProductFacts.2]
      _ = generatedQm31ToExact totalClaim := by ring
  have outputBoundaryEq : outputBoundary = totalClaim :=
    generatedQm31ToExactInjective outputBoundary totalClaim
      outputBoundaryCanonical totalCanonical outputExactTotal
  refine ⟨output, mixedCall, ?_⟩
  simpa [outputBoundaryEq] using outputBoundaryCall

/-- The strongest mixed-round endpoint theorem for the extracted deterministic
    Component-B algebra.  Every operational intermediate is produced by an
    actual generated function.  The only state invariant is that the selected
    stored zero-boundary round has canonical coefficients and actual generated
    Boolean boundary zero. -/
theorem generated_mixed_round_polynomial_endpoint
    (mask : V5SumcheckMask) (round : Std.Usize)
    (totalClaim eta : QM31) (real : Polynomial)
    (roundInRange : round.val < 10)
    (totalCanonical : GeneratedCanonicalQM31 totalClaim)
    (etaCanonical : GeneratedCanonicalQM31 eta)
    (realCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31 real.val[i.val])
    (storedCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31
        (roundStored mask round roundInRange).val[i.val])
    (storedZeroBoundary :
      aspis_core.state_only_sumcheck.state_only_boundary_sum
          (roundStored mask round roundInRange) = .ok extractedQM31Zero) :
    ∃ output,
      V5SumcheckMask.mixed_round_polynomial
          mask round totalClaim eta real = .ok (some output) ∧
      aspis_core.state_only_sumcheck.state_only_boundary_sum output =
        .ok totalClaim := by
  obtain ⟨realClaim, realBoundaryCall, realClaimCanonical,
      _realClaimExact⟩ := generatedBoundaryCorresponds real
  obtain ⟨claimProduct, claimMulCall, claimProductCanonical,
      _claimProductExact⟩ := generated_qm31_mul_corresponds
    eta realClaim etaCanonical realClaimCanonical
  obtain ⟨maskClaim, claimSubCall, maskClaimCanonical,
      _maskClaimExact⟩ := generated_qm31_sub_corresponds
    totalClaim claimProduct totalCanonical claimProductCanonical
  have maskClaimBoundaryCanonical : BoundaryCanonicalQM31 maskClaim :=
    (boundaryCanonicalIffGenerated maskClaim).mpr maskClaimCanonical
  have storedZeroCanonical : BoundaryCanonicalQM31
      (roundStored mask round roundInRange).val[0] :=
    (boundaryCanonicalIffGenerated
      (roundStored mask round roundInRange).val[0]).mpr
        (storedCanonical ⟨0, by norm_num⟩)
  obtain ⟨base, roundCall, baseBoundaryCall⟩ :=
    generated_round_polynomial_endpoint mask round maskClaim roundInRange
      maskClaimBoundaryCanonical storedZeroCanonical storedZeroBoundary

  have maskClaimHalfCanonical : ComponentBGenerated.CanonicalQM31 maskClaim := by
    simpa [ComponentBGenerated.CanonicalQM31, GeneratedCanonicalQM31,
      GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using maskClaimCanonical
  obtain ⟨half, halfCall, halfCanonical, _halfDouble⟩ :=
    ComponentBGenerated.generated_qm31_half_doubles_canonical
      maskClaim maskClaimHalfCanonical
  have halfGeneratedCanonical : GeneratedCanonicalQM31 half := by
    simpa [ComponentBGenerated.CanonicalQM31, GeneratedCanonicalQM31,
      GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using halfCanonical
  obtain ⟨updated, updatedCall, updatedCanonical, _updatedExact⟩ :=
    generated_qm31_add_corresponds
      (roundStored mask round roundInRange).val[0] half
      (storedCanonical ⟨0, by norm_num⟩) halfGeneratedCanonical
  have publicRoundUpdate := generatedRoundExactUpdatePublic
    mask round maskClaim half updated roundInRange halfCall updatedCall
  have baseEq :
      base = (roundStored mask round roundInRange).set 0#usize updated := by
    exact Option.some.inj (Result.ok.inj
      (roundCall.symm.trans publicRoundUpdate))
  have baseCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31 base.val[i.val] := by
    intro i
    rw [baseEq, setZeroAt]
    by_cases indexZero : i.val = 0
    · simp [indexZero, updatedCanonical]
    · simp [indexZero, storedCanonical i]

  have productExists : ∀ i : Fin 28, ∃ product,
      aspis_core.field.QM31.mul eta real.val[i.val] = .ok product ∧
      GeneratedCanonicalQM31 product ∧
      generatedQm31ToExact product =
        generatedQm31ToExact eta *
          generatedQm31ToExact real.val[i.val] := by
    intro i
    exact generated_qm31_mul_corresponds eta real.val[i.val]
      etaCanonical (realCanonical i)
  choose products productFacts using productExists
  have productCalls : ∀ i : Fin 28,
      aspis_core.field.QM31.mul eta real.val[i.val] = .ok (products i) :=
    fun i => (productFacts i).1
  have productCanonical : ∀ i : Fin 28,
      GeneratedCanonicalQM31 (products i) :=
    fun i => (productFacts i).2.1
  have combinedExists : ∀ i : Fin 28, ∃ combined,
      aspis_core.field.QM31.add base.val[i.val] (products i) = .ok combined ∧
      GeneratedCanonicalQM31 combined ∧
      generatedQm31ToExact combined =
        generatedQm31ToExact base.val[i.val] +
          generatedQm31ToExact (products i) := by
    intro i
    exact generated_qm31_add_corresponds base.val[i.val] (products i)
      (baseCanonical i) (productCanonical i)
  choose combined combinedFacts using combinedExists
  have combinedCalls : ∀ i : Fin 28,
      aspis_core.field.QM31.add base.val[i.val] (products i) =
        .ok (combined i) := fun i => (combinedFacts i).1
  exact mixedRoundEndpointFromOperationalGraph
    mask round totalClaim eta realClaim claimProduct maskClaim
    real base products combined totalCanonical etaCanonical realCanonical
    baseCanonical realBoundaryCall claimMulCall claimSubCall roundCall
    baseBoundaryCall productCalls combinedCalls

#print axioms generatedBoundaryCorresponds
#print axioms exactBoundaryLinear
#print axioms generatedQm31ToExactInjective
#print axioms generated_mixed_round_polynomial_endpoint

end ComponentBGenerated.v5_sumcheck_mask
