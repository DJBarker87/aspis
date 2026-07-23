import ComponentBBoundaryProof
import ComponentBHalfProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.v5_sumcheck_mask

private abbrev QM31 := aspis_core.field.QM31
private abbrev Polynomial := Array QM31 28#usize
private abbrev M31Exact := BoundaryM31Exact

def extractedQM31Zero : QM31 :=
  ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

def roundStored (mask : V5SumcheckMask) (round : Std.Usize)
    (hround : round.val < 10) : Polynomial :=
  mask.zero_boundary_rounds.val[round.val]'(by simpa using hround)

private theorem generatedM31AddExactOfRun
    (x y out : Std.U32)
    (hx : x.val < 2147483647) (hy : y.val < 2147483647)
    (hrun : ComponentBGenerated.aspis_core.field.M31.add x y = .ok out) :
    out.val < 2147483647 ∧
    ((out.val : Nat) : M31Exact) =
      (x.val : M31Exact) + (y.val : M31Exact) := by
  let sum := Std.U32.wrapping_add x y
  have hsumBound : x.val + y.val < 4294967296 := by omega
  have hsumVal : sum.val = x.val + y.val := by
    unfold sum
    rw [U32.wrapping_add_val_eq]
    have hsize : UScalar.size .U32 = 4294967296 := by
      simp [U32.size, U32.numBits]
    rw [hsize, Nat.mod_eq_of_lt hsumBound]
  by_cases hhigh : 2147483647 ≤ x.val + y.val
  · have hbranch : sum >= aspis_core.field.P := by
      change aspis_core.field.P.val ≤ sum.val
      unfold aspis_core.field.P
      simpa [hsumVal] using hhigh
    have hsubVal :
        (Std.U32.wrapping_sub sum aspis_core.field.P).val =
          x.val + y.val - 2147483647 := by
      rw [U32.wrapping_sub_val_eq]
      have hsize : UScalar.size .U32 = 4294967296 := by
        simp [U32.size, U32.numBits]
      rw [hsize, hsumVal]
      unfold aspis_core.field.P
      norm_num
      have hreduced : x.val + y.val - 2147483647 < 4294967296 := by
        omega
      have hrewrite :
          x.val + y.val + (4294967296 - 2147483647) =
            (x.val + y.val - 2147483647) + 4294967296 := by
        omega
      rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hreduced]
    unfold aspis_core.field.M31.add at hrun
    simp only [lift, bind_tc_ok] at hrun
    rw [if_pos hbranch] at hrun
    have hout : out = Std.U32.wrapping_sub sum aspis_core.field.P := by
      exact (Result.ok.inj hrun).symm
    subst out
    constructor
    · rw [hsubVal]
      omega
    · rw [hsubVal, Nat.cast_sub hhigh, Nat.cast_add,
        ZMod.natCast_self, sub_zero]
  · have hbranch : ¬ sum >= aspis_core.field.P := by
      intro h
      apply hhigh
      change aspis_core.field.P.val ≤ sum.val at h
      unfold aspis_core.field.P at h
      simpa [hsumVal] using h
    unfold aspis_core.field.M31.add at hrun
    simp only [lift, bind_tc_ok] at hrun
    rw [if_neg hbranch] at hrun
    have hout : out = sum := (Result.ok.inj hrun).symm
    subst out
    constructor
    · rw [hsumVal]
      omega
    · rw [hsumVal, Nat.cast_add]

private theorem generatedQM31AddExactOfRun
    (x y out : QM31)
    (hx : BoundaryCanonicalQM31 x) (hy : BoundaryCanonicalQM31 y)
    (hrun : aspis_core.field.QM31.add x y = .ok out) :
    BoundaryCanonicalQM31 out ∧
    ((out.c0.a.val : Nat) : M31Exact) =
        (x.c0.a.val : M31Exact) + (y.c0.a.val : M31Exact) ∧
    ((out.c0.b.val : Nat) : M31Exact) =
        (x.c0.b.val : M31Exact) + (y.c0.b.val : M31Exact) ∧
    ((out.c1.a.val : Nat) : M31Exact) =
        (x.c1.a.val : M31Exact) + (y.c1.a.val : M31Exact) ∧
    ((out.c1.b.val : Nat) : M31Exact) =
        (x.c1.b.val : M31Exact) + (y.c1.b.val : M31Exact) := by
  unfold aspis_core.field.QM31.add aspis_core.field.CM31.add at hrun
  cases h0 : aspis_core.field.M31.add x.c0.a y.c0.a with
  | fail error =>
    rw [h0] at hrun
    simp at hrun
  | div =>
    rw [h0] at hrun
    simp at hrun
  | ok o00 =>
    rw [h0] at hrun
    simp only [bind_tc_ok] at hrun
    cases h1 : aspis_core.field.M31.add x.c0.b y.c0.b with
    | fail error =>
      rw [h1] at hrun
      simp at hrun
    | div =>
      rw [h1] at hrun
      simp at hrun
    | ok o01 =>
      rw [h1] at hrun
      simp only [bind_tc_ok] at hrun
      cases h2 : aspis_core.field.M31.add x.c1.a y.c1.a with
      | fail error =>
          rw [h2] at hrun
          simp at hrun
      | div =>
          rw [h2] at hrun
          simp at hrun
      | ok o10 =>
        rw [h2] at hrun
        simp only [bind_tc_ok] at hrun
        cases h3 : aspis_core.field.M31.add x.c1.b y.c1.b with
        | fail error =>
            rw [h3] at hrun
            simp at hrun
        | div =>
            rw [h3] at hrun
            simp at hrun
        | ok o11 =>
          rw [h3] at hrun
          simp only [bind_tc_ok] at hrun
          have hout : out = ⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩ := by
            exact (Result.ok.inj hrun).symm
          subst out
          have e00 := generatedM31AddExactOfRun x.c0.a y.c0.a o00
            hx.1 hy.1 h0
          have e01 := generatedM31AddExactOfRun x.c0.b y.c0.b o01
            hx.2.1 hy.2.1 h1
          have e10 := generatedM31AddExactOfRun x.c1.a y.c1.a o10
            hx.2.2.1 hy.2.2.1 h2
          have e11 := generatedM31AddExactOfRun x.c1.b y.c1.b o11
            hx.2.2.2 hy.2.2.2 h3
          exact ⟨⟨e00.1, e01.1, e10.1, e11.1⟩,
            e00.2, e01.2, e10.2, e11.2⟩

private theorem generatedM31AddTotal (x y : Std.U32) :
    ∃ out, aspis_core.field.M31.add x y = .ok out := by
  unfold aspis_core.field.M31.add
  simp only [lift, bind_tc_ok]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem generatedQM31AddTotal (x y : QM31) :
    ∃ out, aspis_core.field.QM31.add x y = .ok out := by
  obtain ⟨o00, h00⟩ := generatedM31AddTotal x.c0.a y.c0.a
  obtain ⟨o01, h01⟩ := generatedM31AddTotal x.c0.b y.c0.b
  obtain ⟨o10, h10⟩ := generatedM31AddTotal x.c1.a y.c1.a
  obtain ⟨o11, h11⟩ := generatedM31AddTotal x.c1.b y.c1.b
  exact ⟨⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩, by
    simp [aspis_core.field.QM31.add, aspis_core.field.CM31.add,
      h00, h01, h10, h11]⟩

private theorem boundaryTailSetZero
    (polynomial : Polynomial) (updated : QM31) :
    boundaryTail (polynomial.set 0#usize updated) =
      boundaryTail polynomial := by
  unfold boundaryTail
  rw [Array.set_val_eq]
  cases hvalues : polynomial.val with
  | nil =>
      have hlength := polynomial.property
      simp [hvalues] at hlength
  | cons value values => simp

private theorem setZeroFirst
    (polynomial : Polynomial) (updated : QM31) :
    (polynomial.set 0#usize updated).val[0] = updated := by
  simp [Array.set_val_eq]

private theorem canonicalM31ExactInjective
    (x y : Std.U32) (hx : x.val < 2147483647)
    (hy : y.val < 2147483647)
    (heq : ((x.val : Nat) : M31Exact) = (y.val : Nat)) : x = y := by
  apply UScalar.eq_of_val_eq
  have hval := congrArg ZMod.val heq
  simpa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hval

private theorem cm31ExtFields
    (x y : aspis_core.field.CM31) (ha : x.a = y.a) (hb : x.b = y.b) :
    x = y := by
  cases x
  cases y
  simp_all

private theorem qm31ExtFields
    (x y : QM31) (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x
  cases y
  simp_all

private theorem exactQM31Injective
    (x y : QM31) (hx : BoundaryCanonicalQM31 x)
    (hy : BoundaryCanonicalQM31 y)
    (h00 : ((x.c0.a.val : Nat) : M31Exact) = y.c0.a.val)
    (h01 : ((x.c0.b.val : Nat) : M31Exact) = y.c0.b.val)
    (h10 : ((x.c1.a.val : Nat) : M31Exact) = y.c1.a.val)
    (h11 : ((x.c1.b.val : Nat) : M31Exact) = y.c1.b.val) : x = y := by
  have e00 := canonicalM31ExactInjective x.c0.a y.c0.a hx.1 hy.1 h00
  have e01 := canonicalM31ExactInjective x.c0.b y.c0.b hx.2.1 hy.2.1 h01
  have e10 := canonicalM31ExactInjective x.c1.a y.c1.a hx.2.2.1 hy.2.2.1 h10
  have e11 := canonicalM31ExactInjective x.c1.b y.c1.b hx.2.2.2 hy.2.2.2 h11
  have ec0 : x.c0 = y.c0 := cm31ExtFields x.c0 y.c0 e00 e01
  have ec1 : x.c1 = y.c1 := cm31ExtFields x.c1 y.c1 e10 e11
  exact qm31ExtFields x y ec0 ec1

private theorem updatedFormulaEqIncoming
    (base half updated incoming : Std.U32) (tail : Nat)
    (hbase : ((2 * base.val + tail : Nat) : M31Exact) = 0)
    (hupdated : ((updated.val : Nat) : M31Exact) =
      (base.val : M31Exact) + (half.val : M31Exact))
    (hdouble : ((incoming.val : Nat) : M31Exact) =
      (half.val : M31Exact) + (half.val : M31Exact)) :
    ((2 * updated.val + tail : Nat) : M31Exact) =
      (incoming.val : M31Exact) := by
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hbase ⊢
  rw [hupdated]
  calc
    2 * ((base.val : M31Exact) + (half.val : M31Exact)) +
        (tail : M31Exact) =
      (2 * (base.val : M31Exact) + (tail : M31Exact)) +
        ((half.val : M31Exact) + (half.val : M31Exact)) := by ring
    _ = 0 + ((half.val : M31Exact) + (half.val : M31Exact)) := by
      rw [hbase]
    _ = (incoming.val : M31Exact) := by simpa [hdouble]

/-- Conditional endpoint theorem for the actual extracted round constructor.
    The stored-zero-boundary premise is explicit because the extracted Rust
    structure permits arbitrary stored arrays; its field name alone does not
    establish this invariant. -/
theorem generated_round_polynomial_endpoint
    (mask : V5SumcheckMask) (round : Std.Usize) (incoming : QM31)
    (hround : round.val < 10)
    (hincoming : BoundaryCanonicalQM31 incoming)
    (hstoredCanonical :
      BoundaryCanonicalQM31 (roundStored mask round hround).val[0])
    (hstoredZero :
      aspis_core.state_only_sumcheck.state_only_boundary_sum
          (roundStored mask round hround) = .ok extractedQM31Zero) :
    ∃ output,
      V5SumcheckMask.round_polynomial mask round incoming = .ok (some output) ∧
      aspis_core.state_only_sumcheck.state_only_boundary_sum output =
        .ok incoming := by
  have hincomingHalf : ComponentBGenerated.CanonicalQM31 incoming := by
    simpa [ComponentBGenerated.CanonicalQM31, BoundaryCanonicalQM31] using hincoming
  obtain ⟨half, hhalf, hhalfCanonical, hdouble⟩ :=
    ComponentBGenerated.generated_qm31_half_doubles_canonical incoming hincomingHalf
  have hhalfBoundary : BoundaryCanonicalQM31 half := by
    simpa [ComponentBGenerated.CanonicalQM31, BoundaryCanonicalQM31] using
      hhalfCanonical
  obtain ⟨updated, hupdated⟩ := generatedQM31AddTotal
    (roundStored mask round hround).val[0] half
  have hupdatedExact := generatedQM31AddExactOfRun
    (roundStored mask round hround).val[0] half updated
    hstoredCanonical hhalfBoundary hupdated
  have hdoubleExact := generatedQM31AddExactOfRun half half incoming
    hhalfBoundary hhalfBoundary hdouble

  obtain ⟨storedBoundary, hstoredBoundaryRun, _hstoredBoundaryCanonical,
      hstored00, hstored01, hstored10, hstored11⟩ :=
    generated_boundary_sum_exact (roundStored mask round hround)
  have hstoredBoundaryEq : storedBoundary = extractedQM31Zero := by
    rw [hstoredZero] at hstoredBoundaryRun
    exact (Result.ok.inj hstoredBoundaryRun).symm
  have hbase00 :
      ((2 * (roundStored mask round hround).val[0].c0.a.val +
        boundaryRawC0ASum (boundaryTail (roundStored mask round hround)) :
          Nat) : M31Exact) = 0 := by
    rw [hstoredBoundaryEq] at hstored00
    simpa [extractedQM31Zero] using hstored00.symm
  have hbase01 :
      ((2 * (roundStored mask round hround).val[0].c0.b.val +
        boundaryRawC0BSum (boundaryTail (roundStored mask round hround)) :
          Nat) : M31Exact) = 0 := by
    rw [hstoredBoundaryEq] at hstored01
    simpa [extractedQM31Zero] using hstored01.symm
  have hbase10 :
      ((2 * (roundStored mask round hround).val[0].c1.a.val +
        boundaryRawC1ASum (boundaryTail (roundStored mask round hround)) :
          Nat) : M31Exact) = 0 := by
    rw [hstoredBoundaryEq] at hstored10
    simpa [extractedQM31Zero] using hstored10.symm
  have hbase11 :
      ((2 * (roundStored mask round hround).val[0].c1.b.val +
        boundaryRawC1BSum (boundaryTail (roundStored mask round hround)) :
          Nat) : M31Exact) = 0 := by
    rw [hstoredBoundaryEq] at hstored11
    simpa [extractedQM31Zero] using hstored11.symm

  let output : Polynomial :=
    (roundStored mask round hround).set 0#usize updated
  obtain ⟨boundaryOutput, hboundaryRun, hboundaryCanonical,
      hboundary00, hboundary01, hboundary10, hboundary11⟩ :=
    generated_boundary_sum_exact output
  have houtputFirst : output.val[0] = updated := by
    exact setZeroFirst (roundStored mask round hround) updated
  have houtputTail : boundaryTail output =
      boundaryTail (roundStored mask round hround) := by
    exact boundaryTailSetZero (roundStored mask round hround) updated
  rw [houtputFirst, houtputTail] at hboundary00 hboundary01
  rw [houtputFirst, houtputTail] at hboundary10 hboundary11
  have hout00 : ((boundaryOutput.c0.a.val : Nat) : M31Exact) =
      (incoming.c0.a.val : M31Exact) := hboundary00.trans
    (updatedFormulaEqIncoming _ _ _ _ _ hbase00
      hupdatedExact.2.1 hdoubleExact.2.1)
  have hout01 : ((boundaryOutput.c0.b.val : Nat) : M31Exact) =
      (incoming.c0.b.val : M31Exact) := hboundary01.trans
    (updatedFormulaEqIncoming _ _ _ _ _ hbase01
      hupdatedExact.2.2.1 hdoubleExact.2.2.1)
  have hout10 : ((boundaryOutput.c1.a.val : Nat) : M31Exact) =
      (incoming.c1.a.val : M31Exact) := hboundary10.trans
    (updatedFormulaEqIncoming _ _ _ _ _ hbase10
      hupdatedExact.2.2.2.1 hdoubleExact.2.2.2.1)
  have hout11 : ((boundaryOutput.c1.b.val : Nat) : M31Exact) =
      (incoming.c1.b.val : M31Exact) := hboundary11.trans
    (updatedFormulaEqIncoming _ _ _ _ _ hbase11
      hupdatedExact.2.2.2.2 hdoubleExact.2.2.2.2)
  have hboundaryOutputEq : boundaryOutput = incoming :=
    exactQM31Injective boundaryOutput incoming hboundaryCanonical hincoming
      hout00 hout01 hout10 hout11
  have houtputBoundary :
      aspis_core.state_only_sumcheck.state_only_boundary_sum output =
        .ok incoming := by
    simpa [hboundaryOutputEq] using hboundaryRun

  have hsome : mask.zero_boundary_rounds.val[round.val]? =
      some (roundStored mask round hround) := by
    simp [roundStored, hround]
  refine ⟨output, ?_, houtputBoundary⟩
  simp [V5SumcheckMask.round_polynomial, lift, Array.to_slice,
    core.slice.Slice.get, core.slice.index.Usize.get, hsome, hhalf, hupdated,
    Array.index_usize, Array.update, output]
  apply Subtype.ext
  rfl

#print axioms generated_round_polynomial_endpoint

end ComponentBGenerated.v5_sumcheck_mask
