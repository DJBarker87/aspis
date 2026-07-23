import ComponentBSamplerMixingEvaluateUnified20260722
import M31ReduceU64Proof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.v5_sumcheck_mask

private abbrev QM31 := aspis_core.field.QM31
private abbrev Limbs := Array Std.U64 4#usize

def boundaryIterOf (pre suffix : List QM31)
    (h : (pre ++ suffix).length ≤ Std.Usize.max) :
    core.slice.iter.Iter QM31 :=
  { slice := ⟨pre ++ suffix, h⟩
    i := pre.length }

private theorem nextNil
    (pre : List QM31)
    (hLen : (pre ++ []).length ≤ Std.Usize.max) :
    core.slice.iter.IteratorSliceIter.next (boundaryIterOf pre [] hLen) =
      .ok (none, boundaryIterOf pre [] hLen) := by
  rw [core.slice.iter.IteratorSliceIter.next]
  rw [dif_neg (by simp [boundaryIterOf])]

private theorem nextCons
    (pre suffix : List QM31) (coefficient : QM31)
    (hLen : (pre ++ coefficient :: suffix).length ≤ Std.Usize.max)
    (hLen' : ((pre ++ [coefficient]) ++ suffix).length ≤
      Std.Usize.max) :
    core.slice.iter.IteratorSliceIter.next
        (boundaryIterOf pre (coefficient :: suffix) hLen) =
      .ok (some coefficient,
        boundaryIterOf (pre ++ [coefficient]) suffix hLen') := by
  have hiter :
      ({ slice := ⟨pre ++ coefficient :: suffix, hLen⟩
         i := pre.length + 1 } : core.slice.iter.Iter QM31) =
        boundaryIterOf (pre ++ [coefficient]) suffix hLen' := by
    simp [boundaryIterOf, List.append_assoc]
  rw [core.slice.iter.IteratorSliceIter.next]
  rw [dif_pos (by simp [boundaryIterOf])]
  have hbound :
      (boundaryIterOf pre (coefficient :: suffix) hLen).i <
        (boundaryIterOf pre (coefficient :: suffix) hLen).slice.length := by
    simp [boundaryIterOf]
  have hcoefficient :
      (boundaryIterOf pre (coefficient :: suffix) hLen).slice[
        (boundaryIterOf pre (coefficient :: suffix) hLen).i]'hbound =
          coefficient := by
    simp [boundaryIterOf]
  have hit :
      ({ slice := (boundaryIterOf pre (coefficient :: suffix) hLen).slice
         i := (boundaryIterOf pre (coefficient :: suffix) hLen).i + 1 } :
          core.slice.iter.Iter QM31) =
        boundaryIterOf (pre ++ [coefficient]) suffix hLen' := by
    simpa [boundaryIterOf] using hiter
  simp only
  apply congrArg Result.ok
  exact Prod.ext (congrArg Option.some hcoefficient) hit

private def addCoefficient (limbs : Limbs) (coefficient : QM31) : Limbs :=
  let limbs := limbs.set 0#usize
    (Std.U64.wrapping_add limbs.val[0]
      (core.convert.num.FromU64U32.from coefficient.c0.a))
  let limbs := limbs.set 1#usize
    (Std.U64.wrapping_add limbs.val[1]
      (core.convert.num.FromU64U32.from coefficient.c0.b))
  let limbs := limbs.set 2#usize
    (Std.U64.wrapping_add limbs.val[2]
      (core.convert.num.FromU64U32.from coefficient.c1.a))
  limbs.set 3#usize
    (Std.U64.wrapping_add limbs.val[3]
      (core.convert.num.FromU64U32.from coefficient.c1.b))

private def addCoefficients : List QM31 → Limbs → Limbs
  | [], limbs => limbs
  | coefficient :: suffix, limbs =>
      addCoefficients suffix (addCoefficient limbs coefficient)

def boundaryRawC0ASum (coefficients : List QM31) : Nat :=
  (coefficients.map (fun coefficient => coefficient.c0.a.val)).sum

def boundaryRawC0BSum (coefficients : List QM31) : Nat :=
  (coefficients.map (fun coefficient => coefficient.c0.b.val)).sum

def boundaryRawC1ASum (coefficients : List QM31) : Nat :=
  (coefficients.map (fun coefficient => coefficient.c1.a.val)).sum

def boundaryRawC1BSum (coefficients : List QM31) : Nat :=
  (coefficients.map (fun coefficient => coefficient.c1.b.val)).sum

def boundaryTail (polynomial : Array QM31 28#usize) : List QM31 :=
  polynomial.val.drop 1

def boundaryInitialLimbs (polynomial : Array QM31 28#usize) : Limbs :=
  let first := polynomial.val[0]
  Array.make 4#usize
    [ Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from first.c0.a),
      Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from first.c0.b),
      Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from first.c1.a),
      Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from first.c1.b) ]

private theorem boundaryInitialLimbsEqGenerated
    (polynomial : Array QM31 28#usize) :
    boundaryInitialLimbs polynomial =
      Array.make 4#usize
        [ Std.U64.wrapping_mul 2#u64
            (core.convert.num.FromU64U32.from polynomial.val[0].c0.a),
          Std.U64.wrapping_mul 2#u64
            (core.convert.num.FromU64U32.from polynomial.val[0].c0.b),
          Std.U64.wrapping_mul 2#u64
            (core.convert.num.FromU64U32.from polynomial.val[0].c1.a),
          Std.U64.wrapping_mul 2#u64
            (core.convert.num.FromU64U32.from polynomial.val[0].c1.b) ] := by
  apply Subtype.ext
  rfl

private theorem boundaryTailLength
    (polynomial : Array QM31 28#usize) :
    (boundaryTail polynomial).length = 27 := by
  simp [boundaryTail]

private def boundaryTailSlice
    (polynomial : Array QM31 28#usize) : Slice QM31 :=
  ⟨boundaryTail polynomial, by
    rw [boundaryTailLength]
    scalar_tac⟩

private theorem generatedBoundaryTailIterator
    (polynomial : Array QM31 28#usize) :
    ∃ hLen : (boundaryTail polynomial).length ≤ Std.Usize.max,
      core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice QM31))
          polynomial { start := 1#usize } =
        .ok (boundaryTailSlice polynomial) ∧
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          (boundaryTailSlice polynomial) =
        .ok (boundaryIterOf [] (boundaryTail polynomial) hLen) := by
  have hLen : (boundaryTail polynomial).length ≤ Std.Usize.max := by
    rw [boundaryTailLength]
    scalar_tac
  refine ⟨hLen, ?_⟩
  constructor
  · simp [core.array.Array.index, core.ops.index.IndexSlice,
      core.slice.index.SliceIndexRangeFromUsizeSlice,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index,
      Array.to_slice, Slice.drop, boundaryTailSlice, boundaryTail]
  · simp [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      boundaryTailSlice, boundaryTail, boundaryIterOf]

private theorem twiceCastU32Val (x : Std.U32) :
    (Std.U64.wrapping_mul 2#u64
      (core.convert.num.FromU64U32.from x)).val = 2 * x.val := by
  rw [U64.wrapping_mul_val_eq,
    core.convert.num.FromU64U32.from_val_eq]
  apply Nat.mod_eq_of_lt
  have hx := UScalar.hSize x
  simp [U32.size, U32.numBits, U64.size, U64.numBits] at hx ⊢
  omega

private theorem boundaryInitialLimbValues
    (polynomial : Array QM31 28#usize) :
    (boundaryInitialLimbs polynomial).val[0].val =
        2 * polynomial.val[0].c0.a.val ∧
    (boundaryInitialLimbs polynomial).val[1].val =
        2 * polynomial.val[0].c0.b.val ∧
    (boundaryInitialLimbs polynomial).val[2].val =
        2 * polynomial.val[0].c1.a.val ∧
    (boundaryInitialLimbs polynomial).val[3].val =
        2 * polynomial.val[0].c1.b.val := by
  change
    (Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from polynomial.val[0].c0.a)).val =
          2 * polynomial.val[0].c0.a.val ∧
    (Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from polynomial.val[0].c0.b)).val =
          2 * polynomial.val[0].c0.b.val ∧
    (Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from polynomial.val[0].c1.a)).val =
          2 * polynomial.val[0].c1.a.val ∧
    (Std.U64.wrapping_mul 2#u64
        (core.convert.num.FromU64U32.from polynomial.val[0].c1.b)).val =
          2 * polynomial.val[0].c1.b.val
  exact ⟨twiceCastU32Val _, twiceCastU32Val _, twiceCastU32Val _,
    twiceCastU32Val _⟩

private theorem sumU32ValuesLe
    {T : Type} (values : List T) (raw : T → Std.U32) :
    (values.map (fun value => (raw value).val)).sum ≤
      values.length * 4294967295 := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hvalue := UScalar.hSize (raw value)
      simp [U32.size, U32.numBits] at hvalue
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private theorem boundaryNoWrapBounds
    (polynomial : Array QM31 28#usize) :
    (boundaryInitialLimbs polynomial).val[0].val +
        boundaryRawC0ASum (boundaryTail polynomial) < U64.size ∧
    (boundaryInitialLimbs polynomial).val[1].val +
        boundaryRawC0BSum (boundaryTail polynomial) < U64.size ∧
    (boundaryInitialLimbs polynomial).val[2].val +
        boundaryRawC1ASum (boundaryTail polynomial) < U64.size ∧
    (boundaryInitialLimbs polynomial).val[3].val +
        boundaryRawC1BSum (boundaryTail polynomial) < U64.size := by
  have hfirst00 := UScalar.hSize polynomial.val[0].c0.a
  have hfirst01 := UScalar.hSize polynomial.val[0].c0.b
  have hfirst10 := UScalar.hSize polynomial.val[0].c1.a
  have hfirst11 := UScalar.hSize polynomial.val[0].c1.b
  simp [U32.size, U32.numBits] at hfirst00 hfirst01 hfirst10 hfirst11
  have hsum00 := sumU32ValuesLe (boundaryTail polynomial)
    (fun coefficient : QM31 => coefficient.c0.a)
  have hsum01 := sumU32ValuesLe (boundaryTail polynomial)
    (fun coefficient : QM31 => coefficient.c0.b)
  have hsum10 := sumU32ValuesLe (boundaryTail polynomial)
    (fun coefficient : QM31 => coefficient.c1.a)
  have hsum11 := sumU32ValuesLe (boundaryTail polynomial)
    (fun coefficient : QM31 => coefficient.c1.b)
  have htailLength := boundaryTailLength polynomial
  have hinitial := boundaryInitialLimbValues polynomial
  change boundaryRawC0ASum (boundaryTail polynomial) ≤
    (boundaryTail polynomial).length * 4294967295 at hsum00
  change boundaryRawC0BSum (boundaryTail polynomial) ≤
    (boundaryTail polynomial).length * 4294967295 at hsum01
  change boundaryRawC1ASum (boundaryTail polynomial) ≤
    (boundaryTail polynomial).length * 4294967295 at hsum10
  change boundaryRawC1BSum (boundaryTail polynomial) ≤
    (boundaryTail polynomial).length * 4294967295 at hsum11
  rw [htailLength] at hsum00 hsum01 hsum10 hsum11
  simp [U64.size, U64.numBits]
  constructor
  · rw [hinitial.1]
    omega
  constructor
  · rw [hinitial.2.1]
    omega
  constructor
  · rw [hinitial.2.2.1]
    omega
  · rw [hinitial.2.2.2]
    omega

abbrev BoundaryM31Exact := AspisAeneasM31ReduceU64.M31Exact

private theorem generatedPEqualsAuthenticated :
    ComponentBGenerated.aspis_core.field.P = _root_.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold ComponentBGenerated.aspis_core.field.P _root_.aspis_core.field.P
  rfl

private theorem generatedReduceU64EqualsAuthenticated (x : Std.U64) :
    ComponentBGenerated.aspis_core.field.M31.reduce_u64 x =
      _root_.aspis_core.field.reduce_u64 x := by
  unfold ComponentBGenerated.aspis_core.field.M31.reduce_u64
    ComponentBGenerated.aspis_core.field.reduce_u64
    _root_.aspis_core.field.reduce_u64
  rw [generatedPEqualsAuthenticated]
  simp only [lift, bind_tc_ok]
  split <;> rfl

private theorem generatedArrayIndexExact
    {T : Type} {n : Std.Usize} (values : Array T n) (index : Std.Usize)
    (hindex : index.val < values.length) :
    Array.index_usize values index = .ok values.val[index.val] := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hindex]

private theorem addCoefficientValues
    (limbs : Limbs) (coefficient : QM31)
    (h0 : limbs.val[0].val + coefficient.c0.a.val < U64.size)
    (h1 : limbs.val[1].val + coefficient.c0.b.val < U64.size)
    (h2 : limbs.val[2].val + coefficient.c1.a.val < U64.size)
    (h3 : limbs.val[3].val + coefficient.c1.b.val < U64.size) :
    (addCoefficient limbs coefficient).val[0].val =
        limbs.val[0].val + coefficient.c0.a.val ∧
    (addCoefficient limbs coefficient).val[1].val =
        limbs.val[1].val + coefficient.c0.b.val ∧
    (addCoefficient limbs coefficient).val[2].val =
        limbs.val[2].val + coefficient.c1.a.val ∧
    (addCoefficient limbs coefficient).val[3].val =
        limbs.val[3].val + coefficient.c1.b.val := by
  simp [addCoefficient, Aeneas.Std.Array.set, U64.wrapping_add_val_eq,
    core.convert.num.FromU64U32.from_val_eq, Nat.mod_eq_of_lt,
    h0, h1, h2, h3]

private theorem addCoefficientsValues
    (coefficients : List QM31) (limbs : Limbs)
    (h0 : limbs.val[0].val + boundaryRawC0ASum coefficients < U64.size)
    (h1 : limbs.val[1].val + boundaryRawC0BSum coefficients < U64.size)
    (h2 : limbs.val[2].val + boundaryRawC1ASum coefficients < U64.size)
    (h3 : limbs.val[3].val + boundaryRawC1BSum coefficients < U64.size) :
    (addCoefficients coefficients limbs).val[0].val =
        limbs.val[0].val + boundaryRawC0ASum coefficients ∧
    (addCoefficients coefficients limbs).val[1].val =
        limbs.val[1].val + boundaryRawC0BSum coefficients ∧
    (addCoefficients coefficients limbs).val[2].val =
        limbs.val[2].val + boundaryRawC1ASum coefficients ∧
    (addCoefficients coefficients limbs).val[3].val =
        limbs.val[3].val + boundaryRawC1BSum coefficients := by
  induction coefficients generalizing limbs with
  | nil =>
      simp [addCoefficients, boundaryRawC0ASum, boundaryRawC0BSum,
        boundaryRawC1ASum, boundaryRawC1BSum]
  | cons coefficient suffix ih =>
      have hstep0 : limbs.val[0].val + coefficient.c0.a.val <
          U64.size := by
        simp [boundaryRawC0ASum] at h0
        omega
      have hstep1 : limbs.val[1].val + coefficient.c0.b.val <
          U64.size := by
        simp [boundaryRawC0BSum] at h1
        omega
      have hstep2 : limbs.val[2].val + coefficient.c1.a.val <
          U64.size := by
        simp [boundaryRawC1ASum] at h2
        omega
      have hstep3 : limbs.val[3].val + coefficient.c1.b.val <
          U64.size := by
        simp [boundaryRawC1BSum] at h3
        omega
      have hstep := addCoefficientValues limbs coefficient
        hstep0 hstep1 hstep2 hstep3
      have htail0 :
          (addCoefficient limbs coefficient).val[0].val +
              boundaryRawC0ASum suffix <
            U64.size := by
        rw [hstep.1]
        simpa [boundaryRawC0ASum, Nat.add_assoc] using h0
      have htail1 :
          (addCoefficient limbs coefficient).val[1].val +
              boundaryRawC0BSum suffix <
            U64.size := by
        rw [hstep.2.1]
        simpa [boundaryRawC0BSum, Nat.add_assoc] using h1
      have htail2 :
          (addCoefficient limbs coefficient).val[2].val +
              boundaryRawC1ASum suffix <
            U64.size := by
        rw [hstep.2.2.1]
        simpa [boundaryRawC1ASum, Nat.add_assoc] using h2
      have htail3 :
          (addCoefficient limbs coefficient).val[3].val +
              boundaryRawC1BSum suffix <
            U64.size := by
        rw [hstep.2.2.2]
        simpa [boundaryRawC1BSum, Nat.add_assoc] using h3
      have htail := ih (addCoefficient limbs coefficient)
        htail0 htail1 htail2 htail3
      rw [hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2] at htail
      simpa [addCoefficients, boundaryRawC0ASum, boundaryRawC0BSum,
        boundaryRawC1ASum, boundaryRawC1BSum, Nat.add_assoc] using htail

private theorem generatedBoundaryLoopEqAddCoefficients
    (pre suffix : List QM31) (limbs : Limbs)
    (hLen : (pre ++ suffix).length ≤ Std.Usize.max) :
    aspis_core.state_only_sumcheck.state_only_boundary_sum_loop
        (boundaryIterOf pre suffix hLen) limbs =
      .ok (addCoefficients suffix limbs) := by
  induction suffix generalizing pre limbs with
  | nil =>
      rw [aspis_core.state_only_sumcheck.state_only_boundary_sum_loop]
      rw [Aeneas.Std.loop.eq_def]
      unfold aspis_core.state_only_sumcheck.state_only_boundary_sum_loop.body
      simp only
      rw [nextNil pre hLen]
      rfl
  | cons coefficient suffix ih =>
      have hLen' : ((pre ++ [coefficient]) ++ suffix).length ≤
          Std.Usize.max := by
        simpa [List.append_assoc] using hLen
      rw [aspis_core.state_only_sumcheck.state_only_boundary_sum_loop]
      rw [Aeneas.Std.loop.eq_def]
      unfold aspis_core.state_only_sumcheck.state_only_boundary_sum_loop.body
      simp only
      rw [nextCons pre suffix coefficient hLen hLen']
      simp only [bind_tc_ok, lift]
      simp [Array.index_usize, Array.update, addCoefficient,
        addCoefficients]
      have htail :=
        ih (pre ++ [coefficient]) (addCoefficient limbs coefficient) hLen'
      rw [aspis_core.state_only_sumcheck.state_only_boundary_sum_loop] at htail
      unfold aspis_core.state_only_sumcheck.state_only_boundary_sum_loop.body at htail
      simpa [bind_tc_ok, lift, Array.index_usize, Array.update,
        addCoefficient, Aeneas.Std.Array.set] using htail

/-- The extracted iterator loop accumulates each of the four production QM31
    raw limbs exactly once.  The explicit bounds state precisely when the
    generated `U64::wrapping_add` operations are ordinary natural addition. -/
theorem generated_boundary_loop_exact_limb_sums
    (pre suffix : List QM31) (limbs : Limbs)
    (hLen : (pre ++ suffix).length ≤ Std.Usize.max)
    (h0 : limbs.val[0].val + boundaryRawC0ASum suffix < U64.size)
    (h1 : limbs.val[1].val + boundaryRawC0BSum suffix < U64.size)
    (h2 : limbs.val[2].val + boundaryRawC1ASum suffix < U64.size)
    (h3 : limbs.val[3].val + boundaryRawC1BSum suffix < U64.size) :
    ∃ output,
      aspis_core.state_only_sumcheck.state_only_boundary_sum_loop
          (boundaryIterOf pre suffix hLen) limbs = .ok output ∧
      output.val[0].val =
          limbs.val[0].val + boundaryRawC0ASum suffix ∧
      output.val[1].val =
          limbs.val[1].val + boundaryRawC0BSum suffix ∧
      output.val[2].val =
          limbs.val[2].val + boundaryRawC1ASum suffix ∧
      output.val[3].val =
          limbs.val[3].val + boundaryRawC1BSum suffix := by
  refine ⟨addCoefficients suffix limbs,
    generatedBoundaryLoopEqAddCoefficients pre suffix limbs hLen, ?_⟩
  exact addCoefficientsValues suffix limbs h0 h1 h2 h3

def BoundaryCanonicalQM31 (x : QM31) : Prop :=
  x.c0.a.val < 2147483647 ∧ x.c0.b.val < 2147483647 ∧
  x.c1.a.val < 2147483647 ∧ x.c1.b.val < 2147483647

/-- The complete extracted production boundary wrapper computes
    `2 * c0 + c1 + ... + c27` independently in all four raw M31 limbs,
    then invokes the extracted Mersenne reduction. -/
theorem generated_boundary_sum_exact
    (polynomial : Array QM31 28#usize) :
    ∃ output,
      aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial =
        .ok output ∧
      BoundaryCanonicalQM31 output ∧
      ((output.c0.a.val : Nat) : BoundaryM31Exact) =
        (2 * polynomial.val[0].c0.a.val +
          boundaryRawC0ASum (boundaryTail polynomial) : Nat) ∧
      ((output.c0.b.val : Nat) : BoundaryM31Exact) =
        (2 * polynomial.val[0].c0.b.val +
          boundaryRawC0BSum (boundaryTail polynomial) : Nat) ∧
      ((output.c1.a.val : Nat) : BoundaryM31Exact) =
        (2 * polynomial.val[0].c1.a.val +
          boundaryRawC1ASum (boundaryTail polynomial) : Nat) ∧
      ((output.c1.b.val : Nat) : BoundaryM31Exact) =
        (2 * polynomial.val[0].c1.b.val +
          boundaryRawC1BSum (boundaryTail polynomial) : Nat) := by
  obtain ⟨hLen, hTailSlice, hIterator⟩ :=
    generatedBoundaryTailIterator polynomial
  have hbounds := boundaryNoWrapBounds polynomial
  obtain ⟨limbs, hLoop, hlimb0, hlimb1, hlimb2, hlimb3⟩ :=
    generated_boundary_loop_exact_limb_sums [] (boundaryTail polynomial)
      (boundaryInitialLimbs polynomial) hLen hbounds.1 hbounds.2.1
      hbounds.2.2.1 hbounds.2.2.2
  obtain ⟨m0, hm0, hm0raw, hm0canonical, hm0exact⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds limbs.val[0]
  obtain ⟨m1, hm1, hm1raw, hm1canonical, hm1exact⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds limbs.val[1]
  obtain ⟨m2, hm2, hm2raw, hm2canonical, hm2exact⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds limbs.val[2]
  obtain ⟨m3, hm3, hm3raw, hm3canonical, hm3exact⟩ :=
    AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds limbs.val[3]
  have hm0generated : aspis_core.field.M31.reduce_u64 limbs.val[0] =
      .ok m0 := by
    rw [generatedReduceU64EqualsAuthenticated]
    exact hm0
  have hm1generated : aspis_core.field.M31.reduce_u64 limbs.val[1] =
      .ok m1 := by
    rw [generatedReduceU64EqualsAuthenticated]
    exact hm1
  have hm2generated : aspis_core.field.M31.reduce_u64 limbs.val[2] =
      .ok m2 := by
    rw [generatedReduceU64EqualsAuthenticated]
    exact hm2
  have hm3generated : aspis_core.field.M31.reduce_u64 limbs.val[3] =
      .ok m3 := by
    rw [generatedReduceU64EqualsAuthenticated]
    exact hm3
  let output : QM31 := ⟨⟨m0, m1⟩, ⟨m2, m3⟩⟩
  have hFirst : Array.index_usize polynomial 0#usize =
      .ok polynomial.val[0] :=
    generatedArrayIndexExact polynomial 0#usize (by simp)
  have hLimb0 : Array.index_usize limbs 0#usize = .ok limbs.val[0] :=
    generatedArrayIndexExact limbs 0#usize (by simp)
  have hLimb1 : Array.index_usize limbs 1#usize = .ok limbs.val[1] :=
    generatedArrayIndexExact limbs 1#usize (by simp)
  have hLimb2 : Array.index_usize limbs 2#usize = .ok limbs.val[2] :=
    generatedArrayIndexExact limbs 2#usize (by simp)
  have hLimb3 : Array.index_usize limbs 3#usize = .ok limbs.val[3] :=
    generatedArrayIndexExact limbs 3#usize (by simp)
  refine ⟨output, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold aspis_core.state_only_sumcheck.state_only_boundary_sum
    rw [hFirst]
    simp only [lift, bind_tc_ok]
    rw [hTailSlice]
    simp only [bind_tc_ok]
    rw [hIterator]
    simp only [bind_tc_ok]
    rw [← boundaryInitialLimbsEqGenerated polynomial]
    rw [hLoop]
    simp only [bind_tc_ok]
    rw [hLimb0]
    simp only [bind_tc_ok]
    rw [hm0generated]
    simp only [bind_tc_ok]
    rw [hLimb1]
    simp only [bind_tc_ok]
    rw [hm1generated]
    simp only [bind_tc_ok, aspis_core.field.CM31.new]
    rw [hLimb2]
    simp only [bind_tc_ok]
    rw [hm2generated]
    simp only [bind_tc_ok]
    rw [hLimb3]
    simp only [bind_tc_ok]
    rw [hm3generated]
    rfl
  · simpa [BoundaryCanonicalQM31, output,
      AspisAeneasM31ReduceU64.CanonicalRawM31,
      AspisAeneasM31ReduceU64.m31Modulus] using
      ⟨hm0canonical, hm1canonical, hm2canonical, hm3canonical⟩
  · rw [show output.c0.a = m0 by rfl, hm0exact, hlimb0]
    rw [(boundaryInitialLimbValues polynomial).1]
  · rw [show output.c0.b = m1 by rfl, hm1exact, hlimb1]
    rw [(boundaryInitialLimbValues polynomial).2.1]
  · rw [show output.c1.a = m2 by rfl, hm2exact, hlimb2]
    rw [(boundaryInitialLimbValues polynomial).2.2.1]
  · rw [show output.c1.b = m3 by rfl, hm3exact, hlimb3]
    rw [(boundaryInitialLimbValues polynomial).2.2.2]

#print axioms generated_boundary_loop_exact_limb_sums
#print axioms generated_boundary_sum_exact

end ComponentBGenerated.v5_sumcheck_mask
