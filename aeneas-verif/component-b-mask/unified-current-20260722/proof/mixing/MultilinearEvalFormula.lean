import MLEBFormulaPrelude
import CM31MultiplicativeProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.MultilinearEvalProofs

/-! ## Arbitrary-arity algebraic recurrence

The generated kernels process the coordinate list from right to left and fold
adjacent coefficient pairs.  The definitions below make that exact recurrence
explicit for an arbitrary commutative ring.  A binary table records the
big-endian coefficient layout: the left subtree is the high-bit-zero block and
the right subtree is the high-bit-one block.
-/

def BinaryTable (R : Type) : Nat → Type
  | 0 => R
  | n + 1 => BinaryTable R n × BinaryTable R n

def binaryTableToList {R : Type} : (n : Nat) → BinaryTable R n → List R
  | 0, value => [value]
  | n + 1, (left, right) =>
      binaryTableToList n left ++ binaryTableToList n right

def binaryTableEval {R : Type} [Ring R] :
    (coordinates : List R) → BinaryTable R coordinates.length → R
  | [], value => value
  | zi :: rest, (left, right) =>
      blend zi (binaryTableEval rest left) (binaryTableEval rest right)

def foldAdjacent {R : Type} [Ring R] (zi : R) : List R → List R
  | left :: right :: rest =>
      blend zi left right :: foldAdjacent zi rest
  | _ => []

def foldReverse {R : Type} [Ring R] : List R → List R → List R
  | [], layer => layer
  | zi :: rest, layer => foldAdjacent zi (foldReverse rest layer)

def listDot {R : Type} [Ring R] : List R → List R → R
  | x :: xs, y :: ys => x * y + listDot xs ys
  | _, _ => 0

def cubeWeights {R : Type} [Ring R] : List R → List R
  | [] => [1]
  | zi :: rest =>
      let tail := cubeWeights rest
      tail.map (fun weight => (1 - zi) * weight) ++
        tail.map (fun weight => zi * weight)

def bigEndianBitVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      let tail := bigEndianBitVectors n
      tail.map (fun bits => false :: bits) ++
        tail.map (fun bits => true :: bits)

def booleanWeight {R : Type} [Ring R]
    (coordinates : List R) (bits : List Bool) : R :=
  (List.zipWith
    (fun zi bit => if bit then zi else 1 - zi)
    coordinates bits).prod

def standardBigEndianMLE {R : Type} [Ring R]
    (coefficients coordinates : List R) : R :=
  listDot coefficients
    ((bigEndianBitVectors coordinates.length).map
      (booleanWeight coordinates))

@[simp] private theorem binaryTableToList_length {R : Type}
    (n : Nat) (table : BinaryTable R n) :
    (binaryTableToList n table).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rcases table with ⟨left, right⟩
      simp [binaryTableToList, inductionHypothesis, pow_succ]
      omega

@[simp] private theorem foldAdjacent_length {R : Type} [Ring R]
    (zi : R) (values : List R) :
    (foldAdjacent zi values).length = values.length / 2 := by
  induction values using List.twoStepInduction with
  | nil => simp [foldAdjacent]
  | singleton value => simp [foldAdjacent]
  | cons_cons left right rest inductionHypothesis =>
      simp [foldAdjacent, inductionHypothesis]
      omega

private theorem foldAdjacent_append_of_double_length {R : Type} [Ring R]
    (zi : R) (left right : List R) (pairCount : Nat)
    (leftLength : left.length = 2 * pairCount) :
    foldAdjacent zi (left ++ right) =
      foldAdjacent zi left ++ foldAdjacent zi right := by
  induction pairCount generalizing left with
  | zero =>
      have leftLengthZero : left.length = 0 := by omega
      have leftEmpty : left = [] := List.eq_nil_of_length_eq_zero leftLengthZero
      subst left
      rfl
  | succ pairCount inductionHypothesis =>
      rcases left with _ | ⟨first, left⟩
      · simp at leftLength
      rcases left with _ | ⟨second, rest⟩
      · simp at leftLength
      have restLength : rest.length = 2 * pairCount := by
        simp only [List.length_cons] at leftLength
        omega
      simp only [List.cons_append, foldAdjacent]
      rw [inductionHypothesis rest restLength]

private theorem foldReverse_length_of_power_multiple {R : Type} [Ring R]
    (coordinates values : List R) (blockCount : Nat)
    (valuesLength : values.length = blockCount * 2 ^ coordinates.length) :
    (foldReverse coordinates values).length = blockCount := by
  induction coordinates generalizing values blockCount with
  | nil => simpa [foldReverse] using valuesLength
  | cons zi rest inductionHypothesis =>
      have valuesLength' : values.length =
          (2 * blockCount) * 2 ^ rest.length := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using valuesLength
      rw [foldReverse, foldAdjacent_length,
        inductionHypothesis values (2 * blockCount) valuesLength']
      omega

private theorem foldReverse_append_of_power_lengths {R : Type} [Ring R]
    (coordinates left right : List R) (leftBlocks rightBlocks : Nat)
    (leftLength : left.length = leftBlocks * 2 ^ coordinates.length)
    (rightLength : right.length = rightBlocks * 2 ^ coordinates.length) :
    foldReverse coordinates (left ++ right) =
      foldReverse coordinates left ++ foldReverse coordinates right := by
  induction coordinates generalizing left right leftBlocks rightBlocks with
  | nil => rfl
  | cons zi rest inductionHypothesis =>
      have leftLength' : left.length =
          (2 * leftBlocks) * 2 ^ rest.length := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using leftLength
      have rightLength' : right.length =
          (2 * rightBlocks) * 2 ^ rest.length := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using rightLength
      rw [foldReverse, inductionHypothesis left right
        (2 * leftBlocks) (2 * rightBlocks) leftLength' rightLength']
      apply foldAdjacent_append_of_double_length zi
        (foldReverse rest left) (foldReverse rest right) leftBlocks
      exact foldReverse_length_of_power_multiple rest left
        (2 * leftBlocks) leftLength'

private theorem foldReverse_binaryTable {R : Type} [CommRing R]
    (coordinates : List R) (table : BinaryTable R coordinates.length) :
    foldReverse coordinates (binaryTableToList coordinates.length table) =
      [binaryTableEval coordinates table] := by
  induction coordinates with
  | nil => rfl
  | cons zi rest inductionHypothesis =>
      rcases table with ⟨left, right⟩
      change foldAdjacent zi
          (foldReverse rest
            (binaryTableToList rest.length left ++
              binaryTableToList rest.length right)) =
        [blend zi (binaryTableEval rest left)
          (binaryTableEval rest right)]
      rw [foldReverse_append_of_power_lengths rest
        (binaryTableToList rest.length left)
        (binaryTableToList rest.length right) 1 1 (by simp) (by simp),
        inductionHypothesis left, inductionHypothesis right]
      rfl

private theorem listDot_append {R : Type} [Ring R]
    (xs ys ws vs : List R) (aligned : xs.length = ws.length) :
    listDot (xs ++ ys) (ws ++ vs) =
      listDot xs ws + listDot ys vs := by
  induction xs generalizing ws with
  | nil =>
      have wsLengthZero : ws.length = 0 := by simpa using aligned.symm
      have wsEmpty : ws = [] := List.eq_nil_of_length_eq_zero wsLengthZero
      subst ws
      simp [listDot]
  | cons x xs inductionHypothesis =>
      rcases ws with _ | ⟨w, ws⟩
      · simp at aligned
      simp only [List.length_cons] at aligned
      have aligned' : xs.length = ws.length := by omega
      simp only [List.cons_append, listDot]
      rw [inductionHypothesis ws aligned']
      simp [add_assoc]

private theorem listDot_scale_weights {R : Type} [CommRing R]
    (scale : R) (values weights : List R) :
    listDot values (weights.map (fun weight => scale * weight)) =
      scale * listDot values weights := by
  induction values generalizing weights with
  | nil => simp [listDot]
  | cons value values inductionHypothesis =>
      cases weights with
      | nil => simp [listDot]
      | cons weight weights =>
          simp [listDot, inductionHypothesis]
          ring

@[simp] private theorem cubeWeights_length {R : Type} [Ring R]
    (coordinates : List R) :
    (cubeWeights coordinates).length = 2 ^ coordinates.length := by
  induction coordinates with
  | nil => rfl
  | cons zi rest inductionHypothesis =>
      simp [cubeWeights, inductionHypothesis, pow_succ]
      omega

private theorem binaryTableEval_eq_cube_sum_product {R : Type} [CommRing R]
    (coordinates : List R) (table : BinaryTable R coordinates.length) :
    binaryTableEval coordinates table =
      listDot (binaryTableToList coordinates.length table)
        (cubeWeights coordinates) := by
  induction coordinates with
  | nil => simp [binaryTableEval, binaryTableToList, cubeWeights, listDot]
  | cons zi rest inductionHypothesis =>
      rcases table with ⟨left, right⟩
      change blend zi (binaryTableEval rest left)
          (binaryTableEval rest right) =
        listDot
          (binaryTableToList rest.length left ++
            binaryTableToList rest.length right)
          ((cubeWeights rest).map (fun weight => (1 - zi) * weight) ++
            (cubeWeights rest).map (fun weight => zi * weight))
      rw [inductionHypothesis left, inductionHypothesis right]
      rw [listDot_append _ _ _ _ (by simp),
        listDot_scale_weights, listDot_scale_weights]
      simp [blend]
      ring

@[simp] private theorem bigEndianBitVectors_length (arity : Nat) :
    (bigEndianBitVectors arity).length = 2 ^ arity := by
  induction arity with
  | zero => rfl
  | succ arity inductionHypothesis =>
      simp [bigEndianBitVectors, inductionHypothesis, pow_succ]
      omega

@[simp] private theorem booleanWeight_false_cons {R : Type} [Ring R]
    (zi : R) (rest : List R) (bits : List Bool) :
    booleanWeight (zi :: rest) (false :: bits) =
      (1 - zi) * booleanWeight rest bits := by
  simp [booleanWeight]

@[simp] private theorem booleanWeight_true_cons {R : Type} [Ring R]
    (zi : R) (rest : List R) (bits : List Bool) :
    booleanWeight (zi :: rest) (true :: bits) =
      zi * booleanWeight rest bits := by
  simp [booleanWeight]

private theorem cubeWeights_eq_bigEndian_products {R : Type} [CommRing R]
    (coordinates : List R) :
    cubeWeights coordinates =
      (bigEndianBitVectors coordinates.length).map
        (booleanWeight coordinates) := by
  induction coordinates with
  | nil => rfl
  | cons zi rest inductionHypothesis =>
      simp [cubeWeights, bigEndianBitVectors, inductionHypothesis,
        List.map_map, Function.comp_def]

private theorem binaryTableEval_eq_standard_bigEndian_sum_product
    {R : Type} [CommRing R]
    (coordinates : List R) (table : BinaryTable R coordinates.length) :
    binaryTableEval coordinates table =
      standardBigEndianMLE
        (binaryTableToList coordinates.length table) coordinates := by
  rw [binaryTableEval_eq_cube_sum_product,
    cubeWeights_eq_bigEndian_products]
  rfl

def binaryTableOfList {R : Type} [Zero R] :
    (n : Nat) → List R → BinaryTable R n
  | 0, values => values.headD 0
  | n + 1, values =>
      (binaryTableOfList n (values.take (2 ^ n)),
        binaryTableOfList n (values.drop (2 ^ n)))

private theorem binaryTableToList_ofList {R : Type} [Zero R]
    (n : Nat) (values : List R) (validLength : values.length = 2 ^ n) :
    binaryTableToList n (binaryTableOfList n values) = values := by
  induction n generalizing values with
  | zero =>
      rcases values with _ | ⟨value, rest⟩
      · simp at validLength
      have restLengthZero : rest.length = 0 := by
        simp only [List.length_cons, pow_zero] at validLength
        omega
      have restEmpty : rest = [] :=
        List.eq_nil_of_length_eq_zero restLengthZero
      subst rest
      rfl
  | succ n inductionHypothesis =>
      have takeLength : (values.take (2 ^ n)).length = 2 ^ n := by
        rw [List.length_take]
        have enough : 2 ^ n ≤ values.length := by
          rw [validLength, pow_succ]
          omega
        exact Nat.min_eq_left enough
      have dropLength : (values.drop (2 ^ n)).length = 2 ^ n := by
        rw [List.length_drop, validLength, pow_succ]
        omega
      simp only [binaryTableOfList, binaryTableToList]
      rw [inductionHypothesis _ takeLength, inductionHypothesis _ dropLength,
        List.take_append_drop]

/-- Arbitrary-arity structural theorem: reverse-coordinate adjacent folding
of any valid `2^n` coefficient table is exactly the standard big-endian
sum/product over all lexicographically ordered Boolean assignments. -/
theorem foldReverse_valid_eq_standard_bigEndian_sum_product
    {R : Type} [CommRing R]
    (coefficients coordinates : List R)
    (validLength : coefficients.length = 2 ^ coordinates.length) :
    foldReverse coordinates coefficients =
      [standardBigEndianMLE coefficients coordinates] := by
  let table := binaryTableOfList coordinates.length coefficients
  have tableList : binaryTableToList coordinates.length table = coefficients :=
    binaryTableToList_ofList coordinates.length coefficients validLength
  rw [← tableList, foldReverse_binaryTable,
    binaryTableEval_eq_standard_bigEndian_sum_product, tableList]

/-! ## Exact semantics of the generated QM31 operations

This bridge uses the single source-authentic multiplicative extraction already
proved in `CM31MultiplicativeProof`.  The generated MLE module owns distinct
CM31/QM31 structures, so the bridge is explicit at every coordinate; the M31
words themselves are definitionally the same `U32` type.
-/

abbrev GeneratedCM31 := ComponentBGenerated.aspis_core.field.CM31
abbrev ExactM31 := AspisAeneasCM31Exact.M31Exact
abbrev ExactCM31 := AspisAeneasCM31Exact.CM31Exact

def exactQm31R : ExactCM31 := ⟨2, 1⟩

abbrev ExactQM31 := QuadraticAlgebra ExactCM31 exactQm31R 0

def generatedCm31ToExact (x : GeneratedCM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def generatedQm31ToExact (x : QM31) : ExactQM31 :=
  ⟨generatedCm31ToExact x.c0, generatedCm31ToExact x.c1⟩

def GeneratedCanonicalCM31 (x : GeneratedCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 x.b.val

def GeneratedCanonicalQM31 (x : QM31) : Prop :=
  GeneratedCanonicalCM31 x.c0 ∧ GeneratedCanonicalCM31 x.c1

private theorem generated_P_eq_multiplicative :
    ComponentBGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold ComponentBGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem generated_reduce_u64_eq_multiplicative (x : Std.U64) :
    ComponentBGenerated.aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold ComponentBGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_add_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_sub_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_mul_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.mul a b =
      AspisCoreCM31Multiplicative.field.M31.mul a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [generated_reduce_u64_eq_multiplicative]

private theorem generated_m31_add_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.add a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_add_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_sub_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.sub a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) - (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_sub_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_mul_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.mul a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) * (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_mul_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_double_corresponds
    (a : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.double a = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (a.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    generated_m31_add_corresponds a a ha ha
  exact ⟨out, outputEquation, outputCanonical, outputExact⟩

private theorem generated_cm31_add_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.add x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x + generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_add_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_add_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.add, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_sub_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.sub x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x - generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_sub_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_sub_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.sub, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_mul_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.mul x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x * generatedCm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_m31_mul_corresponds x.a y.a hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_m31_mul_corresponds x.b y.b hx.2 hy.2
  obtain ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩ :=
    generated_m31_add_corresponds x.a x.b hx.1 hx.2
  obtain ⟨ysum, hysum, hysumCanonical, hysumExact⟩ :=
    generated_m31_add_corresponds y.a y.b hy.1 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_m31_mul_corresponds xsum ysum hxsumCanonical hysumCanonical
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical
  obtain ⟨imagPartial, himagPartial, himagPartialCanonical,
      himagPartialExact⟩ :=
    generated_m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_sub_corresponds imagPartial m1
      himagPartialCanonical hm1Canonical
  have realExact :
      ((real.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.a.val : ExactM31) -
          (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
    rw [hrealExact, hm0Exact, hm1Exact]
  have imagExact :
      ((imag.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.b.val : ExactM31) +
          (x.b.val : ExactM31) * (y.a.val : ExactM31) := by
    calc
      ((imag.val : Nat) : ExactM31) =
          ((imagPartial.val : Nat) : ExactM31) -
            ((m1.val : Nat) : ExactM31) := himagExact
      _ = (((m2.val : Nat) : ExactM31) -
            ((m0.val : Nat) : ExactM31)) -
            ((m1.val : Nat) : ExactM31) := by rw [himagPartialExact]
      _ = (((x.a.val : ExactM31) + (x.b.val : ExactM31)) *
            ((y.a.val : ExactM31) + (y.b.val : ExactM31)) -
            (x.a.val : ExactM31) * (y.a.val : ExactM31)) -
            (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
          rw [hm2Exact, hxsumExact, hysumExact, hm0Exact, hm1Exact]
      _ = (x.a.val : ExactM31) * (y.b.val : ExactM31) +
            (x.b.val : ExactM31) * (y.a.val : ExactM31) := by ring
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hreal, himagPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · simpa [generatedCm31ToExact, sub_eq_add_neg] using realExact
    · simpa [generatedCm31ToExact] using imagExact

private theorem generated_mul_by_r_corresponds
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.mul_by_r x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x * exactQm31R := by
  obtain ⟨doubleA, hdoubleA, hdoubleACanonical, hdoubleAExact⟩ :=
    generated_m31_add_corresponds x.a x.a hx.1 hx.1
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds doubleA x.b hdoubleACanonical hx.2
  obtain ⟨doubleB, hdoubleB, hdoubleBCanonical, hdoubleBExact⟩ :=
    generated_m31_add_corresponds x.b x.b hx.2 hx.2
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_add_corresponds x.a doubleB hx.1 hdoubleBCanonical
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.mul_by_r,
      ComponentBGenerated.aspis_core.field.M31.double,
      hdoubleA, hreal, hdoubleB, himag, out]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).re
      rw [hrealExact, hdoubleAExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).im
      rw [himagExact, hdoubleBExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring

theorem generated_qm31_add_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.add x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨o0, hcall0, hcan0, hexact0⟩ :=
    generated_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨o1, hcall1, hcan1, hexact1⟩ :=
    generated_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2
  let out : QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.add, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem generated_qm31_sub_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.sub x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x - generatedQm31ToExact y := by
  obtain ⟨o0, hcall0, hcan0, hexact0⟩ :=
    generated_cm31_sub_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨o1, hcall1, hcan1, hexact1⟩ :=
    generated_cm31_sub_corresponds x.c1 y.c1 hx.2 hy.2
  let out : QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.sub, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem generated_qm31_mul_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.mul x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2
  obtain ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩ :=
    generated_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2
  obtain ⟨ysum, hysum, hysumCanonical, hysumExact⟩ :=
    generated_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_cm31_mul_corresponds xsum ysum hxsumCanonical hysumCanonical
  obtain ⟨rm1, hrm1, hrm1Canonical, hrm1Exact⟩ :=
    generated_mul_by_r_corresponds m1 hm1Canonical
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_cm31_add_corresponds m0 rm1 hm0Canonical hrm1Canonical
  obtain ⟨crossPartial, hcrossPartial, hcrossPartialCanonical,
      hcrossPartialExact⟩ :=
    generated_cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_cm31_sub_corresponds crossPartial m1
      hcrossPartialCanonical hm1Canonical
  let out : QM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hrm1, hreal, hcrossPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact real =
        (generatedQm31ToExact x * generatedQm31ToExact y).re
      rw [hrealExact, hm0Exact, hrm1Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring
    · change generatedCm31ToExact imag =
        (generatedQm31ToExact x * generatedQm31ToExact y).im
      rw [himagExact, hcrossPartialExact, hm2Exact, hxsumExact,
        hysumExact, hm0Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring

#print axioms foldReverse_valid_eq_standard_bigEndian_sum_product
#print axioms generated_qm31_add_corresponds
#print axioms generated_qm31_sub_corresponds
#print axioms generated_qm31_mul_corresponds

end ComponentBGenerated.MultilinearEvalProofs
