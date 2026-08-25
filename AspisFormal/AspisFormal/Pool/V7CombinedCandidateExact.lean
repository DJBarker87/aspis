import AspisFormal.Pool.V7CoherentTraceExtraction
import AspisFormal.Pool.V7C1ConcreteProjectionBinding

/-!
# Exact V7 combined candidate

`batchInitialWords` batches twenty-nine encoded words of length `2^20`.
The selected decoder candidates are instead coefficient messages of length
`1024`, so this module gives their coefficient-level analogue
`batchInitialMessages` a separate name.

The abstract projection binding already makes the decoder's initial encoder
injective, and the coherent extraction therefore fixes the encoded combined
candidate exactly.  Recovering the literal coefficient batch additionally
uses the auditable equality with `exactInitialEncoder` and a proof that this
concrete mathematical encoder commutes with the width-29 gamma batch.
-/

set_option autoImplicit false

namespace AspisPool.V7CombinedCandidateExact

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6Width29CorrelatedAgreement
open AspisCircleTensorBinding

/-- The exact coefficient-level gamma batch.  This is deliberately distinct
from `batchInitialWords`, whose inputs and output are encoded words. -/
def batchInitialMessages
    (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact) :
    InitialMessage QM31Exact :=
  fun row => width29Batch (fun lane => components lane row) gamma

@[simp] theorem batchInitialMessages_apply
    (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact)
    (row : Fin 1024) :
    batchInitialMessages components gamma row =
      width29Batch (fun lane => components lane row) gamma := by
  rfl

/-- The 1024-overlap cap forces the length-`2^20` initial encoder to be
injective: equal codewords agree at all `2^20` positions. -/
theorem InitialProjectionBinding.initialEncoder_injective
    {decoder : ExactDecoderInstantiation QM31Exact}
    (binding : InitialProjectionBinding decoder) :
    Function.Injective decoder.initialEncoder := by
  classical
  intro left right encodedEqual
  by_contra different
  have overlap := binding.overlapCap left right different
  have full :
      agreementCount (decoder.initialEncoder left)
          (decoder.initialEncoder right) = 1048576 := by
    rw [encodedEqual]
    simp [agreementCount]
  omega

/-- The generic coherent extraction unconditionally identifies the combined
candidate's codeword with the word-level gamma batch of the twenty-nine
selected component codewords. -/
theorem CoherentTraceExtraction.combinedEncoder_eq_batchInitialWords
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    decoder.initialEncoder extraction.combined.1 =
      batchInitialWords
        (fun lane => decoder.initialEncoder (extraction.components lane))
        gamma := by
  change decoder.initialEncoder extraction.combined.1 =
    fun index => width29Batch
      (fun lane => decoder.initialEncoder (extraction.components lane) index)
      gamma
  simpa only [Width29CandidateOnCurve, selectedCandidateStrategy_candidate,
    width29CurveValue] using extraction.combinedOnCurve

/-- Pointwise form of the unconditional encoded batching equality. -/
theorem CoherentTraceExtraction.combinedEncoder_eq_gammaSum_apply
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) (index : Fin 1048576) :
    decoder.initialEncoder extraction.combined.1 index =
      ∑ lane : Fin 29,
        decoder.initialEncoder (extraction.components lane) index *
          gamma ^ lane.val := by
  have encoded := congrFun
    (CoherentTraceExtraction.combinedEncoder_eq_batchInitialWords extraction)
    index
  simpa only [batchInitialWords, width29Batch] using encoded

/-! ## Linearity of the exact mathematical encoder -/

private theorem qm31Exact_two_ne_zero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact (0 : M31Exact) := by
    calc
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
          (2 : QM31Exact) := map_ofNat _ 2
      _ = 0 := equalZero
      _ = algebraMap M31Exact QM31Exact (0 : M31Exact) := (map_zero _).symm
  have baseEqual :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31Exact_two_ne_zero⟩

/-- Natural-basis evaluation commutes with the exact finite gamma batch. -/
private theorem naturalCoefficientPolynomial_eval_batch
    {n : Nat} (positive : 0 < n)
    (components : Fin 29 → Fin n → QM31Exact)
    (gamma x : QM31Exact) :
    (naturalCoefficientPolynomial
        (fun coefficient =>
          width29Batch (fun lane => components lane coefficient) gamma)).eval x =
      width29Batch
        (fun lane => (naturalCoefficientPolynomial (components lane)).eval x)
        gamma := by
  calc
    (naturalCoefficientPolynomial
        (fun coefficient =>
          width29Batch (fun lane => components lane coefficient) gamma)).eval x =
        ∑ coefficient : Fin n,
          (∑ lane : Fin 29,
              components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      rw [naturalCoefficientPolynomial_eval_eq_sum positive]
      rfl
    _ = ∑ coefficient : Fin n, ∑ lane : Fin 29,
          (components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      apply Finset.sum_congr rfl
      intro coefficient _
      rw [Finset.sum_mul]
    _ = ∑ lane : Fin 29, ∑ coefficient : Fin n,
          (components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      rw [Finset.sum_comm]
    _ = ∑ lane : Fin 29,
          (∑ coefficient : Fin n,
              components lane coefficient * naturalLineValue x coefficient) *
            gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro coefficient _
      ring
    _ = ∑ lane : Fin 29,
          (naturalCoefficientPolynomial (components lane)).eval x *
            gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [naturalCoefficientPolynomial_eval_eq_sum positive]
    _ = width29Batch
          (fun lane => (naturalCoefficientPolynomial (components lane)).eval x)
          gamma := by
      rfl

private theorem initialP0_eval_batchInitialMessages
    (components : Width29InitialMessages QM31Exact) (gamma x : QM31Exact) :
    (initialP0 (batchInitialMessages components gamma)).eval x =
      width29Batch (fun lane => (initialP0 (components lane)).eval x) gamma := by
  unfold initialP0
  have coefficientBatch :
      evenCoefficients (batchInitialMessages components gamma) =
        fun coefficient : Fin 512 =>
          width29Batch
            (fun lane => evenCoefficients (components lane) coefficient)
            gamma := by
    funext coefficient
    rfl
  rw [coefficientBatch]
  exact naturalCoefficientPolynomial_eval_batch (by norm_num) _ gamma x

private theorem initialP1_eval_batchInitialMessages
    (components : Width29InitialMessages QM31Exact) (gamma x : QM31Exact) :
    (initialP1 (batchInitialMessages components gamma)).eval x =
      width29Batch (fun lane => (initialP1 (components lane)).eval x) gamma := by
  unfold initialP1
  have coefficientBatch :
      oddCoefficients (batchInitialMessages components gamma) =
        fun coefficient : Fin 512 =>
          width29Batch
            (fun lane => oddCoefficients (components lane) coefficient)
            gamma := by
    funext coefficient
    rfl
  rw [coefficientBatch]
  exact naturalCoefficientPolynomial_eval_batch (by norm_num) _ gamma x

/-- The exact mathematical circle encoder carries a coefficient gamma batch
to the existing word-level gamma batch. -/
theorem exactInitialEncoder_batchInitialMessages
    (components : Width29InitialMessages QM31Exact) (gamma : QM31Exact) :
    exactInitialEncoder (batchInitialMessages components gamma) =
      batchInitialWords (fun lane => exactInitialEncoder (components lane))
        gamma := by
  funext index
  simp only [exactInitialEncoder]
  rw [initialP0_eval_batchInitialMessages,
    initialP1_eval_batchInitialMessages]
  simp only [batchInitialWords, width29Batch, exactInitialEncoder,
    Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]

/-! ## Concrete coefficient recovery -/

/-- Once the decoder's production encoder is identified with the existing
exact mathematical encoder, the selected combined candidate is literally the
coefficient-level gamma batch, not merely a message with the same codeword. -/
theorem CoherentTraceExtraction.combined_eq_batchInitialMessages
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder) :
    extraction.combined.1 = batchInitialMessages extraction.components gamma := by
  apply InitialProjectionBinding.initialEncoder_injective binding
  rw [initialEncoderEq]
  calc
    exactInitialEncoder extraction.combined.1 =
        batchInitialWords
          (fun lane => exactInitialEncoder (extraction.components lane))
          gamma := by
      simpa only [initialEncoderEq] using
        CoherentTraceExtraction.combinedEncoder_eq_batchInitialWords extraction
    _ = exactInitialEncoder
          (batchInitialMessages extraction.components gamma) :=
      (exactInitialEncoder_batchInitialMessages extraction.components gamma).symm

/-- Exact pointwise coefficient statement: every combined coefficient is the
literal sum of all twenty-nine component coefficients with powers of gamma. -/
theorem CoherentTraceExtraction.combined_eq_gammaSum_apply
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (row : Fin 1024) :
    extraction.combined.1 row =
      ∑ lane : Fin 29,
        extraction.components lane row * gamma ^ lane.val := by
  have combined := congrFun
    (CoherentTraceExtraction.combined_eq_batchInitialMessages extraction
      initialEncoderEq) row
  simpa only [batchInitialMessages, width29Batch] using combined

#print axioms InitialProjectionBinding.initialEncoder_injective
#print axioms CoherentTraceExtraction.combinedEncoder_eq_batchInitialWords
#print axioms exactInitialEncoder_batchInitialMessages
#print axioms CoherentTraceExtraction.combined_eq_batchInitialMessages
#print axioms CoherentTraceExtraction.combined_eq_gammaSum_apply

end AspisPool.V7CombinedCandidateExact
