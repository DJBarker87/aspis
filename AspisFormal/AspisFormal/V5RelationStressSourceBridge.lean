import AspisFormal.V5Tag67ModeledRelationAcceptanceBridge
import AspisFormal.V5ComponentCRelationTailCodec
import AspisFormal.V5ComponentCPreProjectionDeployed
import AspisFormal.V5CompactTerminalOptimized

/-!
# The scalar success path of the deployed V5 relation checker

This file gives the production V5 relation path a small, direct Lean shape.
The first version of this file started after byte decoding and after the main
and additive weight states had been formed.  The sections below now also pin
the 928-byte tail layout, the four-by-nineteen claim table, the generic dual
weight folds, the compact Component-B evaluator, and the caller's final
coefficient comparison.  On a successful path, the scalar checker performs:

1. add two claimed off-domain values to the running claim;
2. compare the seven-coefficient polynomial's boundary with that claim;
3. evaluate the polynomial at the round challenge;
4. repeat for four rounds; and
5. compare the sum of the main and additive final dots with the last claim.

`SourceRelationInputMatchesFamily` states exactly how decoded values and final
weights are identified with the maintained relation family.  The final
theorems prove that a successful source-shaped caller gives success of that
model and that the four coefficients accepted by the relation checker are the
same four coefficients already supplied to FRI.

This file does not claim that the production Rust functions have all been
extracted.  It separates the remaining executable equalities at the decoder,
generic `WeightAccumulator`, compact Component-B operations, relation loop,
and caller.  Existing Charon/Aeneas work proves related current
`WeightAccumulator` arithmetic, but it was extracted through a different
caller and therefore is not silently treated as a proof of this verifier.
-/

namespace AspisV5RelationStressSourceBridge

open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCPreProjectionDeployed
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRelationTailCodec
open AspisV5CompactTerminal
open AspisV5CompactTerminalOptimized

variable {K : Type*} [Field K]

/-! ## Exact parsing positions for the 928-byte relation tail -/

/-- One sixteen-byte field read from the fixed 928-byte relation tail. -/
def decodeSourceRelationTailField
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (bytes : RelationTailBytes)
    (field : Fin physicalRelationTailFieldCount) : Option K :=
  (decodeQM31LE (relationTailFieldBytes bytes field)).map e

/-- The four circle-coordinate fields occupy words `0..3`. -/
def sourceCircleWord (coordinate : Fin 4) :
    Fin physicalRelationTailFieldCount :=
  ⟨coordinate.val, by
    simp only [physicalRelationTailFieldCount]
    omega⟩

/-- The six line-point fields occupy words `4..9`. -/
def sourceLineWord (point : Fin 6) : Fin physicalRelationTailFieldCount :=
  ⟨4 + point.val, by
    simp only [physicalRelationTailFieldCount]
    omega⟩

/-- The eight OOD-value fields occupy words `10..17`, round-major. -/
def sourceOodWord (round : Fin 4) (sample : Fin 2) :
    Fin physicalRelationTailFieldCount :=
  physicalRelationIndex (round, .inl sample)

/-- The eight OOD-mix fields occupy words `18..25`, round-major. -/
def sourceMixWord (round : Fin 4) (sample : Fin 2) :
    Fin physicalRelationTailFieldCount :=
  ⟨physicalMixStart + 2 * round.val + sample.val, by
    simp only [physicalRelationTailFieldCount, physicalMixStart]
    omega⟩

/-- The twenty-eight sumcheck fields occupy words `26..53`, round-major. -/
def sourcePolynomialWord (round : Fin 4) (degree : Fin 7) :
    Fin physicalRelationTailFieldCount :=
  physicalRelationIndex (round, .inr degree)

/-- The four final coefficients occupy words `54..57`. -/
def sourceFinalWord (coefficient : Fin 4) :
    Fin physicalRelationTailFieldCount :=
  ⟨physicalFinalStart + coefficient.val, by
    simp only [physicalRelationTailFieldCount, physicalFinalStart]
    omega⟩

theorem source_relation_tail_word_positions
    (circle : Fin 4) (line : Fin 6) (round : Fin 4)
    (sample : Fin 2) (degree : Fin 7) (final : Fin 4) :
    (sourceCircleWord circle).val = circle.val ∧
    (sourceLineWord line).val = 4 + line.val ∧
    (sourceOodWord round sample).val = 10 + 2 * round.val + sample.val ∧
    (sourceMixWord round sample).val = 18 + 2 * round.val + sample.val ∧
    (sourcePolynomialWord round degree).val = 26 + 7 * round.val + degree.val ∧
      (sourceFinalWord final).val = 54 + final.val := by
  simp only [sourceCircleWord, sourceLineWord, sourceOodWord, sourceMixWord,
    sourcePolynomialWord, sourceFinalWord, physicalRelationIndex_ood_val,
    physicalRelationIndex_polynomial_val, physicalMixStart, physicalFinalStart]
  simp

/-- Successful canonical decoding of every one of the 58 words.  The six
fields below cover `4 + 6 + 8 + 8 + 28 + 4 = 58` words with no omitted
category. -/
structure SourceRelationTailDecodeSuccess
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (bytes : RelationTailBytes)
    (fields : PhysicalRelationFields K) : Prop where
  circle : ∀ coordinate,
    decodeSourceRelationTailField e bytes (sourceCircleWord coordinate) =
      some (fields.circlePointCoordinates coordinate)
  line : ∀ point,
    decodeSourceRelationTailField e bytes (sourceLineWord point) =
      some (fields.linePoints point)
  ood : ∀ round sample,
    decodeSourceRelationTailField e bytes (sourceOodWord round sample) =
      some (fields.oodValues round sample)
  mix : ∀ round sample,
    decodeSourceRelationTailField e bytes (sourceMixWord round sample) =
      some (fields.oodMixes round sample)
  polynomial : ∀ round degree,
    decodeSourceRelationTailField e bytes
        (sourcePolynomialWord round degree) =
      some (fields.polynomialCoefficients round degree)
  final : ∀ coefficient,
    decodeSourceRelationTailField e bytes (sourceFinalWord coefficient) =
      some (fields.finalCoefficients coefficient)

/-- The parser inventory is exactly the 58 words and 928 bytes used by the
production relation checker. -/
theorem source_relation_tail_inventory :
    4 + 6 + 4 * 2 + 4 * 2 + 4 * 7 + 4 =
        physicalRelationTailFieldCount ∧
      physicalRelationTailFieldCount * qm31EncodedByteCount = 928 := by
  decide

/-- Exact remaining decoder boundary.  `rustDecode` denotes the result
reported by extracted production code; the right side is the field-by-field
canonical little-endian decoder above. -/
noncomputable def ExactRustRelationTailDecoderEquality
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (rustDecode : RelationTailBytes → Option (Fin physicalRelationTailFieldCount → K)) :
    Prop := by
  classical
  exact rustDecode = fun bytes =>
      if h : ∀ field, ∃ value,
          decodeSourceRelationTailField e bytes field = some value then
        some (fun field => Classical.choose (h field))
      else
        none

/-- The pinned mathematical decoder accepts every canonically encoded
58-field tail and returns every field unchanged. -/
theorem decodeSourceRelationTailField_encode
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (tail : Fin physicalRelationTailFieldCount → K)
    (field : Fin physicalRelationTailFieldCount) :
    decodeSourceRelationTailField e (encodeRelationTailValues e tail) field =
      some (tail field) := by
  simp [decodeSourceRelationTailField, encodeRelationTailValues,
    relationTailFieldBytes_encodeRelationTailFields,
    decodeQM31LE_encodeQM31LE]

/-! ### Byte parsing of the four-by-nineteen claim table -/

abbrev SourcePointClaimBytes :=
  Fin (76 * qm31EncodedByteCount) → AspisV5ComponentCQM31Representation.Byte

def sourcePointClaimByteIndexEquiv :
    (Fin 76 × Fin qm31EncodedByteCount) ≃ Fin (76 * qm31EncodedByteCount) :=
  finProdFinEquiv

def sourcePointClaimFieldBytes (bytes : SourcePointClaimBytes)
    (field : Fin 76) : QM31Bytes :=
  fun byte => bytes (sourcePointClaimByteIndexEquiv (field, byte))

def decodeSourcePointClaimField
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (bytes : SourcePointClaimBytes) (field : Fin 76) : Option K :=
  (decodeQM31LE (sourcePointClaimFieldBytes bytes field)).map e

/-- Canonical field-major encoder used to prove the 76-field parser
round-trip independently of the production implementation. -/
noncomputable def encodeSourcePointClaimValues
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (claims : Fin 76 → K) : SourcePointClaimBytes :=
  fun index =>
    let fieldByte := sourcePointClaimByteIndexEquiv.symm index
    encodeQM31LE (e.symm (claims fieldByte.1)) fieldByte.2

theorem sourcePointClaimFieldBytes_encode
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (claims : Fin 76 → K) (field : Fin 76) :
    sourcePointClaimFieldBytes (encodeSourcePointClaimValues e claims) field =
      encodeQM31LE (e.symm (claims field)) := by
  funext byte
  simp [sourcePointClaimFieldBytes, encodeSourcePointClaimValues]

theorem decodeSourcePointClaimField_encode
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (claims : Fin 76 → K) (field : Fin 76) :
    decodeSourcePointClaimField e (encodeSourcePointClaimValues e claims) field =
      some (claims field) := by
  simp [decodeSourcePointClaimField, sourcePointClaimFieldBytes_encode,
    decodeQM31LE_encodeQM31LE]

theorem source_point_claim_byte_index
    (point : PointClaimRow) (lane : TotalLane)
    (byte : Fin qm31EncodedByteCount) :
    (sourcePointClaimByteIndexEquiv
      (pointMajorClaimLayout (point, lane), byte)).val =
        16 * (19 * point.val + lane.val) + byte.val := by
  change byte.val + 16 * (lane.val + 19 * point.val) =
    16 * (19 * point.val + lane.val) + byte.val
  ring

theorem source_point_claim_table_bytes :
    4 * 19 = 76 ∧ 76 * qm31EncodedByteCount = 1216 := by
  decide

/-- Successful canonical decoding of all 76 claim-table fields. -/
structure SourcePointClaimDecodeSuccess
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (bytes : SourcePointClaimBytes) (claims : Fin 76 → K) : Prop where
  field : ∀ index,
    decodeSourcePointClaimField e bytes index = some (claims index)

/-- Exact remaining byte-decoder boundary for the claim table. -/
noncomputable def ExactRustPointClaimTableDecoderEquality
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (rustDecode : SourcePointClaimBytes → Option (Fin 76 → K)) : Prop := by
  classical
  exact rustDecode = fun bytes =>
      if h : ∀ field, ∃ value,
          decodeSourcePointClaimField e bytes field = some value then
        some (fun field => Classical.choose (h field))
      else
        none

/-! ## The exact four-by-nineteen point-claim table -/

/-- Gamma power assigned to one of the nineteen committed columns. -/
def sourceGammaWeight (gamma : K) (lane : TotalLane) : K :=
  gamma ^ lane.val

/-- Literal nineteen-product dot for one of the four opening points. -/
def sourcePointClaim (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) : K :=
  ∑ lane : TotalLane,
    sourceGammaWeight gamma lane *
      claims (pointMajorClaimLayout (point, lane))

/-- The five production blocks: four blocks of four columns, followed by the
three columns `16..18`. -/
def sourceClaimBlockOfLane (lane : TotalLane) : Fin 5 :=
  if h : lane.val < 16 then
    ⟨lane.val / 4, by omega⟩
  else
    ⟨4, by decide⟩

def sourcePointClaimBlock (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) (block : Fin 5) : K :=
  ∑ lane : TotalLane,
    if sourceClaimBlockOfLane lane = block then
      sourceGammaWeight gamma lane *
        claims (pointMajorClaimLayout (point, lane))
    else
      0

/-- Source-shaped five-block claim aggregation. -/
def sourcePreparedPointClaim (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) : K :=
  ∑ block : Fin 5, sourcePointClaimBlock gamma claims point block

/-- The five blocks contain exactly `4,4,4,4,3` lanes. -/
theorem source_point_claim_block_sizes :
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (0 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (1 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (2 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (3 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (4 : Fin 5))).card = 3 := by
  decide

/-- The five-block implementation is exactly the literal nineteen-column
dot, independently of the values and of gamma. -/
theorem sourcePreparedPointClaim_eq_sourcePointClaim
    (gamma : K) (claims : Fin 76 → K) (point : PointClaimRow) :
    sourcePreparedPointClaim gamma claims point =
      sourcePointClaim gamma claims point := by
  classical
  unfold sourcePreparedPointClaim sourcePointClaimBlock sourcePointClaim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lane _
  simp

/-- All four prepared point claims. -/
def sourcePreparedPointClaims (gamma : K) (claims : Fin 76 → K) :
    PointClaimRow → K :=
  fun point => sourcePreparedPointClaim gamma claims point

/-- Exact remaining boundary for `prepare_v5_pcs_claims`.  The right-hand
side includes the point-major `19 * point + lane` layout and the five-block
aggregation proved equal to the literal dot above. -/
def ExactRustPreparedPointClaimsEquality
    (rustPrepare : K → (Fin 76 → K) → Option (PointClaimRow → K)) : Prop :=
  rustPrepare = fun gamma claims => some (sourcePreparedPointClaims gamma claims)

def sourcePoint0 : PointClaimRow := ⟨0, by decide⟩
def sourcePoint1 : PointClaimRow := ⟨1, by decide⟩
def sourcePoint2 : PointClaimRow := ⟨2, by decide⟩
def sourcePoint3 : PointClaimRow := ⟨3, by decide⟩

/-- Initial relation claim assembled by the four-claim caller. -/
def sourceCallerInitialClaim (inactive kappa gamma : K)
    (claims : Fin 76 → K) : K :=
  inactive + sourcePreparedPointClaim gamma claims sourcePoint0 +
    kappa * sourcePreparedPointClaim gamma claims sourcePoint1 +
    kappa ^ 2 * sourcePreparedPointClaim gamma claims sourcePoint2 +
    kappa ^ 3 * sourcePreparedPointClaim gamma claims sourcePoint3

theorem sourceCallerInitialClaim_explicit
    (inactive kappa gamma : K) (claims : Fin 76 → K) :
    sourceCallerInitialClaim inactive kappa gamma claims =
      inactive + sourcePreparedPointClaim gamma claims sourcePoint0 +
        kappa * sourcePreparedPointClaim gamma claims sourcePoint1 +
        kappa ^ 2 * sourcePreparedPointClaim gamma claims sourcePoint2 +
        kappa ^ 3 * sourcePreparedPointClaim gamma claims sourcePoint3 := by
  rfl

/-! ## Generic main-weight folds and the separate compact weights -/

/-- Concrete weight functions added by the two OOD observations in each of
the four rounds.  The second function retains its dependence on the first
mix, matching the maintained transcript order. -/
structure SourceMainWeightSchedule (K : Type*) where
  initial : Fin 1024 → K
  round0First : Fin 1024 → K
  round0Second : K → Fin 1024 → K
  round1First : Fin 256 → K
  round1Second : K → Fin 256 → K
  round2First : Fin 64 → K
  round2Second : K → Fin 64 → K
  round3First : Fin 16 → K
  round3Second : K → Fin 16 → K

def sourceMainWeights1 (schedule : SourceMainWeightSchedule K)
    (challenges : TwelveRelationChallenges K) : Fin 256 → K :=
  let block := round0Block challenges
  dualWeightFoldLayer 256 block.2
    (mixedWeights schedule.initial schedule.round0First schedule.round0Second
      block.1.1 block.1.2)

def sourceMainWeights2 (schedule : SourceMainWeightSchedule K)
    (challenges : TwelveRelationChallenges K) : Fin 64 → K :=
  let block := round1Block challenges
  dualWeightFoldLayer 64 block.2
    (mixedWeights (sourceMainWeights1 schedule challenges)
      schedule.round1First schedule.round1Second block.1.1 block.1.2)

def sourceMainWeights3 (schedule : SourceMainWeightSchedule K)
    (challenges : TwelveRelationChallenges K) : Fin 16 → K :=
  let block := round2Block challenges
  dualWeightFoldLayer 16 block.2
    (mixedWeights (sourceMainWeights2 schedule challenges)
      schedule.round2First schedule.round2Second block.1.1 block.1.2)

/-- Final four main weights after the exact four arity-four folds. -/
def sourceMainFinalWeights (schedule : SourceMainWeightSchedule K)
    (challenges : TwelveRelationChallenges K) : Fin 4 → K :=
  let block := round3Block challenges
  dualWeightFoldLayer 4 block.2
    (mixedWeights (sourceMainWeights3 schedule challenges)
      schedule.round3First schedule.round3Second block.1.1 block.1.2)

def sourceMainFinalDot (schedule : SourceMainWeightSchedule K)
    (challenges : TwelveRelationChallenges K) (finalValues : Fin 4 → K) : K :=
  candidateClaim (sourceMainFinalWeights schedule challenges) finalValues

/-- The four alpha challenges projected from the maintained nested transcript
shape. -/
def sourceRelationAlphas (challenges : TwelveRelationChallenges K) : Fin 4 → K :=
  fun round =>
    if round = 0 then (round0Block challenges).2
    else if round = 1 then (round1Block challenges).2
    else if round = 2 then (round2Block challenges).2
    else (round3Block challenges).2

/-- Fold an additive covector without adding the OOD functionals a second
time.  This is how the separate compact Component-B state shares the four
relation challenges. -/
def sourceFoldOnly1 (alphas : Fin 4 → K) (weights : Fin 1024 → K) :
    Fin 256 → K :=
  dualWeightFoldLayer 256 (alphas 0) weights

def sourceFoldOnly2 (alphas : Fin 4 → K) (weights : Fin 1024 → K) :
    Fin 64 → K :=
  dualWeightFoldLayer 64 (alphas 1) (sourceFoldOnly1 alphas weights)

def sourceFoldOnly3 (alphas : Fin 4 → K) (weights : Fin 1024 → K) :
    Fin 16 → K :=
  dualWeightFoldLayer 16 (alphas 2) (sourceFoldOnly2 alphas weights)

def sourceFoldOnlyFinal (alphas : Fin 4 → K) (weights : Fin 1024 → K) :
    Fin 4 → K :=
  dualWeightFoldLayer 4 (alphas 3) (sourceFoldOnly3 alphas weights)

def sourceFoldOnlyFinalDot (alphas : Fin 4 → K)
    (weights : Fin 1024 → K) (finalValues : Fin 4 → K) : K :=
  candidateClaim (sourceFoldOnlyFinal alphas weights) finalValues

theorem mixedWeights_add_incoming {n : Nat}
    (incoming extra first : Fin (4 * n) → K)
    (second : K → Fin (4 * n) → K) (firstMix secondMix : K) :
    mixedWeights (fun index => incoming index + extra index) first second
        firstMix secondMix =
      fun index => mixedWeights incoming first second firstMix secondMix index +
        extra index := by
  funext index
  simp only [mixedWeights]
  ring

theorem dualWeightFoldLayer_add (n : Nat) (alpha : K)
    (left right : Fin (4 * n) → K) :
    dualWeightFoldLayer n alpha (fun index => left index + right index) =
      fun fibre => dualWeightFoldLayer n alpha left fibre +
        dualWeightFoldLayer n alpha right fibre := by
  funext fibre
  unfold dualWeightFoldLayer dualWeightFoldValue
  ring

theorem candidateClaim_add_weights {n : Nat}
    (left right values : Fin n → K) :
    candidateClaim (fun index => left index + right index) values =
      candidateClaim left values + candidateClaim right values := by
  simp only [candidateClaim, mul_add, Finset.sum_add_distrib]

/-- Replace only the initial main covector, leaving every OOD addition
unchanged. -/
def SourceMainWeightSchedule.withInitial
    (schedule : SourceMainWeightSchedule K) (initial : Fin 1024 → K) :
    SourceMainWeightSchedule K :=
  { schedule with initial := initial }

/-- Linearity of the complete generic weight run.  An extra initial covector
passes through all four folds but never receives the OOD additions again. -/
theorem sourceMainFinalWeights_add_initial
    (schedule : SourceMainWeightSchedule K)
    (extra : Fin 1024 → K) (challenges : TwelveRelationChallenges K) :
    sourceMainFinalWeights
        (schedule.withInitial (fun index => schedule.initial index + extra index))
        challenges =
      fun index => sourceMainFinalWeights schedule challenges index +
        sourceFoldOnlyFinal (sourceRelationAlphas challenges) extra index := by
  let alphas : Fin 4 → K := sourceRelationAlphas challenges
  have halpha0 : alphas 0 = (round0Block challenges).2 := by
    simp [alphas, sourceRelationAlphas]
  have halpha1 : alphas 1 = (round1Block challenges).2 := by
    simp [alphas, sourceRelationAlphas]
  have halpha2 : alphas 2 = (round2Block challenges).2 := by
    simp [alphas, sourceRelationAlphas, Fin.ext_iff]
  have halpha3 : alphas 3 = (round3Block challenges).2 := by
    simp [alphas, sourceRelationAlphas, Fin.ext_iff]
  have h1 :
      sourceMainWeights1
          (schedule.withInitial
            (fun index => schedule.initial index + extra index)) challenges =
        fun index => sourceMainWeights1 schedule challenges index +
          sourceFoldOnly1 alphas extra index := by
    unfold sourceMainWeights1 SourceMainWeightSchedule.withInitial
    simp only
    rw [mixedWeights_add_incoming, dualWeightFoldLayer_add]
    simp only [sourceFoldOnly1, halpha0]
  have h2 :
      sourceMainWeights2
          (schedule.withInitial
            (fun index => schedule.initial index + extra index)) challenges =
        fun index => sourceMainWeights2 schedule challenges index +
          sourceFoldOnly2 alphas extra index := by
    unfold sourceMainWeights2
    rw [h1]
    simp only [SourceMainWeightSchedule.withInitial]
    rw [mixedWeights_add_incoming, dualWeightFoldLayer_add]
    simp only [sourceFoldOnly2, halpha1]
  have h3 :
      sourceMainWeights3
          (schedule.withInitial
            (fun index => schedule.initial index + extra index)) challenges =
        fun index => sourceMainWeights3 schedule challenges index +
          sourceFoldOnly3 alphas extra index := by
    unfold sourceMainWeights3
    rw [h2]
    simp only [SourceMainWeightSchedule.withInitial]
    rw [mixedWeights_add_incoming, dualWeightFoldLayer_add]
    simp only [sourceFoldOnly3, halpha2]
  unfold sourceMainFinalWeights
  rw [h3]
  simp only [SourceMainWeightSchedule.withInitial]
  rw [mixedWeights_add_incoming, dualWeightFoldLayer_add]
  simp only [sourceFoldOnlyFinal, halpha3, alphas]

/-- The `/4` dual fold used by the maintained relation model is exactly the
two-halving fold used by the compact evaluator. -/
theorem dualWeightFoldLayer_eq_dualFold4
    (h2 : (2 : K) ≠ 0) (n : Nat) (alpha : K)
    (weights : Fin (4 * n) → K) :
    dualWeightFoldLayer n alpha weights = dualFold4 alpha weights := by
  funext fibre
  have hindex0 :
      (⟨4 * fibre.val, by omega⟩ : Fin (4 * n)) =
        AspisV5ComponentCConcreteFoldLinearity.childIndex fibre 0 := by
    apply Fin.ext
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex]
  have hindex1 :
      (⟨4 * fibre.val + 1, by omega⟩ : Fin (4 * n)) =
        AspisV5ComponentCConcreteFoldLinearity.childIndex fibre 1 := by
    apply Fin.ext
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex]
  have hindex2 :
      (⟨4 * fibre.val + 2, by omega⟩ : Fin (4 * n)) =
        AspisV5ComponentCConcreteFoldLinearity.childIndex fibre 2 := by
    apply Fin.ext
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex]
  have hindex3 :
      (⟨4 * fibre.val + 3, by omega⟩ : Fin (4 * n)) =
        AspisV5ComponentCConcreteFoldLinearity.childIndex fibre 3 := by
    apply Fin.ext
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex]
  unfold dualWeightFoldLayer dualWeightFoldValue dualFold4
  rw [div_four_eq_quarter_mul h2]
  rw [hindex0, hindex1, hindex2, hindex3]

theorem sourceFoldOnlyFinal_eq_fourDualFolds
    (h2 : (2 : K) ≠ 0) (alphas : Fin 4 → K)
    (weights : Fin 1024 → K) :
    sourceFoldOnlyFinal alphas weights = fourDualFolds alphas weights := by
  unfold sourceFoldOnlyFinal sourceFoldOnly3 sourceFoldOnly2 sourceFoldOnly1
    fourDualFolds
  rw [dualWeightFoldLayer_eq_dualFold4 h2,
    dualWeightFoldLayer_eq_dualFold4 h2,
    dualWeightFoldLayer_eq_dualFold4 h2,
    dualWeightFoldLayer_eq_dualFold4 h2]

/-- The independently modeled compact state computes the same additive dot
as four generic folds of its dense initial covector. -/
theorem sourceFoldOnlyFinalDot_terminalWeights_eq_optimized
    (h2 : (2 : K) ≠ 0) (point : Fin 10 → K) (scale : K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K) :
    sourceFoldOnlyFinalDot alphas (terminalWeights point scale) finalValues =
      optimizedCompactFinalDot point scale alphas finalValues := by
  rw [optimizedCompactFinalDot_eq_fourDenseDualFolds h2]
  unfold sourceFoldOnlyFinalDot compactFinalDot
  rw [sourceFoldOnlyFinal_eq_fourDualFolds h2]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Exact remaining generic `WeightAccumulator` boundary, after constructors
have supplied the nine concrete weight functions above. -/
def ExactRustMainWeightFoldAndDotEquality
    (rustRun : SourceMainWeightSchedule K → TwelveRelationChallenges K →
      (Fin 4 → K) → K) : Prop :=
  rustRun = sourceMainFinalDot

/-! ### The compact Component-B operations -/

/-- Stage-typed spelling of the compact operations.  The production method
uses one fold counter; stage-typed functions make the exact equality needed
at each of the four calls independently inspectable. -/
structure SourceCompactBOperations (K : Type*) where
  newState : (Fin 10 → K) → K → OptimizedState K
  fold0 : K → OptimizedState K → OptimizedState K
  fold1 : K → OptimizedState K → OptimizedState K
  fold2 : K → OptimizedState K → OptimizedState K
  fold3 : K → OptimizedState K → OptimizedState K
  finalWeights : OptimizedState K → Fin 4 → K
  dot : OptimizedState K → (Fin 4 → K) → K

def runSourceCompactB (operations : SourceCompactBOperations K)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K)
    (finalValues : Fin 4 → K) : K :=
  operations.dot
    (operations.fold3 (alphas 3)
      (operations.fold2 (alphas 2)
        (operations.fold1 (alphas 1)
          (operations.fold0 (alphas 0)
            (operations.newState point scale)))))
    finalValues

/-- Seven separate executable equalities for
`CompactBTerminalWeights::{new,fold,final_weights,dot}`.  This is the exact
remaining Charon/Aeneas boundary for the compact state; it does not assume a
terminal check or a relation-acceptance conclusion. -/
structure ExactRustCompactBOperations
    (operations : SourceCompactBOperations K) : Prop where
  newState : operations.newState = optimizedInit
  fold0 : operations.fold0 = optimizedFoldZero
  fold1 : operations.fold1 = optimizedFoldOne
  fold2 : operations.fold2 = optimizedFoldTwo
  fold3 : operations.fold3 = optimizedFoldThree
  finalWeights : operations.finalWeights = optimizedFinalWeights
  dot : operations.dot = fun state finalValues =>
    ∑ index, optimizedFinalWeights state index * finalValues index

/-- Once the seven operation equalities are supplied, the complete compact
run is definitionally the independently proved optimized evaluator. -/
theorem runSourceCompactB_eq_optimized
    (operations : SourceCompactBOperations K)
    (exact : ExactRustCompactBOperations operations)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K)
    (finalValues : Fin 4 → K) :
    runSourceCompactB operations point scale alphas finalValues =
      optimizedCompactFinalDot point scale alphas finalValues := by
  unfold runSourceCompactB
  rw [exact.newState, exact.fold0, exact.fold1, exact.fold2, exact.fold3,
    exact.dot]
  rfl

/-! ### Combining the main and compact covectors -/

/-- Exact field-by-field projection of a source weight schedule into the
maintained family at one transcript.  Component B is represented in the
family's initial dense covector but is carried separately by production Rust. -/
structure SourceWeightScheduleMatchesFamily
    {Candidate : Type*}
    (schedule : SourceMainWeightSchedule K)
    (componentBPoint : Fin 10 → K) (componentBScale : K)
    (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop where
  initial : family.initialWeights = fun index =>
    schedule.initial index + terminalWeights componentBPoint componentBScale index
  round0First : family.round0.firstWeights () = schedule.round0First
  round0Second : family.round0.secondWeights () = schedule.round0Second
  round1First : family.round1.firstWeights (round0Block challenges) =
    schedule.round1First
  round1Second : family.round1.secondWeights (round0Block challenges) =
    schedule.round1Second
  round2First : family.round2.firstWeights challenges.1.1 = schedule.round2First
  round2Second : family.round2.secondWeights challenges.1.1 = schedule.round2Second
  round3First : family.round3.firstWeights challenges.1 = schedule.round3First
  round3Second : family.round3.secondWeights challenges.1 = schedule.round3Second

/-- The maintained combined final weights are the sum of the generic main
weights and the four-fold dense Component-B weights. -/
theorem sharedFinalWeights_eq_source_main_additive
    {Candidate : Type*}
    (schedule : SourceMainWeightSchedule K)
    (componentBPoint : Fin 10 → K) (componentBScale : K)
    (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K)
    (correspondence : SourceWeightScheduleMatchesFamily schedule componentBPoint
      componentBScale family challenges) :
    sharedFinalWeights family challenges = fun index =>
      sourceMainFinalWeights schedule challenges index +
        sourceFoldOnlyFinal (sourceRelationAlphas challenges)
          (terminalWeights componentBPoint componentBScale) index := by
  have hcombined :
      sharedFinalWeights family challenges =
        sourceMainFinalWeights
          (schedule.withInitial (fun index =>
            schedule.initial index +
              terminalWeights componentBPoint componentBScale index))
          challenges := by
    have hround1First := correspondence.round1First
    have hround1Second := correspondence.round1Second
    have hround2First := correspondence.round2First
    have hround2Second := correspondence.round2Second
    have hround3First := correspondence.round3First
    have hround3Second := correspondence.round3Second
    simp only [round0Block] at hround1First hround1Second
    unfold sharedFinalWeights sharedWeights3 sharedWeights2 sharedWeights1
      RelationRoundMessages.nextWeights sourceMainFinalWeights
      sourceMainWeights3 sourceMainWeights2 sourceMainWeights1
    rw [correspondence.initial, correspondence.round0First,
      correspondence.round0Second, hround1First, hround1Second,
      hround2First, hround2Second, hround3First, hround3Second]
    simp only [SourceMainWeightSchedule.withInitial, round0Block, round1Block,
      round2Block, round3Block]
  rw [hcombined]
  exact sourceMainFinalWeights_add_initial schedule
    (terminalWeights componentBPoint componentBScale) challenges

/-- Consequently, the maintained terminal dot is exactly the sum of the
production main dot and the independently proved compact Component-B dot. -/
theorem sharedFinalDot_eq_source_main_additive
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (schedule : SourceMainWeightSchedule K)
    (componentBPoint : Fin 10 → K) (componentBScale : K)
    (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K)
    (finalValues : Fin 4 → K)
    (correspondence : SourceWeightScheduleMatchesFamily schedule componentBPoint
      componentBScale family challenges) :
    candidateClaim (sharedFinalWeights family challenges) finalValues =
      sourceMainFinalDot schedule challenges finalValues +
        optimizedCompactFinalDot componentBPoint componentBScale
          (sourceRelationAlphas challenges) finalValues := by
  rw [sharedFinalWeights_eq_source_main_additive schedule componentBPoint
    componentBScale family challenges correspondence]
  rw [candidateClaim_add_weights]
  change sourceMainFinalDot schedule challenges finalValues +
      sourceFoldOnlyFinalDot (sourceRelationAlphas challenges)
        (terminalWeights componentBPoint componentBScale) finalValues = _
  rw [sourceFoldOnlyFinalDot_terminalWeights_eq_optimized h2]

/-- The decoded scalar data used by one iteration of
`verify_v5_relation_stress_with_additive`.

The two weight additions are represented at the final check by
`mainFinalDot + additiveFinalDot`.  Their vector-state correspondence is part
of `SourceRelationInputMatchesFamily`, rather than being silently assumed by
this control-flow definition. -/
structure SourceRelationRound (K : Type*) where
  firstValue : K
  secondValue : K
  firstMix : K
  secondMix : K
  polynomial : RelationCoefficients K
  alpha : K

/-- The three transcript challenges consumed in one relation round. -/
def SourceRelationRound.challenges
    (round : SourceRelationRound K) : RelationRoundChallenges K :=
  ((round.firstMix, round.secondMix), round.alpha)

/-- The decoded values and two final dot products used by the complete
four-round Rust relation checker. -/
structure SourceRelationInput (K : Type*) where
  initialClaim : K
  round0 : SourceRelationRound K
  round1 : SourceRelationRound K
  round2 : SourceRelationRound K
  round3 : SourceRelationRound K
  finalCoefficients : Fin 4 → K
  mainFinalDot : K
  additiveFinalDot : K

/-- The twelve relation challenges in their maintained nested order. -/
def SourceRelationInput.challenges
    (input : SourceRelationInput K) : TwelveRelationChallenges K :=
  (((input.round0.challenges, input.round1.challenges),
    input.round2.challenges), input.round3.challenges)

/-! ## The production relation caller at field level -/

/-- Values available after the current production parsers and transcript
driver have succeeded.  Raw byte decoding is kept separate above so malformed
encodings remain rejecting rather than becoming arbitrary field values. -/
structure SourceMode9CallerData (K : Type*) where
  inactiveClaim : K
  kappa : K
  gamma : K
  pointMajorClaims : Fin 76 → K
  relationTail : PhysicalRelationFields K
  alphas : Fin 4 → K
  mainWeights : SourceMainWeightSchedule K
  componentBPoint : Fin 10 → K

/-- One of the four decoded relation rounds. -/
def sourceCallerRound (data : SourceMode9CallerData K) (round : Fin 4) :
    SourceRelationRound K where
  firstValue := data.relationTail.oodValues round 0
  secondValue := data.relationTail.oodValues round 1
  firstMix := data.relationTail.oodMixes round 0
  secondMix := data.relationTail.oodMixes round 1
  polynomial := data.relationTail.polynomialCoefficients round
  alpha := data.alphas round

/-- The exact twelve relation challenges read by the scalar verifier. -/
def sourceCallerChallenges (data : SourceMode9CallerData K) :
    TwelveRelationChallenges K :=
  let round0 : RelationRoundChallenges K :=
    ((data.relationTail.oodMixes 0 0,
      data.relationTail.oodMixes 0 1), data.alphas 0)
  let round1 : RelationRoundChallenges K :=
    ((data.relationTail.oodMixes 1 0,
      data.relationTail.oodMixes 1 1), data.alphas 1)
  let round2 : RelationRoundChallenges K :=
    ((data.relationTail.oodMixes 2 0,
      data.relationTail.oodMixes 2 1), data.alphas 2)
  let round3 : RelationRoundChallenges K :=
    ((data.relationTail.oodMixes 3 0,
      data.relationTail.oodMixes 3 1), data.alphas 3)
  (((round0, round1), round2), round3)

/-- Assemble exactly the arguments passed to
`verify_v5_relation_stress_with_additive`. -/
def sourceMode9RelationInput (data : SourceMode9CallerData K) :
    SourceRelationInput K where
  initialClaim := sourceCallerInitialClaim data.inactiveClaim data.kappa
    data.gamma data.pointMajorClaims
  round0 := sourceCallerRound data 0
  round1 := sourceCallerRound data 1
  round2 := sourceCallerRound data 2
  round3 := sourceCallerRound data 3
  finalCoefficients := data.relationTail.finalCoefficients
  mainFinalDot := sourceMainFinalDot data.mainWeights
    (sourceCallerChallenges data) data.relationTail.finalCoefficients
  additiveFinalDot := optimizedCompactFinalDot data.componentBPoint
    (data.kappa ^ 3) data.alphas data.relationTail.finalCoefficients

theorem sourceMode9RelationInput_challenges
    (data : SourceMode9CallerData K) :
    (sourceMode9RelationInput data).challenges = sourceCallerChallenges data := by
  rfl

theorem sourceCallerChallenges_alphas (data : SourceMode9CallerData K) :
    sourceRelationAlphas (sourceCallerChallenges data) = data.alphas := by
  funext round
  fin_cases round <;>
    simp [sourceRelationAlphas, sourceCallerChallenges, round0Block,
      round1Block, round2Block, round3Block, Fin.ext_iff]

/-- The exact running-claim update before a boundary check. -/
def sourceClaimAfterMixes (claim : K) (round : SourceRelationRound K) : K :=
  claim + round.firstMix * round.firstValue +
    round.secondMix * round.secondValue

/-- One early-return iteration of the Rust relation loop. -/
noncomputable def runSourceRelationRound [DecidableEq K]
    (claim : K) (round : SourceRelationRound K) : Option K :=
  if relationBoundary round.polynomial = sourceClaimAfterMixes claim round then
    some ((relationPolynomial round.polynomial).eval round.alpha)
  else
    none

/-- Output returned by the source-shaped relation checker. -/
structure SourceRelationOutput (K : Type*) where
  finalCoefficients : Fin 4 → K
  terminalClaim : K

/-- Four ordered boundary checks followed by the final combined dot check.

The nested tests mirror Rust's early-return control flow. -/
noncomputable def runSourceRelationVerifier [DecidableEq K]
    (input : SourceRelationInput K) : Option (SourceRelationOutput K) :=
  if relationBoundary input.round0.polynomial =
      sourceClaimAfterMixes input.initialClaim input.round0 then
    let claim1 := (relationPolynomial input.round0.polynomial).eval
      input.round0.alpha
    if relationBoundary input.round1.polynomial =
        sourceClaimAfterMixes claim1 input.round1 then
      let claim2 := (relationPolynomial input.round1.polynomial).eval
        input.round1.alpha
      if relationBoundary input.round2.polynomial =
          sourceClaimAfterMixes claim2 input.round2 then
        let claim3 := (relationPolynomial input.round2.polynomial).eval
          input.round2.alpha
        if relationBoundary input.round3.polynomial =
            sourceClaimAfterMixes claim3 input.round3 then
          let finalClaim := (relationPolynomial input.round3.polynomial).eval
            input.round3.alpha
          if input.mainFinalDot + input.additiveFinalDot = finalClaim then
            some
              { finalCoefficients := input.finalCoefficients
                terminalClaim := finalClaim }
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- The same verifier written as four calls to a one-round function.

This spelling exists because the pinned Aeneas version can translate the
one-round shape but rejects the deployed function's early returns inside its
nested loops.  `roundVerifier` is kept as an argument so an extracted helper
can be connected without assuming anything about its implementation. -/
noncomputable def runSourceRelationVerifierWithRound [DecidableEq K]
    (roundVerifier : K → SourceRelationRound K → Option K)
    (input : SourceRelationInput K) : Option (SourceRelationOutput K) :=
  match roundVerifier input.initialClaim input.round0 with
  | none => none
  | some claim1 =>
      match roundVerifier claim1 input.round1 with
      | none => none
      | some claim2 =>
          match roundVerifier claim2 input.round2 with
          | none => none
          | some claim3 =>
              match roundVerifier claim3 input.round3 with
              | none => none
              | some finalClaim =>
                  if input.mainFinalDot + input.additiveFinalDot = finalClaim then
                    some
                      { finalCoefficients := input.finalCoefficients
                        terminalClaim := finalClaim }
                  else
                    none

/-- Four explicit calls to the maintained one-round function. -/
noncomputable def runSourceRelationVerifierFourCalls [DecidableEq K]
    (input : SourceRelationInput K) : Option (SourceRelationOutput K) :=
  runSourceRelationVerifierWithRound runSourceRelationRound input

/-- Exact equality between the four-call spelling and the source-shaped
nested checks, for every field input.  This is a proof of the control-flow
rewrite itself; it is not a claim that the deployed Rust binary used the
four-call spelling. -/
theorem runSourceRelationVerifierFourCalls_eq_source [DecidableEq K]
    (input : SourceRelationInput K) :
    runSourceRelationVerifierFourCalls input =
      runSourceRelationVerifier input := by
  by_cases h0 : relationBoundary input.round0.polynomial =
      sourceClaimAfterMixes input.initialClaim input.round0
  · by_cases h1 : relationBoundary input.round1.polynomial =
        sourceClaimAfterMixes
          (∑ degree,
            input.round0.polynomial degree * input.round0.alpha ^ degree.val)
          input.round1
    · by_cases h2 : relationBoundary input.round2.polynomial =
          sourceClaimAfterMixes
            (∑ degree,
              input.round1.polynomial degree * input.round1.alpha ^ degree.val)
            input.round2
      · by_cases h3 : relationBoundary input.round3.polynomial =
            sourceClaimAfterMixes
              (∑ degree,
                input.round2.polynomial degree * input.round2.alpha ^ degree.val)
              input.round3
        · simp [runSourceRelationVerifierFourCalls,
            runSourceRelationVerifierWithRound, runSourceRelationRound,
            runSourceRelationVerifier, h0, h1, h2, h3]
        · simp [runSourceRelationVerifierFourCalls,
            runSourceRelationVerifierWithRound, runSourceRelationRound,
            runSourceRelationVerifier, h0, h1, h2, h3]
      · simp [runSourceRelationVerifierFourCalls,
          runSourceRelationVerifierWithRound, runSourceRelationRound,
          runSourceRelationVerifier, h0, h1, h2]
    · simp [runSourceRelationVerifierFourCalls,
        runSourceRelationVerifierWithRound, runSourceRelationRound,
        runSourceRelationVerifier, h0, h1]
  · simp [runSourceRelationVerifierFourCalls,
      runSourceRelationVerifierWithRound, runSourceRelationRound,
      runSourceRelationVerifier, h0]

/-- Small implementation boundary left by making the extracted one-round
helper's field, decoder, sumcheck-kernel, and weight operations opaque.

`extractedRound` denotes that generated helper after its opaque Rust values
have been mapped into `K` and after successful weight updates have been
projected away; the generated definition and temporary rewrite are pinned in
the relation-acceptance replay bundle.

Only the soundness direction is required: whenever that extracted helper
returns success, its scalar claim transition is accepted by the maintained
one-round model with the same output.  Rejections need not agree. -/
def ExtractedUnrolledRoundPrimitivesAgree [DecidableEq K]
    (extractedRound : K → SourceRelationRound K → Option K) : Prop :=
  ∀ claim round output,
    extractedRound claim round = some output →
      runSourceRelationRound claim round = some output

/-- Per-round primitive correspondence transfers a successful four-call
execution to the maintained four-call verifier. -/
theorem extractedRound_success_implies_fourCallVerifier_success
    [DecidableEq K]
    (extractedRound : K → SourceRelationRound K → Option K)
    (primitiveCorrespondence :
      ExtractedUnrolledRoundPrimitivesAgree extractedRound)
    {input : SourceRelationInput K} {output : SourceRelationOutput K}
    (success :
      runSourceRelationVerifierWithRound extractedRound input = some output) :
    runSourceRelationVerifierFourCalls input = some output := by
  cases h0 : extractedRound input.initialClaim input.round0 with
  | none =>
      simp [runSourceRelationVerifierWithRound, h0] at success
  | some claim1 =>
    cases h1 : extractedRound claim1 input.round1 with
    | none =>
        simp [runSourceRelationVerifierWithRound, h0, h1] at success
    | some claim2 =>
      cases h2 : extractedRound claim2 input.round2 with
      | none =>
          simp [runSourceRelationVerifierWithRound, h0, h1, h2] at success
      | some claim3 =>
        cases h3 : extractedRound claim3 input.round3 with
        | none =>
            simp [runSourceRelationVerifierWithRound, h0, h1, h2, h3] at success
        | some finalClaim =>
          have hs0 := primitiveCorrespondence
            input.initialClaim input.round0 claim1 h0
          have hs1 := primitiveCorrespondence claim1 input.round1 claim2 h1
          have hs2 := primitiveCorrespondence claim2 input.round2 claim3 h2
          have hs3 := primitiveCorrespondence claim3 input.round3 finalClaim h3
          simpa [runSourceRelationVerifierFourCalls,
            runSourceRelationVerifierWithRound, hs0, hs1, hs2, hs3] using
            (show
              (if input.mainFinalDot + input.additiveFinalDot = finalClaim then
                some
                  { finalCoefficients := input.finalCoefficients
                    terminalClaim := finalClaim }
              else none) = some output by
                simpa [runSourceRelationVerifierWithRound, h0, h1, h2, h3]
                  using success)

/-- Remaining syntactic transformation boundary for the unchanged deployed
Rust function.  It states only the direction needed for soundness: a success
of the original nested-loop function is also a success of the extracted
four-call spelling with the same output.  Tests cannot discharge this
universal statement. -/
def OriginalNestedLoopSuccessImpliesFourCallSuccess [DecidableEq K]
    (originalVerifier : SourceRelationInput K → Option (SourceRelationOutput K))
    (extractedRound : K → SourceRelationRound K → Option K) : Prop :=
  ∀ input output, originalVerifier input = some output →
    runSourceRelationVerifierWithRound extractedRound input = some output

/-- The named loop-unrolling boundary and success-only primitive
correspondence reduce an original Rust success to a success of the maintained
source model. -/
theorem originalNestedLoop_success_implies_source_success [DecidableEq K]
    (originalVerifier : SourceRelationInput K → Option (SourceRelationOutput K))
    (extractedRound : K → SourceRelationRound K → Option K)
    (primitiveCorrespondence :
      ExtractedUnrolledRoundPrimitivesAgree extractedRound)
    (transformation :
      OriginalNestedLoopSuccessImpliesFourCallSuccess originalVerifier
        extractedRound)
    {input : SourceRelationInput K} {output : SourceRelationOutput K}
    (success : originalVerifier input = some output) :
    runSourceRelationVerifier input = some output := by
  have fourCallSuccess := transformation input output success
  have sourceFourCallSuccess :=
    extractedRound_success_implies_fourCallVerifier_success extractedRound
      primitiveCorrespondence fourCallSuccess
  rw [runSourceRelationVerifierFourCalls_eq_source] at sourceFourCallSuccess
  exact sourceFourCallSuccess

/-- The production caller accepts the scalar relation result only when its
four decoded final coefficients equal the final polynomial already passed to
the FRI checker. -/
noncomputable def runSourceMode9RelationCaller [DecidableEq K]
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K) :
    Option K :=
  match runSourceRelationVerifier (sourceMode9RelationInput data) with
  | none => none
  | some output =>
      if output.finalCoefficients = friFinalPolynomial then
        some output.terminalClaim
      else
        none

/-- Exact remaining scalar-loop extraction boundary. -/
def ExactRustRelationVerifierEquality [DecidableEq K]
    (rustVerifier : SourceRelationInput K → Option (SourceRelationOutput K)) :
    Prop :=
  rustVerifier = runSourceRelationVerifier

/-- Exact remaining `verify_mode9_relation_phase` extraction boundary. -/
def ExactRustMode9RelationCallerEquality [DecidableEq K]
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K) : Prop :=
  rustCaller = runSourceMode9RelationCaller

/-- The small post-relation part of the production caller, parameterized by
the relation checker it invokes.  Keeping this wrapper separate means an
extraction proof for the scalar checker and an extraction proof for the
caller's final-coefficient comparison do not have to be bundled into one
opaque equality. -/
noncomputable def runSourceMode9RelationCallerWith [DecidableEq K]
    (relationVerifier : SourceRelationInput K → Option (SourceRelationOutput K))
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K) :
    Option K :=
  match relationVerifier (sourceMode9RelationInput data) with
  | none => none
  | some output =>
      if output.finalCoefficients = friFinalPolynomial then
        some output.terminalClaim
      else
        none

/-- Exact remaining equality for only the wrapper around the relation call.
It contains the final four-coefficient comparison and returned terminal
claim, but not the scalar relation loop itself. -/
def ExactRustMode9CallerPostRelationEquality [DecidableEq K]
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K)
    (rustVerifier : SourceRelationInput K → Option (SourceRelationOutput K)) :
    Prop :=
  rustCaller = runSourceMode9RelationCallerWith rustVerifier

/-- The broad caller equality follows from the two smaller executable
equalities.  This is the form intended for separate Charon/Aeneas extraction
of the scalar loop and its production call site. -/
theorem exactRustMode9RelationCallerEquality_of_parts [DecidableEq K]
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K)
    (rustVerifier : SourceRelationInput K → Option (SourceRelationOutput K))
    (verifierEquality : ExactRustRelationVerifierEquality rustVerifier)
    (wrapperEquality :
      ExactRustMode9CallerPostRelationEquality rustCaller rustVerifier) :
    ExactRustMode9RelationCallerEquality rustCaller := by
  rw [wrapperEquality, verifierEquality]
  rfl

section SourceCallerSuccess

variable [DecidableEq K]

/-- A successful scalar checker returns the same final coefficients carried
by its input; they cannot be replaced by a separately chosen array. -/
theorem sourceRelationVerifier_output_final_coefficients
    (input : SourceRelationInput K) (output : SourceRelationOutput K)
    (success : runSourceRelationVerifier input = some output) :
    output.finalCoefficients = input.finalCoefficients := by
  unfold runSourceRelationVerifier at success
  split at success <;> rename_i hboundary0
  · simp only [] at success
    split at success <;> rename_i hboundary1
    · split at success <;> rename_i hboundary2
      · split at success <;> rename_i hboundary3
        · split at success <;> rename_i hterminal
          · simp only [Option.some.injEq] at success
            cases success
            rfl
          · simp at success
        · simp at success
      · simp at success
    · simp at success
  · simp at success

/-- Caller success contains an actual successful scalar relation run. -/
theorem sourceCaller_success_implies_relation_success
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K)
    {terminalClaim : K}
    (success : runSourceMode9RelationCaller data friFinalPolynomial =
      some terminalClaim) :
    ∃ output,
      runSourceRelationVerifier (sourceMode9RelationInput data) = some output := by
  cases hrun : runSourceRelationVerifier (sourceMode9RelationInput data) with
  | none => simp [runSourceMode9RelationCaller, hrun] at success
  | some output => exact ⟨output, rfl⟩

/-- Mandatory caller equality: every successful caller execution uses exactly
the same four final coefficients as FRI. -/
theorem sourceCaller_success_implies_final_coefficients_equal_fri
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K)
    {terminalClaim : K}
    (success : runSourceMode9RelationCaller data friFinalPolynomial =
      some terminalClaim) :
    data.relationTail.finalCoefficients = friFinalPolynomial := by
  cases hrun : runSourceRelationVerifier (sourceMode9RelationInput data) with
  | none => simp [runSourceMode9RelationCaller, hrun] at success
  | some output =>
      have hreturned := sourceRelationVerifier_output_final_coefficients
        (sourceMode9RelationInput data) output hrun
      have callerSuccess := success
      simp only [runSourceMode9RelationCaller, hrun] at callerSuccess
      split at callerSuccess <;> rename_i hequal
      · have hinput :
            (sourceMode9RelationInput data).finalCoefficients =
              friFinalPolynomial := hreturned.symm.trans hequal
        exact hinput
      · simp at callerSuccess

end SourceCallerSuccess

/-! ## Exact projection into the maintained family -/

/-- The decoded source input is exactly the data used by one maintained
coherent family at the challenges carried by that same input.

The last field is the one place where the separately folded Rust main and
additive states are combined.  It asks only for equality of their actual
final dots with the maintained combined final weight dot. -/
structure SourceRelationInputMatchesFamily
    {Candidate : Type*}
    (input : SourceRelationInput K)
    (family : CoherentCandidateFamily K Candidate) : Prop where
  initialClaim : input.initialClaim = family.initialClaim
  round0First : input.round0.firstValue = family.round0.claimedFirst ()
  round0Second : input.round0.secondValue =
    family.round0.claimedSecond () input.round0.firstMix
  round0Polynomial : input.round0.polynomial =
    family.round0.claimedPolynomial ()
      (input.round0.firstMix, input.round0.secondMix)
  round1First : input.round1.firstValue =
    family.round1.claimedFirst input.round0.challenges
  round1Second : input.round1.secondValue =
    family.round1.claimedSecond input.round0.challenges input.round1.firstMix
  round1Polynomial : input.round1.polynomial =
    family.round1.claimedPolynomial input.round0.challenges
      (input.round1.firstMix, input.round1.secondMix)
  round2First : input.round2.firstValue =
    family.round2.claimedFirst
      (input.round0.challenges, input.round1.challenges)
  round2Second : input.round2.secondValue =
    family.round2.claimedSecond
      (input.round0.challenges, input.round1.challenges) input.round2.firstMix
  round2Polynomial : input.round2.polynomial =
    family.round2.claimedPolynomial
      (input.round0.challenges, input.round1.challenges)
      (input.round2.firstMix, input.round2.secondMix)
  round3First : input.round3.firstValue =
    family.round3.claimedFirst
      ((input.round0.challenges, input.round1.challenges),
        input.round2.challenges)
  round3Second : input.round3.secondValue =
    family.round3.claimedSecond
      ((input.round0.challenges, input.round1.challenges),
        input.round2.challenges) input.round3.firstMix
  round3Polynomial : input.round3.polynomial =
    family.round3.claimedPolynomial
      ((input.round0.challenges, input.round1.challenges),
        input.round2.challenges)
      (input.round3.firstMix, input.round3.secondMix)
  finalCoefficients : input.finalCoefficients =
    family.publishedFinal input.challenges
  finalDot : input.mainFinalDot + input.additiveFinalDot =
    candidateClaim (sharedFinalWeights family input.challenges)
      (family.publishedFinal input.challenges)

/-- Exact projection of the caller's decoded claims and polynomials into one
maintained family.  This contains no verifier-success or acceptance premise. -/
structure SourceCallerClaimsMatchFamily
    {Candidate : Type*}
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate) : Prop where
  initialClaim :
    sourceCallerInitialClaim data.inactiveClaim data.kappa data.gamma
      data.pointMajorClaims = family.initialClaim
  round0First : data.relationTail.oodValues 0 0 = family.round0.claimedFirst ()
  round0Second : data.relationTail.oodValues 0 1 =
    family.round0.claimedSecond () (data.relationTail.oodMixes 0 0)
  round0Polynomial : data.relationTail.polynomialCoefficients 0 =
    family.round0.claimedPolynomial ()
      (data.relationTail.oodMixes 0 0, data.relationTail.oodMixes 0 1)
  round1First : data.relationTail.oodValues 1 0 =
    family.round1.claimedFirst (round0Block (sourceCallerChallenges data))
  round1Second : data.relationTail.oodValues 1 1 =
    family.round1.claimedSecond (round0Block (sourceCallerChallenges data))
      (data.relationTail.oodMixes 1 0)
  round1Polynomial : data.relationTail.polynomialCoefficients 1 =
    family.round1.claimedPolynomial (round0Block (sourceCallerChallenges data))
      (data.relationTail.oodMixes 1 0, data.relationTail.oodMixes 1 1)
  round2First : data.relationTail.oodValues 2 0 =
    family.round2.claimedFirst (sourceCallerChallenges data).1.1
  round2Second : data.relationTail.oodValues 2 1 =
    family.round2.claimedSecond (sourceCallerChallenges data).1.1
      (data.relationTail.oodMixes 2 0)
  round2Polynomial : data.relationTail.polynomialCoefficients 2 =
    family.round2.claimedPolynomial (sourceCallerChallenges data).1.1
      (data.relationTail.oodMixes 2 0, data.relationTail.oodMixes 2 1)
  round3First : data.relationTail.oodValues 3 0 =
    family.round3.claimedFirst (sourceCallerChallenges data).1
  round3Second : data.relationTail.oodValues 3 1 =
    family.round3.claimedSecond (sourceCallerChallenges data).1
      (data.relationTail.oodMixes 3 0)
  round3Polynomial : data.relationTail.polynomialCoefficients 3 =
    family.round3.claimedPolynomial (sourceCallerChallenges data).1
      (data.relationTail.oodMixes 3 0, data.relationTail.oodMixes 3 1)
  finalCoefficients : data.relationTail.finalCoefficients =
    family.publishedFinal (sourceCallerChallenges data)

/-- The two independent caller projections: claim/message data and the
main-plus-compact weight construction. -/
structure SourceMode9CallerMatchesFamily
    {Candidate : Type*}
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate) : Prop where
  claims : SourceCallerClaimsMatchFamily data family
  weights : SourceWeightScheduleMatchesFamily data.mainWeights
    data.componentBPoint (data.kappa ^ 3) family (sourceCallerChallenges data)

/-- Build the old scalar-input projection from the separately checked caller
claims and weight construction.  In particular, the final-dot field is now a
theorem from generic-fold linearity and the compact evaluator proof. -/
theorem sourceMode9RelationInput_matches_family
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate)
    (correspondence : SourceMode9CallerMatchesFamily data family) :
    SourceRelationInputMatchesFamily (sourceMode9RelationInput data) family := by
  let input := sourceMode9RelationInput data
  have halphas := sourceCallerChallenges_alphas data
  refine
    { initialClaim := correspondence.claims.initialClaim
      round0First := correspondence.claims.round0First
      round0Second := correspondence.claims.round0Second
      round0Polynomial := correspondence.claims.round0Polynomial
      round1First := ?_
      round1Second := ?_
      round1Polynomial := ?_
      round2First := ?_
      round2Second := ?_
      round2Polynomial := ?_
      round3First := ?_
      round3Second := ?_
      round3Polynomial := ?_
      finalCoefficients := ?_
      finalDot := ?_ }
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges, round0Block]
      using correspondence.claims.round1First
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges, round0Block]
      using correspondence.claims.round1Second
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges, round0Block]
      using correspondence.claims.round1Polynomial
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round2First
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round2Second
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round2Polynomial
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round3First
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round3Second
  · simpa [sourceMode9RelationInput, sourceCallerRound,
      SourceRelationRound.challenges, sourceCallerChallenges]
      using correspondence.claims.round3Polynomial
  · change data.relationTail.finalCoefficients =
      family.publishedFinal (sourceMode9RelationInput data).challenges
    rw [sourceMode9RelationInput_challenges]
    exact correspondence.claims.finalCoefficients
  · change sourceMainFinalDot data.mainWeights (sourceCallerChallenges data)
        data.relationTail.finalCoefficients +
        optimizedCompactFinalDot data.componentBPoint (data.kappa ^ 3)
          data.alphas data.relationTail.finalCoefficients =
      candidateClaim
        (sharedFinalWeights family (sourceCallerChallenges data))
        (family.publishedFinal (sourceCallerChallenges data))
    rw [← correspondence.claims.finalCoefficients]
    rw [← halphas]
    exact (sharedFinalDot_eq_source_main_additive h2 data.mainWeights
      data.componentBPoint (data.kappa ^ 3) family
      (sourceCallerChallenges data) data.relationTail.finalCoefficients
      correspondence.weights).symm

section DecidableField

variable [DecidableEq K]

set_option maxHeartbeats 800000 in
/-- A successful source-shaped run exposes all four boundary equalities and
the final combined-dot equality. -/
theorem source_success_implies_shared_checks
    {Candidate : Type*}
    (input : SourceRelationInput K)
    (family : CoherentCandidateFamily K Candidate)
    (projection : SourceRelationInputMatchesFamily input family)
    (hsuccess : ∃ output, runSourceRelationVerifier input = some output) :
    SharedRelationChecks family input.challenges := by
  rcases hsuccess with ⟨output, hsuccess⟩
  rcases projection with
    ⟨hinitial, h0first, h0second, h0poly,
      h1first, h1second, h1poly,
      h2first, h2second, h2poly,
      h3first, h3second, h3poly, hfinal, hdot⟩
  unfold runSourceRelationVerifier at hsuccess
  split at hsuccess <;> rename_i hboundary0
  · simp only [] at hsuccess
    split at hsuccess <;> rename_i hboundary1
    · split at hsuccess <;> rename_i hboundary2
      · split at hsuccess <;> rename_i hboundary3
        · split at hsuccess <;> rename_i hterminal
          · simp only [Option.some.injEq] at hsuccess
            unfold SharedRelationChecks boundaryCheck0 boundaryCheck1
              boundaryCheck2 boundaryCheck3 terminalCheck
            simp only [SourceRelationInput.challenges, round0Block,
              round1Block, round2Block, round3Block,
              SourceRelationRound.challenges]
            simp only [sourceClaimAfterMixes] at hboundary0 hboundary1 hboundary2 hboundary3
            rw [hinitial] at hboundary0
            rw [h0first, h0second, h0poly] at hboundary0
            rw [h0poly] at hboundary1
            rw [h1first, h1second, h1poly] at hboundary1
            rw [h1poly] at hboundary2
            rw [h2first, h2second, h2poly] at hboundary2
            rw [h2poly] at hboundary3
            rw [h3first, h3second, h3poly] at hboundary3
            rw [h3poly] at hterminal
            exact ⟨hboundary0, hboundary1, hboundary2, hboundary3,
              hdot.symm.trans hterminal⟩
          · simp at hsuccess
        · simp at hsuccess
      · simp at hsuccess
    · simp at hsuccess
  · simp at hsuccess

/-- Main bridge theorem: successful execution of the exact scalar Rust shape
gives success of the maintained relation verifier. -/
theorem source_success_implies_modeled_relation_success
    {Candidate : Type*}
    (input : SourceRelationInput K)
    (family : CoherentCandidateFamily K Candidate)
    (projection : SourceRelationInputMatchesFamily input family)
    (hsuccess : ∃ output, runSourceRelationVerifier input = some output) :
    ∃ output,
      runModeledRelationVerifier family input.challenges = some output := by
  apply (modeled_relation_success_iff_shared_checks
    family input.challenges).mpr
  exact source_success_implies_shared_checks input family projection hsuccess

/-- Soundness-facing theorem for the unchanged nested-loop verifier.  All
field/model reasoning is proved below this point.  Its two implementation
inputs are explicit: success preservation for the fixed-loop rewrite, and
success-only correspondence for the opaque operations in one extracted
round. -/
theorem originalNestedLoop_success_implies_modeled_relation_success
    {Candidate : Type*}
    (input : SourceRelationInput K)
    (family : CoherentCandidateFamily K Candidate)
    (projection : SourceRelationInputMatchesFamily input family)
    (originalVerifier : SourceRelationInput K → Option (SourceRelationOutput K))
    (extractedRound : K → SourceRelationRound K → Option K)
    (primitiveCorrespondence :
      ExtractedUnrolledRoundPrimitivesAgree extractedRound)
    (transformation :
      OriginalNestedLoopSuccessImpliesFourCallSuccess originalVerifier
        extractedRound)
    {output : SourceRelationOutput K}
    (success : originalVerifier input = some output) :
    ∃ modeledOutput,
      runModeledRelationVerifier family input.challenges = some modeledOutput := by
  apply source_success_implies_modeled_relation_success input family projection
  exact ⟨output,
    originalNestedLoop_success_implies_source_success originalVerifier
      extractedRound primitiveCorrespondence transformation success⟩

/-- Complete field-level caller theorem.  Successful caller execution gives
modeled relation success and proves that the relation's final coefficients
are the same coefficients consumed by FRI.  The only inputs beyond caller
success are the explicit claim/weight projection and the characteristic
guard used by the compact-fold proof. -/
theorem sourceMode9Caller_success_implies_modeled_success_and_fri_equality
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate)
    (correspondence : SourceMode9CallerMatchesFamily data family)
    (friFinalPolynomial : Fin 4 → K) {terminalClaim : K}
    (success : runSourceMode9RelationCaller data friFinalPolynomial =
      some terminalClaim) :
    (∃ output,
      runModeledRelationVerifier family (sourceCallerChallenges data) =
        some output) ∧
      data.relationTail.finalCoefficients = friFinalPolynomial := by
  have projection := sourceMode9RelationInput_matches_family
    h2 data family correspondence
  have relationSuccess := sourceCaller_success_implies_relation_success
    data friFinalPolynomial success
  have modeled := source_success_implies_modeled_relation_success
    (sourceMode9RelationInput data) family projection relationSuccess
  constructor
  · simpa only [sourceMode9RelationInput_challenges] using modeled
  · exact sourceCaller_success_implies_final_coefficients_equal_fri
      data friFinalPolynomial success

/-- The previous broad raw-Rust premise follows from an exact extracted
caller equality plus the explicit field-level projection. -/
theorem exact_rust_caller_implies_modeled_success_and_fri_equality
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate)
    (correspondence : SourceMode9CallerMatchesFamily data family)
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K)
    (callerEquality : ExactRustMode9RelationCallerEquality rustCaller)
    (friFinalPolynomial : Fin 4 → K) {terminalClaim : K}
    (rustSuccess : rustCaller data friFinalPolynomial = some terminalClaim) :
    (∃ output,
      runModeledRelationVerifier family (sourceCallerChallenges data) =
        some output) ∧
      data.relationTail.finalCoefficients = friFinalPolynomial := by
  rw [callerEquality] at rustSuccess
  exact sourceMode9Caller_success_implies_modeled_success_and_fri_equality
    h2 data family correspondence friFinalPolynomial rustSuccess

/-! ## Discharging the maintained raw-relation interface -/

/-- The raw-acceptance predicate induced by one fully decoded source caller.
The challenge equality prevents a success at one transcript from being
relabelled as success at another. -/
def SourceMode9RawAccepts
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  challenges = sourceCallerChallenges data ∧
    ∃ terminalClaim,
      runSourceMode9RelationCaller data friFinalPolynomial = some terminalClaim

/-- The field-level caller closes the old raw-success interface for its exact
decoded transcript.  No Rust equality is used in this theorem. -/
theorem sourceMode9RawSuccessImpliesModeledRelationSuccess
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate)
    (correspondence : SourceMode9CallerMatchesFamily data family)
    (friFinalPolynomial : Fin 4 → K) :
    RustSuccessImpliesModeledRelationSuccess family
      (SourceMode9RawAccepts data friFinalPolynomial) := by
  intro challenges rawSuccess
  rcases rawSuccess with ⟨rfl, terminalClaim, callerSuccess⟩
  exact (sourceMode9Caller_success_implies_modeled_success_and_fri_equality
    h2 data family correspondence friFinalPolynomial callerSuccess).1

/-- The corresponding predicate for a separately extracted production
caller. -/
def ExactRustMode9RawAccepts
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K)
    (data : SourceMode9CallerData K) (friFinalPolynomial : Fin 4 → K)
    (challenges : TwelveRelationChallenges K) : Prop :=
  challenges = sourceCallerChallenges data ∧
    ∃ terminalClaim, rustCaller data friFinalPolynomial = some terminalClaim

/-- Once the exact caller equality is supplied, the extracted caller closes
the maintained raw-success interface as well. -/
theorem exactRustMode9RawSuccessImpliesModeledRelationSuccess
    {Candidate : Type*}
    (h2 : (2 : K) ≠ 0)
    (data : SourceMode9CallerData K)
    (family : CoherentCandidateFamily K Candidate)
    (correspondence : SourceMode9CallerMatchesFamily data family)
    (rustCaller : SourceMode9CallerData K → (Fin 4 → K) → Option K)
    (callerEquality : ExactRustMode9RelationCallerEquality rustCaller)
    (friFinalPolynomial : Fin 4 → K) :
    RustSuccessImpliesModeledRelationSuccess family
      (ExactRustMode9RawAccepts rustCaller data friFinalPolynomial) := by
  intro challenges rawSuccess
  rcases rawSuccess with ⟨rfl, terminalClaim, callerSuccess⟩
  have result := exact_rust_caller_implies_modeled_success_and_fri_equality
    h2 data family correspondence rustCaller callerEquality
      friFinalPolynomial callerSuccess
  exact result.1

#print axioms source_relation_tail_word_positions
#print axioms source_relation_tail_inventory
#print axioms source_point_claim_byte_index
#print axioms source_point_claim_table_bytes
#print axioms source_point_claim_block_sizes
#print axioms sourcePreparedPointClaim_eq_sourcePointClaim
#print axioms sourceCallerInitialClaim_explicit
#print axioms mixedWeights_add_incoming
#print axioms dualWeightFoldLayer_add
#print axioms candidateClaim_add_weights
#print axioms sourceMainFinalWeights_add_initial
#print axioms dualWeightFoldLayer_eq_dualFold4
#print axioms sourceFoldOnlyFinal_eq_fourDualFolds
#print axioms sourceFoldOnlyFinalDot_terminalWeights_eq_optimized
#print axioms runSourceCompactB_eq_optimized
#print axioms sharedFinalWeights_eq_source_main_additive
#print axioms sharedFinalDot_eq_source_main_additive
#print axioms sourceCallerChallenges_alphas
#print axioms runSourceRelationVerifierFourCalls_eq_source
#print axioms extractedRound_success_implies_fourCallVerifier_success
#print axioms originalNestedLoop_success_implies_source_success
#print axioms sourceRelationVerifier_output_final_coefficients
#print axioms sourceCaller_success_implies_relation_success
#print axioms sourceCaller_success_implies_final_coefficients_equal_fri
#print axioms sourceMode9RelationInput_matches_family
#print axioms source_success_implies_shared_checks
#print axioms source_success_implies_modeled_relation_success
#print axioms originalNestedLoop_success_implies_modeled_relation_success
#print axioms sourceMode9Caller_success_implies_modeled_success_and_fri_equality
#print axioms exact_rust_caller_implies_modeled_success_and_fri_equality
#print axioms exactRustMode9RelationCallerEquality_of_parts
#print axioms sourceMode9RawSuccessImpliesModeledRelationSuccess
#print axioms exactRustMode9RawSuccessImpliesModeledRelationSuccess

end DecidableField

end AspisV5RelationStressSourceBridge
