import AspisFormal.Pool.KnowledgeExtractorInterface
import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Exact algorithmic circle-decoder boundary for V7

Knowledge extraction needs executable finite-list decoders, not existential
decodability predicates.  This module fixes the two deployed one-fold stages,
their exact agreement thresholds and their proved list caps.  A concrete
instantiation carries reviewable GRS conversion data and deterministic
algorithms; only the Guruswami--Sudan decoder theorem remains a published
external boundary.
-/

set_option autoImplicit false

namespace AspisPool.AlgorithmicCircleDecoderV7

open AspisPool.KnowledgeExtractorInterface
open Polynomial

abbrev InitialMessage (K : Type*) := Fin 1024 → K
abbrev InitialWord (K : Type*) := Fin 1048576 → K
abbrev FinalMessage (K : Type*) := Fin 256 → K
abbrev FinalWord (K : Type*) := Fin 262144 → K

def initialAgreementThreshold : Nat := 38230
def finalAgreementThreshold : Nat := 9558
def initialListSizeCap : Nat := 100
def finalListSizeCap : Nat := 99

def agreementCount {K : Type*} [DecidableEq K] {n : Nat}
    (received encoded : Fin n → K) : Nat :=
  (Finset.univ.filter fun index => received index = encoded index).card

def closeAtLeast {K Message : Type*} [DecidableEq K] {n : Nat}
    (threshold : Nat) (encoder : Message → Fin n → K)
    (received : Fin n → K) (message : Message) : Prop :=
  threshold ≤ agreementCount received (encoder message)

/-! ## Reviewable generalized Reed--Solomon conversion boundary -/

/-- Conventional generalized Reed--Solomon evaluation with evaluation points
`aᵢ`, nonzero column multipliers `vᵢ`, and polynomial message `p`:
the `i`-th symbol is `vᵢ * p(aᵢ)`. -/
def generalizedReedSolomonEncode {K : Type*} [Field K] {n : Nat}
    (points multipliers : Fin n → K) (polynomial : K[X]) : Fin n → K :=
  fun index => multipliers index * polynomial.eval (points index)

/-- Exact mathematical data identifying a released encoder with a
generalized Reed--Solomon evaluation code of bounded polynomial degree.

The structure contains only conversion data and its algebraic invariants:
the message-coordinate dimension, points, column multipliers,
message-to-polynomial map, distinctness, nonvanishing, injectivity, degree
bound, and the pointwise coordinate identity.  Agreement transport is derived
below rather than stored as an opaque field.

The separate `messageDimension` and `maximumDegree` parameters matter for the
initial circle code: its 1024-dimensional message space embeds into the
degree-at-most-1024 ambient GRS code.  The final line code has 256 message
coordinates and maximum degree 255. -/
structure ExactGRSConversion {K Message : Type*} [Field K] {n : Nat}
    (messageDimension maximumDegree : Nat)
    (releasedEncoder : Message → Fin n → K) where
  messageCoordinates : Message ≃ (Fin messageDimension → K)
  points : Fin n → K
  multipliers : Fin n → K
  messagePolynomial : Message → K[X]
  points_injective : Function.Injective points
  multipliers_ne_zero : ∀ index, multipliers index ≠ 0
  messagePolynomial_injective : Function.Injective messagePolynomial
  messagePolynomial_degree_le : ∀ message,
    (messagePolynomial message).natDegree ≤ maximumDegree
  coordinate_identity : ∀ message index,
    releasedEncoder message index =
      generalizedReedSolomonEncode points multipliers
        (messagePolynomial message) index

def ExactGRSConversion.grsEncoder
    {K Message : Type*} [Field K]
    {n messageDimension maximumDegree : Nat}
    {releasedEncoder : Message → Fin n → K}
    (conversion : ExactGRSConversion messageDimension maximumDegree
      releasedEncoder) :
    Message → Fin n → K :=
  fun message => generalizedReedSolomonEncode conversion.points
    conversion.multipliers (conversion.messagePolynomial message)

/-- Multiplication by each GRS column multiplier is explicitly invertible.
This witnesses that the nonzero scaling in the conversion loses no symbol
information. -/
def ExactGRSConversion.coordinateScalingEquiv
    {K Message : Type*} [Field K]
    {n messageDimension maximumDegree : Nat}
    {releasedEncoder : Message → Fin n → K}
    (conversion : ExactGRSConversion messageDimension maximumDegree
      releasedEncoder)
    (index : Fin n) : K ≃ K where
  toFun value := conversion.multipliers index * value
  invFun value := (conversion.multipliers index)⁻¹ * value
  left_inv value := by
    change (conversion.multipliers index)⁻¹ *
      (conversion.multipliers index * value) = value
    rw [← mul_assoc, inv_mul_cancel₀ (conversion.multipliers_ne_zero index),
      one_mul]
  right_inv value := by
    change conversion.multipliers index *
      ((conversion.multipliers index)⁻¹ * value) = value
    rw [← mul_assoc, mul_inv_cancel₀ (conversion.multipliers_ne_zero index),
      one_mul]

theorem ExactGRSConversion.releasedEncoder_eq_grsEncoder
    {K Message : Type*} [Field K]
    {n messageDimension maximumDegree : Nat}
    {releasedEncoder : Message → Fin n → K}
    (conversion : ExactGRSConversion messageDimension maximumDegree
      releasedEncoder)
    (message : Message) :
    releasedEncoder message = conversion.grsEncoder message := by
  funext index
  exact conversion.coordinate_identity message index

/-- Exact Hamming-agreement transport.  The concrete V7 conversions index
their GRS points in the released bit-reversed order, so no coordinate
permutation or received-word rewrite is necessary. -/
theorem ExactGRSConversion.agreementCount_eq
    {K Message : Type*} [Field K] [DecidableEq K]
    {n messageDimension maximumDegree : Nat}
    {releasedEncoder : Message → Fin n → K}
    (conversion : ExactGRSConversion messageDimension maximumDegree
      releasedEncoder)
    (received : Fin n → K) (message : Message) :
    agreementCount received (releasedEncoder message) =
      agreementCount received (conversion.grsEncoder message) := by
  rw [conversion.releasedEncoder_eq_grsEncoder]

/-- Every agreement threshold, and in particular the two fixed V7
thresholds, is preserved as an equivalence rather than merely an inequality. -/
theorem ExactGRSConversion.closeAtLeast_iff
    {K Message : Type*} [Field K] [DecidableEq K]
    {n messageDimension maximumDegree : Nat}
    {releasedEncoder : Message → Fin n → K}
    (conversion : ExactGRSConversion messageDimension maximumDegree
      releasedEncoder)
    (threshold : Nat) (received : Fin n → K) (message : Message) :
    closeAtLeast threshold releasedEncoder received message ↔
      closeAtLeast threshold conversion.grsEncoder received message := by
  unfold closeAtLeast
  rw [conversion.agreementCount_eq]

theorem exact_decoder_parameters :
    initialAgreementThreshold = 38230 ∧
      finalAgreementThreshold = 9558 ∧
      initialListSizeCap = 100 ∧
      finalListSizeCap = 99 := by
  norm_num [initialAgreementThreshold, finalAgreementThreshold,
    initialListSizeCap, finalListSizeCap]

/-!
The soundness ledger writes the two agreement cutoffs in strict form
(`38229 < card` and `9557 < card`), while an executable decoder naturally
accepts a non-strict minimum count (`38230 ≤ card` and `9558 ≤ card`).  The
following two lemmas close that off-by-one interface explicitly.  They prevent
an algorithmic decoder from being connected to a nearby, weaker radius.
-/

theorem initial_close_iff_published_strict
    {K Message : Type*} [DecidableEq K]
    (encoder : Message → InitialWord K)
    (received : InitialWord K) (message : Message) :
    closeAtLeast initialAgreementThreshold encoder received message ↔
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold <
        agreementCount received (encoder message) := by
  change 38230 ≤ agreementCount received (encoder message) ↔
    38229 < agreementCount received (encoder message)
  omega

theorem final_close_iff_published_strict
    {K Message : Type*} [DecidableEq K]
    (encoder : Message → FinalWord K)
    (received : FinalWord K) (message : Message) :
    closeAtLeast finalAgreementThreshold encoder received message ↔
      AspisV6PublishedTheoremInterfaces.outputAgreementThreshold <
        agreementCount received (encoder message) := by
  change 9558 ≤ agreementCount received (encoder message) ↔
    9557 < agreementCount received (encoder message)
  omega

/-- Exact algorithm package needed for the two reconstructed V7 received
words.  The conversion fields are mathematical data with checked coordinate
identities, not opaque applicability propositions. -/
structure ExactDecoderInstantiation (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] where
  initialEncoder : InitialMessage K → InitialWord K
  finalEncoder : FinalMessage K → FinalWord K
  initialDecode : InitialWord K → List (InitialMessage K)
  finalDecode : FinalWord K → List (FinalMessage K)
  initialComplete : ∀ received message,
    closeAtLeast initialAgreementThreshold initialEncoder received message →
      message ∈ initialDecode received
  initialSound : ∀ received message,
    message ∈ initialDecode received →
      closeAtLeast initialAgreementThreshold initialEncoder received message
  initialOutputBound : ∀ received,
    (initialDecode received).length ≤ initialListSizeCap
  finalComplete : ∀ received message,
    closeAtLeast finalAgreementThreshold finalEncoder received message →
      message ∈ finalDecode received
  finalSound : ∀ received message,
    message ∈ finalDecode received →
      closeAtLeast finalAgreementThreshold finalEncoder received message
  finalOutputBound : ∀ received,
    (finalDecode received).length ≤ finalListSizeCap
  initialGrsConversion : ExactGRSConversion 1024 1024 initialEncoder
  finalGrsConversion : ExactGRSConversion 256 255 finalEncoder
  multiplicityThreeGuruswamiSudanApplicable : Prop
  initialDeterministicPolynomialTime : Prop
  finalDeterministicPolynomialTime : Prop

theorem ExactDecoderInstantiation.initialAgreementCount_eq_grs
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (received : InitialWord K) (message : InitialMessage K) :
    agreementCount received (decoder.initialEncoder message) =
      agreementCount received
        (decoder.initialGrsConversion.grsEncoder message) :=
  decoder.initialGrsConversion.agreementCount_eq received message

theorem ExactDecoderInstantiation.finalAgreementCount_eq_grs
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (received : FinalWord K) (message : FinalMessage K) :
    agreementCount received (decoder.finalEncoder message) =
      agreementCount received
        (decoder.finalGrsConversion.grsEncoder message) :=
  decoder.finalGrsConversion.agreementCount_eq received message

theorem ExactDecoderInstantiation.initialThreshold_transport
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (received : InitialWord K) (message : InitialMessage K) :
    closeAtLeast initialAgreementThreshold decoder.initialEncoder received
        message ↔
      closeAtLeast initialAgreementThreshold
        decoder.initialGrsConversion.grsEncoder received message :=
  decoder.initialGrsConversion.closeAtLeast_iff initialAgreementThreshold
    received message

theorem ExactDecoderInstantiation.finalThreshold_transport
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (received : FinalWord K) (message : FinalMessage K) :
    closeAtLeast finalAgreementThreshold decoder.finalEncoder received
        message ↔
      closeAtLeast finalAgreementThreshold
        decoder.finalGrsConversion.grsEncoder received message :=
  decoder.finalGrsConversion.closeAtLeast_iff finalAgreementThreshold received
    message

/-- Package the exact initial algorithm as the common operational decoder
interface used by the K1 extraction composition. -/
def ExactDecoderInstantiation.initialAlgorithm
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) :
    AlgorithmicListDecoder (InitialWord K) (InitialMessage K) where
  close := closeAtLeast initialAgreementThreshold decoder.initialEncoder
  decode := decoder.initialDecode
  listSizeCap := initialListSizeCap
  complete := decoder.initialComplete
  sound := decoder.initialSound
  outputBound := decoder.initialOutputBound
  deterministicPolynomialTime := decoder.initialDeterministicPolynomialTime

/-- Package the exact post-fold algorithm. -/
def ExactDecoderInstantiation.finalAlgorithm
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) :
    AlgorithmicListDecoder (FinalWord K) (FinalMessage K) where
  close := closeAtLeast finalAgreementThreshold decoder.finalEncoder
  decode := decoder.finalDecode
  listSizeCap := finalListSizeCap
  complete := decoder.finalComplete
  sound := decoder.finalSound
  outputBound := decoder.finalOutputBound
  deterministicPolynomialTime := decoder.finalDeterministicPolynomialTime

/-- The concrete K1.3 output consumed by candidate-chain extraction.  Keeping
both lists in one value makes it impossible for a later composition theorem to
silently invoke a different decoder between the initial and final stages. -/
structure DecodedCandidateLists (K : Type*) where
  initial : List (InitialMessage K)
  final : List (FinalMessage K)

def ExactDecoderInstantiation.decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K) :
    DecodedCandidateLists K where
  initial := decoder.initialDecode initialReceived
  final := decoder.finalDecode finalReceived

theorem decodeBoth_has_exact_caps
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K) :
    (decoder.decodeBoth initialReceived finalReceived).initial.length ≤ 100 ∧
      (decoder.decodeBoth initialReceived finalReceived).final.length ≤ 99 := by
  exact ⟨decoder.initialOutputBound initialReceived,
    decoder.finalOutputBound finalReceived⟩

theorem initial_close_candidate_mem_decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K)
    (message : InitialMessage K)
    (close : closeAtLeast initialAgreementThreshold decoder.initialEncoder
      initialReceived message) :
    message ∈ (decoder.decodeBoth initialReceived finalReceived).initial := by
  exact decoder.initialComplete initialReceived message close

theorem final_close_candidate_mem_decodeBoth
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K)
    (initialReceived : InitialWord K) (finalReceived : FinalWord K)
    (message : FinalMessage K)
    (close : closeAtLeast finalAgreementThreshold decoder.finalEncoder
      finalReceived message) :
    message ∈ (decoder.decodeBoth initialReceived finalReceived).final := by
  exact decoder.finalComplete finalReceived message close

theorem initial_output_at_most_100
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) (received : InitialWord K) :
    (decoder.initialDecode received).length ≤ 100 := by
  simpa [initialListSizeCap] using decoder.initialOutputBound received

theorem final_output_at_most_99
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) (received : FinalWord K) :
    (decoder.finalDecode received).length ≤ 99 := by
  simpa [finalListSizeCap] using decoder.finalOutputBound received

/-- Circle/line-to-GRS conversion is now intrinsic checked data.  The only
remaining published applicability proposition here is the exact
Guruswami--Sudan decoder theorem. -/
def ExactDecoderInstantiation.publishedApplicability
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (decoder : ExactDecoderInstantiation K) : Prop :=
  decoder.multiplicityThreeGuruswamiSudanApplicable

#print axioms exact_decoder_parameters
#print axioms initial_close_iff_published_strict
#print axioms final_close_iff_published_strict
#print axioms decodeBoth_has_exact_caps
#print axioms initial_close_candidate_mem_decodeBoth
#print axioms final_close_candidate_mem_decodeBoth
#print axioms initial_output_at_most_100
#print axioms final_output_at_most_99
#print axioms ExactGRSConversion.coordinateScalingEquiv
#print axioms ExactGRSConversion.releasedEncoder_eq_grsEncoder
#print axioms ExactGRSConversion.agreementCount_eq
#print axioms ExactGRSConversion.closeAtLeast_iff
#print axioms ExactDecoderInstantiation.initialAgreementCount_eq_grs
#print axioms ExactDecoderInstantiation.finalAgreementCount_eq_grs
#print axioms ExactDecoderInstantiation.initialThreshold_transport
#print axioms ExactDecoderInstantiation.finalThreshold_transport

end AspisPool.AlgorithmicCircleDecoderV7
