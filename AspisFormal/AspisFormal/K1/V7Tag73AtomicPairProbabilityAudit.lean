import AspisFormal.K1.V7Tag73PostForkContinuationBoundary
import AspisFormal.K1.V7Tag73AdaptiveLazyOracle
import AspisFormal.K1.V7Tag73SamplerDecoder

/-!
# Atomic squeeze-pair probability audit

Tag-73 associates two distinct random-oracle inputs with one complete squeeze
state:

* `H(S || 0x01)` supplies a raw 256-bit block to a bounded decoder;
* `H(S || 0x02)` advances the transcript state.

The second input can be queried without the first.  Moreover, proof-visible
data are functions of the decoded challenge, not necessarily of the complete
raw `0x01` answer.  Therefore absence of the first input from Q1 is not, by
itself, a singleton 256-bit prediction event.  Uniform probability is the
cardinality of the accepted decoder fiber divided by `2^256`.

This module kernel-checks that obstruction.  It gives both an operational
advance-only program and a finite decoded-fiber counterexample.  It does not
assign a Tag-73 failure coefficient, assert that deployed acceptance realizes
the counterexample, or introduce a trace-cover/compiler premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AtomicPairProbabilityAudit

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73PostForkContinuationBoundary
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## The advance half can occur without the output half -/

/-- A one-query program that asks only for the transcript-advance answer. -/
def advanceOnlyProgram (state : Digest256) : OracleMachine Digest256 :=
  .query (bytes state ++ [domAdvance]) fun advance => .pure advance

theorem advance_only_queries_advance_but_not_output (state : Digest256) :
    QueriesNext (advanceOnlyProgram state) (bytes state ++ [domAdvance]) ∧
      ¬ QueriesNext (advanceOnlyProgram state) (bytes state ++ [domSqueeze]) := by
  constructor
  · rfl
  · simp only [QueriesNext, advanceOnlyProgram]
    exact (squeeze_output_and_advance_inputs_are_distinct state).symm

/-! ## A decoded view does not in general determine the raw output -/

/-- Information retained from one atomic pair when the raw output block is
used only through a decoder.  Both input names and the independent advance
answer are retained. -/
structure AtomicDecodedView (Challenge : Type*) where
  outputInput : ShaInput
  advanceInput : ShaInput
  decodedChallenge : Challenge
  advanceOutput : Digest256
  deriving DecidableEq

def atomicDecodedView {Challenge : Type*}
    (state : Digest256) (decode : Digest256 → Challenge)
    (output advance : Digest256) : AtomicDecodedView Challenge where
  outputInput := bytes state ++ [domSqueeze]
  advanceInput := bytes state ++ [domAdvance]
  decodedChallenge := decode output
  advanceOutput := advance

theorem atomic_decoded_view_uses_distinct_pair_inputs
    {Challenge : Type*} (state : Digest256)
    (decode : Digest256 → Challenge) (output advance : Digest256) :
    (atomicDecodedView state decode output advance).outputInput ≠
      (atomicDecodedView state decode output advance).advanceInput := by
  exact squeeze_output_and_advance_inputs_are_distinct state

/-- Fixing the independent advance answer cannot distinguish two raw output
blocks that the decoder identifies. -/
theorem atomic_decoded_view_eq_of_decode_eq
    {Challenge : Type*} (state : Digest256)
    (decode : Digest256 → Challenge) (first second advance : Digest256)
    (sameDecoded : decode first = decode second) :
    atomicDecodedView state decode first advance =
      atomicDecodedView state decode second advance := by
  simp only [atomicDecodedView, sameDecoded]

/-! ## An explicit full-digest collision under a decoded-only view -/

/-- A simple 16-byte decoded view used only as an interface countermodel.  It
is not asserted to replace the deployed rejection sampler. -/
def digestPrefix16 (output : Digest256) : Qm31Bytes :=
  fun index => output ⟨index.val, by omega⟩

/-- A digest differing from zero only in its last byte. -/
def lastByteOneDigest : Digest256 := fun index =>
  if index.val = 31 then 1 else 0

theorem zero_digest_ne_last_byte_one :
    zeroBytes 32 ≠ lastByteOneDigest := by
  intro equal
  have atLast := congrFun equal (⟨31, by omega⟩ : Fin 32)
  change (0 : UInt8) = 1 at atLast
  exact (by decide : (0 : UInt8) ≠ 1) atLast

@[simp] theorem digest_prefix_zero :
    digestPrefix16 (zeroBytes 32) = zeroBytes 16 := by
  rfl

@[simp] theorem digest_prefix_last_byte_one :
    digestPrefix16 lastByteOneDigest = zeroBytes 16 := by
  funext index
  have notLast : index.val ≠ 31 := by omega
  simp [digestPrefix16, lastByteOneDigest, zeroBytes, notLast]

/-- Even after retaining the advance output and both distinct input names, the
decoded-only atomic view is not injective in the raw output block. -/
theorem decoded_atomic_view_not_injective
    (state advance : Digest256) :
    ¬ Function.Injective
      (fun output => atomicDecodedView state digestPrefix16 output advance) := by
  intro injective
  apply zero_digest_ne_last_byte_one
  apply injective
  exact atomic_decoded_view_eq_of_decode_eq state digestPrefix16
    (zeroBytes 32) lastByteOneDigest advance (by simp)

/-! ## Exact finite-uniform decoder-fiber law -/

def decodedFiber {Challenge : Type*}
    (decode : Digest256 → Challenge) (challenge : Challenge) : Set Digest256 :=
  {output | decode output = challenge}

noncomputable def uniformRawDigestLaw : PMF Digest256 :=
  PMF.uniformOfFintype Digest256

/-- The exact probability of guessing only a decoded value is the full raw
fiber size divided by the raw output-space size.  No independence assumption
is used. -/
theorem uniform_decoded_fiber_probability_exact
    {Challenge : Type*} [DecidableEq Challenge]
    (decode : Digest256 → Challenge)
    (challenge : Challenge) :
    uniformRawDigestLaw.toOuterMeasure (decodedFiber decode challenge) =
      (Fintype.card {output : Digest256 // decode output = challenge} : ENNReal) /
        ((2 : ENNReal) ^ 256) := by
  classical
  let fiberEquiv :
      (decodedFiber decode challenge) ≃
        {output : Digest256 // decode output = challenge} :=
    { toFun := fun output : ↥(decodedFiber decode challenge) =>
        ⟨output.1, output.2⟩
      invFun := fun output :
          {output : Digest256 // decode output = challenge} =>
        ⟨output.1, output.2⟩
      left_inv := by intro output; cases output; rfl
      right_inv := by intro output; cases output; rfl }
  unfold uniformRawDigestLaw
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr fiberEquiv]
  have digestCard :
      (Fintype.card Digest256 : ENNReal) = (2 : ENNReal) ^ 256 := by
    rw [deployed_digest_256_cardinality]
    norm_num
  rw [digestCard]

/-- Two concrete raw blocks in the zero-prefix fiber. -/
def twoPrefixFiberOutputs :
    Bool ↪ {output : Digest256 // digestPrefix16 output = zeroBytes 16} where
  toFun
    | false => ⟨zeroBytes 32, digest_prefix_zero⟩
    | true => ⟨lastByteOneDigest, digest_prefix_last_byte_one⟩
  inj' := by
    intro first second equal
    cases first <;> cases second
    · rfl
    · exfalso
      exact zero_digest_ne_last_byte_one (congrArg Subtype.val equal)
    · exfalso
      exact zero_digest_ne_last_byte_one (congrArg Subtype.val equal).symm
    · rfl

theorem decoded_prefix_fiber_card_at_least_two :
    2 ≤ Fintype.card
      {output : Digest256 // digestPrefix16 output = zeroBytes 16} := by
  simpa using Fintype.card_le_of_injective twoPrefixFiberOutputs
    twoPrefixFiberOutputs.injective

/-- The countermodel's decoded-value event has at least twice the mass of a
single raw 256-bit output. -/
theorem decoded_prefix_probability_at_least_two_over_two_pow_256 :
    (2 : ENNReal) / ((2 : ENNReal) ^ 256) ≤
      uniformRawDigestLaw.toOuterMeasure
        (decodedFiber digestPrefix16 (zeroBytes 16)) := by
  rw [uniform_decoded_fiber_probability_exact]
  apply ENNReal.div_le_div_right
  exact_mod_cast decoded_prefix_fiber_card_at_least_two

theorem decoded_prefix_event_is_not_singleton_probability :
    ¬ uniformRawDigestLaw.toOuterMeasure
        (decodedFiber digestPrefix16 (zeroBytes 16)) ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  intro singletonBound
  have reversed :
      (2 : ENNReal) / ((2 : ENNReal) ^ 256) ≤
        (1 : ENNReal) / ((2 : ENNReal) ^ 256) :=
    decoded_prefix_probability_at_least_two_over_two_pow_256.trans
      singletonBound
  have strict :
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) <
        (2 : ENNReal) / ((2 : ENNReal) ^ 256) :=
    ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num)
  exact (not_le_of_gt strict) reversed

/-- With no restriction on the decoder interface at all, the fiber event can
be the whole output space and hence have probability one. -/
theorem constant_decoded_fiber_probability_one
    {Challenge : Type*} (challenge : Challenge) :
    uniformRawDigestLaw.toOuterMeasure
        (decodedFiber (fun _ : Digest256 => challenge) challenge) = 1 := by
  have eventUniv :
      decodedFiber (fun _ : Digest256 => challenge) challenge = Set.univ := by
    ext output
    simp [decodedFiber]
  rw [eventUniv]
  change (PMF.uniformOfFintype Digest256).toOuterMeasure
    (Set.univ : Set Digest256) = 1
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (Equiv.Set.univ Digest256)]
  apply ENNReal.div_self
  · exact_mod_cast (Fintype.card_ne_zero : Fintype.card Digest256 ≠ 0)
  · exact ENNReal.natCast_ne_top _

/-! ## The exact additional property needed for a singleton charge -/

/-- A decoded accepted value pins one complete raw output.  This is strictly
stronger than decoder functionality: functionality maps raw blocks to decoded
values, while this predicate requires the relevant inverse fiber to be a
singleton. -/
def RawOutputPinnedByDecodedValue {Challenge : Type*}
    (decode : Digest256 → Challenge) (challenge : Challenge) : Prop :=
  ∃ target : Digest256,
    ∀ output, decode output = challenge → output = target

theorem decoded_prefix_does_not_pin_raw_output :
    ¬ RawOutputPinnedByDecodedValue digestPrefix16 (zeroBytes 16) := by
  rintro ⟨target, pinned⟩
  have zeroPinned := pinned (zeroBytes 32) digest_prefix_zero
  have lastPinned := pinned lastByteOneDigest digest_prefix_last_byte_one
  exact zero_digest_ne_last_byte_one (zeroPinned.trans lastPinned.symm)

/-- The local interactive condition needed before a missing output-half query
can be treated as a singleton raw-output prediction: the adversary continuation
must make the output-then-advance pair atomically, and the accepted decoded view
must pin the complete raw output.  This is only a definition of the remaining
property; no theorem here assumes it or claims Tag-73 acceptance proves it. -/
def AtomicSingletonPredictionReady {Result Challenge : Type*}
    (program : OracleMachine Result) (state : Digest256)
    (decode : Digest256 → Challenge) (challenge : Challenge) : Prop :=
  HasAtomicOutputAdvanceContinuation program
      (bytes state ++ [domSqueeze]) (bytes state ++ [domAdvance]) ∧
    RawOutputPinnedByDecodedValue decode challenge

/-- Querying only the independent advance half cannot satisfy the required
atomic-continuation component. -/
theorem advance_only_is_not_atomic_singleton_ready
    {Challenge : Type*} (state : Digest256)
    (decode : Digest256 → Challenge) (challenge : Challenge) :
    ¬ AtomicSingletonPredictionReady (advanceOnlyProgram state) state decode
      challenge := by
  rintro ⟨atomic, _pinned⟩
  change
    bytes state ++ [domAdvance] = bytes state ++ [domSqueeze] ∧
      (∀ _output : Digest256, False) at atomic
  exact (squeeze_output_and_advance_inputs_are_distinct state) atomic.1.symm

/-! The deployed primitive already visibly loses a raw bit before field
decoding.  This does not by itself count the complete decoder fiber, but it
shows why injectivity cannot be inferred from decoder functionality. -/
theorem deployed_m31_mask_forgets_high_bit :
    (0 : Nat) ≠ 2 ^ 31 ∧ maskedM31 0 = maskedM31 (2 ^ 31) := by
  norm_num [maskedM31, m31MaskModulus]

#print axioms advance_only_queries_advance_but_not_output
#print axioms atomic_decoded_view_eq_of_decode_eq
#print axioms decoded_atomic_view_not_injective
#print axioms uniform_decoded_fiber_probability_exact
#print axioms decoded_prefix_fiber_card_at_least_two
#print axioms decoded_prefix_probability_at_least_two_over_two_pow_256
#print axioms decoded_prefix_event_is_not_singleton_probability
#print axioms constant_decoded_fiber_probability_one
#print axioms decoded_prefix_does_not_pin_raw_output
#print axioms advance_only_is_not_atomic_singleton_ready
#print axioms deployed_m31_mask_forgets_high_bit

end

end AspisK1.V7Tag73AtomicPairProbabilityAudit
