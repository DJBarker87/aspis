import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Narrow BCS applicability gates for Tag-73

This file kernel-checks three concrete mismatches between the deployed Tag-73
schedule model and a literal SHA-256 instantiation of the Section-6 compiler
from Ben-Sasson--Chiesa--Spooner (2016).  It does **not** state that Tag-73 has
no argument-of-knowledge theorem.  A protocol-specific extension of the BCS
simulation proof remains possible.

In particular, `Messages.challengeValue` is intentionally only the decoded
value carried by the schedule model.  The transition schedule consumes the
recorded number of duplex blocks, but the schedule file does not equate those
blocks with that decoded value.  The countermodel below makes this separation
literal and motivates an explicit decoder relation in any fixed-table
refinement.
-/

set_option autoImplicit false

namespace AspisK1.V7BcsApplicabilityGate

open AspisK1.V7Tag73TranscriptSchedule

/-! ## Full-output Section-6 roots are not Tag-73's truncated roots -/

/-- A literal SHA-256 instantiation of the BCS Section-6 Merkle compiler uses
the full 32-byte random-oracle output as its root.  This constant records that
pinned instantiation; it is not a claim that the abstract BCS parameter
`lambda` is always 256. -/
def bcsSection6Sha256FullRootBytes : Nat := 32

def tag73Digest208Bytes : Nat := 26

theorem literal_bcs_sha256_root_width_differs_from_tag73 :
    bcsSection6Sha256FullRootBytes ≠ tag73Digest208Bytes := by
  decide

theorem digest_types_have_different_encoded_lengths
    (fullRoot : Digest256) (tag73Root : Digest208) :
    (bytes fullRoot).length ≠ (bytes tag73Root).length := by
  simp

/-! ## A Tag squeeze is a two-input transition -/

theorem tag73_squeeze_uses_distinct_33_byte_inputs (state : MachineState) :
    (squeezeOutputInput state).length = 33 ∧
    (squeezeAdvanceInput state).length = 33 ∧
    squeezeOutputInput state ≠ squeezeAdvanceInput state := by
  simp [squeezeOutputInput, squeezeAdvanceInput, domSqueeze, domAdvance]

/-- Agreement at the advance input alone fixes the next digest.  No agreement
at the independently queried output input is assumed. -/
theorem squeeze_advance_depends_only_on_advance_answer
    (left right : HashOracle) (state : MachineState)
    (agree : left.answer (squeezeAdvanceInput state) =
      right.answer (squeezeAdvanceInput state)) :
    (squeezeBlock left state).2.digest =
      (squeezeBlock right state).2.digest := by
  simpa [squeezeBlock] using agree

/-- Dually, the returned raw block depends only on the output-input answer;
the independently sampled advance answer is irrelevant to this projection. -/
theorem squeeze_output_depends_only_on_output_answer
    (left right : HashOracle) (state : MachineState)
    (agree : left.answer (squeezeOutputInput state) =
      right.answer (squeezeOutputInput state)) :
    (squeezeBlock left state).1 = (squeezeBlock right state).1 := by
  simpa [squeezeBlock] using agree

/-! ## The transition schedule does not determine decoded challenge values -/

def replaceLambdaValue
    (values : ChallengeId → Qm31Bytes) (newLambda : Qm31Bytes) :
    ChallengeId → Qm31Bytes
  | .lambda => newLambda
  | id => values id

/-- Re-index the dependent C2 commitment at a new `lambda`, retaining the same
root and every event-carrying message. -/
def rebuildWithLambda (messages : Messages)
    (newLambda : Qm31Bytes) : Messages where
  context := messages.context
  challengeValue := replaceLambdaValue messages.challengeValue newLambda
  challengeUse := messages.challengeUse
  c1Root := messages.c1Root
  c2 := ⟨messages.c2.root⟩
  initialClaim := messages.initialClaim
  semanticSent := messages.semanticSent
  pointClaims := messages.pointClaims
  batchGrinding := messages.batchGrinding
  inactiveClaim := messages.inactiveClaim
  oodValue := messages.oodValue
  relationSent := messages.relationSent
  foldGrinding := messages.foldGrinding
  finalValues := messages.finalValues
  finalGrinding := messages.finalGrinding
  queryBatchClaim := messages.queryBatchClaim

@[simp] theorem rebuildWithLambda_lambda
    (messages : Messages) (newLambda : Qm31Bytes) :
    (rebuildWithLambda messages newLambda).challengeValue .lambda =
      newLambda := by
  rfl

@[simp] theorem rebuildWithLambda_chi
    (messages : Messages) (newLambda : Qm31Bytes) :
    (rebuildWithLambda messages newLambda).challengeValue .chi =
      messages.challengeValue .chi := by
  rfl

@[simp] theorem rebuildWithLambda_c2_root
    (messages : Messages) (newLambda : Qm31Bytes) :
    (rebuildWithLambda messages newLambda).c2.root = messages.c2.root := by
  rfl

/-- `lambda` is absent from event payloads.  Rebuilding dependent C2 with the
same root therefore leaves the entire pre-query event schedule unchanged. -/
theorem rebuildWithLambda_preserves_before_query_schedule
    (oracle : HashOracle) (messages : Messages)
    (newLambda : Qm31Bytes) :
    beforeQueryScan oracle (rebuildWithLambda messages newLambda) =
      beforeQueryScan oracle messages := by
  rfl

theorem rebuildWithLambda_preserves_after_query_schedule
    (messages : Messages) (newLambda : Qm31Bytes) :
    afterAcceptedQueryScan (rebuildWithLambda messages newLambda) =
      afterAcceptedQueryScan messages := by
  rfl

def alternateFirstByte (value : Qm31Bytes) : Qm31Bytes :=
  Function.update value (0 : Fin 16)
    (if value 0 = 0 then 1 else 0)

theorem alternateFirstByte_ne (value : Qm31Bytes) :
    alternateFirstByte value ≠ value := by
  intro equal
  have atZero := congrFun equal (0 : Fin 16)
  by_cases isZero : value 0 = 0
  · simp [alternateFirstByte, isZero] at atZero
  · simp [alternateFirstByte, isZero] at atZero
    exact isZero atZero.symm

/-- Concrete schedule-level countermodel: one can alter decoded `lambda`,
rebuild the type-indexed C2 with exactly the same root, and retain both lists
of oracle-transition events.  This refutes determination *from the schedule
projection alone*; it is not a cryptographic attack or an AoK impossibility. -/
theorem identical_transition_schedule_with_altered_lambda
    (oracle : HashOracle) (messages : Messages) :
    let altered := rebuildWithLambda messages
      (alternateFirstByte (messages.challengeValue .lambda))
    altered.challengeValue .lambda ≠ messages.challengeValue .lambda ∧
    altered.c2.root = messages.c2.root ∧
    beforeQueryScan oracle altered = beforeQueryScan oracle messages ∧
    afterAcceptedQueryScan altered = afterAcceptedQueryScan messages := by
  dsimp
  exact ⟨alternateFirstByte_ne _, rfl, rfl, rfl⟩

/-! ## Fixed-table refinement needs an explicit decoder relation -/

/-- A decoder relation connects an identifier, the exact raw squeeze blocks,
and the decoded field encoding.  Making this relation explicit avoids assuming
the missing sampler theorem as part of the transition schedule. -/
abbrev ChallengeDecoderRelation :=
  (id : ChallengeId) → List Digest256 → Qm31Bytes → Prop

def DecoderFunctional (decoder : ChallengeDecoderRelation) : Prop :=
  ∀ id blocks first second,
    decoder id blocks first → decoder id blocks second → first = second

def lambdaState (oracle : HashOracle) (messages : Messages) :
    MachineState :=
  stateBefore oracle initialState (beforeQueryScan oracle messages) 7

def lambdaRawBlocks (oracle : HashOracle) (messages : Messages) :
    List Digest256 :=
  (squeezeBlocks oracle (messages.challengeUse .lambda).blocksUsed
    (lambdaState oracle messages)).1

def LambdaDecoderLinked (decoder : ChallengeDecoderRelation)
    (oracle : HashOracle) (messages : Messages) : Prop :=
  decoder .lambda (lambdaRawBlocks oracle messages)
    (messages.challengeValue .lambda)

theorem rebuildWithLambda_preserves_lambda_raw_blocks
    (oracle : HashOracle) (messages : Messages)
    (newLambda : Qm31Bytes) :
    lambdaRawBlocks oracle (rebuildWithLambda messages newLambda) =
      lambdaRawBlocks oracle messages := by
  rfl

/-- A functional explicit decoder can link at most one of the two altered
claims to the common raw blocks.  Hence equality of the fixed-oracle transition
schedule alone cannot establish the missing decoder link. -/
theorem explicit_decoder_link_excludes_schedule_countermodel
    (decoder : ChallengeDecoderRelation) (functional : DecoderFunctional decoder)
    (oracle : HashOracle) (messages : Messages)
    (linked : LambdaDecoderLinked decoder oracle messages) :
    ¬ LambdaDecoderLinked decoder oracle
      (rebuildWithLambda messages
        (alternateFirstByte (messages.challengeValue .lambda))) := by
  intro alteredLinked
  change decoder .lambda
    (lambdaRawBlocks oracle
      (rebuildWithLambda messages
        (alternateFirstByte (messages.challengeValue .lambda))))
    (alternateFirstByte (messages.challengeValue .lambda)) at alteredLinked
  change decoder .lambda (lambdaRawBlocks oracle messages)
    (messages.challengeValue .lambda) at linked
  rw [rebuildWithLambda_preserves_lambda_raw_blocks] at alteredLinked
  have decodedEqual := functional .lambda (lambdaRawBlocks oracle messages)
    (messages.challengeValue .lambda)
    (alternateFirstByte (messages.challengeValue .lambda)) linked alteredLinked
  exact alternateFirstByte_ne _ decodedEqual.symm

#print axioms literal_bcs_sha256_root_width_differs_from_tag73
#print axioms digest_types_have_different_encoded_lengths
#print axioms tag73_squeeze_uses_distinct_33_byte_inputs
#print axioms squeeze_advance_depends_only_on_advance_answer
#print axioms squeeze_output_depends_only_on_output_answer
#print axioms identical_transition_schedule_with_altered_lambda
#print axioms rebuildWithLambda_preserves_lambda_raw_blocks
#print axioms explicit_decoder_link_excludes_schedule_countermodel

end AspisK1.V7BcsApplicabilityGate
