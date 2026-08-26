import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Raw prover messages for future-free Tag-73 replay

`Messages` is a convenient record for replaying one already completed
Fiat--Shamir proof, but it also stores verifier-derived challenge values,
sampler lengths, grinding-query histories, and a C2 commitment indexed by the
old lambda and chi.  Those fields cannot be copied from a returned child when
an interactive verifier is restored before the corresponding challenge.

This module isolates exactly the prover-controlled transcript fields.  The
future-free verifier must recompute challenges, sampler stopping points, and
q16 from its own public coins; oracle histories supply grinding probes.  A raw
C2 root is rewrapped only after the live verifier has decoded its current
lambda and chi.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawProverMessages

open AspisK1.V7Tag73TranscriptSchedule

/-- Prover-controlled values appearing in the deployed transcript.  No
verifier-derived challenge, sampler-use count, circle point, q16 result, or
grinding-query history occurs in this type. -/
structure RawTag73ProverMessages where
  context : Context
  c1Root : Digest208
  c2Root : Digest208
  initialClaim : Qm31Bytes
  semanticSent : Fin 10 → Fin 27 → Qm31Bytes
  pointClaims : Fin 3 → Fin 29 → Qm31Bytes
  batchNonce : NonceBytes
  inactiveClaim : Qm31Bytes
  oodValue : Fin 2 → Qm31Bytes
  relationSent : Fin 4 → Fin 6 → Qm31Bytes
  foldNonce : NonceBytes
  finalValues : Fin 256 → Qm31Bytes
  finalNonce : NonceBytes
  queryBatchClaim : Qm31Bytes

/-- Forget all verifier-derived data from one completed fixed-tape message
record. -/
def rawOfMessages (messages : Messages) : RawTag73ProverMessages where
  context := messages.context
  c1Root := messages.c1Root
  c2Root := messages.c2.root
  initialClaim := messages.initialClaim
  semanticSent := messages.semanticSent
  pointClaims := messages.pointClaims
  batchNonce := messages.batchGrinding.selected
  inactiveClaim := messages.inactiveClaim
  oodValue := messages.oodValue
  relationSent := messages.relationSent
  foldNonce := messages.foldGrinding.selected
  finalValues := messages.finalValues
  finalNonce := messages.finalGrinding.selected
  queryBatchClaim := messages.queryBatchClaim

/-- Reindex the raw C2 root only after the live verifier has decoded its
current lambda and chi. -/
def RawTag73ProverMessages.c2Commitment
    (raw : RawTag73ProverMessages) (lambda chi : Qm31Bytes) :
    C2Commitment lambda chi where
  root := raw.c2Root

@[simp] theorem c2Commitment_root
    (raw : RawTag73ProverMessages) (lambda chi : Qm31Bytes) :
    (raw.c2Commitment lambda chi).root = raw.c2Root := by
  rfl

/-- Assemble the old fixed-run convenience record from raw prover fields and
explicitly recomputed verifier data.  This is a projection aid, not the
future-free verifier: a controller must derive these arguments operationally. -/
def RawTag73ProverMessages.withDerived
    (raw : RawTag73ProverMessages)
    (challengeValue : ChallengeId → Qm31Bytes)
    (challengeUse : (id : ChallengeId) → SamplerUse id)
    (batchProbes foldProbes finalProbes : List NonceBytes) : Messages where
  context := raw.context
  challengeValue := challengeValue
  challengeUse := challengeUse
  c1Root := raw.c1Root
  c2 := raw.c2Commitment (challengeValue .lambda) (challengeValue .chi)
  initialClaim := raw.initialClaim
  semanticSent := raw.semanticSent
  pointClaims := raw.pointClaims
  batchGrinding :=
    { probesBeforeSelected := batchProbes, selected := raw.batchNonce }
  inactiveClaim := raw.inactiveClaim
  oodValue := raw.oodValue
  relationSent := raw.relationSent
  foldGrinding :=
    { probesBeforeSelected := foldProbes, selected := raw.foldNonce }
  finalValues := raw.finalValues
  finalGrinding :=
    { probesBeforeSelected := finalProbes, selected := raw.finalNonce }
  queryBatchClaim := raw.queryBatchClaim

/-- Re-deriving every verifier-owned field, even with different values and
different grinding histories, cannot alter the raw prover payload. -/
theorem rawOfMessages_withDerived
    (raw : RawTag73ProverMessages)
    (challengeValue : ChallengeId → Qm31Bytes)
    (challengeUse : (id : ChallengeId) → SamplerUse id)
    (batchProbes foldProbes finalProbes : List NonceBytes) :
    rawOfMessages
        (raw.withDerived challengeValue challengeUse batchProbes foldProbes
          finalProbes) = raw := by
  cases raw
  rfl

/-- In particular, two restored executions may derive unrelated lambda/chi
values and sampler lengths while consuming exactly the same raw proof fields.
This theorem does not assert that either execution accepts. -/
theorem raw_payload_is_independent_of_rederived_challenges
    (raw : RawTag73ProverMessages)
    (firstValues secondValues : ChallengeId → Qm31Bytes)
    (firstUses secondUses : (id : ChallengeId) → SamplerUse id)
    (firstBatch firstFold firstFinal : List NonceBytes)
    (secondBatch secondFold secondFinal : List NonceBytes) :
    rawOfMessages
        (raw.withDerived firstValues firstUses firstBatch firstFold firstFinal) =
      rawOfMessages
        (raw.withDerived secondValues secondUses secondBatch secondFold
          secondFinal) := by
  rw [rawOfMessages_withDerived, rawOfMessages_withDerived]

/-- The same raw C2 bytes can be presented at either restored challenge pair;
the dependent commitment indices are created from the live pair, never
transported from an old whole-proof type. -/
theorem raw_c2_is_reindexed_at_each_live_challenge_pair
    (raw : RawTag73ProverMessages)
    (lambda₁ chi₁ lambda₂ chi₂ : Qm31Bytes) :
    (raw.c2Commitment lambda₁ chi₁).root = raw.c2Root ∧
      (raw.c2Commitment lambda₂ chi₂).root = raw.c2Root := by
  exact ⟨rfl, rfl⟩

/-- Fixed program, release, statement, attempt, and proof-account bindings are
carried by the raw context and do not come from verifier-derived data. -/
theorem raw_fixed_bindings_are_exact (messages : Messages) :
    (rawOfMessages messages).context = messages.context := by
  rfl

#print axioms rawOfMessages_withDerived
#print axioms raw_payload_is_independent_of_rederived_challenges
#print axioms raw_c2_is_reindexed_at_each_live_challenge_pair
#print axioms raw_fixed_bindings_are_exact

end AspisK1.V7Tag73RawProverMessages
