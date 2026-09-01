import AspisFormal.K1.V7Tag73ChallengeRecordControlInvariant

/-!
# Duplicate-free challenge records for restored Tag-73 nodes

The restored K1.3 provider obtains gamma and alpha zero from the verifier's
decoded-challenge ledger.  Existence alone is insufficient: a classical
choice over two records with the same logical challenge id would make the
derived view noncanonical.

This module tracks one exact invariant through the executable controller:

`decoded challenge ids ++ challenge ids still pending in the control`

is duplicate-free.  The pending list includes lambda/chi during the adaptive
prefix and the literal remaining linear schedule afterwards.  A successful
sampler therefore moves exactly one id from the pending suffix to the decoded
prefix; retries move neither.  Restoration is safe because it reinstalls an
already certified snapshot.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ChallengeRecordUniquenessInvariant

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7FsAokExperiment

noncomputable section

/-- Challenge ids occurring in a future-free linear slot suffix. -/
def challengeIdsInSlots : List FutureFreeSlot → List ChallengeId
  | [] => []
  | .challenge id :: remaining => id :: challengeIdsInSlots remaining
  | _ :: remaining => challengeIdsInSlots remaining

/-- Logical challenges which the current executable control may still
decode.  Rejection controls have no continuation and hence no pending ids. -/
def pendingChallengeIds : FutureFreeControl → List ChallengeId
  | .adaptive control =>
      match control with
      | .fixedPrefix _ | .awaitingC1 | .requestC1Salt _ | .absorbC1 _ |
          .sampleLambda _ =>
          [.lambda, .chi] ++ challengeIdsInSlots fullFutureFreeSlots
      | .sampleChi _ _ => .chi :: challengeIdsInSlots fullFutureFreeSlots
      | .awaitingC2 _ _ | .requestC2Salt _ _ _ | .absorbC2 _ _ _ |
          .afterAdaptiveC2 _ _ => challengeIdsInSlots fullFutureFreeSlots
      | .rejected => []
  | .linear remaining => challengeIdsInSlots remaining
  | .absorbPayload _ remaining => challengeIdsInSlots remaining
  | .workCheck _ _ remaining => challengeIdsInSlots remaining
  | .workCheckpoint _ _ remaining => challengeIdsInSlots remaining
  | .workAbsorb _ _ remaining => challengeIdsInSlots remaining
  | .sampleChallenge id _ remaining =>
      id :: challengeIdsInSlots remaining
  | .q16Absorb _ _ remaining => challengeIdsInSlots remaining
  | .q16Sample _ _ _ remaining => challengeIdsInSlots remaining
  | .q16Restore _ _ _ remaining => challengeIdsInSlots remaining
  | .q16Selected _ _ _ remaining => challengeIdsInSlots remaining
  | .q16SamplerReject _ _ | .q16AllNoncompactReject | .rejected _ | .done => []

/-- Entering the remaining linear schedule (or finishing when it is empty)
does not alter its pending challenge inventory. -/
@[simp] theorem pending_challenge_ids_linear_or_done
    (remaining : List FutureFreeSlot) :
    pendingChallengeIds (linearOrDone remaining) =
      challengeIdsInSlots remaining := by
  cases remaining <;> rfl

/-- The complete deployed challenge schedule has no repeated logical id. -/
theorem deployed_pending_challenge_ids_nodup :
    ([ChallengeId.lambda, ChallengeId.chi] ++
      challengeIdsInSlots fullFutureFreeSlots).Nodup := by
  decide

/-- Exact snapshot invariant.  It simultaneously proves uniqueness of the
decoded ledger, freshness of every pending id, and uniqueness of the pending
suffix. -/
def SnapshotChallengeRecordUniqueness
    (snapshot : FutureFreeSnapshot) : Prop :=
  ((snapshot.decodedChallenges.map DecodedChallenge.id) ++
    pendingChallengeIds snapshot.control).Nodup

@[simp] theorem initial_snapshot_challenge_record_uniqueness
    (bindings : FixedBindings) :
    SnapshotChallengeRecordUniqueness (initialFutureFreeSnapshot bindings) := by
  simpa [SnapshotChallengeRecordUniqueness, initialFutureFreeSnapshot,
    pendingChallengeIds] using deployed_pending_challenge_ids_nodup

/-- Discarding a pending suffix on rejection cannot create a duplicate in the
already decoded prefix. -/
theorem decoded_prefix_nodup_of_snapshot
    {snapshot : FutureFreeSnapshot}
    (invariant : SnapshotChallengeRecordUniqueness snapshot) :
    (snapshot.decodedChallenges.map DecodedChallenge.id).Nodup := by
  exact (List.nodup_append.mp invariant).1

/-- Mapping record ids is injective on any ledger whose mapped ids are
duplicate-free. -/
theorem decoded_challenge_value_unique_in_list
    (records : List DecodedChallenge)
    (mappedNodup : (records.map DecodedChallenge.id).Nodup)
    (id : ChallengeId) (left right : Qm31Bytes)
    (leftMember : { id := id, value := left } ∈ records)
    (rightMember : { id := id, value := right } ∈ records) :
    left = right := by
  induction records generalizing left right with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · subst head
        rcases rightMember with rightHead | rightTail
        · exact congrArg DecodedChallenge.value rightHead.symm
        · exact False.elim (headFresh (List.mem_map.mpr
            ⟨{ id := id, value := right }, rightTail, rfl⟩))
      · rcases rightMember with rightHead | rightTail
        · subst head
          exact False.elim (headFresh (List.mem_map.mpr
            ⟨{ id := id, value := left }, leftTail, rfl⟩))
        · exact ih tailNodup left right leftTail rightTail

/-- Two records for one logical id in a certified snapshot are the same list
element, hence have the same canonical bytes. -/
theorem decoded_challenge_value_unique
    {snapshot : FutureFreeSnapshot}
    (invariant : SnapshotChallengeRecordUniqueness snapshot)
    (id : ChallengeId) (left right : Qm31Bytes)
    (leftMember : { id := id, value := left } ∈ snapshot.decodedChallenges)
    (rightMember : { id := id, value := right } ∈ snapshot.decodedChallenges) :
    left = right := by
  exact decoded_challenge_value_unique_in_list snapshot.decodedChallenges
    (decoded_prefix_nodup_of_snapshot invariant) id left right leftMember
    rightMember

/-- Record uniqueness depends only on the decoded ledger and the pending-id
inventory, so all other snapshot fields may change freely. -/
theorem snapshot_challenge_record_uniqueness_transport
    {before after : FutureFreeSnapshot}
    (recordsExact : after.decodedChallenges = before.decodedChallenges)
    (pendingExact : pendingChallengeIds after.control =
      pendingChallengeIds before.control)
    (invariant : SnapshotChallengeRecordUniqueness before) :
    SnapshotChallengeRecordUniqueness after := by
  unfold SnapshotChallengeRecordUniqueness at invariant ⊢
  rw [recordsExact, pendingExact]
  exact invariant

/-- Generic form of moving the head pending id into the append-only decoded
ledger.  The adaptive lambda/chi samplers use a virtual pending list rather
than a `FutureFreeSlot` suffix, so they need this list-level statement. -/
theorem append_decoded_challenge_moves_pending_ids
    (records : List DecodedChallenge) (id : ChallengeId)
    (value : Qm31Bytes) (remaining : List ChallengeId)
    (invariant :
      (records.map DecodedChallenge.id ++ id :: remaining).Nodup) :
    (((records ++ [({ id := id, value := value } : DecodedChallenge)]).map
        DecodedChallenge.id) ++ remaining).Nodup := by
  simpa [List.map_append, List.append_assoc] using invariant

/-- Exact ledger update performed by the adaptive wrapper. -/
def adaptiveDecodedChallenges (records : List DecodedChallenge)
    (control nextControl : OpenAdaptiveControl) : List DecodedChallenge :=
  match control, nextControl with
  | .sampleLambda _, .sampleChi lambda _ =>
      records ++ [{ id := .lambda, value := lambda }]
  | .sampleChi _ _, .awaitingC2 _ chi =>
      records ++ [{ id := .chi, value := chi }]
  | _, _ => records

/-- Exact embedding of the next adaptive control into the full controller. -/
def embedNextAdaptiveControl (nextControl : OpenAdaptiveControl) :
    FutureFreeControl :=
  match nextControl with
  | .afterAdaptiveC2 _ _ => .linear fullFutureFreeSlots
  | _ => .adaptive nextControl

/-- The literal adaptive controller either preserves the pending inventory,
moves lambda/chi exactly once into the decoded ledger, or rejects and drops
the pending suffix.  In particular an incremental sampler retry cannot create
a second logical record. -/
theorem open_adaptive_after_reply_preserves_record_uniqueness
    (decoders : DeterministicDecoders) (records : List DecodedChallenge)
    (control nextControl : OpenAdaptiveControl) (reply : VerifierReply)
    (invariant :
      (records.map DecodedChallenge.id ++
        pendingChallengeIds (.adaptive control)).Nodup)
    (run : control.afterVerifierReply decoders reply = some nextControl) :
    ((adaptiveDecodedChallenges records control nextControl).map
        DecodedChallenge.id ++
      pendingChallengeIds (embedNextAdaptiveControl nextControl)).Nodup := by
  cases control with
  | fixedPrefix remaining =>
      cases remaining with
      | nil =>
          cases reply <;>
            simp [OpenAdaptiveControl.afterVerifierReply] at run
      | cons action remaining =>
          simp [OpenAdaptiveControl.afterVerifierReply] at run
          subst nextControl
          cases remaining <;>
            simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
              finishFixedPrefixControl, pendingChallengeIds] using invariant
  | awaitingC1 =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
  | requestC1Salt root =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
      subst nextControl
      simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
        pendingChallengeIds] using invariant
  | absorbC1 root =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
      subst nextControl
      simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
        pendingChallengeIds] using invariant
  | sampleLambda outputs =>
      cases reply with
      | none => simp [OpenAdaptiveControl.afterVerifierReply] at run
      | single output => simp [OpenAdaptiveControl.afterVerifierReply] at run
      | squeeze output advance =>
          simp only [OpenAdaptiveControl.afterVerifierReply] at run
          split at run
          next lambda decoded =>
            have nextExact : .sampleChi lambda [] = nextControl :=
              Option.some.inj run
            clear run
            subst nextControl
            have moved := append_decoded_challenge_moves_pending_ids records
              .lambda lambda
              (.chi :: challengeIdsInSlots fullFutureFreeSlots) invariant
            simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
              pendingChallengeIds] using moved
          next undecoded =>
            split at run
            next belowCap =>
              have nextExact : .sampleLambda (outputs ++ [output]) =
                  nextControl := Option.some.inj run
              clear run
              subst nextControl
              simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
                pendingChallengeIds] using invariant
            next atCap =>
              have nextExact : OpenAdaptiveControl.rejected = nextControl :=
                Option.some.inj run
              clear run
              subst nextControl
              have decodedPrefix := (List.nodup_append.mp invariant).1
              simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
                pendingChallengeIds] using decodedPrefix
  | sampleChi lambda outputs =>
      cases reply with
      | none => simp [OpenAdaptiveControl.afterVerifierReply] at run
      | single output => simp [OpenAdaptiveControl.afterVerifierReply] at run
      | squeeze output advance =>
          simp only [OpenAdaptiveControl.afterVerifierReply] at run
          split at run
          next chi decoded =>
            have nextExact : .awaitingC2 lambda chi = nextControl :=
              Option.some.inj run
            clear run
            subst nextControl
            have moved := append_decoded_challenge_moves_pending_ids records
              .chi chi (challengeIdsInSlots fullFutureFreeSlots) invariant
            simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
              pendingChallengeIds] using moved
          next undecoded =>
            split at run
            next belowCap =>
              have nextExact : .sampleChi lambda (outputs ++ [output]) =
                  nextControl := Option.some.inj run
              clear run
              subst nextControl
              simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
                pendingChallengeIds] using invariant
            next atCap =>
              have nextExact : OpenAdaptiveControl.rejected = nextControl :=
                Option.some.inj run
              clear run
              subst nextControl
              have decodedPrefix := (List.nodup_append.mp invariant).1
              simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
                pendingChallengeIds] using decodedPrefix
  | awaitingC2 lambda chi =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
  | requestC2Salt lambda chi commitment =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
      subst nextControl
      simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
        pendingChallengeIds] using invariant
  | absorbC2 lambda chi commitment =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
      subst nextControl
      simpa [adaptiveDecodedChallenges, embedNextAdaptiveControl,
        pendingChallengeIds] using invariant
  | afterAdaptiveC2 lambda chi =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run
  | rejected =>
      cases reply <;>
        simp [OpenAdaptiveControl.afterVerifierReply] at run

/-! ## Executable transition preservation -/

/-- Appending the challenge at the head of the pending list simply moves its
id across the decoded/pending concatenation boundary. -/
theorem append_decoded_challenge_moves_pending
    (snapshot : FutureFreeSnapshot) (id : ChallengeId) (value : Qm31Bytes)
    (remaining : List FutureFreeSlot)
    (invariant :
      (snapshot.decodedChallenges.map DecodedChallenge.id ++
        id :: challengeIdsInSlots remaining).Nodup) :
    (((snapshot.decodedChallenges ++
          [({ id := id, value := value } : DecodedChallenge)]).map
          DecodedChallenge.id) ++ challengeIdsInSlots remaining).Nodup := by
  simpa [List.map_append, List.append_assoc] using invariant

/-- A successful challenge which immediately rejects still preserves the
duplicate-free decoded prefix. -/
theorem append_decoded_challenge_prefix_nodup
    (snapshot : FutureFreeSnapshot) (id : ChallengeId) (value : Qm31Bytes)
    (remaining : List FutureFreeSlot)
    (invariant :
      (snapshot.decodedChallenges.map DecodedChallenge.id ++
        id :: challengeIdsInSlots remaining).Nodup) :
    ((snapshot.decodedChallenges ++
        [({ id := id, value := value } : DecodedChallenge)]).map
      DecodedChallenge.id).Nodup := by
  have moved := append_decoded_challenge_moves_pending snapshot id value
    remaining invariant
  exact (List.nodup_append.mp moved).1

/-- The incremental ordinary sampler preserves record uniqueness.  A retry
keeps the same pending head; success moves that head to the decoded ledger;
and rejection discards only a pending suffix. -/
theorem process_challenge_block_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (invariant :
      (snapshot.decodedChallenges.map DecodedChallenge.id ++
        id :: challengeIdsInSlots remaining).Nodup) :
    SnapshotChallengeRecordUniqueness
      (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore) := by
  simp only [processFutureFreeChallengeBlock]
  split
  next encoded accepted =>
    have moved := append_decoded_challenge_moves_pending snapshot id encoded
      remaining invariant
    have decodedPrefix := append_decoded_challenge_prefix_nodup snapshot id encoded
      remaining invariant
    cases id <;>
      simp only [completeFutureFreeChallenge]
    all_goals try
      simpa [SnapshotChallengeRecordUniqueness] using moved
    case circlePoint sample =>
      split
      · simpa [SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
          decodedPrefix
      · simpa [SnapshotChallengeRecordUniqueness] using moved
  next rejected =>
    have decodedPrefix :
        (snapshot.decodedChallenges.map DecodedChallenge.id).Nodup :=
      (List.nodup_append.mp invariant).1
    split
    · simpa [SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
        invariant
    · simpa [SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
        decodedPrefix

/-- The q16 sampler never changes the decoded challenge ledger.  Its live and
successful controls retain the same post-q16 schedule; rejecting branches may
only discard that pending suffix. -/
theorem process_candidate_block_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (invariant :
      (snapshot.decodedChallenges.map DecodedChallenge.id ++
        challengeIdsInSlots remaining).Nodup) :
    SnapshotChallengeRecordUniqueness
      (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore) := by
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | none =>
      by_cases belowCap : outputs.length + 1 < 8
      · simpa [processFutureFreeCandidateBlock, decoded, belowCap,
          SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
          invariant
      · have decodedPrefix := (List.nodup_append.mp invariant).1
        simpa [processFutureFreeCandidateBlock, decoded, belowCap,
          SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
          decodedPrefix
  | some outcome =>
      cases outcome with
      | samplerAbort =>
          have decodedPrefix := (List.nodup_append.mp invariant).1
          simpa [processFutureFreeCandidateBlock, decoded,
            SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
            decodedPrefix
      | schedule schedule =>
          by_cases compact : environment.frontierNodes schedule ≤ 203
          · simpa [processFutureFreeCandidateBlock, decoded, compact,
              SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
              invariant
          · simpa [processFutureFreeCandidateBlock, decoded, compact,
              SnapshotChallengeRecordUniqueness, pendingChallengeIds] using
              invariant

/-! ## Complete executable verifier-step preservation -/

/-- Every successful raw controller update preserves uniqueness.  This covers
the adaptive prefix, every linear slot, all work stages, the complete q16
search, and all fail-closed exits. -/
theorem raw_after_verifier_reply_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (invariant : SnapshotChallengeRecordUniqueness snapshot)
    (run : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore = some next) :
    SnapshotChallengeRecordUniqueness next := by
  cases controlExact : snapshot.control with
  | adaptive control =>
      simp only [rawAfterFutureFreeVerifierReply, controlExact] at run
      cases nextAdaptiveExact :
          control.afterVerifierReply environment.decoders reply with
      | none => simp [nextAdaptiveExact] at run
      | some nextAdaptive =>
          simp [nextAdaptiveExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                pendingChallengeIds (.adaptive control)).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact] using
              invariant
          have preserved :=
            open_adaptive_after_reply_preserves_record_uniqueness
              environment.decoders snapshot.decodedChallenges control
              nextAdaptive reply current nextAdaptiveExact
          unfold SnapshotChallengeRecordUniqueness
          change
            ((adaptiveDecodedChallenges snapshot.decodedChallenges control
                nextAdaptive).map DecodedChallenge.id ++
              pendingChallengeIds
                (embedNextAdaptiveControl nextAdaptive)).Nodup
          exact preserved
  | linear remaining =>
      cases remaining with
      | nil =>
          cases reply <;>
            simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | cons slot remaining =>
          cases slot with
          | fixed action =>
              simp [rawAfterFutureFreeVerifierReply, controlExact] at run
              subst next
              have current :
                  (snapshot.decodedChallenges.map DecodedChallenge.id ++
                    challengeIdsInSlots remaining).Nodup := by
                simpa [SnapshotChallengeRecordUniqueness, controlExact,
                  pendingChallengeIds, challengeIdsInSlots] using invariant
              simpa [SnapshotChallengeRecordUniqueness] using current
          | challenge id =>
              cases reply with
              | none =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
              | single output =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
              | squeeze output advance =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
                  subst next
                  have current :
                      (snapshot.decodedChallenges.map DecodedChallenge.id ++
                        id :: challengeIdsInSlots remaining).Nodup := by
                    simpa [SnapshotChallengeRecordUniqueness, controlExact,
                      pendingChallengeIds, challengeIdsInSlots] using invariant
                  exact process_challenge_block_preserves_record_uniqueness
                    environment snapshot id [] remaining output nextCore current
          | payload site =>
              cases reply <;>
                simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          | work stage =>
              cases reply <;>
                simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          | beginQ16 =>
              cases reply with
              | none =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
                  subst next
                  have current :
                      (snapshot.decodedChallenges.map DecodedChallenge.id ++
                        challengeIdsInSlots remaining).Nodup := by
                    simpa [SnapshotChallengeRecordUniqueness, controlExact,
                      pendingChallengeIds, challengeIdsInSlots] using invariant
                  simpa [SnapshotChallengeRecordUniqueness,
                    pendingChallengeIds] using current
              | single output =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
              | squeeze output advance =>
                  simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | absorbPayload payload remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          simpa [SnapshotChallengeRecordUniqueness] using current
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | workCheck stage nonce remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          simpa [SnapshotChallengeRecordUniqueness,
            pendingChallengeIds] using current
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | workCheckpoint stage nonce remaining =>
      cases reply with
      | none =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          simpa [SnapshotChallengeRecordUniqueness,
            pendingChallengeIds] using current
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | workAbsorb stage nonce remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          simpa [SnapshotChallengeRecordUniqueness] using current
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | sampleChallenge id outputs remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                id :: challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds, challengeIdsInSlots] using invariant
          exact process_challenge_block_preserves_record_uniqueness
            environment snapshot id outputs remaining output nextCore current
  | q16Absorb base counter remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          simpa [SnapshotChallengeRecordUniqueness, controlExact,
            pendingChallengeIds] using invariant
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | q16Sample base counter outputs remaining =>
      cases reply with
      | none => simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          exact process_candidate_block_preserves_record_uniqueness
            environment snapshot base counter outputs remaining output nextCore
            current
  | q16Restore base counter nextCounter remaining =>
      cases reply with
      | none =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          cases nextCounter with
          | none =>
              have current :
                  (snapshot.decodedChallenges.map DecodedChallenge.id ++
                    challengeIdsInSlots remaining).Nodup := by
                simpa [SnapshotChallengeRecordUniqueness, controlExact,
                  pendingChallengeIds] using invariant
              have decodedPrefix := (List.nodup_append.mp current).1
              simpa [SnapshotChallengeRecordUniqueness,
                pendingChallengeIds] using decodedPrefix
          | some nextCounter =>
              simpa [SnapshotChallengeRecordUniqueness, controlExact,
                pendingChallengeIds] using invariant
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | q16Selected base counter schedule remaining =>
      cases reply with
      | none =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have current :
              (snapshot.decodedChallenges.map DecodedChallenge.id ++
                challengeIdsInSlots remaining).Nodup := by
            simpa [SnapshotChallengeRecordUniqueness, controlExact,
              pendingChallengeIds] using invariant
          simpa [SnapshotChallengeRecordUniqueness] using current
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | q16SamplerReject counter reason =>
      cases reply with
      | none =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have decodedPrefix := decoded_prefix_nodup_of_snapshot invariant
          simpa [SnapshotChallengeRecordUniqueness,
            pendingChallengeIds] using decodedPrefix
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | q16AllNoncompactReject =>
      cases reply with
      | none =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
          subst next
          have decodedPrefix := decoded_prefix_nodup_of_snapshot invariant
          simpa [SnapshotChallengeRecordUniqueness,
            pendingChallengeIds] using decodedPrefix
      | single output =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
      | squeeze output advance =>
          simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | rejected reason =>
      cases reply <;>
        simp [rawAfterFutureFreeVerifierReply, controlExact] at run
  | done =>
      cases reply <;>
        simp [rawAfterFutureFreeVerifierReply, controlExact] at run

/-- The fixed-binding wrapper changes neither control nor the decoded ledger,
so the raw preservation theorem lifts to the production verifier update. -/
theorem after_verifier_reply_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (invariant : SnapshotChallengeRecordUniqueness snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    SnapshotChallengeRecordUniqueness next := by
  unfold afterFutureFreeVerifierReply at run
  cases rawExact : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore with
  | none => simp [rawExact] at run
  | some rawNext =>
      simp [rawExact] at run
      subst next
      have preserved := raw_after_verifier_reply_preserves_record_uniqueness
        environment snapshot rawNext reply nextCore invariant rawExact
      simpa [SnapshotChallengeRecordUniqueness] using preserved

/-! ## Saved-history and restoration preservation -/

/-- Every live and retained snapshot has a duplicate-free decoded/pending
challenge inventory. -/
def FutureFreeChallengeRecordUniqueness
    (state : FutureFreeVerifierState) : Prop :=
  SnapshotChallengeRecordUniqueness state.current ∧
    ∀ snapshot ∈ state.seen, SnapshotChallengeRecordUniqueness snapshot

@[simp] theorem initial_future_free_challenge_record_uniqueness
    (bindings : FixedBindings) :
    FutureFreeChallengeRecordUniqueness
      (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeChallengeRecordUniqueness, initialFutureFreeVerifierState,
    initial_snapshot_challenge_record_uniqueness]

theorem append_future_free_snapshot_preserves_record_uniqueness
    (state : FutureFreeVerifierState) (event : FutureFreeEvent)
    (next : FutureFreeSnapshot)
    (invariant : FutureFreeChallengeRecordUniqueness state)
    (nextInvariant : SnapshotChallengeRecordUniqueness next) :
    FutureFreeChallengeRecordUniqueness
      (appendFutureFreeSnapshot state event next) := by
  constructor
  · exact nextInvariant
  · intro snapshot member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact invariant.2 snapshot old
    · exact nextInvariant

/-- Prover-owned C1/C2, payload, and work-nonce submissions do not decode a
challenge and preserve the exact pending inventory. -/
theorem submit_next_raw_message_preserves_record_uniqueness
    (raw : RawTag73ProverMessages) (state next : FutureFreeVerifierState)
    (invariant : FutureFreeChallengeRecordUniqueness state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeChallengeRecordUniqueness next := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlExact =>
    unfold submitFutureFreeC1 at submitted
    split at submitted
    next =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      apply append_future_free_snapshot_preserves_record_uniqueness
        state _ _ invariant
      simpa [SnapshotChallengeRecordUniqueness, controlExact,
        pendingChallengeIds] using invariant.1
    all_goals simp at submitted
  next lambda chi controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    apply append_future_free_snapshot_preserves_record_uniqueness
      state _ _ invariant
    simpa [SnapshotChallengeRecordUniqueness, controlExact,
      pendingChallengeIds] using invariant.1
  next site remaining controlExact =>
    unfold submitFutureFreePayload at submitted
    split at submitted
    next _control site' remaining' controlExact' =>
      split at submitted
      next =>
        have branchExact : site = site' ∧ remaining = remaining' := by
          have controlsEqual := controlExact.symm.trans controlExact'
          simpa using controlsEqual
        rcases branchExact with ⟨rfl, rfl⟩
        have nextExact := Option.some.inj submitted
        rw [← nextExact]
        apply append_future_free_snapshot_preserves_record_uniqueness
          state _ _ invariant
        simpa [SnapshotChallengeRecordUniqueness, controlExact,
          pendingChallengeIds, challengeIdsInSlots] using invariant.1
      next => simp at submitted
    all_goals simp at submitted
  next stage remaining controlExact =>
    unfold submitFutureFreeWorkNonce at submitted
    split at submitted
    next _control stage' remaining' controlExact' =>
      have branchExact : stage = stage' ∧ remaining = remaining' := by
        have controlsEqual := controlExact.symm.trans controlExact'
        simpa using controlsEqual
      rcases branchExact with ⟨rfl, rfl⟩
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      apply append_future_free_snapshot_preserves_record_uniqueness
        state _ _ invariant
      simpa [SnapshotChallengeRecordUniqueness, controlExact,
        pendingChallengeIds, challengeIdsInSlots] using invariant.1
    all_goals simp at submitted
  all_goals simp at submitted

theorem advance_future_free_verifier_preserves_record_uniqueness
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (invariant : FutureFreeChallengeRecordUniqueness state)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeChallengeRecordUniqueness next := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, _actionExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, _coreExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextSnapshot, snapshotExact, finalExact⟩ :=
    Option.bind_eq_some_iff.mp run
  have nextSnapshotInvariant :=
    after_verifier_reply_preserves_record_uniqueness environment state.current
      nextSnapshot reply nextCore invariant.1 snapshotExact
  have nextExact := Option.some.inj finalExact
  subst next
  exact append_future_free_snapshot_preserves_record_uniqueness
    state (.verifier action reply) nextSnapshot invariant nextSnapshotInvariant

theorem future_free_operational_step_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next)
    (invariant : FutureFreeChallengeRecordUniqueness state) :
    FutureFreeChallengeRecordUniqueness next := by
  cases step with
  | prover submitted event snapshot appendExact =>
      exact submit_next_raw_message_preserves_record_uniqueness
        raw state next invariant submitted
  | verifier forced replyPath advanced =>
      exact advance_future_free_verifier_preserves_record_uniqueness
        environment state next _ invariant advanced
  | stutter noSubmission noAction => exact invariant

theorem future_free_operational_trace_preserves_record_uniqueness
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (trace : FutureFreeOperationalTrace environment raw state pairs final)
    (invariant : FutureFreeChallengeRecordUniqueness state) :
    FutureFreeChallengeRecordUniqueness final := by
  induction trace with
  | stop current => exact invariant
  | next step rest inductionHypothesis =>
      exact inductionHypothesis
        (future_free_operational_step_preserves_record_uniqueness
          environment raw _ _ _ step invariant)

/-- Restoration reinstalls one already retained pre-transition snapshot, so it
cannot manufacture a duplicate challenge record. -/
theorem restore_indexed_transition_preserves_record_uniqueness
    (state : FutureFreeVerifierState) (transition : FutureFreeTransition)
    (invariant : FutureFreeChallengeRecordUniqueness state)
    (closed : FutureFreeHistoryClosed state)
    (member : transition ∈ state.transitions) :
    FutureFreeChallengeRecordUniqueness
      (restoreIndexedTransition transition) := by
  have beforeSeen : transition.before ∈ state.seen :=
    (closed.2.2 transition member).1
  have beforeInvariant := invariant.2 transition.before beforeSeen
  exact ⟨beforeInvariant, by
    intro snapshot seen
    simp [restoreIndexedTransition] at seen
    subst snapshot
    exact beforeInvariant⟩

/-- A completed state has a unique canonical record value for each challenge
id; gamma and alpha zero therefore cannot depend on a later classical choice. -/
theorem done_state_gamma_alpha_zero_records_unique
    (state : FutureFreeVerifierState)
    (invariant : FutureFreeChallengeRecordUniqueness state)
    (done : state.current.control = .done) :
    (state.current.decodedChallenges.map DecodedChallenge.id).Nodup := by
  have current := invariant.1
  simpa [SnapshotChallengeRecordUniqueness, done, pendingChallengeIds] using
    current

#print axioms deployed_pending_challenge_ids_nodup
#print axioms initial_snapshot_challenge_record_uniqueness
#print axioms decoded_prefix_nodup_of_snapshot
#print axioms decoded_challenge_value_unique_in_list
#print axioms decoded_challenge_value_unique
#print axioms append_decoded_challenge_moves_pending
#print axioms process_challenge_block_preserves_record_uniqueness
#print axioms open_adaptive_after_reply_preserves_record_uniqueness
#print axioms raw_after_verifier_reply_preserves_record_uniqueness
#print axioms after_verifier_reply_preserves_record_uniqueness
#print axioms submit_next_raw_message_preserves_record_uniqueness
#print axioms future_free_operational_trace_preserves_record_uniqueness
#print axioms restore_indexed_transition_preserves_record_uniqueness
#print axioms done_state_gamma_alpha_zero_records_unique

end

end AspisK1.V7Tag73ChallengeRecordUniquenessInvariant
