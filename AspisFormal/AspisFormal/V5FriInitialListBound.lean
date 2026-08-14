import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5FriJohnsonListBound

/-!
# Initial V5 FRI list bound from code distance

This file applies the direct Johnson double-counting theorem to the actual
`initialCandidateList`.  The only remaining coding-theory premise is stated
separately: distinct outputs of the initial circle-code encoder agree in at
most `1024` of the `524288` positions.  That is the minimum-distance fact for
the release's rate-`1/512` circle code.
-/

namespace AspisV5FriInitialListBound

open AspisV5FriCoherentCandidateExtraction
open AspisV5FriJohnsonListBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The exact distance fact needed by the elementary list-size proof.  It is
about encoder outputs, not about the received word or a chosen decoder list. -/
def InitialEncoderDistance (encoders : CodeEncoders K) : Prop :=
  ∀ c e : Coeff0 K, c ≠ e ->
    (agreementSet (encoders.layer0 c) (encoders.layer0 e)).card ≤ 1024

def Layer1EncoderDistance (encoders : CodeEncoders K) : Prop :=
  ∀ c e : Coeff1 K, c ≠ e ->
    (agreementSet (encoders.layer1 c) (encoders.layer1 e)).card ≤ 255

def Layer2EncoderDistance (encoders : CodeEncoders K) : Prop :=
  ∀ c e : Coeff2 K, c ≠ e ->
    (agreementSet (encoders.layer2 c) (encoders.layer2 e)).card ≤ 63

def Layer3EncoderDistance (encoders : CodeEncoders K) : Prop :=
  ∀ c e : Coeff3 K, c ≠ e ->
    (agreementSet (encoders.layer3 c) (encoders.layer3 e)).card ≤ 15

structure AllEncoderDistances (encoders : CodeEncoders K) : Prop where
  initial : InitialEncoderDistance encoders
  layer1 : Layer1EncoderDistance encoders
  layer2 : Layer2EncoderDistance encoders
  layer3 : Layer3EncoderDistance encoders

/-- Agreement with the same received word can overlap only where the two
encoded candidates agree with each other. -/
theorem received_agreement_intersection_le
    {n : Nat} {Coeff : Type*}
    (received : Fin n -> K) (encoder : Coeff -> Fin n -> K)
    (overlapCap : Nat)
    (hdistance : ∀ c e : Coeff, c ≠ e ->
      (agreementSet (encoder c) (encoder e)).card ≤ overlapCap)
    (c e : Coeff) (hne : c ≠ e) :
    ((agreementSet received (encoder c)) ∩
      (agreementSet received (encoder e))).card ≤ overlapCap := by
  classical
  apply (Finset.card_le_card ?_).trans (hdistance c e hne)
  intro x hx
  simp only [Finset.mem_inter, agreementSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx ⊢
  exact hx.1.symm.trans hx.2

/-- Two candidate/received agreement sets intersect only where the two
candidate codewords agree with each other. -/
theorem initial_agreement_intersection_le
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : InitialEncoderDistance encoders)
    (c e : Coeff0 K) (hne : c ≠ e) :
    ((agreementSet transcript.layer0 (encoders.layer0 c)) ∩
      (agreementSet transcript.layer0 (encoders.layer0 e))).card ≤ 1024 := by
  exact received_agreement_intersection_le transcript.layer0 encoders.layer0
    1024 hdistance c e hne

set_option maxRecDepth 10000 in
/-- The explicit initial decoder list has at most 222 members.  This is a
stronger integer result than the release cap 240. -/
theorem initialCandidateList_card_le_222
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : InitialEncoderDistance encoders) :
    (initialCandidateList encoders transcript).card ≤ 222 := by
  classical
  let Candidate :=
    {c : Coeff0 K // c ∈ initialCandidateList encoders transcript}
  let candidateAgreement : Candidate -> Finset (Fin 524288) := fun c =>
    agreementSet transcript.layer0 (encoders.layer0 c.1)
  have hlarge : ∀ c : Candidate, 24329 ≤ (candidateAgreement c).card := by
    intro c
    have hnear : Near0 encoders transcript c.1 :=
      (mem_initialCandidateList_iff encoders transcript c.1).mp c.2
    change 24329 ≤
      (agreementSet transcript.layer0 (encoders.layer0 c.1)).card
    unfold Near0 agreementCap0 at hnear
    omega
  have hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((candidateAgreement c) ∩ (candidateAgreement e)).card ≤ 1024 := by
    intro c e hne
    have hvalue : c.1 ≠ e.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq
    exact initial_agreement_intersection_le
      encoders transcript hdistance c.1 e.1 hvalue
  have hbound : Fintype.card Candidate ≤ 222 :=
    v5_initial_list_card_le_222
      (Candidate := Candidate) (Coordinate := Fin 524288)
      (by simp) candidateAgreement hlarge hoverlap
  change Fintype.card
    {c : Coeff0 K // c ∈ initialCandidateList encoders transcript} ≤ 222 at hbound
  rw [Fintype.card_coe] at hbound
  exact hbound

set_option maxRecDepth 10000 in
theorem initialCandidateList_card_le_240
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : InitialEncoderDistance encoders) :
    (initialCandidateList encoders transcript).card ≤ 240 :=
  (initialCandidateList_card_le_222 encoders transcript hdistance).trans (by omega)

/-- Under the circle-code distance premise, the old list-cap failure predicate
cannot occur. -/
theorem not_initialListCapFailure
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : InitialEncoderDistance encoders) :
    ¬ InitialListCapFailure encoders transcript := by
  unfold InitialListCapFailure
  exact Nat.not_lt_of_ge
    (initialCandidateList_card_le_240 encoders transcript hdistance)

set_option maxRecDepth 10000 in
theorem layer1CandidateList_card_le_213
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : Layer1EncoderDistance encoders) :
    (layer1CandidateList encoders transcript).card ≤ 213 := by
  classical
  let Candidate :=
    {c : Coeff1 K // c ∈ layer1CandidateList encoders transcript}
  let candidateAgreement : Candidate -> Finset (Fin 131072) := fun c =>
    agreementSet transcript.layer1 (encoders.layer1 c.1)
  have hlarge : ∀ c : Candidate, 6083 ≤ (candidateAgreement c).card := by
    intro c
    have hnear : Near1 encoders transcript c.1 :=
      (mem_layer1CandidateList_iff encoders transcript c.1).mp c.2
    change 6083 ≤ (agreementSet transcript.layer1 (encoders.layer1 c.1)).card
    unfold Near1 agreementCap1 at hnear
    omega
  have hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((candidateAgreement c) ∩ (candidateAgreement e)).card ≤ 255 := by
    intro c e hne
    have hvalue : c.1 ≠ e.1 := fun heq => hne (Subtype.ext heq)
    exact received_agreement_intersection_le transcript.layer1 encoders.layer1
      255 hdistance c.1 e.1 hvalue
  have hbound : Fintype.card Candidate ≤ 213 :=
    v5_layer1_list_card_le_213
      (Candidate := Candidate) (Coordinate := Fin 131072)
      (by simp) candidateAgreement hlarge hoverlap
  change Fintype.card
    {c : Coeff1 K // c ∈ layer1CandidateList encoders transcript} ≤ 213 at hbound
  rw [Fintype.card_coe] at hbound
  exact hbound

set_option maxRecDepth 10000 in
theorem layer2CandidateList_card_le_191
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : Layer2EncoderDistance encoders) :
    (layer2CandidateList encoders transcript).card ≤ 191 := by
  classical
  let Candidate :=
    {c : Coeff2 K // c ∈ layer2CandidateList encoders transcript}
  let candidateAgreement : Candidate -> Finset (Fin 32768) := fun c =>
    agreementSet transcript.layer2 (encoders.layer2 c.1)
  have hlarge : ∀ c : Candidate, 1521 ≤ (candidateAgreement c).card := by
    intro c
    have hnear : Near2 encoders transcript c.1 :=
      (mem_layer2CandidateList_iff encoders transcript c.1).mp c.2
    change 1521 ≤ (agreementSet transcript.layer2 (encoders.layer2 c.1)).card
    unfold Near2 agreementCap2 at hnear
    omega
  have hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((candidateAgreement c) ∩ (candidateAgreement e)).card ≤ 63 := by
    intro c e hne
    have hvalue : c.1 ≠ e.1 := fun heq => hne (Subtype.ext heq)
    exact received_agreement_intersection_le transcript.layer2 encoders.layer2
      63 hdistance c.1 e.1 hvalue
  have hbound : Fintype.card Candidate ≤ 191 :=
    v5_layer2_list_card_le_191
      (Candidate := Candidate) (Coordinate := Fin 32768)
      (by simp) candidateAgreement hlarge hoverlap
  change Fintype.card
    {c : Coeff2 K // c ∈ layer2CandidateList encoders transcript} ≤ 191 at hbound
  rw [Fintype.card_coe] at hbound
  exact hbound

set_option maxRecDepth 10000 in
theorem layer3CandidateList_card_le_134
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : Layer3EncoderDistance encoders) :
    (layer3CandidateList encoders transcript).card ≤ 134 := by
  classical
  let Candidate :=
    {c : Coeff3 K // c ∈ layer3CandidateList encoders transcript}
  let candidateAgreement : Candidate -> Finset (Fin 8192) := fun c =>
    agreementSet transcript.layer3 (encoders.layer3 c.1)
  have hlarge : ∀ c : Candidate, 381 ≤ (candidateAgreement c).card := by
    intro c
    have hnear : Near3 encoders transcript c.1 :=
      (mem_layer3CandidateList_iff encoders transcript c.1).mp c.2
    change 381 ≤ (agreementSet transcript.layer3 (encoders.layer3 c.1)).card
    unfold Near3 agreementCap3 at hnear
    omega
  have hoverlap : ∀ c e : Candidate, c ≠ e ->
      ((candidateAgreement c) ∩ (candidateAgreement e)).card ≤ 15 := by
    intro c e hne
    have hvalue : c.1 ≠ e.1 := fun heq => hne (Subtype.ext heq)
    exact received_agreement_intersection_le transcript.layer3 encoders.layer3
      15 hdistance c.1 e.1 hvalue
  have hbound : Fintype.card Candidate ≤ 134 :=
    v5_layer3_list_card_le_134
      (Candidate := Candidate) (Coordinate := Fin 8192)
      (by simp) candidateAgreement hlarge hoverlap
  change Fintype.card
    {c : Coeff3 K // c ∈ layer3CandidateList encoders transcript} ≤ 134 at hbound
  rw [Fintype.card_coe] at hbound
  exact hbound

theorem allCandidateLists_card_le_240
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (hdistance : AllEncoderDistances encoders) :
    (initialCandidateList encoders transcript).card ≤ 240 /\
      (layer1CandidateList encoders transcript).card ≤ 240 /\
      (layer2CandidateList encoders transcript).card ≤ 240 /\
      (layer3CandidateList encoders transcript).card ≤ 240 := by
  exact ⟨initialCandidateList_card_le_240 encoders transcript hdistance.initial,
    (layer1CandidateList_card_le_213 encoders transcript hdistance.layer1).trans (by omega),
    (layer2CandidateList_card_le_191 encoders transcript hdistance.layer2).trans (by omega),
    (layer3CandidateList_card_le_134 encoders transcript hdistance.layer3).trans (by omega)⟩

/-! ## The one list used by the relation union bound -/

/-- Candidate type fixed from the initial committed word.  It is formed
before any of the twelve relation challenges are sampled. -/
abbrev FrozenInitialCandidate
    (encoders : CodeEncoders K) (initialTranscript : IdealTranscript K) :=
  {c : Coeff0 K // c ∈ initialCandidateList encoders initialTranscript}

/-- An adaptive later response may depend on a challenge, but cannot change
the already committed initial word. -/
structure Layer0FixedResponseStrategy
    (initialTranscript : IdealTranscript K) (Challenge : Type*) where
  respond : Challenge -> IdealTranscript K
  layer0_fixed : ∀ challenge, (respond challenge).layer0 = initialTranscript.layer0

/-- Every adaptive response sees exactly the same initial decoder list. -/
theorem initialCandidateList_eq_for_response
    (encoders : CodeEncoders K) (initialTranscript : IdealTranscript K)
    {Challenge : Type*}
    (strategy : Layer0FixedResponseStrategy initialTranscript Challenge)
    (challenge : Challenge) :
    initialCandidateList encoders (strategy.respond challenge) =
      initialCandidateList encoders initialTranscript :=
  initialCandidateList_eq_of_layer0_eq encoders _ _
    (strategy.layer0_fixed challenge)

/-- Membership transports from any adaptive later transcript back to the one
pre-challenge candidate family. -/
theorem mem_frozenInitialCandidate_iff_response
    (encoders : CodeEncoders K) (initialTranscript : IdealTranscript K)
    {Challenge : Type*}
    (strategy : Layer0FixedResponseStrategy initialTranscript Challenge)
    (challenge : Challenge) (candidate : Coeff0 K) :
    candidate ∈ initialCandidateList encoders (strategy.respond challenge) <->
      candidate ∈ initialCandidateList encoders initialTranscript := by
  rw [initialCandidateList_eq_for_response encoders initialTranscript strategy challenge]

set_option maxRecDepth 10000 in
/-- The single pre-challenge candidate type used by the custom-relation union
has cardinality at most 240.  No later adaptive response creates another
factor of 240. -/
theorem frozenInitialCandidate_card_le_240
    (encoders : CodeEncoders K) (initialTranscript : IdealTranscript K)
    (hdistance : InitialEncoderDistance encoders) :
    Fintype.card (FrozenInitialCandidate encoders initialTranscript) ≤ 240 := by
  simpa only [FrozenInitialCandidate, Fintype.card_coe] using
    initialCandidateList_card_le_240 encoders initialTranscript hdistance

#print axioms initial_agreement_intersection_le
#print axioms initialCandidateList_card_le_222
#print axioms initialCandidateList_card_le_240
#print axioms not_initialListCapFailure
#print axioms layer1CandidateList_card_le_213
#print axioms layer2CandidateList_card_le_191
#print axioms layer3CandidateList_card_le_134
#print axioms allCandidateLists_card_le_240
#print axioms initialCandidateList_eq_for_response
#print axioms frozenInitialCandidate_card_le_240

end AspisV5FriInitialListBound
