import AspisFormal.V5AcceptedExecutionSecurityBridge
import AspisFormal.V5FinalSecurityAccounting
import AspisFormal.V5FixedVictimTheftGame
import AspisFormal.V5TheftStateTransitionReduction

/-!
# Fixed-victim theft after observing other proofs

This file models a first fraudulent spend attempted after an arbitrary finite,
ordered history of other valid proofs.  The history records each honest
witness for the game, while the adversary interface receives a public
statement/proof projection and a separate coins projection.  The definition
does not claim that those projections are independent of the victim secret;
that is exactly why credential recovery remains a separately bounded event.

The extractor runs after the public history and the adversary's final attempt
are fixed.  Failure of that history-dependent extractor, recovery of the
victim credential, the three deployed-hash collision forms, and Solana runtime
divergence all remain named events.  The theorems below classify the attack and
give set/measure inclusions.  They do not assign probabilities to those events.
-/

namespace AspisV5AdaptiveObservedTheftGame

open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open Aspis.TheftResistance
open AspisV5AcceptedSpendRelation
open AspisV5FinalSecurityAccounting
open AspisV5FixedVictimTheftGame
open AspisV5TheftResistance
open AspisV5TheftStateTransitionReduction
open AspisApplicationMerkleBinding

/-! ## What the adversary is allowed to observe -/

/-- One public statement and its public proof artifact.  The artifact can be
the proof bytes plus any genuinely public metadata. -/
structure PublicObservedProof (PublicArtifact : Type*) where
  statement : V5PublicStatement
  artifact : PublicArtifact

/-- The experiment's full record for an honestly generated observed proof.
The adversary only receives `view`; `execution` and `witness` stay in the
game record so validity can be stated without using the attack extractor. -/
structure ObservedProofRecord
    (PublicArtifact Execution : Type*) where
  view : PublicObservedProof PublicArtifact
  execution : Execution
  witness : V5Witness

/-- Whether one history entry really is an accepted proof for a different
spend.  "Other" means it neither uses the victim nullifier nor targets the
victim's exact tree position. -/
def ValidOtherObservedProof
    {PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (record : ObservedProofRecord PublicArtifact Execution) : Prop :=
  Accepts record.view.statement record.execution ∧
    V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode
      record.view.statement record.witness ∧
    record.view.statement.nullifier ≠
      victimNullifier deployedNullifier victim ∧
    ¬ (record.witness.opened.bits = victim.bits ∧
      record.view.statement.currentAnchor =
        victimAnchor deployedOwner deployedNote deployedNode victim)

/-- Every entry in the ordered history is a valid proof for another spend.
There is no length cap. -/
def ValidOtherObservationHistory
    {PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (history : List (ObservedProofRecord PublicArtifact Execution)) : Prop :=
  ∀ record ∈ history,
    ValidOtherObservedProof deployedOwner deployedNote deployedNullifier
      deployedNode Accepts victim record

/-- Erase the witnesses and verifier-side execution records before giving the
ordered history to the adversary. -/
def publicHistory
    {PublicArtifact Execution : Type*}
    (history : List (ObservedProofRecord PublicArtifact Execution)) :
    List (PublicObservedProof PublicArtifact) :=
  history.map ObservedProofRecord.view

theorem public_history_preserves_length
    {PublicArtifact Execution : Type*}
    (history : List (ObservedProofRecord PublicArtifact Execution)) :
    (publicHistory history).length = history.length := by
  simp [publicHistory]

/-! ## Adaptive experiment and first fraudulent attempt -/

/-- The statement and complete verifier/extractor execution record produced by
the adversary after seeing the public history. -/
structure SpendAttempt (Execution : Type*) where
  statement : V5PublicStatement
  execution : Execution

/-- The whole experiment.  `Sample` may contain challenger randomness and
hidden witnesses.  The adversary interface receives `coinsOf sample` and the
erased public history; non-leakage through those projections is not assumed. -/
structure AdaptiveObservationExperiment
    (Sample AdversaryCoins PublicArtifact Execution : Type*) where
  history : Sample → List (ObservedProofRecord PublicArtifact Execution)
  coinsOf : Sample → AdversaryCoins
  adversary : AdversaryCoins → List (PublicObservedProof PublicArtifact) →
    SpendAttempt Execution

def visibleHistory
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (sample : Sample) : List (PublicObservedProof PublicArtifact) :=
  publicHistory (experiment.history sample)

def chosenAttempt
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (sample : Sample) : SpendAttempt Execution :=
  experiment.adversary (experiment.coinsOf sample)
    (visibleHistory experiment sample)

/-- The extractor is selected for the adversary after its observed public
history.  Its security for such history-dependent executions is not assumed
by this definition. -/
abbrev ExtractAfterObservation
    (PublicArtifact Execution : Type*) :=
  List (PublicObservedProof PublicArtifact) →
    V5PublicStatement → Execution → V5Witness

def chosenWitness
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : V5Witness :=
  extractAfter (visibleHistory experiment sample)
    (chosenAttempt experiment sample).statement
    (chosenAttempt experiment sample).execution

/-- The first fraudulent-spend event.  All earlier observations are valid and
do not target the victim; the final adaptive attempt both verifies and commits
while targeting either the victim nullifier or the victim's exact tree
position. -/
def AdaptiveFirstFraudulentSpendEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  ValidOtherObservationHistory deployedOwner deployedNote deployedNullifier
      deployedNode Accepts victim (experiment.history sample) ∧
    Accepts (chosenAttempt experiment sample).statement
      (chosenAttempt experiment sample).execution ∧
    Commits (chosenAttempt experiment sample).statement
      (chosenAttempt experiment sample).execution ∧
    ((chosenAttempt experiment sample).statement.nullifier =
        victimNullifier deployedNullifier victim ∨
      ((chosenWitness experiment extractAfter sample).opened.bits =
          victim.bits ∧
        (chosenAttempt experiment sample).statement.currentAnchor =
          victimAnchor deployedOwner deployedNote deployedNode victim))

/-! ## Named failures after observation -/

/-- Knowledge extraction failed for the final accepting execution after the
extractor received the complete public observation history. -/
def ExtractorAfterObservationFailureEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  Accepts (chosenAttempt experiment sample).statement
      (chosenAttempt experiment sample).execution ∧
    ¬ V5WitnessRelation deployedOwner deployedNote deployedNullifier
      deployedNode (chosenAttempt experiment sample).statement
      (chosenWitness experiment extractAfter sample)

/-- The history-dependent extractor recovered the exact victim credential. -/
def CredentialRecoveryAfterObservationEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  Accepts (chosenAttempt experiment sample).statement
      (chosenAttempt experiment sample).execution ∧
    (witnessSecret (chosenWitness experiment extractAfter sample),
      witnessRandomness (chosenWitness experiment extractAfter sample)) =
      (victim.opening.secret, victim.opening.randomness)

/-- A different extracted secret/randomness pair with the victim nullifier. -/
def NullifierSecondPreimageAfterObservationEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedNullifier : Digest → Digest → Digest)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  TargetSecondPreimageAt deployedNullifier victim.opening.secret
    victim.opening.randomness
    (witnessSecret (chosenWitness experiment extractAfter sample),
      witnessRandomness (chosenWitness experiment extractAfter sample))

/-- A different valid note opening with the victim note commitment. -/
def NoteSecondPreimageAfterObservationEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  InputNoteTargetSecondPreimageAt deployedOwner deployedNote victim.opening
    (witnessInputNoteOpening (chosenAttempt experiment sample).statement
      (chosenWitness experiment extractAfter sample))

/-- A different leaf under the victim root at the victim's exact position. -/
def AlternativeLeafAfterObservationEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  Accepts (chosenAttempt experiment sample).statement
      (chosenAttempt experiment sample).execution ∧
    (chosenWitness experiment extractAfter sample).opened.bits = victim.bits ∧
    (chosenWitness experiment extractAfter sample).opened.L_in ≠
      victimLeaf deployedOwner deployedNote victim ∧
    Root deployedNode
        (chosenWitness experiment extractAfter sample).opened.L_in victim.bits
        (chosenWitness experiment extractAfter sample).opened.sib =
      victimAnchor deployedOwner deployedNote deployedNode victim

/-- The concrete node collision exposed by the alternative-leaf branch. -/
def VictimTreeCollisionAfterObservationEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  PathsExposeNodeCollision deployedNode
    (chosenWitness experiment extractAfter sample).opened.L_in
    (victimLeaf deployedOwner deployedNote victim)
    victim.bits
    (chosenWitness experiment extractAfter sample).opened.sib
    victim.siblings

theorem alternative_leaf_after_observation_exposes_node_collision
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) :
    AlternativeLeafAfterObservationEvent deployedOwner deployedNote
        deployedNode Accepts victim experiment extractAfter sample →
      VictimTreeCollisionAfterObservationEvent deployedOwner deployedNote
        deployedNode victim experiment extractAfter sample := by
  rintro ⟨_accepted, _samePosition, differentLeaf, sameRoot⟩
  exact same_position_different_leaf_same_root_exposes_node_collision
    deployedNode differentLeaf (by simpa [victimAnchor] using sameRoot)

/-- The five mathematical events covering the final adaptive attempt.  The
observation history changes the extractor input but does not change the
pointwise case split. -/
def AdaptiveMathematicalFailureEvent
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) : Prop :=
  ExtractorAfterObservationFailureEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts experiment extractAfter sample ∨
    CredentialRecoveryAfterObservationEvent Accepts victim experiment
      extractAfter sample ∨
    NullifierSecondPreimageAfterObservationEvent deployedNullifier victim
      experiment extractAfter sample ∨
    NoteSecondPreimageAfterObservationEvent deployedOwner deployedNote victim
      experiment extractAfter sample ∨
    VictimTreeCollisionAfterObservationEvent deployedOwner deployedNote
      deployedNode victim experiment extractAfter sample

/-! ## Adaptive-history reduction -/

theorem adaptive_first_fraudulent_spend_implies_mathematical_failure
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (sample : Sample) :
    AdaptiveFirstFraudulentSpendEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts Commits victim experiment
        extractAfter sample →
      AdaptiveMathematicalFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts victim experiment extractAfter
        sample := by
  rintro ⟨_validHistory, accepted, _committed, attackTarget⟩
  by_cases relation :
      V5WitnessRelation deployedOwner deployedNote deployedNullifier
        deployedNode (chosenAttempt experiment sample).statement
        (chosenWitness experiment extractAfter sample)
  · rcases attackTarget with targetsNullifier | ⟨samePosition, targetsAnchor⟩
    · by_cases recovered :
        (witnessSecret (chosenWitness experiment extractAfter sample),
          witnessRandomness (chosenWitness experiment extractAfter sample)) =
        (victim.opening.secret, victim.opening.randomness)
      · exact Or.inr (Or.inl ⟨accepted, recovered⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨recovered, ?_⟩))
        exact (relation_binds_public_nullifier relation).trans targetsNullifier
    · by_cases sameOpening :
        witnessInputNoteOpening (chosenAttempt experiment sample).statement
            (chosenWitness experiment extractAfter sample) =
          victim.opening
      · refine Or.inr (Or.inl ⟨accepted, ?_⟩)
        exact congrArg (fun opening => (opening.secret, opening.randomness))
          sameOpening
      · by_cases sameLeaf :
          (chosenWitness experiment extractAfter sample).opened.L_in =
            victimLeaf deployedOwner deployedNote victim
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          refine ⟨sameOpening, victim.valueBound, relation.2.range_in.1, ?_⟩
          exact (relation_binds_input_leaf relation).symm.trans
            (sameLeaf.trans (by rfl))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          apply alternative_leaf_after_observation_exposes_node_collision
            deployedOwner deployedNote deployedNode Accepts victim experiment
            extractAfter sample
          refine ⟨accepted, samePosition, sameLeaf, ?_⟩
          rw [← samePosition]
          exact relation.2.input_root.symm.trans
            (relation.1.currentAnchor.trans targetsAnchor)
  · exact Or.inl ⟨accepted, relation⟩

theorem adaptive_first_fraudulent_spend_subset_mathematical_failures
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution) :
    {sample | AdaptiveFirstFraudulentSpendEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter sample} ⊆
    {sample | AdaptiveMathematicalFailureEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts victim experiment extractAfter
      sample} := by
  intro sample attack
  exact adaptive_first_fraudulent_spend_implies_mathematical_failure
    deployedOwner deployedNote deployedNullifier deployedNode Accepts Commits
    victim experiment extractAfter sample attack

/-! ## Probability-free and measure forms -/

/-- Union bound for the adaptive experiment.  Every right-hand term remains
an event whose probability must be established separately. -/
theorem adaptive_first_fraudulent_spend_measure_le_five_failures
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    [MeasurableSpace Sample]
    (measure : Measure Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution) :
    measure {sample | AdaptiveFirstFraudulentSpendEvent deployedOwner
      deployedNote deployedNullifier deployedNode Accepts Commits victim
      experiment extractAfter sample} ≤
      measure {sample | ExtractorAfterObservationFailureEvent deployedOwner
        deployedNote deployedNullifier deployedNode Accepts experiment
        extractAfter sample} +
      measure {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample} +
      measure {sample | NullifierSecondPreimageAfterObservationEvent
        deployedNullifier victim experiment extractAfter sample} +
      measure {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample} +
      measure {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample} := by
  let extraction : Set Sample :=
    {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts experiment extractAfter sample}
  let credential : Set Sample :=
    {sample | CredentialRecoveryAfterObservationEvent Accepts victim experiment
      extractAfter sample}
  let nullifier : Set Sample :=
    {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
      victim experiment extractAfter sample}
  let note : Set Sample :=
    {sample | NoteSecondPreimageAfterObservationEvent deployedOwner deployedNote
      victim experiment extractAfter sample}
  let tree : Set Sample :=
    {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
      deployedNote deployedNode victim experiment extractAfter sample}
  have subset :
      {sample | AdaptiveFirstFraudulentSpendEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts Commits victim experiment
        extractAfter sample} ⊆
      (((extraction ∪ credential) ∪ nullifier) ∪ note) ∪ tree := by
    intro sample attack
    have classified :=
      adaptive_first_fraudulent_spend_implies_mathematical_failure
        deployedOwner deployedNote deployedNullifier deployedNode Accepts
        Commits victim experiment extractAfter sample attack
    rcases classified with extractionFailure | credentialRecovery |
        nullifierCollision | noteCollision | treeCollision
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_left _ extractionFailure)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_right _ credentialRecovery)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ nullifierCollision))
    · exact Set.mem_union_left _ (Set.mem_union_right _ noteCollision)
    · exact Set.mem_union_right _ treeCollision
  calc
    measure {sample | AdaptiveFirstFraudulentSpendEvent deployedOwner
        deployedNote deployedNullifier deployedNode Accepts Commits victim
        experiment extractAfter sample} ≤
        measure ((((extraction ∪ credential) ∪ nullifier) ∪ note) ∪ tree) :=
      MeasureTheory.measure_mono subset
    _ ≤ measure (((extraction ∪ credential) ∪ nullifier) ∪ note) +
          measure tree := MeasureTheory.measure_union_le _ _
    _ ≤ (measure ((extraction ∪ credential) ∪ nullifier) + measure note) +
          measure tree := add_le_add_left (MeasureTheory.measure_union_le _ _) _
    _ ≤ ((measure (extraction ∪ credential) + measure nullifier) +
          measure note) + measure tree :=
      add_le_add_left (add_le_add_left (MeasureTheory.measure_union_le _ _) _) _
    _ ≤ (((measure extraction + measure credential) + measure nullifier) +
          measure note) + measure tree := by
      gcongr
      exact MeasureTheory.measure_union_le _ _
    _ = _ := rfl

/-! ## Explicit connection to an observed Solana spend -/

/-- A setup failure means that the advertised fixed victim was not one
unambiguous live note at the stated root and position. -/
structure AdaptiveChainFailures (Sample : Type*) where
  victimSetup : Sample → Prop

/-- Required connection from a real, committed first theft to this adaptive
game.  A run must either reach the exact modeled event, hit one of the seven
already named implementation/runtime failures, or have an invalid victim
setup.  Marker-address collisions are not a theft branch: an occupied
colliding marker rejects a second spend and can only deny service. -/
def DeployedAdaptiveAttackConnection
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (deployedFirstFraudulentSpend : Sample → Prop)
    (runtime : RuntimeFailurePredicates Sample)
    (chain : AdaptiveChainFailures Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution) : Prop :=
  ∀ sample, deployedFirstFraudulentSpend sample →
    AdaptiveFirstFraudulentSpendEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts Commits victim experiment
        extractAfter sample ∨
    NamedRuntimeFailureEvent runtime sample ∨
    chain.victimSetup sample

/-- The cryptographic containment obligations for the adaptive-history game.
The first field is specifically the extractor-after-observation obligation;
ordinary fixture extraction is not enough to inhabit it. -/
structure AdaptiveHistoryFailureCoverage
    {Sample : Type*} (events : FinalSecurityEvents Sample)
    (extractorAfterObservation credentialAfterObservation
      nullifierSecondPreimage noteSecondPreimage
      victimTreeCollision : Set Sample) : Prop where
  extractorAfterObservation :
    extractorAfterObservation ⊆ proofSoundnessFailure events
  credentialAfterObservation :
    credentialAfterObservation ⊆ events.victimCredentialRecovery
  nullifierSecondPreimage : nullifierSecondPreimage ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision
  noteSecondPreimage : noteSecondPreimage ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision
  victimTreeCollision : victimTreeCollision ⊆
    events.transcriptAndPrimitives.event .poseidon2Collision

/-- Outside its explicitly supplied containment assumptions, the modeled
adaptive first-spend event lands in the existing non-duplicated final ledger. -/
theorem adaptive_first_fraudulent_spend_subset_total_final_failure
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (events : FinalSecurityEvents Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (coverage : AdaptiveHistoryFailureCoverage events
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    {sample | AdaptiveFirstFraudulentSpendEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter sample} ⊆ totalFinalFailure events := by
  intro sample attack
  have classified :=
    adaptive_first_fraudulent_spend_implies_mathematical_failure deployedOwner
      deployedNote deployedNullifier deployedNode Accepts Commits victim
      experiment extractAfter sample attack
  rcases classified with extraction | credential | nullifier | note | tree
  · exact proof_soundness_failure_subset_total events
      (coverage.extractorAfterObservation extraction)
  · exact one_final_failure_is_in_total events .victimCredentialRecovery
      (coverage.credentialAfterObservation credential)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.nullifierSecondPreimage nullifier)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.noteSecondPreimage note)
  · exact one_final_failure_is_in_total events .poseidon2Collision
      (coverage.victimTreeCollision tree)

/-- Full deployed inclusion.  Victim-setup failure stays outside the current
24-event ledger rather than being hidden inside an unrelated budget. -/
theorem deployed_adaptive_first_fraudulent_spend_subset_final_or_setup
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    (events : FinalSecurityEvents Sample)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (chain : AdaptiveChainFailures Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      events.runtime chain deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter)
    (coverage : AdaptiveHistoryFailureCoverage events
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    {sample | deployedFirstFraudulentSpend sample} ⊆
      totalFinalFailure events ∪ {sample | chain.victimSetup sample} := by
  intro sample attack
  rcases connection sample attack with modeled | runtime | setup
  · exact Set.mem_union_left _
      (adaptive_first_fraudulent_spend_subset_total_final_failure events
        deployedOwner deployedNote deployedNullifier deployedNode Accepts
        Commits victim experiment extractAfter
        { extractorAfterObservation := coverage.extractorAfterObservation
          credentialAfterObservation := coverage.credentialAfterObservation
          nullifierSecondPreimage := coverage.nullifierSecondPreimage
          noteSecondPreimage := coverage.noteSecondPreimage
          victimTreeCollision := coverage.victimTreeCollision }
        modeled)
  · apply Set.mem_union_left
    rcases runtime with rust | system | lock | rollback | persistence |
        finality | close
    · exact one_final_failure_is_in_total events .rustStateModelMismatch rust
    · exact one_final_failure_is_in_total events .systemProgramOrPdaMismatch
        system
    · exact one_final_failure_is_in_total events .writableAccountLockFailure lock
    · exact one_final_failure_is_in_total events
        .rejectedTransactionRollbackFailure rollback
    · exact one_final_failure_is_in_total events
        .committedMarkerPersistenceFailure persistence
    · exact one_final_failure_is_in_total events
        .finalizedStateObservationFailure finality
    · exact one_final_failure_is_in_total events .closeOrRefundModelMismatch
        close
  · exact Set.mem_union_right _ setup

/-- Final probability statement.  The current released subtotal and external
ledger budgets are reused exactly; the independently named victim-setup event
is added rather than assigned a fabricated value. -/
theorem deployed_adaptive_first_fraudulent_spend_probability_le_explicit_budget
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    [MeasurableSpace Sample]
    (measure : Measure Sample)
    [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Sample)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (chain : AdaptiveChainFailures Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      events.runtime chain deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter)
    (coverage : AdaptiveHistoryFailureCoverage events
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
      ((1 : Real) / 2 ^ 108 + budget.total) +
        measure.real {sample | chain.victimSetup sample} := by
  have subset :=
    deployed_adaptive_first_fraudulent_spend_subset_final_or_setup events
      deployedFirstFraudulentSpend chain deployedOwner
      deployedNote deployedNullifier deployedNode Accepts Commits victim
      experiment extractAfter connection coverage
  calc
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
        measure.real
          (totalFinalFailure events ∪ {sample | chain.victimSetup sample}) :=
      MeasureTheory.measureReal_mono subset
    _ ≤ measure.real (totalFinalFailure events) +
          measure.real {sample | chain.victimSetup sample} :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ ((1 : Real) / 2 ^ 108 + budget.total) +
          measure.real {sample | chain.victimSetup sample} := by
      gcongr
      exact total_final_failure_probability_le_released_subtotal_plus_external
        measure events budget assumed

/-! ## Axiom audit -/

#print axioms public_history_preserves_length
#print axioms alternative_leaf_after_observation_exposes_node_collision
#print axioms adaptive_first_fraudulent_spend_implies_mathematical_failure
#print axioms adaptive_first_fraudulent_spend_measure_le_five_failures
#print axioms adaptive_first_fraudulent_spend_subset_total_final_failure
#print axioms deployed_adaptive_first_fraudulent_spend_subset_final_or_setup
#print axioms
  deployed_adaptive_first_fraudulent_spend_probability_le_explicit_budget

end AspisV5AdaptiveObservedTheftGame
