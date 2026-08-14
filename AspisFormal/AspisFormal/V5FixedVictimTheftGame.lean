import AspisFormal.ApplicationMerkleBinding
import AspisFormal.V5TheftResistance

/-!
# A fixed-victim theft game for V5

This file defines one concrete target note and classifies every accepted attack
on either its nullifier or its tree position.  Outside extraction failure, an
attack yields one of four precise events:

1. recovery of the victim's secret/nullifier-randomness pair;
2. a different pair with the victim's nullifier;
3. a different valid opening of the victim's exact note commitment; or
4. a different leaf at the victim's tree position, exposing a node collision.

The fourth case allows arbitrary alternative siblings.  Different direction
bits identify a different tree position and are not automatically an attack;
`ApplicationMerkleBinding.lean` records why treating every alternative path as
a collision would be false.

The final section adds the chain-level boundaries needed by a deployed game:
PDA aliasing, runtime/state failure, and invalid victim setup.  Conditional on
the caller-supplied `DeployedAttackConnection`, the theorem gives a complete
case split for the attack event defined here and a measure union bound.  It
does not prove that every real attack satisfies that connection or invent
probabilities for Poseidon2 collision resistance, credential recovery,
extraction, PDA derivation, or Solana runtime behavior.  Those statements
remain external cryptographic or platform assumptions.
-/

namespace AspisV5FixedVictimTheftGame

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open Aspis.TheftResistance
open AspisV5AcceptedSpendRelation
open AspisV5TheftResistance
open AspisApplicationMerkleBinding

/-- One target note, including its intended depth-20 tree position. -/
structure FixedVictim where
  opening : InputNoteOpening
  valueBound : ValidInputNoteOpening opening
  bits : Fin 20 → Bool
  siblings : Fin 20 → Digest

def victimLeaf
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (victim : FixedVictim) : Digest :=
  deployedInputNoteCommitment deployedOwner deployedNote victim.opening

def victimAnchor
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (victim : FixedVictim) : Digest :=
  Root deployedNode (victimLeaf deployedOwner deployedNote victim)
    victim.bits victim.siblings

def victimNullifier
    (deployedNullifier : Digest → Digest → Digest)
    (victim : FixedVictim) : Digest :=
  deployedNullifier victim.opening.secret victim.opening.randomness

/-- The extractor recovered the exact secret/randomness pair that controls the
victim's nullifier.  This is a key-recovery event, not a hash collision. -/
def VictimCredentialRecoveryEvent
    {Execution Coins : Type*}
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  Accepts statement (adversary coins) ∧
    (witnessSecret (extract statement (adversary coins)),
      witnessRandomness (extract statement (adversary coins))) =
    (victim.opening.secret, victim.opening.randomness)

/-- The extracted witness uses a different leaf at the victim's exact tree
position and nevertheless reaches the victim root.  The next theorem turns
this run-specific event into a concrete node-collision witness. -/
def AlternativeLeafAtVictimPositionEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  let witness := extract statement (adversary coins)
  Accepts statement (adversary coins) ∧
    witness.opened.bits = victim.bits ∧
    witness.opened.L_in ≠ victimLeaf deployedOwner deployedNote victim ∧
    Root deployedNode witness.opened.L_in victim.bits witness.opened.sib =
      victimAnchor deployedOwner deployedNote deployedNode victim

/-- An alternative leaf at the fixed victim position supplies two different
ordered node inputs with the same deployed node-hash output at some level. -/
theorem alternative_leaf_at_victim_position_exposes_node_collision
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) :
    AlternativeLeafAtVictimPositionEvent deployedOwner deployedNote deployedNode
        Accepts extract statement victim adversary coins →
      PathsExposeNodeCollision deployedNode
        (extract statement (adversary coins)).opened.L_in
        (victimLeaf deployedOwner deployedNote victim)
        victim.bits
        (extract statement (adversary coins)).opened.sib
        victim.siblings := by
  rintro ⟨_accepted, _samePosition, differentLeaf, sameRoot⟩
  exact same_position_different_leaf_same_root_exposes_node_collision
    deployedNode differentLeaf (by simpa [victimAnchor] using sameRoot)

/-- A model-level attack either spends with the victim nullifier or replaces
the leaf at the victim's intended position under the victim anchor.  This
definition deliberately includes the honest owner; in the reduction, an
honest owner lands in the credential-recovery branch.  A security game bounds
that branch by withholding the sampled credential from the adversary. -/
def FixedVictimAttackEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  let witness := extract statement (adversary coins)
  Accepts statement (adversary coins) ∧
    (statement.nullifier = victimNullifier deployedNullifier victim ∨
      (witness.opened.bits = victim.bits ∧
        statement.currentAnchor =
          victimAnchor deployedOwner deployedNote deployedNode victim))

/-- The five mathematical failure events covering a fixed-victim attack. -/
def FixedVictimMathematicalFailureEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) : Prop :=
  ExtractionFailureEvent
      (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
      Accepts extract statement adversary coins ∨
    VictimCredentialRecoveryEvent Accepts extract statement victim adversary coins ∨
    TargetSecondPreimageEvent deployedNullifier witnessSecret witnessRandomness
      extract statement victim.opening.secret victim.opening.randomness
      adversary coins ∨
    InputNoteTargetSecondPreimageEvent deployedOwner deployedNote extract
      statement victim.opening adversary coins ∨
    AlternativeLeafAtVictimPositionEvent deployedOwner deployedNote deployedNode
      Accepts extract statement victim adversary coins

/-- Every accepted fixed-victim attack is classified without assuming that a
compressing hash is injective. -/
theorem fixed_victim_attack_implies_mathematical_failure
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) (coins : Coins) :
    FixedVictimAttackEvent deployedOwner deployedNote deployedNullifier
        deployedNode Accepts extract statement victim adversary coins →
      FixedVictimMathematicalFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts extract statement victim
        adversary coins := by
  rintro ⟨accepted, attackTarget⟩
  by_cases relation :
    V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode
      statement (extract statement (adversary coins))
  · rcases attackTarget with targetsNullifier | ⟨samePosition, targetsAnchor⟩
    · by_cases recovered :
        (witnessSecret (extract statement (adversary coins)),
          witnessRandomness (extract statement (adversary coins))) =
        (victim.opening.secret, victim.opening.randomness)
      · exact Or.inr (Or.inl ⟨accepted, recovered⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨recovered, ?_⟩))
        exact (relation_binds_public_nullifier relation).trans targetsNullifier
    · by_cases sameOpening :
        witnessInputNoteOpening statement (extract statement (adversary coins)) =
          victim.opening
      · refine Or.inr (Or.inl ⟨accepted, ?_⟩)
        exact congrArg (fun opening => (opening.secret, opening.randomness)) sameOpening
      · by_cases sameLeaf :
        (extract statement (adversary coins)).opened.L_in =
          victimLeaf deployedOwner deployedNote victim
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          refine ⟨sameOpening, victim.valueBound, relation.2.range_in.1, ?_⟩
          exact (relation_binds_input_leaf relation).symm.trans
            (sameLeaf.trans (by rfl))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          refine ⟨accepted, samePosition, sameLeaf, ?_⟩
          rw [← samePosition]
          exact relation.2.input_root.symm.trans
            (relation.1.currentAnchor.trans targetsAnchor)
  · exact Or.inl ⟨accepted, relation⟩

/-- Set inclusion form of the fixed-victim reduction. -/
theorem fixed_victim_attack_subset_mathematical_failures
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) :
    {coins | FixedVictimAttackEvent deployedOwner deployedNote deployedNullifier
      deployedNode Accepts extract statement victim adversary coins} ⊆
    {coins | FixedVictimMathematicalFailureEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts extract statement victim adversary coins} := by
  intro coins attack
  exact fixed_victim_attack_implies_mathematical_failure deployedOwner deployedNote
    deployedNullifier deployedNode Accepts extract statement victim adversary coins attack

/-- Probability union bound for the five mathematical events.  The measure is
over the adversary's complete random tape and any experiment randomness packed
into it. -/
theorem fixed_victim_attack_measure_le_five_failures
    {Execution Coins : Type*} [MeasurableSpace Coins]
    (measure : MeasureTheory.Measure Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) :
    measure {coins | FixedVictimAttackEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts extract statement victim adversary coins} ≤
      measure {coins | ExtractionFailureEvent
        (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
        Accepts extract statement adversary coins} +
      measure {coins | VictimCredentialRecoveryEvent Accepts extract statement
        victim adversary coins} +
      measure {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
        witnessRandomness extract statement victim.opening.secret
        victim.opening.randomness adversary coins} +
      measure {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
        extract statement victim.opening adversary coins} +
      measure {coins | AlternativeLeafAtVictimPositionEvent deployedOwner deployedNote
        deployedNode Accepts extract statement victim adversary coins} := by
  let extractionFailures : Set Coins := {coins | ExtractionFailureEvent
    (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
    Accepts extract statement adversary coins}
  let credentialRecoveries : Set Coins := {coins | VictimCredentialRecoveryEvent
    Accepts extract statement victim adversary coins}
  let nullifierCollisions : Set Coins := {coins | TargetSecondPreimageEvent
    deployedNullifier witnessSecret witnessRandomness extract statement
    victim.opening.secret victim.opening.randomness adversary coins}
  let noteCollisions : Set Coins := {coins | InputNoteTargetSecondPreimageEvent
    deployedOwner deployedNote extract statement victim.opening adversary coins}
  let merkleCollisions : Set Coins := {coins | AlternativeLeafAtVictimPositionEvent
    deployedOwner deployedNote deployedNode Accepts extract statement victim
    adversary coins}
  have subset : {coins | FixedVictimAttackEvent deployedOwner deployedNote
      deployedNullifier deployedNode Accepts extract statement victim adversary coins} ⊆
      (((extractionFailures ∪ credentialRecoveries) ∪ nullifierCollisions) ∪
        noteCollisions) ∪ merkleCollisions := by
    intro coins attack
    have classified := fixed_victim_attack_implies_mathematical_failure
      deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
      statement victim adversary coins attack
    rcases classified with extraction | recovery | nullifier | note | merkle
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_left _ extraction)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_right _ recovery)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ nullifier))
    · exact Set.mem_union_left _ (Set.mem_union_right _ note)
    · exact Set.mem_union_right _ merkle
  calc
    measure {coins | FixedVictimAttackEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts extract statement victim adversary coins} ≤
        measure ((((extractionFailures ∪ credentialRecoveries) ∪ nullifierCollisions) ∪
          noteCollisions) ∪ merkleCollisions) := MeasureTheory.measure_mono subset
    _ ≤ measure (((extractionFailures ∪ credentialRecoveries) ∪ nullifierCollisions) ∪
          noteCollisions) + measure merkleCollisions := MeasureTheory.measure_union_le _ _
    _ ≤ (measure ((extractionFailures ∪ credentialRecoveries) ∪ nullifierCollisions) +
          measure noteCollisions) + measure merkleCollisions :=
      add_le_add_left (MeasureTheory.measure_union_le _ _) _
    _ ≤ ((measure (extractionFailures ∪ credentialRecoveries) +
          measure nullifierCollisions) + measure noteCollisions) +
          measure merkleCollisions :=
      add_le_add_left (add_le_add_left (MeasureTheory.measure_union_le _ _) _) _
    _ ≤ (((measure extractionFailures + measure credentialRecoveries) +
          measure nullifierCollisions) + measure noteCollisions) +
          measure merkleCollisions :=
      by
        gcongr
        exact MeasureTheory.measure_union_le _ _
    _ = _ := rfl

/-! ## Deployed boundary -/

/-- The extra failures between the mathematical spend game and the chain:
different nullifiers resolving to the victim marker account, a failure of
account locking/rollback/marker persistence or exact runtime behavior, and a
victim setup that did not create one unambiguous live target note. -/
structure ChainFailureEvents (Coins : Type*) where
  pdaAlias : Coins → Prop
  runtimeOrState : Coins → Prop
  victimSetup : Coins → Prop

/-- Connection required from a deployed attack experiment to the mathematical
game.  The deployed Tag-67 program did not enforce bump 255; this interface
therefore says nothing about a particular bump.  PDA derivation and aliasing
are represented directly. -/
def DeployedAttackConnection
    {Execution Coins : Type*}
    (deployedAttack : Coins → Prop)
    (chainFailures : ChainFailureEvents Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution) : Prop :=
  ∀ coins, deployedAttack coins →
    FixedVictimAttackEvent deployedOwner deployedNote deployedNullifier
      deployedNode Accepts extract statement victim adversary coins ∨
    chainFailures.pdaAlias coins ∨
    chainFailures.runtimeOrState coins ∨
    chainFailures.victimSetup coins

/-- A deployed attack is contained in the mathematical failure union plus the
three explicit chain/setup failures. -/
theorem deployed_attack_implies_listed_failure
    {Execution Coins : Type*}
    (deployedAttack : Coins → Prop)
    (chainFailures : ChainFailureEvents Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution)
    (connection : DeployedAttackConnection deployedAttack chainFailures
      deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
      statement victim adversary)
    (coins : Coins) :
    deployedAttack coins →
      FixedVictimMathematicalFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts extract statement victim
        adversary coins ∨
      chainFailures.pdaAlias coins ∨
      chainFailures.runtimeOrState coins ∨
      chainFailures.victimSetup coins := by
  intro attack
  rcases connection coins attack with modelAttack | pdaAlias | runtime | setup
  · exact Or.inl (fixed_victim_attack_implies_mathematical_failure
      deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
      statement victim adversary coins modelAttack)
  · exact Or.inr (Or.inl pdaAlias)
  · exact Or.inr (Or.inr (Or.inl runtime))
  · exact Or.inr (Or.inr (Or.inr setup))

/-- Full measure bound for the deployed game.  Each term corresponds to one
independent statement that a real security claim must bound. -/
theorem deployed_attack_measure_le_eight_failures
    {Execution Coins : Type*} [MeasurableSpace Coins]
    (measure : MeasureTheory.Measure Coins)
    (deployedAttack : Coins → Prop)
    (chainFailures : ChainFailureEvents Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victim : FixedVictim)
    (adversary : Coins → Execution)
    (connection : DeployedAttackConnection deployedAttack chainFailures
      deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
      statement victim adversary) :
    measure {coins | deployedAttack coins} ≤
      measure {coins | ExtractionFailureEvent
        (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
        Accepts extract statement adversary coins} +
      measure {coins | VictimCredentialRecoveryEvent Accepts extract statement
        victim adversary coins} +
      measure {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
        witnessRandomness extract statement victim.opening.secret
        victim.opening.randomness adversary coins} +
      measure {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
        extract statement victim.opening adversary coins} +
      measure {coins | AlternativeLeafAtVictimPositionEvent deployedOwner deployedNote
        deployedNode Accepts extract statement victim adversary coins} +
      measure {coins | chainFailures.pdaAlias coins} +
      measure {coins | chainFailures.runtimeOrState coins} +
      measure {coins | chainFailures.victimSetup coins} := by
  let modelAttacks : Set Coins := {coins | FixedVictimAttackEvent deployedOwner
    deployedNote deployedNullifier deployedNode Accepts extract statement victim
    adversary coins}
  let pdaFailures : Set Coins := {coins | chainFailures.pdaAlias coins}
  let runtimeFailures : Set Coins := {coins | chainFailures.runtimeOrState coins}
  let setupFailures : Set Coins := {coins | chainFailures.victimSetup coins}
  have subset : {coins | deployedAttack coins} ⊆
      ((modelAttacks ∪ pdaFailures) ∪ runtimeFailures) ∪ setupFailures := by
    intro coins attack
    rcases connection coins attack with model | pda | runtime | setup
    · exact Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_left _ model))
    · exact Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_right _ pda))
    · exact Set.mem_union_left _ (Set.mem_union_right _ runtime)
    · exact Set.mem_union_right _ setup
  have modelBound := fixed_victim_attack_measure_le_five_failures measure
    deployedOwner deployedNote deployedNullifier deployedNode Accepts extract
    statement victim adversary
  calc
    measure {coins | deployedAttack coins} ≤
        measure (((modelAttacks ∪ pdaFailures) ∪ runtimeFailures) ∪ setupFailures) :=
      MeasureTheory.measure_mono subset
    _ ≤ measure ((modelAttacks ∪ pdaFailures) ∪ runtimeFailures) +
          measure setupFailures := MeasureTheory.measure_union_le _ _
    _ ≤ (measure (modelAttacks ∪ pdaFailures) + measure runtimeFailures) +
          measure setupFailures :=
      add_le_add_left (MeasureTheory.measure_union_le _ _) _
    _ ≤ ((measure modelAttacks + measure pdaFailures) + measure runtimeFailures) +
          measure setupFailures :=
      add_le_add_left (add_le_add_left (MeasureTheory.measure_union_le _ _) _) _
    _ ≤ (((((measure {coins | ExtractionFailureEvent
            (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
            Accepts extract statement adversary coins} +
          measure {coins | VictimCredentialRecoveryEvent Accepts extract statement
            victim adversary coins}) +
          measure {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
            witnessRandomness extract statement victim.opening.secret
            victim.opening.randomness adversary coins}) +
          measure {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
            extract statement victim.opening adversary coins}) +
          measure {coins | AlternativeLeafAtVictimPositionEvent deployedOwner deployedNote
            deployedNode Accepts extract statement victim adversary coins}) +
          measure pdaFailures) + measure runtimeFailures + measure setupFailures := by
      gcongr
    _ = _ := rfl

end AspisV5FixedVictimTheftGame

#print axioms
  AspisV5FixedVictimTheftGame.alternative_leaf_at_victim_position_exposes_node_collision
#print axioms AspisV5FixedVictimTheftGame.fixed_victim_attack_implies_mathematical_failure
#print axioms AspisV5FixedVictimTheftGame.fixed_victim_attack_measure_le_five_failures
#print axioms AspisV5FixedVictimTheftGame.deployed_attack_implies_listed_failure
#print axioms AspisV5FixedVictimTheftGame.deployed_attack_measure_le_eight_failures
