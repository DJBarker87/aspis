import AspisFormal.TheftResistance
import AspisFormal.V5AcceptedSpendRelation

/-!
# V5 wrong-secret reduction

This file instantiates `TheftResistance.lean` with the maintained V5 spend
relation.  A V5 witness contains the opened columns and the two integer values
used by `SpendRelation`.  Its relation requires both:

* an exact match between the six public spend fields and the opened columns;
* the complete maintained `SpendRelation` for those columns and values.

From those two facts, the public nullifier is forced to equal
`deployedNullifier opened.k_nu opened.r_in`.  That equality is proved below; it
is not supplied as a premise to the V5 reduction.

The remaining bad events stay explicit.  An accepted prover execution that
extracts a wrong secret implies either extraction failure or a target second
preimage of the deployed nullifier function.  The execution record may include
the proof, prover, and random-oracle query transcript; no theorem here claims
that the public proof bytes reveal the witness.  A separate reduction below covers the
narrow case where the extracted input leaf is exactly a fixed victim leaf but
the extracted note opening differs: this yields extractor failure or a target
second preimage of the combined deployed owner-and-note commitment.

Neither reduction supplies a probability bound or proves that the abstract
acceptance predicate is the deployed Rust verifier.  The second reduction also
does not prove that an alternative leaf or path reaches the victim's public
anchor; that needs a separate Merkle-binding argument.  This file therefore
does not define a complete ledger-level or efficient-adversary theft game.
-/

namespace AspisV5TheftResistance

open AspisFormal.ArithmetizationCore
open Aspis.TheftResistance
open AspisV5AcceptedSpendRelation

/-- Data returned by a V5 knowledge extractor. -/
structure V5Witness where
  opened : OpenedColumns
  inputValue : Nat
  outputValue : Nat

/-- The exact public-field match together with the complete maintained spend
relation. -/
def V5WitnessRelation
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (statement : V5PublicStatement) (witness : V5Witness) : Prop :=
  OpenedColumnsMatchStatement statement witness.opened ∧
    SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
      witness.opened witness.inputValue witness.outputValue

def witnessSecret (witness : V5Witness) : Digest := witness.opened.k_nu

def witnessRandomness (witness : V5Witness) : Digest := witness.opened.r_in

/-! ## A different opening of the same input leaf -/

/-- The four values that determine an input note.  The value remains a natural
number so the target-second-preimage predicate can restrict both openings to
the V5 30-bit value domain before it is cast into the field. -/
structure InputNoteOpening where
  secret : Digest
  value : Nat
  asset : F
  randomness : Digest

/-- The deployed input-note commitment, including owner-key derivation. -/
def deployedInputNoteCommitment
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (opening : InputNoteOpening) : Digest :=
  deployedNote (deployedOwner opening.secret) (opening.value : F)
    opening.asset opening.randomness

/-- The candidate opening read from an extracted V5 witness.  A valid V5
relation forces its asset to equal this public statement asset. -/
def witnessInputNoteOpening
    (statement : V5PublicStatement) (witness : V5Witness) : InputNoteOpening where
  secret := witness.opened.k_nu
  value := witness.inputValue
  asset := statement.asset
  randomness := witness.opened.r_in

/-- The valid V5 input-value domain for the combined commitment. -/
def ValidInputNoteOpening (opening : InputNoteOpening) : Prop :=
  opening.value < 2 ^ 30

/-- A target second preimage of the combined owner-and-note commitment, with
both the fixed target and candidate restricted to valid V5 input values. -/
def InputNoteTargetSecondPreimageAt
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (target candidate : InputNoteOpening) : Prop :=
  candidate ≠ target ∧
    ValidInputNoteOpening target ∧
    ValidInputNoteOpening candidate ∧
    deployedInputNoteCommitment deployedOwner deployedNote candidate =
      deployedInputNoteCommitment deployedOwner deployedNote target

/-- An accepted adversary run extracts the fixed victim leaf but a different
combined note opening. -/
def DifferentOpeningSameLeafEvent
    {Execution Coins : Type*}
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (victimLeaf : Digest)
    (target : InputNoteOpening)
    (A : Coins → Execution) (coins : Coins) : Prop :=
  Accepts statement (A coins) ∧
    (extract statement (A coins)).opened.L_in = victimLeaf ∧
    witnessInputNoteOpening statement (extract statement (A coins)) ≠ target

/-- The target-second-preimage event produced from an extracted witness. -/
def InputNoteTargetSecondPreimageEvent
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (extract : V5PublicStatement → Execution → V5Witness)
    (statement : V5PublicStatement) (target : InputNoteOpening)
    (A : Coins → Execution) (coins : Coins) : Prop :=
  InputNoteTargetSecondPreimageAt deployedOwner deployedNote target
    (witnessInputNoteOpening statement (extract statement (A coins)))

/-- The complete V5 relation binds the extracted input leaf to the combined
deployed owner-and-note commitment of the extracted opening. -/
theorem relation_binds_input_leaf
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {statement : V5PublicStatement} {witness : V5Witness}
    (hrelation : V5WitnessRelation deployedOwner deployedNote
      deployedNullifier deployedNode statement witness) :
    witness.opened.L_in =
      deployedInputNoteCommitment deployedOwner deployedNote
        (witnessInputNoteOpening statement witness) := by
  calc
    witness.opened.L_in =
        deployedNote witness.opened.pk_in (witness.inputValue : F)
          witness.opened.a_in witness.opened.r_in :=
      hrelation.2.input_note
    _ = deployedNote (deployedOwner witness.opened.k_nu)
          (witness.inputValue : F) statement.asset witness.opened.r_in := by
      rw [hrelation.2.owner_key, hrelation.2.asset_equality, hrelation.1.asset]
    _ = deployedInputNoteCommitment deployedOwner deployedNote
          (witnessInputNoteOpening statement witness) := rfl

/-- For one V5 adversary run, extracting the fixed victim leaf with a
different valid opening implies either extraction failure or a target second
preimage of the combined owner-and-note commitment. -/
theorem different_opening_same_leaf_reduction
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    {statement : V5PublicStatement} {victimLeaf : Digest}
    {target : InputNoteOpening}
    (targetValid : ValidInputNoteOpening target)
    (targetLeaf : victimLeaf =
      deployedInputNoteCommitment deployedOwner deployedNote target)
    (A : Coins → Execution) (coins : Coins) :
    DifferentOpeningSameLeafEvent Accepts extract statement victimLeaf target
        A coins →
      ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins ∨
        InputNoteTargetSecondPreimageEvent deployedOwner deployedNote extract
          statement target A coins := by
  rintro ⟨accepted, extractedLeaf, different⟩
  by_cases hrelation :
      V5WitnessRelation deployedOwner deployedNote deployedNullifier
        deployedNode statement (extract statement (A coins))
  · right
    refine ⟨different, targetValid, ?_, ?_⟩
    · exact hrelation.2.range_in.1
    · exact (relation_binds_input_leaf hrelation).symm.trans
        (extractedLeaf.trans targetLeaf)
  · exact Or.inl ⟨accepted, hrelation⟩

/-- Set form of `different_opening_same_leaf_reduction`. -/
theorem different_opening_same_leaf_event_subset_bad_events
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    {statement : V5PublicStatement} {victimLeaf : Digest}
    {target : InputNoteOpening}
    (targetValid : ValidInputNoteOpening target)
    (targetLeaf : victimLeaf =
      deployedInputNoteCommitment deployedOwner deployedNote target)
    (A : Coins → Execution) :
    {coins | DifferentOpeningSameLeafEvent Accepts extract statement victimLeaf
        target A coins} ⊆
      {coins | ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins} ∪
        {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
          extract statement target A coins} := by
  intro coins event
  exact different_opening_same_leaf_reduction deployedOwner deployedNote
    deployedNullifier deployedNode Accepts extract targetValid targetLeaf
    A coins event

/-- Measure form of the same reduction.  This supplies only a union bound; it
does not bound extractor failure or the combined commitment's target-second-
preimage probability. -/
theorem different_opening_same_leaf_measure_le_bad_events
    {Execution Coins : Type*} [MeasurableSpace Coins]
    (measure : MeasureTheory.Measure Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    {statement : V5PublicStatement} {victimLeaf : Digest}
    {target : InputNoteOpening}
    (targetValid : ValidInputNoteOpening target)
    (targetLeaf : victimLeaf =
      deployedInputNoteCommitment deployedOwner deployedNote target)
    (A : Coins → Execution) :
    measure {coins | DifferentOpeningSameLeafEvent Accepts extract statement
        victimLeaf target A coins} ≤
      measure {coins | ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins} +
        measure {coins | InputNoteTargetSecondPreimageEvent deployedOwner
          deployedNote extract statement target A coins} := by
  calc
    measure {coins | DifferentOpeningSameLeafEvent Accepts extract statement
        victimLeaf target A coins} ≤
      measure ({coins | ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins} ∪
        {coins | InputNoteTargetSecondPreimageEvent deployedOwner deployedNote
          extract statement target A coins}) :=
      MeasureTheory.measure_mono
        (different_opening_same_leaf_event_subset_bad_events deployedOwner
          deployedNote deployedNullifier deployedNode Accepts extract
          targetValid targetLeaf A)
    _ ≤ measure {coins | ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins} +
        measure {coins | InputNoteTargetSecondPreimageEvent deployedOwner
          deployedNote extract statement target A coins} :=
      MeasureTheory.measure_union_le _ _

/-- The V5 relation itself binds the extracted secret and randomness to the
public nullifier.  No hash injectivity or preimage-uniqueness statement is used. -/
theorem relation_binds_public_nullifier
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {statement : V5PublicStatement} {witness : V5Witness}
    (hrelation : V5WitnessRelation deployedOwner deployedNote
      deployedNullifier deployedNode statement witness) :
    deployedNullifier (witnessSecret witness) (witnessRandomness witness) =
      statement.nullifier := by
  exact hrelation.2.nullifier.symm.trans hrelation.1.nullifier

/-- For one V5 adversary run, an accepted execution extracting a secret
different from the fixed nullifier preimage's secret implies extraction
failure or a target second preimage.  This theorem does not assert that the
fixed preimage opens a leaf under the statement's anchor.  The extraction-
failure predicate is for the exact V5 witness relation above. -/
theorem wrong_secret_reduction
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    {statement : V5PublicStatement}
    {targetSecret targetRandomness : Digest}
    (targetNullifierPreimage : statement.nullifier =
      deployedNullifier targetSecret targetRandomness)
    (A : Coins → Execution) (coins : Coins) :
    WrongSecretEvent witnessSecret Accepts extract statement targetSecret A coins →
      ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins ∨
        TargetSecondPreimageEvent deployedNullifier witnessSecret
          witnessRandomness extract statement targetSecret targetRandomness
          A coins := by
  exact Aspis.TheftResistance.wrong_secret_reduction
    deployedNullifier V5PublicStatement.nullifier witnessSecret
    witnessRandomness
    (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
    Accepts extract
    (fun _ _ hrelation => relation_binds_public_nullifier hrelation)
    targetNullifierPreimage A coins

/-- Measure form of the same V5 reduction.  If `μ` is the adversary's random
coin distribution, the wrong-secret event is bounded by extractor failure plus
the exact target-second-preimage event. -/
theorem wrong_secret_measure_le_bad_events
    {Execution Coins : Type*} [MeasurableSpace Coins]
    (μ : MeasureTheory.Measure Coins)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extract : V5PublicStatement → Execution → V5Witness)
    {statement : V5PublicStatement}
    {targetSecret targetRandomness : Digest}
    (targetNullifierPreimage : statement.nullifier =
      deployedNullifier targetSecret targetRandomness)
    (A : Coins → Execution) :
    μ {coins | WrongSecretEvent witnessSecret Accepts extract
        statement targetSecret A coins} ≤
      μ {coins | ExtractionFailureEvent
          (V5WitnessRelation deployedOwner deployedNote
            deployedNullifier deployedNode)
          Accepts extract statement A coins} +
        μ {coins | TargetSecondPreimageEvent deployedNullifier witnessSecret
          witnessRandomness extract statement targetSecret targetRandomness
          A coins} := by
  exact Aspis.TheftResistance.wrong_secret_measure_le_bad_events
    deployedNullifier V5PublicStatement.nullifier witnessSecret
    witnessRandomness
    (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
    μ Accepts extract
    (fun _ _ hrelation => relation_binds_public_nullifier hrelation)
    targetNullifierPreimage A

/-- On the successful branch of a V5 knowledge extractor, the extraction
failure term disappears.  Target-second-preimage resistance is still an
external computational assumption. -/
theorem wrong_secret_under_successful_extraction
    {Execution Coins : Type*}
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts : V5PublicStatement → Execution → Prop)
    (extractor : KnowledgeExtractor Accepts
      (V5WitnessRelation deployedOwner deployedNote
        deployedNullifier deployedNode))
    {statement : V5PublicStatement}
    {targetSecret targetRandomness : Digest}
    (targetNullifierPreimage : statement.nullifier =
      deployedNullifier targetSecret targetRandomness)
    (A : Coins → Execution) (coins : Coins) :
    WrongSecretEvent witnessSecret Accepts extractor.extract
        statement targetSecret A coins →
      TargetSecondPreimageEvent deployedNullifier witnessSecret
        witnessRandomness extractor.extract statement targetSecret
        targetRandomness A coins := by
  exact Aspis.TheftResistance.wrong_secret_under_successful_extraction
    deployedNullifier V5PublicStatement.nullifier witnessSecret
    witnessRandomness
    (V5WitnessRelation deployedOwner deployedNote deployedNullifier deployedNode)
    Accepts extractor
    (fun _ _ hrelation => relation_binds_public_nullifier hrelation)
    targetNullifierPreimage A coins

end AspisV5TheftResistance

#print axioms AspisV5TheftResistance.relation_binds_public_nullifier
#print axioms AspisV5TheftResistance.relation_binds_input_leaf
#print axioms AspisV5TheftResistance.different_opening_same_leaf_reduction
#print axioms AspisV5TheftResistance.different_opening_same_leaf_event_subset_bad_events
#print axioms AspisV5TheftResistance.different_opening_same_leaf_measure_le_bad_events
#print axioms AspisV5TheftResistance.wrong_secret_reduction
#print axioms AspisV5TheftResistance.wrong_secret_measure_le_bad_events
#print axioms AspisV5TheftResistance.wrong_secret_under_successful_extraction
