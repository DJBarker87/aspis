import AspisFormal.Pool.V7EightLaneForestGeometry

/-!
# Soundness of the three-level V7 forest relation

This module proves the algebraic statement behind the three new Tag-73
historical-membership blocks.  A trace level contains the literal field bit,
current digest, sibling digest, ordered children, and parent output used by
the Rust forest residual evaluator.  Vanishing booleanity and ordering
residuals, together with the parent equation, imply one honest left-or-right
Merkle step.  Composing the exact three levels yields membership under the
public historical global root and a unique private lane number in `Fin 8`.

The input lane is recovered only from the three private path bits.  Nothing in
this file equates it with the public output lane derived from the nullifier.
That separation is intentional: an input note may be in any historical lane
while its output pair is appended to the deterministic live output lane.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneForestRelation

open AspisPool.V7EightLaneForestGeometry

abbrev Digest (K : Type) := Fin 8 → K

/-- Literal row-local equations used for one private forest path direction.
The parent equation abstracts only the Poseidon permutation itself. -/
structure ForestTraceLevel
    (K : Type) [CommRing K]
    (parent : Digest K → Digest K → Digest K) where
  bit : K
  current : Digest K
  sibling : Digest K
  left : Digest K
  right : Digest K
  output : Digest K
  booleanity : bit * (bit - 1) = 0
  leftOrdering : ∀ limb,
    left limb = current limb + bit * (sibling limb - current limb)
  rightOrdering : ∀ limb,
    right limb = sibling limb + bit * (current limb - sibling limb)
  parentCorrect : output = parent left right

/-- Booleanity over an integral domain extracts exactly one path direction. -/
theorem forest_bit_zero_or_one
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (bit : K) (booleanity : bit * (bit - 1) = 0) :
    bit = 0 ∨ bit = 1 := by
  rcases eq_zero_or_eq_zero_of_mul_eq_zero booleanity with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

/-- One vanishing forest trace level is exactly one ordered parent step. -/
theorem forest_trace_level_sound
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (level : ForestTraceLevel K parent) :
    ∃ direction : Bool,
      level.output =
        orderedParent parent direction level.current level.sibling := by
  rcases forest_bit_zero_or_one level.bit level.booleanity with zero | one
  · refine ⟨false, ?_⟩
    have leftExact : level.left = level.current := by
      funext limb
      simpa [zero] using level.leftOrdering limb
    have rightExact : level.right = level.sibling := by
      funext limb
      simpa [zero] using level.rightOrdering limb
    simpa [orderedParent, leftExact, rightExact] using level.parentCorrect
  · refine ⟨true, ?_⟩
    have leftExact : level.left = level.sibling := by
      funext limb
      simpa [one] using level.leftOrdering limb
    have rightExact : level.right = level.current := by
      funext limb
      simpa [one] using level.rightOrdering limb
    simpa [orderedParent, leftExact, rightExact] using level.parentCorrect

/-- The literal three-parent fold placed in physical blocks 54, 55, and 56. -/
def foldThreeForestLevels
    {Node : Type}
    (parent : Node → Node → Node)
    (laneRoot : Node)
    (siblings : Fin 3 → Node)
    (directions : Fin 3 → Bool) : Node :=
  let level0 := orderedParent parent (directions 0) laneRoot (siblings 0)
  let level1 := orderedParent parent (directions 1) level0 (siblings 1)
  orderedParent parent (directions 2) level1 (siblings 2)

/-- Exact chain equalities supplied by the forest copy registry: block 54
starts from the depth-20 lane root, blocks 55 and 56 start from the preceding
parent output, and block 56 ends at the public historical anchor. -/
structure ThreeLevelForestTrace
    (K : Type) [CommRing K]
    (parent : Digest K → Digest K → Digest K) where
  laneRoot : Digest K
  anchor : Digest K
  levels : Fin 3 → ForestTraceLevel K parent
  level0StartsAtLaneRoot : (levels 0).current = laneRoot
  level1ContinuesLevel0 : (levels 1).current = (levels 0).output
  level2ContinuesLevel1 : (levels 2).current = (levels 1).output
  level2EndsAtAnchor : (levels 2).output = anchor

/-- Vanishing of all three physical level relations gives one exact private
three-level Merkle authentication path to the public global anchor. -/
theorem three_level_forest_trace_sound
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (trace : ThreeLevelForestTrace K parent) :
    ∃ directions : Fin 3 → Bool,
      foldThreeForestLevels parent trace.laneRoot
          (fun level => (trace.levels level).sibling) directions =
        trace.anchor := by
  rcases forest_trace_level_sound parent (trace.levels 0) with ⟨d0, h0⟩
  rcases forest_trace_level_sound parent (trace.levels 1) with ⟨d1, h1⟩
  rcases forest_trace_level_sound parent (trace.levels 2) with ⟨d2, h2⟩
  let directions : Fin 3 → Bool := fun level =>
    if level = 0 then d0 else if level = 1 then d1 else d2
  refine ⟨directions, ?_⟩
  simp only [foldThreeForestLevels]
  simp [directions]
  rw [← trace.level0StartsAtLaneRoot, ← h0,
    ← trace.level1ContinuesLevel0, ← h1,
    ← trace.level2ContinuesLevel1, ← h2]
  exact trace.level2EndsAtAnchor

def boolValue (value : Bool) : Nat := if value then 1 else 0

/-- Little-endian lane number encoded by the three private directions. -/
def encodedLaneValue (directions : Fin 3 → Bool) : Nat :=
  boolValue (directions 0) +
    2 * boolValue (directions 1) +
    4 * boolValue (directions 2)

theorem encodedLaneValue_lt_eight (directions : Fin 3 → Bool) :
    encodedLaneValue directions < 8 := by
  cases h0 : directions 0 <;>
    cases h1 : directions 1 <;>
    cases h2 : directions 2 <;>
    simp [encodedLaneValue, boolValue, h0, h1, h2]

def encodedLane (directions : Fin 3 → Bool) : Lane :=
  ⟨encodedLaneValue directions, encodedLaneValue_lt_eight directions⟩

/-- The lane recovered from the witness has exactly the same three
little-endian direction bits. -/
theorem encoded_lane_recovers_directions
    (directions : Fin 3 → Bool) (level : Fin 3) :
    forestSuperDirection (encodedLane directions) level = directions level := by
  fin_cases level <;>
    cases h0 : directions 0 <;>
    cases h1 : directions 1 <;>
    cases h2 : directions 2 <;>
    simp [forestSuperDirection, encodedLane, encodedLaneValue, boolValue,
      h0, h1, h2]

/-- Strong form used by the spend relation: a vanishing three-block trace
constructs a private lane and a valid authentication path for precisely that
lane. -/
theorem three_level_forest_trace_extracts_private_lane
    {K : Type} [CommRing K] [NoZeroDivisors K]
    (parent : Digest K → Digest K → Digest K)
    (trace : ThreeLevelForestTrace K parent) :
    ∃ lane : Lane, ∃ directions : Fin 3 → Bool,
      (∀ level, directions level = forestSuperDirection lane level) ∧
      foldThreeForestLevels parent trace.laneRoot
          (fun level => (trace.levels level).sibling) directions =
        trace.anchor := by
  rcases three_level_forest_trace_sound parent trace with ⟨directions, valid⟩
  refine ⟨encodedLane directions, directions, ?_, valid⟩
  intro level
  exact (encoded_lane_recovers_directions directions level).symm

/-- A canonical checkpoint witness for any of the eight lanes folds to the
same global root.  This is the completeness counterpart of trace soundness. -/
theorem canonical_checkpoint_path_complete
    {Node : Type}
    (parent : Node → Node → Node)
    (roots : LaneVector Node)
    (lane : Lane) :
    foldThreeForestLevels parent (roots lane)
        (forestSuperSibling parent roots lane)
        (forestSuperDirection lane) =
      forestSuperRoot parent roots := by
  simpa [foldThreeForestLevels, reconstructForestSuperRoot] using
    every_lane_reconstructs_same_global_root parent roots lane

/-! ## Input/output lane separation -/

/-- One accepted forest spend carries two deliberately different lane roles:
the private historical input lane extracted above and the public live output
lane derived from the nullifier. -/
structure ForestLaneRoles
    (Nullifier : Type)
    (laneOfNullifier : Nullifier → Lane) where
  privateInputLane : Lane
  nullifier : Nullifier
  publicOutputLane : Lane
  outputLaneExact : publicOutputLane = laneOfNullifier nullifier

theorem output_lane_is_functional_and_independent_of_input
    {Nullifier : Type}
    (laneOfNullifier : Nullifier → Lane)
    (roles : ForestLaneRoles Nullifier laneOfNullifier) :
    roles.publicOutputLane = laneOfNullifier roles.nullifier :=
  roles.outputLaneExact

/-- In particular the relation is constructible when input and output lanes
differ; there is no hidden equality premise conflating the two roles. -/
theorem distinct_input_output_lanes_are_permitted
    {Nullifier : Type}
    (laneOfNullifier : Nullifier → Lane)
    (nullifier : Nullifier)
    (inputLane : Lane)
    (different : inputLane ≠ laneOfNullifier nullifier) :
    ∃ roles : ForestLaneRoles Nullifier laneOfNullifier,
      roles.privateInputLane ≠ roles.publicOutputLane := by
  exact ⟨⟨inputLane, nullifier, laneOfNullifier nullifier, rfl⟩, different⟩

#print axioms forest_bit_zero_or_one
#print axioms forest_trace_level_sound
#print axioms three_level_forest_trace_sound
#print axioms encodedLaneValue_lt_eight
#print axioms encoded_lane_recovers_directions
#print axioms three_level_forest_trace_extracts_private_lane
#print axioms canonical_checkpoint_path_complete
#print axioms output_lane_is_functional_and_independent_of_input
#print axioms distinct_input_output_lanes_are_permitted

end AspisPool.V7EightLaneForestRelation
