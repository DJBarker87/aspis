import AspisFormal.K1.V7Tag73Q16CompactScheduleCount
import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity

/-!
# Exact q16 schedule/frontier representation bridge

This file turns the cap-203 semantic shape count into a statement about the
actual ordered injections output by the Tag-73 q16 sampler.  Query positions
are mapped through the bit-compatible depth-18 leaf equivalence, not through
an arbitrary finite-cardinality bijection.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisK1.V7Tag73Q16SemanticFrontierBridge

open AspisV6CompactFrontierSemantics
open AspisV5WithoutReplacementQuerySoundness
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16FirstCompactUniformity

noncomputable section

/-- The exact set of deployed integer positions in an ordered q16 schedule. -/
def queryPositionFinset (schedule : Q16Schedule) :
    Finset (Fin (2 ^ 18)) :=
  Finset.univ.map schedule

/-- The same set reindexed into the recursive full-binary-tree leaf type. -/
def queryLeafFinset (schedule : Q16Schedule) : Finset (Leaf 18) :=
  (queryPositionFinset schedule).map (leafPositionEquiv 18).symm.toEmbedding

theorem queryPositionFinset_card (schedule : Q16Schedule) :
    (queryPositionFinset schedule).card = 16 := by
  simp [queryPositionFinset]

theorem queryLeafFinset_card (schedule : Q16Schedule) :
    (queryLeafFinset schedule).card = 16 := by
  rw [queryLeafFinset, Finset.card_map, queryPositionFinset_card]

theorem queryLeafFinset_nonempty (schedule : Q16Schedule) :
    (queryLeafFinset schedule).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro empty
  have := queryLeafFinset_card schedule
  rw [empty] at this
  simp at this

/-- The unique semantic binary shape whose selected leaves are exactly the
deployed schedule range. -/
def queryShape (schedule : Q16Schedule) : Shape 18 :=
  (shapeLeafEquiv 18).symm
    ⟨queryLeafFinset schedule, queryLeafFinset_nonempty schedule⟩

theorem queryShape_leaves (schedule : Q16Schedule) :
    shapeLeaves (queryShape schedule) = queryLeafFinset schedule := by
  have inverse := (shapeLeafEquiv 18).apply_symm_apply
    ⟨queryLeafFinset schedule, queryLeafFinset_nonempty schedule⟩
  exact congrArg (fun subset : NonemptyFinset (Leaf 18) => subset.1) inverse

theorem queryShape_selected (schedule : Q16Schedule) :
    selected (queryShape schedule) = 16 := by
  rw [← shapeLeaves_card, queryShape_leaves, queryLeafFinset_card]

/-- Mathematical frontier value of the exact deployed query-position set. -/
def semanticFrontierNodes (schedule : Q16Schedule) : Nat :=
  frontier (queryShape schedule)

def SemanticCap203Admitted (schedule : Q16Schedule) : Prop :=
  semanticFrontierNodes schedule ≤ 203

/-- A canonical ordering exists for every cap-203 shape; it is used only to
represent the permutation factor.  The bit-compatible position map remains
explicit and independent of this choice. -/
def canonicalCapShapeOrdering (capShape : Cap203Shape) :
    Fin 16 ≃ (shapeLeaves capShape.2.1 : Type) :=
  (finCongr capShape.2.2.1.symm).trans
    (canonicalShapeOrdering capShape.2.1)

/-- The direct representation of an ordered cap-203 leaf set. -/
abbrev ExactOrderedCap203Schedule :=
  Σ capShape : Cap203Shape,
    Fin 16 ≃ (shapeLeaves capShape.2.1 : Type)

/-- The counted `(shape, permutation)` representation and the direct
selected-leaf ordering representation are exactly equivalent. -/
def orderedCap203ExactEquiv :
    OrderedCap203Schedule ≃ ExactOrderedCap203Schedule where
  toFun representation :=
    ⟨representation.1,
      representation.2.trans
        (canonicalCapShapeOrdering representation.1)⟩
  invFun representation :=
    ⟨representation.1,
      representation.2.trans
        (canonicalCapShapeOrdering representation.1).symm⟩
  left_inv representation := by
    apply Prod.ext
    · rfl
    · apply Equiv.ext
      intro slot
      simp
  right_inv representation := by
    rcases representation with ⟨capShape, ordering⟩
    dsimp
    congr 1
    apply Equiv.ext
    intro slot
    simp

/-! ## Direct schedules and semantic shapes -/

/-- The exact leaf selected by a deployed query slot, packaged in the
reconstructed semantic shape. -/
def scheduleLeafAt (schedule : Q16Schedule) (slot : Fin 16) :
    (shapeLeaves (queryShape schedule) : Type) := by
  refine ⟨(leafPositionEquiv 18).symm (schedule slot), ?_⟩
  rw [queryShape_leaves]
  simp [queryLeafFinset, queryPositionFinset]

theorem scheduleLeafAt_injective (schedule : Q16Schedule) :
    Function.Injective (scheduleLeafAt schedule) := by
  intro left right equality
  have leafEquality := congrArg Subtype.val equality
  have positionEquality :=
    (leafPositionEquiv 18).symm.injective leafEquality
  exact schedule.injective positionEquality

/-- The deployed slot order is a bijection onto the reconstructed shape's
sixteen selected leaves. -/
def scheduleLeafOrdering (schedule : Q16Schedule) :
    Fin 16 ≃ (shapeLeaves (queryShape schedule) : Type) :=
  Equiv.ofBijective (scheduleLeafAt schedule)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      scheduleLeafAt_injective schedule,
      by
        rw [Fintype.card_fin, Fintype.card_coe,
          shapeLeaves_card, queryShape_selected]⟩)

/-- Turn a direct ordered leaf representation into the exact q16 injection
of low-18-bit integer positions. -/
def exactOrderedToQuerySchedule
    (representation : ExactOrderedCap203Schedule) : Q16Schedule where
  toFun slot :=
    leafPositionEquiv 18 (representation.2 slot).1
  inj' := by
    intro left right equality
    apply representation.2.injective
    apply Subtype.ext
    exact (leafPositionEquiv 18).injective equality

theorem exactOrderedToQuerySchedule_leafFinset
    (representation : ExactOrderedCap203Schedule) :
    queryLeafFinset (exactOrderedToQuerySchedule representation) =
      shapeLeaves representation.1.2.1 := by
  ext leaf
  constructor
  · intro membership
    simp only [queryLeafFinset, Finset.mem_map] at membership
    obtain ⟨position, positionMembership, leafEquality⟩ := membership
    simp only [queryPositionFinset, Finset.mem_map] at positionMembership
    obtain ⟨slot, _slotMembership, positionEquality⟩ := positionMembership
    have selectedLeafEquality :
        (representation.2 slot).1 = leaf := by
      calc
        (representation.2 slot).1 =
            (leafPositionEquiv 18).symm
              (leafPositionEquiv 18 (representation.2 slot).1) :=
          ((leafPositionEquiv 18).symm_apply_apply
            (representation.2 slot).1).symm
        _ = (leafPositionEquiv 18).symm position := by
          apply congrArg (leafPositionEquiv 18).symm
          simpa [exactOrderedToQuerySchedule] using positionEquality
        _ = leaf := leafEquality
    rw [← selectedLeafEquality]
    exact (representation.2 slot).2
  · intro membership
    let selectedLeaf :
        (shapeLeaves representation.1.2.1 : Type) := ⟨leaf, membership⟩
    obtain ⟨slot, slotEquality⟩ := representation.2.surjective selectedLeaf
    simp only [queryLeafFinset, Finset.mem_map]
    refine ⟨leafPositionEquiv 18 leaf, ?_, ?_⟩
    · simp only [queryPositionFinset, Finset.mem_map]
      refine ⟨slot, Finset.mem_univ slot, ?_⟩
      change leafPositionEquiv 18 (representation.2 slot).1 =
        leafPositionEquiv 18 leaf
      exact congrArg (fun value => leafPositionEquiv 18 value.1) slotEquality
    · simp

theorem exactOrderedToQuerySchedule_shape
    (representation : ExactOrderedCap203Schedule) :
    queryShape (exactOrderedToQuerySchedule representation) =
      representation.1.2.1 := by
  apply shapeLeaves_injective 18
  rw [queryShape_leaves,
    exactOrderedToQuerySchedule_leafFinset]

theorem exactOrderedToQuerySchedule_compact
    (representation : ExactOrderedCap203Schedule) :
    SemanticCap203Admitted
      (exactOrderedToQuerySchedule representation) := by
  unfold SemanticCap203Admitted semanticFrontierNodes
  rw [exactOrderedToQuerySchedule_shape]
  rw [representation.1.2.2.2]
  omega

/-- Package the reconstructed schedule shape and its actual frontier value as
a cap-203 shape. -/
def admittedCapShape
    (schedule : AdmittedResult SemanticCap203Admitted) : Cap203Shape := by
  let frontierCount := semanticFrontierNodes schedule.1
  have frontierBound : frontierCount < 204 := by
    unfold SemanticCap203Admitted at schedule
    omega
  refine ⟨⟨frontierCount, frontierBound⟩,
    ⟨queryShape schedule.1, queryShape_selected schedule.1, ?_⟩⟩
  rfl

def admittedToExactOrdered
    (schedule : AdmittedResult SemanticCap203Admitted) :
    ExactOrderedCap203Schedule :=
  ⟨admittedCapShape schedule, scheduleLeafOrdering schedule.1⟩

theorem exactOrderedToQuerySchedule_injective :
    Function.Injective exactOrderedToQuerySchedule := by
  intro left right scheduleEquality
  rcases left with ⟨leftCap, leftOrdering⟩
  rcases right with ⟨rightCap, rightOrdering⟩
  have shapeEquality : leftCap.2.1 = rightCap.2.1 := by
    rw [← exactOrderedToQuerySchedule_shape
        ⟨leftCap, leftOrdering⟩,
      ← exactOrderedToQuerySchedule_shape
        ⟨rightCap, rightOrdering⟩]
    exact congrArg queryShape scheduleEquality
  have frontierIndexEquality : leftCap.1 = rightCap.1 := by
    apply Fin.ext
    rw [← leftCap.2.2.2, ← rightCap.2.2.2, shapeEquality]
  have capEquality : leftCap = rightCap := by
    have predicateEquality : ∀ shape : Shape 18,
        (selected shape = 16 ∧ frontier shape = leftCap.1.val) ↔
          (selected shape = 16 ∧ frontier shape = rightCap.1.val) := by
      intro shape
      rw [frontierIndexEquality]
    exact Sigma.ext frontierIndexEquality
      ((Subtype.heq_iff_coe_eq predicateEquality).2 shapeEquality)
  subst rightCap
  congr 1
  apply Equiv.ext
  intro slot
  apply Subtype.ext
  apply (leafPositionEquiv 18).injective
  exact congrArg (fun schedule : Q16Schedule => schedule slot)
    scheduleEquality

theorem admittedToExactOrdered_maps_back
    (schedule : AdmittedResult SemanticCap203Admitted) :
    exactOrderedToQuerySchedule (admittedToExactOrdered schedule) =
      schedule.1 := by
  apply Function.Embedding.ext
  intro slot
  change leafPositionEquiv 18
      ((scheduleLeafOrdering schedule.1 slot).1) = schedule.1 slot
  unfold scheduleLeafOrdering
  rw [Equiv.ofBijective_apply]
  exact (leafPositionEquiv 18).apply_symm_apply (schedule.1 slot)

theorem exactOrderedToQuerySchedule_surjective_to_admitted :
    Function.Surjective
      (fun representation : ExactOrderedCap203Schedule =>
        (⟨exactOrderedToQuerySchedule representation,
          exactOrderedToQuerySchedule_compact representation⟩ :
            AdmittedResult SemanticCap203Admitted)) := by
  intro schedule
  refine ⟨admittedToExactOrdered schedule, ?_⟩
  apply Subtype.ext
  exact admittedToExactOrdered_maps_back schedule

/-- Exact equivalence between ordered cap-203 semantic shapes and the actual
ordered q16 injections admitted by the semantic frontier predicate. -/
def exactOrderedCap203AdmittedEquiv :
    ExactOrderedCap203Schedule ≃
      AdmittedResult SemanticCap203Admitted :=
  Equiv.ofBijective
    (fun representation =>
      (⟨exactOrderedToQuerySchedule representation,
        exactOrderedToQuerySchedule_compact representation⟩ :
          AdmittedResult SemanticCap203Admitted))
    ⟨fun _left _right equality =>
        exactOrderedToQuerySchedule_injective
          (congrArg Subtype.val equality),
      exactOrderedToQuerySchedule_surjective_to_admitted⟩

def orderedCap203AdmittedEquiv :
    OrderedCap203Schedule ≃ AdmittedResult SemanticCap203Admitted :=
  orderedCap203ExactEquiv.trans exactOrderedCap203AdmittedEquiv

theorem semantic_cap203_admitted_card :
    Fintype.card (AdmittedResult SemanticCap203Admitted) =
      semanticCompactFavourable * Nat.factorial 16 := by
  rw [← Fintype.card_congr orderedCap203AdmittedEquiv,
    ordered_cap203_schedule_card]

/-- Forgetting compactness injects compact-and-bad schedules into all ordered
without-replacement schedules supported by the same bad set. -/
def forgetCompactBad (bad : Finset (Fin 262144)) :
    BadAdmittedResult SemanticCap203Admitted (AllInBad bad) →
      {schedule : Q16Schedule // AllQueriesIn bad schedule} :=
  fun schedule => ⟨schedule.1.1, schedule.2⟩

theorem forgetCompactBad_injective (bad : Finset (Fin 262144)) :
    Function.Injective (forgetCompactBad bad) := by
  intro left right equality
  have scheduleEquality : left.1.1 = right.1.1 :=
    congrArg (fun output => output.1) equality
  apply Subtype.ext
  apply Subtype.ext
  exact scheduleEquality

theorem compact_bad_admitted_card_le_descFactorial
    (bad : Finset (Fin 262144)) :
    Fintype.card
        (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) ≤
      bad.card.descFactorial 16 := by
  calc
    Fintype.card
        (BadAdmittedResult SemanticCap203Admitted (AllInBad bad)) ≤
        Fintype.card
          {schedule : Q16Schedule // AllQueriesIn bad schedule} :=
      Fintype.card_le_of_injective
        (forgetCompactBad bad) (forgetCompactBad_injective bad)
    _ = Fintype.card (MissSchedule (q := 16) bad) :=
      Fintype.card_congr (allQueriesInEquiv (q := 16) bad)
    _ = bad.card.descFactorial 16 := card_miss_schedule bad

/-! ## Audit -/

#print axioms queryShape_leaves
#print axioms queryShape_selected
#print axioms orderedCap203ExactEquiv
#print axioms scheduleLeafOrdering
#print axioms exactOrderedToQuerySchedule_leafFinset
#print axioms exactOrderedToQuerySchedule_compact
#print axioms exactOrderedToQuerySchedule_injective
#print axioms admittedToExactOrdered_maps_back
#print axioms exactOrderedCap203AdmittedEquiv
#print axioms semantic_cap203_admitted_card
#print axioms compact_bad_admitted_card_le_descFactorial

end

end AspisK1.V7Tag73Q16SemanticFrontierBridge
