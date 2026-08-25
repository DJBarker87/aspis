import AspisFormal.V6CompactFrontierPrefactorization

/-!
# Binary-frontier subset semantics and exact total count

This module closes the semantic seam behind the sparse V6 frontier
certificate. `Shape depth` is the canonical nonempty-subset decomposition of
a full binary tree. Its `selected` and `frontier` statistics are proved to
obey the ordinary oriented recurrence, and `Shape depth` is proved bijective
with nonempty subsets of an explicit `2^depth` leaf type. Consequently the
full frontier distribution for `k > 0` sums to `Nat.choose (2^depth) k`.

Together with `V6CompactFrontierPrefactorization`, this establishes that the
generated normalized certificate counts actual binary-tree leaf subsets; it
does not merely replay an unrelated numeric recurrence.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierSemantics

open AspisV6CompactFrontierPrefactorization

@[reducible] def Shape : Nat → Type
  | 0 => PUnit
  | d + 1 => (Bool × Shape d) ⊕ (Shape d × Shape d)

instance shapeFintype (d : Nat) : Fintype (Shape d) := by
  induction d with
  | zero => simp [Shape]; infer_instance
  | succ d ih => simp [Shape]; infer_instance

instance shapeDecidableEq (d : Nat) : DecidableEq (Shape d) := by
  induction d with
  | zero => simp [Shape]; infer_instance
  | succ d ih => simp [Shape]; infer_instance

def selected : {d : Nat} → Shape d → Nat
  | 0, _ => 1
  | _ + 1, Sum.inl (_, child) => selected child
  | _ + 1, Sum.inr (left, right) => selected left + selected right

def frontier : {d : Nat} → Shape d → Nat
  | 0, _ => 0
  | _ + 1, Sum.inl (_, child) => frontier child + 1
  | _ + 1, Sum.inr (left, right) => frontier left + frontier right

theorem selected_pos {d : Nat} (s : Shape d) : 0 < selected s := by
  induction d with
  | zero => simp [selected]
  | succ d ih =>
      cases s with
      | inl one => exact ih one.2
      | inr both =>
          simp only [selected]
          exact Nat.add_pos_left (ih both.1) _

def Fibre (d selectedCount frontierCount : Nat) :=
  {s : Shape d // selected s = selectedCount ∧ frontier s = frontierCount}

noncomputable instance fibreFintype (d selectedCount frontierCount : Nat) :
    Fintype (Fibre d selectedCount frontierCount) := by
  letI : Finite (Fibre d selectedCount frontierCount) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable def semanticCount (d selectedCount frontierCount : Nat) : Nat :=
  Fintype.card (Fibre d selectedCount frontierCount)

def OneFibre (d selectedCount frontierCount : Nat) :=
  {p : Bool × Shape d //
    selected p.2 = selectedCount ∧ frontier p.2 + 1 = frontierCount}

def BothFibre (d selectedCount frontierCount : Nat) :=
  {p : Shape d × Shape d //
    selected p.1 + selected p.2 = selectedCount ∧
      frontier p.1 + frontier p.2 = frontierCount}

noncomputable instance oneFibreFintype (d selectedCount frontierCount : Nat) :
    Fintype (OneFibre d selectedCount frontierCount) := by
  letI : Finite (OneFibre d selectedCount frontierCount) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance bothFibreFintype (d selectedCount frontierCount : Nat) :
    Fintype (BothFibre d selectedCount frontierCount) := by
  letI : Finite (BothFibre d selectedCount frontierCount) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def splitFibreEquiv (d selectedCount frontierCount : Nat) :
    Fibre (d + 1) selectedCount frontierCount ≃
      OneFibre d selectedCount frontierCount ⊕
        BothFibre d selectedCount frontierCount where
  toFun value := by
    rcases value with ⟨shape, property⟩
    cases shape with
    | inl one =>
        exact Sum.inl ⟨one, property⟩
    | inr both =>
        exact Sum.inr ⟨both, property⟩
  invFun value := by
    cases value with
    | inl one => exact ⟨Sum.inl one.1, one.2⟩
    | inr both => exact ⟨Sum.inr both.1, both.2⟩
  left_inv value := by
    rcases value with ⟨shape, property⟩
    cases shape <;> rfl
  right_inv value := by
    cases value <;> rfl

def oneToFibre (d selectedCount frontierCount : Nat)
    (frontierPositive : 0 < frontierCount) :
    OneFibre d selectedCount frontierCount →
      Bool × Fibre d selectedCount (frontierCount - 1) := fun value =>
  ⟨value.1.1, ⟨value.1.2, value.2.1, by
    have frontierEq := value.2.2
    change frontier value.1.2 + 1 = frontierCount at frontierEq
    omega⟩⟩

def fibreToOne (d selectedCount frontierCount : Nat)
    (frontierPositive : 0 < frontierCount) :
    Bool × Fibre d selectedCount (frontierCount - 1) →
      OneFibre d selectedCount frontierCount := fun value =>
  ⟨(value.1, value.2.1), value.2.2.1, by
    have frontierEq := value.2.2.2
    change frontier value.2.1 = frontierCount - 1 at frontierEq
    change frontier value.2.1 + 1 = frontierCount
    omega⟩

def oneFibreEquiv (d selectedCount frontierCount : Nat)
    (frontierPositive : 0 < frontierCount) :
    OneFibre d selectedCount frontierCount ≃
      Bool × Fibre d selectedCount (frontierCount - 1) where
  toFun := oneToFibre d selectedCount frontierCount frontierPositive
  invFun := fibreToOne d selectedCount frontierCount frontierPositive
  left_inv value := by
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

abbrev IndexedBoth (d selectedCount frontierCount : Nat) :=
      Σ offset : Fin (selectedCount - 1),
        Σ leftFrontier : Fin (frontierCount + 1),
          Fibre d (offset + 1) leftFrontier ×
            Fibre d (selectedCount - (offset + 1))
              (frontierCount - leftFrontier)

def FlatIndexedBoth (d selectedCount frontierCount : Nat) :=
  {value : Fin (selectedCount - 1) × Fin (frontierCount + 1) ×
      Shape d × Shape d //
    selected value.2.2.1 = value.1 + 1 ∧
      frontier value.2.2.1 = value.2.1 ∧
      selected value.2.2.2 = selectedCount - (value.1 + 1) ∧
      frontier value.2.2.2 = frontierCount - value.2.1}

noncomputable instance flatIndexedBothFintype
    (d selectedCount frontierCount : Nat) :
    Fintype (FlatIndexedBoth d selectedCount frontierCount) := by
  letI : Finite (FlatIndexedBoth d selectedCount frontierCount) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def bothToFlat (d selectedCount frontierCount : Nat) :
    BothFibre d selectedCount frontierCount →
      FlatIndexedBoth d selectedCount frontierCount := fun value =>
  let offset : Fin (selectedCount - 1) :=
    ⟨selected value.1.1 - 1, by
      have selectedEq := value.2.1
      have leftPositive := selected_pos value.1.1
      have rightPositive := selected_pos value.1.2
      omega⟩
  let leftFrontier : Fin (frontierCount + 1) :=
    ⟨frontier value.1.1, by
      have frontierEq := value.2.2
      omega⟩
  ⟨(offset, leftFrontier, value.1.1, value.1.2), by
    constructor
    · dsimp [offset]
      have leftPositive := selected_pos value.1.1
      omega
    constructor
    · rfl
    constructor
    · dsimp [offset]
      have selectedEq := value.2.1
      have leftPositive := selected_pos value.1.1
      omega
    · dsimp [leftFrontier]
      have frontierEq := value.2.2
      omega⟩

def flatToBoth (d selectedCount frontierCount : Nat) :
    FlatIndexedBoth d selectedCount frontierCount →
      BothFibre d selectedCount frontierCount := fun value =>
  ⟨(value.1.2.2.1, value.1.2.2.2), by
    constructor
    · rw [value.2.1, value.2.2.2.1]
      have offsetLt := value.1.1.isLt
      omega
    · rw [value.2.2.1, value.2.2.2.2]
      have leftFrontierLt := value.1.2.1.isLt
      omega⟩

def bothFlatEquiv (d selectedCount frontierCount : Nat) :
    BothFibre d selectedCount frontierCount ≃
      FlatIndexedBoth d selectedCount frontierCount where
  toFun := bothToFlat d selectedCount frontierCount
  invFun := flatToBoth d selectedCount frontierCount
  left_inv value := by
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Subtype.ext
    simp only [bothToFlat, flatToBoth]
    apply Prod.ext
    · apply Fin.ext
      have selectedEq := value.2.1
      change selected value.1.2.2.1 = value.1.1 + 1 at selectedEq
      change selected value.1.2.2.1 - 1 = value.1.1
      omega
    · apply Prod.ext
      · apply Fin.ext
        have frontierEq := value.2.2.1
        change frontier value.1.2.2.1 = value.1.2.1 at frontierEq
        exact frontierEq
      · rfl

def flatToIndexed (d selectedCount frontierCount : Nat) :
    FlatIndexedBoth d selectedCount frontierCount →
      IndexedBoth d selectedCount frontierCount := fun value =>
  ⟨value.1.1, value.1.2.1,
    ⟨value.1.2.2.1, value.2.1, value.2.2.1⟩,
    ⟨value.1.2.2.2, value.2.2.2.1, value.2.2.2.2⟩⟩

def indexedToFlat (d selectedCount frontierCount : Nat) :
    IndexedBoth d selectedCount frontierCount →
      FlatIndexedBoth d selectedCount frontierCount := fun value =>
  ⟨(value.1, value.2.1, value.2.2.1.1, value.2.2.2.1),
    value.2.2.1.2.1, value.2.2.1.2.2,
    value.2.2.2.2.1, value.2.2.2.2.2⟩

def flatIndexedEquiv (d selectedCount frontierCount : Nat) :
    FlatIndexedBoth d selectedCount frontierCount ≃
      IndexedBoth d selectedCount frontierCount where
  toFun := flatToIndexed d selectedCount frontierCount
  invFun := indexedToFlat d selectedCount frontierCount
  left_inv value := by
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Sigma.ext rfl
    exact HEq.rfl

def bothFibreEquiv (d selectedCount frontierCount : Nat) :
    BothFibre d selectedCount frontierCount ≃
      IndexedBoth d selectedCount frontierCount :=
  (bothFlatEquiv d selectedCount frontierCount).trans
    (flatIndexedEquiv d selectedCount frontierCount)

theorem semanticCount_zero (selectedCount frontierCount : Nat) :
    semanticCount 0 selectedCount frontierCount =
      if selectedCount = 1 ∧ frontierCount = 0 then 1 else 0 := by
  classical
  by_cases selectedOne : selectedCount = 1 <;>
    by_cases frontierZero : frontierCount = 0 <;>
      simp [semanticCount, Fibre, Shape, selected, frontier,
        Fintype.card_subtype, selectedOne, frontierZero] <;> omega

theorem oneFibre_card (d selectedCount frontierCount : Nat) :
    Fintype.card (OneFibre d selectedCount frontierCount) =
      if frontierCount = 0 then 0
      else 2 * semanticCount d selectedCount (frontierCount - 1) := by
  by_cases frontierZero : frontierCount = 0
  · subst frontierCount
    simp only [if_pos]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun value => by
      have impossible := value.2.2
      omega⟩
  · rw [if_neg frontierZero]
    have frontierPositive : 0 < frontierCount := Nat.pos_of_ne_zero frontierZero
    rw [Fintype.card_congr
      (oneFibreEquiv d selectedCount frontierCount frontierPositive)]
    rw [Fintype.card_prod]
    norm_num [semanticCount]

theorem bothFibre_card (d selectedCount frontierCount : Nat) :
    Fintype.card (BothFibre d selectedCount frontierCount) =
      ∑ offset ∈ Finset.range (selectedCount - 1),
        ∑ leftFrontier ∈ Finset.range (frontierCount + 1),
          semanticCount d (offset + 1) leftFrontier *
            semanticCount d (selectedCount - (offset + 1))
              (frontierCount - leftFrontier) := by
  rw [Fintype.card_congr (bothFibreEquiv d selectedCount frontierCount)]
  unfold IndexedBoth
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_prod]
  change (∑ offset : Fin (selectedCount - 1),
      ∑ leftFrontier : Fin (frontierCount + 1),
        semanticCount d (offset + 1) leftFrontier *
          semanticCount d (selectedCount - (offset + 1))
            (frontierCount - leftFrontier)) = _
  calc
    _ = ∑ offset ∈ Finset.range (selectedCount - 1),
        ∑ leftFrontier : Fin (frontierCount + 1),
          semanticCount d (offset + 1) leftFrontier *
            semanticCount d (selectedCount - (offset + 1))
              (frontierCount - leftFrontier) := by
      exact Fin.sum_univ_eq_sum_range
        (fun offset : Nat =>
          ∑ leftFrontier : Fin (frontierCount + 1),
            semanticCount d (offset + 1) leftFrontier *
              semanticCount d (selectedCount - (offset + 1))
                (frontierCount - leftFrontier))
        (selectedCount - 1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro offset offsetMembership
      exact Fin.sum_univ_eq_sum_range
        (fun leftFrontier : Nat =>
          semanticCount d (offset + 1) leftFrontier *
            semanticCount d (selectedCount - (offset + 1))
              (frontierCount - leftFrontier))
        (frontierCount + 1)

theorem semanticCount_succ (d selectedCount frontierCount : Nat) :
    semanticCount (d + 1) selectedCount frontierCount =
      (if frontierCount = 0 then 0
       else 2 * semanticCount d selectedCount (frontierCount - 1)) +
      ∑ offset ∈ Finset.range (selectedCount - 1),
        ∑ leftFrontier ∈ Finset.range (frontierCount + 1),
          semanticCount d (offset + 1) leftFrontier *
            semanticCount d (selectedCount - (offset + 1))
              (frontierCount - leftFrontier) := by
  rw [semanticCount,
    Fintype.card_congr (splitFibreEquiv d selectedCount frontierCount),
    Fintype.card_sum, oneFibre_card, bothFibre_card]

theorem rawFrontierCount_eq_semanticCount
    (depth selectedCount frontierCount : Nat) :
    rawFrontierCount depth selectedCount frontierCount =
      semanticCount depth selectedCount frontierCount := by
  induction depth generalizing selectedCount frontierCount with
  | zero =>
      rw [rawFrontierCount, semanticCount_zero]
  | succ depth inductionHypothesis =>
      rw [rawFrontierCount, semanticCount_succ]
      simp_rw [inductionHypothesis]

def NonemptyFinset (α : Type*) :=
  {subset : Finset α // subset.Nonempty}

@[reducible] def Leaf : Nat → Type
  | 0 => PUnit
  | depth + 1 => Leaf depth ⊕ Leaf depth

instance leafFintype (depth : Nat) : Fintype (Leaf depth) := by
  induction depth with
  | zero => simp [Leaf]; infer_instance
  | succ depth inductionHypothesis => simp [Leaf]; infer_instance

instance leafDecidableEq (depth : Nat) : DecidableEq (Leaf depth) := by
  induction depth with
  | zero => simp [Leaf]; infer_instance
  | succ depth inductionHypothesis => simp [Leaf]; infer_instance

def shapeLeaves : {depth : Nat} → Shape depth → Finset (Leaf depth)
  | 0, _ => {show Leaf 0 from PUnit.unit}
  | _ + 1, Sum.inl (false, child) => shapeLeaves child |>.disjSum ∅
  | _ + 1, Sum.inl (true, child) => (∅ : Finset _) |>.disjSum (shapeLeaves child)
  | _ + 1, Sum.inr (left, right) =>
      (shapeLeaves left).disjSum (shapeLeaves right)

theorem shapeLeaves_nonempty {depth : Nat} (shape : Shape depth) :
    (shapeLeaves shape).Nonempty := by
  induction depth with
  | zero =>
      cases shape
      exact ⟨show Leaf 0 from PUnit.unit, by simp [shapeLeaves]⟩
  | succ depth inductionHypothesis =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          rcases inductionHypothesis child with ⟨leaf, leafMem⟩
          cases orientation
          · exact ⟨Sum.inl leaf,
              Finset.inl_mem_disjSum.mpr leafMem⟩
          · exact ⟨Sum.inr leaf,
              Finset.inr_mem_disjSum.mpr leafMem⟩
      | inr both =>
          rcases both with ⟨left, right⟩
          rcases inductionHypothesis left with ⟨leaf, leafMem⟩
          exact ⟨Sum.inl leaf,
            Finset.inl_mem_disjSum.mpr leafMem⟩

theorem shapeLeaves_card {depth : Nat} (shape : Shape depth) :
    (shapeLeaves shape).card = selected shape := by
  induction depth with
  | zero =>
      cases shape
      norm_num [shapeLeaves, selected]
  | succ depth inductionHypothesis =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          cases orientation
          · change ((shapeLeaves child).disjSum ∅).card = selected child
            rw [Finset.card_disjSum, inductionHypothesis]
            simp
          · change ((∅ : Finset (Leaf depth)).disjSum
                (shapeLeaves child)).card = selected child
            rw [Finset.card_disjSum, inductionHypothesis]
            simp
      | inr both =>
          rcases both with ⟨left, right⟩
          change ((shapeLeaves left).disjSum (shapeLeaves right)).card =
            selected left + selected right
          rw [Finset.card_disjSum, inductionHypothesis,
            inductionHypothesis]

theorem shapeLeaves_injective (depth : Nat) :
    Function.Injective (@shapeLeaves depth) := by
  induction depth with
  | zero =>
      intro left right equality
      cases left
      cases right
      rfl
  | succ depth inductionHypothesis =>
      intro leftShape rightShape equality
      cases leftShape with
      | inl leftOne =>
          rcases leftOne with ⟨leftOrientation, leftChild⟩
          cases leftOrientation
          · cases rightShape with
            | inl rightOne =>
                rcases rightOne with ⟨rightOrientation, rightChild⟩
                cases rightOrientation
                · have childEquality :
                      shapeLeaves leftChild = shapeLeaves rightChild := by
                    have splitEquality :
                        (shapeLeaves leftChild).disjSum ∅ =
                          (shapeLeaves rightChild).disjSum ∅ := equality
                    exact congrArg Finset.toLeft splitEquality |>
                      (by simpa only [Finset.toLeft_disjSum] using ·)
                  cases inductionHypothesis childEquality
                  rfl
                · have impossible : shapeLeaves leftChild = ∅ := by
                    have splitEquality :
                        (shapeLeaves leftChild).disjSum ∅ =
                          (∅ : Finset (Leaf depth)).disjSum
                            (shapeLeaves rightChild) := equality
                    exact congrArg Finset.toLeft splitEquality |>
                      (by simpa only [Finset.toLeft_disjSum] using ·)
                  exact False.elim
                    ((Finset.nonempty_iff_ne_empty.mp
                      (shapeLeaves_nonempty leftChild)) impossible)
            | inr rightBoth =>
                rcases rightBoth with ⟨rightLeft, rightRight⟩
                have impossible : ∅ = shapeLeaves rightRight := by
                  have splitEquality :
                      (shapeLeaves leftChild).disjSum ∅ =
                        (shapeLeaves rightLeft).disjSum
                          (shapeLeaves rightRight) := equality
                  exact congrArg Finset.toRight splitEquality |>
                    (by simpa only [Finset.toRight_disjSum] using ·)
                exact False.elim
                  ((Finset.nonempty_iff_ne_empty.mp
                    (shapeLeaves_nonempty rightRight)) impossible.symm)
          · cases rightShape with
            | inl rightOne =>
                rcases rightOne with ⟨rightOrientation, rightChild⟩
                cases rightOrientation
                · have impossible : ∅ = shapeLeaves rightChild := by
                    have splitEquality :
                        (∅ : Finset (Leaf depth)).disjSum
                            (shapeLeaves leftChild) =
                          (shapeLeaves rightChild).disjSum ∅ := equality
                    exact congrArg Finset.toLeft splitEquality |>
                      (by simpa only [Finset.toLeft_disjSum] using ·)
                  exact False.elim
                    ((Finset.nonempty_iff_ne_empty.mp
                      (shapeLeaves_nonempty rightChild)) impossible.symm)
                · have childEquality :
                      shapeLeaves leftChild = shapeLeaves rightChild := by
                    have splitEquality :
                        (∅ : Finset (Leaf depth)).disjSum
                            (shapeLeaves leftChild) =
                          (∅ : Finset (Leaf depth)).disjSum
                            (shapeLeaves rightChild) := equality
                    exact congrArg Finset.toRight splitEquality |>
                      (by simpa only [Finset.toRight_disjSum] using ·)
                  cases inductionHypothesis childEquality
                  rfl
            | inr rightBoth =>
                rcases rightBoth with ⟨rightLeft, rightRight⟩
                have impossible : ∅ = shapeLeaves rightLeft := by
                  have splitEquality :
                      (∅ : Finset (Leaf depth)).disjSum
                          (shapeLeaves leftChild) =
                        (shapeLeaves rightLeft).disjSum
                          (shapeLeaves rightRight) := equality
                  exact congrArg Finset.toLeft splitEquality |>
                    (by simpa only [Finset.toLeft_disjSum] using ·)
                exact False.elim
                  ((Finset.nonempty_iff_ne_empty.mp
                    (shapeLeaves_nonempty rightLeft)) impossible.symm)
      | inr leftBoth =>
          rcases leftBoth with ⟨leftLeft, leftRight⟩
          cases rightShape with
          | inl rightOne =>
              rcases rightOne with ⟨rightOrientation, rightChild⟩
              cases rightOrientation
              · have impossible : shapeLeaves leftRight = ∅ := by
                  have splitEquality :
                      (shapeLeaves leftLeft).disjSum
                          (shapeLeaves leftRight) =
                        (shapeLeaves rightChild).disjSum ∅ := equality
                  exact congrArg Finset.toRight splitEquality |>
                    (by simpa only [Finset.toRight_disjSum] using ·)
                exact False.elim
                  ((Finset.nonempty_iff_ne_empty.mp
                    (shapeLeaves_nonempty leftRight)) impossible)
              · have impossible : shapeLeaves leftLeft = ∅ := by
                  have splitEquality :
                      (shapeLeaves leftLeft).disjSum
                          (shapeLeaves leftRight) =
                        (∅ : Finset (Leaf depth)).disjSum
                          (shapeLeaves rightChild) := equality
                  exact congrArg Finset.toLeft splitEquality |>
                    (by simpa only [Finset.toLeft_disjSum] using ·)
                exact False.elim
                  ((Finset.nonempty_iff_ne_empty.mp
                    (shapeLeaves_nonempty leftLeft)) impossible)
          | inr rightBoth =>
              rcases rightBoth with ⟨rightLeft, rightRight⟩
              have leftEquality :
                  shapeLeaves leftLeft = shapeLeaves rightLeft := by
                have splitEquality :
                    (shapeLeaves leftLeft).disjSum
                        (shapeLeaves leftRight) =
                      (shapeLeaves rightLeft).disjSum
                        (shapeLeaves rightRight) := equality
                exact congrArg Finset.toLeft splitEquality |>
                  (by simpa only [Finset.toLeft_disjSum] using ·)
              have rightEquality :
                  shapeLeaves leftRight = shapeLeaves rightRight := by
                have splitEquality :
                    (shapeLeaves leftLeft).disjSum
                        (shapeLeaves leftRight) =
                      (shapeLeaves rightLeft).disjSum
                        (shapeLeaves rightRight) := equality
                exact congrArg Finset.toRight splitEquality |>
                  (by simpa only [Finset.toRight_disjSum] using ·)
              cases inductionHypothesis leftEquality
              cases inductionHypothesis rightEquality
              rfl

theorem shapeLeaves_surjective (depth : Nat)
    (subset : Finset (Leaf depth)) (nonempty : subset.Nonempty) :
    ∃ shape : Shape depth, shapeLeaves shape = subset := by
  induction depth with
  | zero =>
      refine ⟨PUnit.unit, ?_⟩
      apply Finset.ext
      intro leaf
      cases leaf
      simp only [shapeLeaves, Finset.mem_singleton]
      rcases nonempty with ⟨onlyLeaf, onlyLeafMem⟩
      cases onlyLeaf
      exact (iff_true_intro onlyLeafMem).symm
  | succ depth inductionHypothesis =>
      by_cases leftNonempty : subset.toLeft.Nonempty
      · obtain ⟨leftShape, leftEquality⟩ :=
          inductionHypothesis subset.toLeft leftNonempty
        by_cases rightNonempty : subset.toRight.Nonempty
        · obtain ⟨rightShape, rightEquality⟩ :=
            inductionHypothesis subset.toRight rightNonempty
          refine ⟨Sum.inr (leftShape, rightShape), ?_⟩
          change (shapeLeaves leftShape).disjSum
            (shapeLeaves rightShape) = subset
          rw [leftEquality, rightEquality,
            Finset.toLeft_disjSum_toRight]
        · have rightEmpty : subset.toRight = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp rightNonempty
          refine ⟨Sum.inl (false, leftShape), ?_⟩
          change (shapeLeaves leftShape).disjSum ∅ = subset
          rw [leftEquality, ← rightEmpty,
            Finset.toLeft_disjSum_toRight]
      · have rightNonempty : subset.toRight.Nonempty := by
          rcases nonempty with ⟨leaf, leafMem⟩
          cases leaf with
          | inl left =>
              exact False.elim (leftNonempty ⟨left, by simpa using leafMem⟩)
          | inr right => exact ⟨right, by simpa using leafMem⟩
        obtain ⟨rightShape, rightEquality⟩ :=
          inductionHypothesis subset.toRight rightNonempty
        have leftEmpty : subset.toLeft = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp leftNonempty
        refine ⟨Sum.inl (true, rightShape), ?_⟩
        change (∅ : Finset (Leaf depth)).disjSum
          (shapeLeaves rightShape) = subset
        rw [rightEquality, ← leftEmpty,
          Finset.toLeft_disjSum_toRight]

def shapeToNonempty {depth : Nat} (shape : Shape depth) :
    NonemptyFinset (Leaf depth) :=
  ⟨shapeLeaves shape, shapeLeaves_nonempty shape⟩

noncomputable def shapeLeafEquiv (depth : Nat) :
    Shape depth ≃ NonemptyFinset (Leaf depth) :=
  Equiv.ofBijective shapeToNonempty (by
    constructor
    · intro left right equality
      apply shapeLeaves_injective depth
      exact congrArg Subtype.val equality
    · intro subset
      obtain ⟨shape, equality⟩ :=
        shapeLeaves_surjective depth subset.1 subset.2
      refine ⟨shape, ?_⟩
      apply Subtype.ext
      exact equality)

theorem leaf_card (depth : Nat) : Fintype.card (Leaf depth) = 2 ^ depth := by
  induction depth with
  | zero => simp [Leaf]
  | succ depth inductionHypothesis =>
      change Fintype.card (Leaf depth ⊕ Leaf depth) = 2 ^ (depth + 1)
      rw [Fintype.card_sum, inductionHypothesis, pow_succ]
      omega

def SelectedFibre (depth selectedCount : Nat) :=
  {shape : Shape depth // selected shape = selectedCount}

noncomputable instance selectedFibreFintype
    (depth selectedCount : Nat) :
    Fintype (SelectedFibre depth selectedCount) := by
  letI : Finite (SelectedFibre depth selectedCount) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def NonemptyCardFibre (α : Type*) (cardinality : Nat) :=
  {subset : NonemptyFinset α // subset.1.card = cardinality}

def CardFibre (α : Type*) (cardinality : Nat) :=
  {subset : Finset α // subset.card = cardinality}

noncomputable instance nonemptyCardFibreFintype
    (α : Type*) [Fintype α] (cardinality : Nat) :
    Fintype (NonemptyCardFibre α cardinality) := by
  letI : Finite (NonemptyCardFibre α cardinality) :=
    Finite.of_injective (fun value => value.1.1) (by
      intro left right equality
      apply Subtype.ext
      apply Subtype.ext
      exact equality)
  exact Fintype.ofFinite _

noncomputable instance cardFibreFintype
    (α : Type*) [Fintype α] (cardinality : Nat) :
    Fintype (CardFibre α cardinality) := by
  letI : Finite (CardFibre α cardinality) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable def selectedShapeNonemptyCardEquiv
    (depth selectedCount : Nat) :
    SelectedFibre depth selectedCount ≃
      NonemptyCardFibre (Leaf depth) selectedCount :=
  Equiv.subtypeEquiv (shapeLeafEquiv depth) (by
    intro shape
    change selected shape = selectedCount ↔
      (shapeLeaves shape).card = selectedCount
    rw [shapeLeaves_card])

noncomputable def nonemptyCardFibreEquiv
    {α : Type*} (cardinality : Nat) (positive : 0 < cardinality) :
    NonemptyCardFibre α cardinality ≃ CardFibre α cardinality where
  toFun value := ⟨value.1.1, value.2⟩
  invFun value :=
    ⟨⟨value.1, Finset.card_pos.mp (by rw [value.2]; exact positive)⟩,
      value.2⟩
  left_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Subtype.ext
    rfl

noncomputable def cardFibrePowersetEquiv
    (α : Type*) [Fintype α] (cardinality : Nat) :
    CardFibre α cardinality ≃
      {subset : Finset α //
        subset ∈ Finset.powersetCard cardinality Finset.univ} :=
  Equiv.subtypeEquivRight (by
    intro subset
    simp)

theorem selectedFibre_card_eq_choose
    (depth selectedCount : Nat) (positive : 0 < selectedCount) :
    Fintype.card (SelectedFibre depth selectedCount) =
      Nat.choose (2 ^ depth) selectedCount := by
  rw [Fintype.card_congr
    (selectedShapeNonemptyCardEquiv depth selectedCount)]
  rw [Fintype.card_congr
    (nonemptyCardFibreEquiv selectedCount positive)]
  rw [Fintype.card_congr
    (cardFibrePowersetEquiv (Leaf depth) selectedCount)]
  simpa [leaf_card] using
    (Finset.card_powersetCard selectedCount
      (Finset.univ : Finset (Leaf depth)))

theorem frontier_le_selected_mul_depth
    {depth : Nat} (shape : Shape depth) :
    frontier shape ≤ selected shape * depth := by
  induction depth with
  | zero =>
      cases shape
      simp [frontier, selected]
  | succ depth inductionHypothesis =>
      cases shape with
      | inl one =>
          rcases one with ⟨orientation, child⟩
          have childBound := inductionHypothesis child
          have selectedPositive := selected_pos child
          simp only [frontier, selected, Nat.mul_succ]
          omega
      | inr both =>
          rcases both with ⟨left, right⟩
          have leftBound := inductionHypothesis left
          have rightBound := inductionHypothesis right
          simp only [frontier, selected, Nat.mul_succ, Nat.add_mul]
          omega

def selectedShapeFinset (depth selectedCount : Nat) : Finset (Shape depth) :=
  Finset.univ.filter fun shape => selected shape = selectedCount

def jointShapeFinset (depth selectedCount frontierCount : Nat) :
    Finset (Shape depth) :=
  Finset.univ.filter fun shape =>
    selected shape = selectedCount ∧ frontier shape = frontierCount

theorem semanticCount_eq_jointShapeFinset_card
    (depth selectedCount frontierCount : Nat) :
    semanticCount depth selectedCount frontierCount =
      (jointShapeFinset depth selectedCount frontierCount).card := by
  classical
  unfold semanticCount Fibre jointShapeFinset
  rw [Fintype.card_subtype]

theorem selectedFibre_card_eq_selectedShapeFinset_card
    (depth selectedCount : Nat) :
    Fintype.card (SelectedFibre depth selectedCount) =
      (selectedShapeFinset depth selectedCount).card := by
  classical
  unfold SelectedFibre selectedShapeFinset
  rw [Fintype.card_subtype]

theorem selectedShapeFinset_partition
    (depth selectedCount : Nat) :
    (selectedShapeFinset depth selectedCount).card =
      ∑ frontierCount ∈ Finset.range (selectedCount * depth + 1),
        semanticCount depth selectedCount frontierCount := by
  classical
  have mapsTo :
      ((selectedShapeFinset depth selectedCount : Finset (Shape depth)) :
          Set (Shape depth)).MapsTo frontier
        (Finset.range (selectedCount * depth + 1) : Finset Nat) := by
    intro shape membership
    have selectedEq := (Finset.mem_filter.mp membership).2
    have bound := frontier_le_selected_mul_depth shape
    rw [selectedEq] at bound
    apply Finset.mem_range.mpr
    omega
  rw [Finset.card_eq_sum_card_fiberwise mapsTo]
  apply Finset.sum_congr rfl
  intro frontierCount frontierMembership
  rw [semanticCount_eq_jointShapeFinset_card]
  apply congrArg Finset.card
  ext shape
  simp [selectedShapeFinset, jointShapeFinset]

theorem rawFrontierCount_sum_eq_choose
    (depth selectedCount : Nat) (positive : 0 < selectedCount) :
    (∑ frontierCount ∈ Finset.range (selectedCount * depth + 1),
        rawFrontierCount depth selectedCount frontierCount) =
      Nat.choose (2 ^ depth) selectedCount := by
  calc
    _ = ∑ frontierCount ∈ Finset.range (selectedCount * depth + 1),
          semanticCount depth selectedCount frontierCount := by
        apply Finset.sum_congr rfl
        intro frontierCount frontierMembership
        exact rawFrontierCount_eq_semanticCount
          depth selectedCount frontierCount
    _ = (selectedShapeFinset depth selectedCount).card :=
      (selectedShapeFinset_partition depth selectedCount).symm
    _ = Fintype.card (SelectedFibre depth selectedCount) :=
      (selectedFibre_card_eq_selectedShapeFinset_card
        depth selectedCount).symm
    _ = Nat.choose (2 ^ depth) selectedCount :=
      selectedFibre_card_eq_choose depth selectedCount positive

theorem concreteFrontierCount_sum_eq_choose
    (depth selectedCount : Nat) (positive : 0 < selectedCount) :
    (∑ frontierCount ∈ Finset.range (selectedCount * depth + 1),
        AspisV6CompactFrontierRecurrence.concreteFrontierCount
          depth selectedCount frontierCount) =
      Nat.choose (2 ^ depth) selectedCount := by
  calc
    _ = ∑ frontierCount ∈ Finset.range (selectedCount * depth + 1),
          rawFrontierCount depth selectedCount frontierCount := by
        apply Finset.sum_congr rfl
        intro frontierCount frontierMembership
        exact (rawFrontierCount_eq_concreteFrontierCount
          depth selectedCount frontierCount).symm
    _ = _ := rawFrontierCount_sum_eq_choose
      depth selectedCount positive

#print axioms rawFrontierCount_eq_semanticCount
#print axioms shapeLeafEquiv
#print axioms selectedFibre_card_eq_choose
#print axioms frontier_le_selected_mul_depth
#print axioms rawFrontierCount_sum_eq_choose
#print axioms concreteFrontierCount_sum_eq_choose

end AspisV6CompactFrontierSemantics
