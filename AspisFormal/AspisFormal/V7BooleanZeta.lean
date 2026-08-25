import Mathlib

/-!
# Boolean subset-zeta transform

`BoolTable F n` is a full Boolean table whose root coordinate is the low bit,
matching the Rust index convention.  `zeta` maps monomial coefficients to the
committed Boolean evaluation table.  `mobius` is its exact inverse, and the
multilinear extension of `zeta a` is the monomial polynomial with coefficients
`a`.
-/

namespace AspisV7BooleanZeta

universe u v

inductive BoolTable (F : Type u) : Nat → Type u where
  | leaf (value : F) : BoolTable F 0
  | node {n : Nat} (low high : BoolTable F n) : BoolTable F (n + 1)

def addTable [Add F] : {n : Nat} → BoolTable F n → BoolTable F n → BoolTable F n
  | 0, .leaf x, .leaf y => .leaf (x + y)
  | _ + 1, .node xl xh, .node yl yh =>
      .node (addTable xl yl) (addTable xh yh)

def subTable [Sub F] : {n : Nat} → BoolTable F n → BoolTable F n → BoolTable F n
  | 0, .leaf x, .leaf y => .leaf (x - y)
  | _ + 1, .node xl xh, .node yl yh =>
      .node (subTable xl yl) (subTable xh yh)

def smulTable [SMul R F] (r : R) : {n : Nat} → BoolTable F n → BoolTable F n
  | 0, .leaf x => .leaf (r • x)
  | _ + 1, .node low high => .node (smulTable r low) (smulTable r high)

def mapTable (f : F → K) : {n : Nat} → BoolTable F n → BoolTable K n
  | 0, .leaf x => .leaf (f x)
  | _ + 1, .node low high => .node (mapTable f low) (mapTable f high)

/-- Recursive form of the standard in-place low-bit-first subset-zeta loop. -/
def zeta [Add F] : {n : Nat} → BoolTable F n → BoolTable F n
  | 0, .leaf x => .leaf x
  | _ + 1, .node low high =>
      let zlow := zeta low
      let zhigh := zeta high
      .node zlow (addTable zlow zhigh)

/-- Möbius inversion, using subtraction in the same low-bit-first order. -/
def mobius [Sub F] : {n : Nat} → BoolTable F n → BoolTable F n
  | 0, .leaf x => .leaf x
  | _ + 1, .node low high =>
      .node (mobius low) (mobius (subTable high low))

theorem subTable_addTable_left [AddCommGroup F] :
    ∀ {n : Nat} (x y : BoolTable F n), subTable (addTable x y) x = y
  | 0, .leaf x, .leaf y => by simp [addTable, subTable]
  | _ + 1, .node xl xh, .node yl yh => by
      simp [addTable, subTable, subTable_addTable_left]

theorem addTable_subTable_left [AddCommGroup F] :
    ∀ {n : Nat} (x y : BoolTable F n), addTable x (subTable y x) = y
  | 0, .leaf x, .leaf y => by simp [addTable, subTable]
  | _ + 1, .node xl xh, .node yl yh => by
      simp [addTable, subTable, addTable_subTable_left]

theorem addTable_exchange [AddCommSemigroup F] :
    ∀ {n : Nat} (a b c d : BoolTable F n),
      addTable (addTable a b) (addTable c d) =
        addTable (addTable a c) (addTable b d)
  | 0, .leaf a, .leaf b, .leaf c, .leaf d => by
      simpa only [addTable, BoolTable.leaf.injEq] using add_add_add_comm a b c d
  | _ + 1, .node al ah, .node bl bh, .node cl ch, .node dl dh => by
      simp [addTable, addTable_exchange]

theorem smulTable_addTable [Semiring R] [AddCommMonoid F] [Module R F] :
    ∀ {n : Nat} (r : R) (x y : BoolTable F n),
      smulTable r (addTable x y) = addTable (smulTable r x) (smulTable r y)
  | 0, r, .leaf x, .leaf y => by simp [addTable, smulTable, smul_add]
  | _ + 1, r, .node xl xh, .node yl yh => by
      simp [addTable, smulTable, smulTable_addTable r]

theorem mobius_zeta [AddCommGroup F] :
    ∀ {n : Nat} (table : BoolTable F n), mobius (zeta table) = table
  | 0, .leaf x => rfl
  | _ + 1, .node low high => by
      simp [zeta, mobius, subTable_addTable_left, mobius_zeta]

theorem zeta_mobius [AddCommGroup F] :
    ∀ {n : Nat} (table : BoolTable F n), zeta (mobius table) = table
  | 0, .leaf x => rfl
  | _ + 1, .node low high => by
      simp [zeta, mobius, zeta_mobius, addTable_subTable_left]

def tailPoint (point : Fin (n + 1) → K) : Fin n → K := fun index => point index.succ

/-- Multilinear extension in Bernstein form, folding the low coordinate first. -/
def mle [Ring K] : {n : Nat} → BoolTable K n → (Fin n → K) → K
  | 0, .leaf x, _ => x
  | _ + 1, .node low high, point =>
      (1 - point 0) * mle low (tailPoint point) + point 0 * mle high (tailPoint point)

/-- Monomial-basis evaluation of the pre-zeta coefficient table. -/
def monomialEval [Ring K] : {n : Nat} → BoolTable K n → (Fin n → K) → K
  | 0, .leaf x, _ => x
  | _ + 1, .node low high, point =>
      monomialEval low (tailPoint point) + point 0 * monomialEval high (tailPoint point)

theorem mle_addTable [CommRing K] :
    ∀ {n : Nat} (x y : BoolTable K n) (point : Fin n → K),
      mle (addTable x y) point = mle x point + mle y point
  | 0, .leaf x, .leaf y, _ => by simp [addTable, mle]
  | _ + 1, .node xl xh, .node yl yh, point => by
      simp only [addTable, mle]
      rw [mle_addTable xl yl, mle_addTable xh yh]
      ring

/-- Core V7 transform identity: MLE of the zeta table equals the monomial
polynomial encoded by the original lane coefficients. -/
theorem mle_zeta_eq_monomial [CommRing K] :
    ∀ {n : Nat} (coefficients : BoolTable K n) (point : Fin n → K),
      mle (zeta coefficients) point = monomialEval coefficients point
  | 0, .leaf x, _ => rfl
  | _ + 1, .node low high, point => by
      simp only [zeta, mle, monomialEval]
      rw [mle_zeta_eq_monomial low, mle_addTable, mle_zeta_eq_monomial low,
        mle_zeta_eq_monomial high]
      ring

theorem zeta_add [AddCommMonoid F] :
    ∀ {n : Nat} (x y : BoolTable F n),
      zeta (addTable x y) = addTable (zeta x) (zeta y)
  | 0, .leaf x, .leaf y => rfl
  | _ + 1, .node xl xh, .node yl yh => by
      simp only [addTable, zeta, zeta_add xl yl, zeta_add xh yh]
      apply congrArg (BoolTable.node (addTable (zeta xl) (zeta yl)))
      exact addTable_exchange _ _ _ _

theorem zeta_smul [Semiring R] [AddCommMonoid F] [Module R F] :
    ∀ {n : Nat} (r : R) (x : BoolTable F n),
      zeta (smulTable r x) = smulTable r (zeta x)
  | 0, _, .leaf _ => rfl
  | _ + 1, r, .node low high => by
      simp only [smulTable, zeta, zeta_smul r low, zeta_smul r high]
      apply congrArg (BoolTable.node (smulTable r (zeta low)))
      exact (smulTable_addTable r _ _).symm

/-- Any coefficient property, including mandatory zero padding, survives
zeta followed by inverse extraction exactly. -/
theorem inverse_extraction_preserves_coefficients [AddCommGroup F]
    {n : Nat} (coefficients : BoolTable F n) :
    mobius (zeta coefficients) = coefficients :=
  mobius_zeta coefficients

end AspisV7BooleanZeta
