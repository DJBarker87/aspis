import AspisFormal.V5ComponentCExactTowerDeployment

/-!
# v5 Component C: exact Rust QM31 formula seam

This leaf narrows the executable field seam without pretending that Lean reads
Rust.  It mirrors the dependency graph in `aspis-core/src/field.rs`:

* canonical M31 `zero/one/add/sub/mul/neg` primitives plus a totalized
  nonzero-inverse adapter for Rust's panicking `M31::inv`;
* CM31 coordinate formulas, including Karatsuba multiplication, the
  two-product square, and multiplication by `2+i`;
* QM31 coordinate formulas, including Karatsuba multiplication, the optimized
  seven-product square, and quadratic-extension inversion.

Every equality with an executable function remains a named hypothesis.  The
theorems below only prove that those local equalities compose algebraically to
the exact tower and deployment bundles already used by Component C.  The
strengthened conclusion retains subtraction and optimized-square fidelity even
though the older deployment ledger did not mention those two operations.
-/

namespace AspisV5ComponentCQM31RustFormulaSeam

open AspisV5ComponentCExactTowerDeployment
open AspisV5ComponentCDeploymentLedger
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open Matrix

/-! ## Canonical base-field source primitives -/

/-- The seven base-field operations used by the deployed tower.  `sub` is a
first-class field: omitting it would leave every Karatsuba reconstruction
unbound.  `tryInv` is a semantic adapter: it agrees with Rust's panicking
`M31::inv` on nonzero inputs and returns `none` at zero. -/
structure M31SourceOps where
  zero : M31Value
  one : M31Value
  add : M31Value → M31Value → M31Value
  sub : M31Value → M31Value → M31Value
  mul : M31Value → M31Value → M31Value
  neg : M31Value → M31Value
  tryInv : M31Value → Option M31Value

/-- Explicit mathematical source functions on canonical M31 residues. -/
def exactM31SourceOps : M31SourceOps where
  zero := m31ResidueEquiv.symm 0
  one := m31ResidueEquiv.symm 1
  add a b := m31ResidueEquiv.symm (m31ResidueEquiv a + m31ResidueEquiv b)
  sub a b := m31ResidueEquiv.symm (m31ResidueEquiv a - m31ResidueEquiv b)
  mul a b := m31ResidueEquiv.symm (m31ResidueEquiv a * m31ResidueEquiv b)
  neg a := m31ResidueEquiv.symm (-m31ResidueEquiv a)
  tryInv a :=
    if m31ResidueEquiv a = 0 then none
    else some (m31ResidueEquiv.symm ((m31ResidueEquiv a)⁻¹))

/-- Exact code/model boundary for the canonical M31 primitives and the
totalized inverse adapter.  A Rust extraction or semantics audit must prove the
six direct function equalities and that the adapter agrees with `M31::inv` on
its nonzero domain. -/
def RustCanonicalM31PrimitivesMatch (rust : M31SourceOps) : Prop :=
  rust.zero = exactM31SourceOps.zero ∧
  rust.one = exactM31SourceOps.one ∧
  rust.add = exactM31SourceOps.add ∧
  rust.sub = exactM31SourceOps.sub ∧
  rust.mul = exactM31SourceOps.mul ∧
  rust.neg = exactM31SourceOps.neg ∧
  rust.tryInv = exactM31SourceOps.tryInv

theorem canonicalM31Primitives_nonvacuous :
    RustCanonicalM31PrimitivesMatch exactM31SourceOps := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem residue_exactM31_zero :
    m31ResidueEquiv exactM31SourceOps.zero = 0 := by
  simp [exactM31SourceOps]

@[simp] theorem residue_exactM31_one :
    m31ResidueEquiv exactM31SourceOps.one = 1 := by
  simp [exactM31SourceOps]

@[simp] theorem residue_exactM31_add (a b : M31Value) :
    m31ResidueEquiv (exactM31SourceOps.add a b) =
      m31ResidueEquiv a + m31ResidueEquiv b := by
  simp [exactM31SourceOps]

@[simp] theorem residue_exactM31_sub (a b : M31Value) :
    m31ResidueEquiv (exactM31SourceOps.sub a b) =
      m31ResidueEquiv a - m31ResidueEquiv b := by
  simp [exactM31SourceOps]

@[simp] theorem residue_exactM31_mul (a b : M31Value) :
    m31ResidueEquiv (exactM31SourceOps.mul a b) =
      m31ResidueEquiv a * m31ResidueEquiv b := by
  simp [exactM31SourceOps]

@[simp] theorem residue_exactM31_neg (a : M31Value) :
    m31ResidueEquiv (exactM31SourceOps.neg a) = -m31ResidueEquiv a := by
  simp [exactM31SourceOps]

theorem exactM31_tryInv_map (a : M31Value) :
    (exactM31SourceOps.tryInv a).map m31ResidueEquiv =
      if m31ResidueEquiv a = 0 then none else some (m31ResidueEquiv a)⁻¹ := by
  by_cases h : m31ResidueEquiv a = 0
  · simp only [exactM31SourceOps, h, if_pos, Option.map_none]
  · simp only [exactM31SourceOps, h, if_false, Option.map_some]
    congr 1

/-! ## CM31 source formulas -/

abbrev CM31Limbs := Fin 2 → M31Value

def cm31LimbsToExact (x : CM31Limbs) : CM31Exact :=
  ⟨m31ResidueEquiv (x 0), m31ResidueEquiv (x 1)⟩

def cm31ExactToLimbs (x : CM31Exact) : CM31Limbs :=
  ![m31ResidueEquiv.symm x.re, m31ResidueEquiv.symm x.im]

@[simp] theorem cm31ExactToLimbs_toExact (x : CM31Limbs) :
    cm31ExactToLimbs (cm31LimbsToExact x) = x := by
  funext i
  fin_cases i <;> simp [cm31ExactToLimbs, cm31LimbsToExact]

@[simp] theorem cm31LimbsToExact_toLimbs (x : CM31Exact) :
    cm31LimbsToExact (cm31ExactToLimbs x) = x := by
  ext <;> simp [cm31ExactToLimbs, cm31LimbsToExact]

def cm31ZeroFormula (m : M31SourceOps) : CM31Limbs := ![m.zero, m.zero]
def cm31OneFormula (m : M31SourceOps) : CM31Limbs := ![m.one, m.zero]
def cm31AddFormula (m : M31SourceOps) (x y : CM31Limbs) : CM31Limbs :=
  ![m.add (x 0) (y 0), m.add (x 1) (y 1)]
def cm31SubFormula (m : M31SourceOps) (x y : CM31Limbs) : CM31Limbs :=
  ![m.sub (x 0) (y 0), m.sub (x 1) (y 1)]
def cm31NegFormula (m : M31SourceOps) (x : CM31Limbs) : CM31Limbs :=
  ![m.neg (x 0), m.neg (x 1)]

/-- Literal three-product CM31 Karatsuba formula from Rust. -/
def cm31MulFormula (m : M31SourceOps) (x y : CM31Limbs) : CM31Limbs :=
  let m0 := m.mul (x 0) (y 0)
  let m1 := m.mul (x 1) (y 1)
  let m2 := m.mul (m.add (x 0) (x 1)) (m.add (y 0) (y 1))
  ![m.sub m0 m1, m.sub (m.sub m2 m0) m1]

/-- Literal two-product CM31 square graph from Rust: compute `a*b` once, then
double that stored cross term. -/
def cm31SquareFormula (m : M31SourceOps) (x : CM31Limbs) : CM31Limbs :=
  let cross := m.mul (x 0) (x 1)
  ![m.mul (m.add (x 0) (x 1)) (m.sub (x 0) (x 1)),
    m.add cross cross]

/-- Literal multiplication by `R=2+i`, using exactly Rust's add/sub graph. -/
def cm31MulByRFormula (m : M31SourceOps) (x : CM31Limbs) : CM31Limbs :=
  ![m.sub (m.add (x 0) (x 0)) (x 1),
    m.add (x 0) (m.add (x 1) (x 1))]

/-- Safe extensional wrapper around Rust's CM31 inverse formula.  The real
source calls a panicking base inverse only after its caller has established a
nonzero norm; the `Option` form records that precondition explicitly. -/
def cm31TryInvFormula (m : M31SourceOps) (x : CM31Limbs) : Option CM31Limbs :=
  if x = cm31ZeroFormula m then none
  else
    let norm := m.add (m.mul (x 0) (x 0)) (m.mul (x 1) (x 1))
    (m.tryInv norm).map fun nInv =>
      ![m.mul (x 0) nInv, m.mul (m.neg (x 1)) nInv]

structure CM31SourceOps where
  zero : CM31Limbs
  one : CM31Limbs
  add : CM31Limbs → CM31Limbs → CM31Limbs
  sub : CM31Limbs → CM31Limbs → CM31Limbs
  neg : CM31Limbs → CM31Limbs
  mul : CM31Limbs → CM31Limbs → CM31Limbs
  square : CM31Limbs → CM31Limbs
  mulByR : CM31Limbs → CM31Limbs
  tryInv : CM31Limbs → Option CM31Limbs

def cm31FormulaOps (m : M31SourceOps) : CM31SourceOps where
  zero := cm31ZeroFormula m
  one := cm31OneFormula m
  add := cm31AddFormula m
  sub := cm31SubFormula m
  neg := cm31NegFormula m
  mul := cm31MulFormula m
  square := cm31SquareFormula m
  mulByR := cm31MulByRFormula m
  tryInv := cm31TryInvFormula m

/-- Exact Rust/source equality for the deployed CM31 formula graph, with
`tryInv` understood as the totalized adapter to panicking `CM31::inv` described
above. -/
def RustCM31FormulasMatch (m : M31SourceOps) (rust : CM31SourceOps) : Prop :=
  rust = cm31FormulaOps m

theorem cm31Formulas_nonvacuous (m : M31SourceOps) :
    RustCM31FormulasMatch m (cm31FormulaOps m) := rfl

theorem exact_cm31_zero :
    cm31LimbsToExact (cm31FormulaOps exactM31SourceOps).zero = 0 := by
  ext <;> simp [cm31FormulaOps, cm31ZeroFormula, cm31LimbsToExact]

theorem exact_cm31_one :
    cm31LimbsToExact (cm31FormulaOps exactM31SourceOps).one = 1 := by
  ext <;>
    simp [cm31FormulaOps, cm31OneFormula, cm31LimbsToExact,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem exact_cm31_add (x y : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).add x y) =
      cm31LimbsToExact x + cm31LimbsToExact y := by
  ext <;> simp [cm31FormulaOps, cm31AddFormula, cm31LimbsToExact]

theorem exact_cm31_sub (x y : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).sub x y) =
      cm31LimbsToExact x - cm31LimbsToExact y := by
  ext <;> simp [cm31FormulaOps, cm31SubFormula, cm31LimbsToExact]

theorem exact_cm31_neg (x : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).neg x) =
      -cm31LimbsToExact x := by
  ext <;> simp [cm31FormulaOps, cm31NegFormula, cm31LimbsToExact]

theorem exact_cm31_mul (x y : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).mul x y) =
      cm31LimbsToExact x * cm31LimbsToExact y := by
  rw [← cm31Karatsuba_eq_mul]
  ext <;>
    simp [cm31FormulaOps, cm31MulFormula, cm31LimbsToExact,
      cm31Karatsuba]

theorem exact_cm31_square (x : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).square x) =
      cm31LimbsToExact x * cm31LimbsToExact x := by
  rw [← cm31Square_eq_sq]
  apply QuadraticAlgebra.ext
  · simp [cm31FormulaOps, cm31SquareFormula, cm31LimbsToExact,
      cm31Square]
  · simp [cm31FormulaOps, cm31SquareFormula, cm31LimbsToExact,
      cm31Square]
    ring

theorem exact_cm31_mulByR (x : CM31Limbs) :
    cm31LimbsToExact ((cm31FormulaOps exactM31SourceOps).mulByR x) =
      qm31R * cm31LimbsToExact x := by
  rw [← cm31MulByR_eq]
  ext <;>
    simp [cm31FormulaOps, cm31MulByRFormula, cm31LimbsToExact,
      cm31MulByR] <;> ring

theorem cm31_zeroFormula_eq_toLimbs_zero :
    cm31ZeroFormula exactM31SourceOps = cm31ExactToLimbs 0 := by
  funext i
  fin_cases i <;>
    simp [cm31ZeroFormula, cm31ExactToLimbs, exactM31SourceOps]

theorem exact_cm31_tryInv (x : CM31Limbs) :
    ((cm31FormulaOps exactM31SourceOps).tryInv x).map cm31LimbsToExact =
      if cm31LimbsToExact x = 0 then none
      else some (cm31LimbsToExact x)⁻¹ := by
  by_cases hx : cm31LimbsToExact x = 0
  · have hxwire : x = cm31ZeroFormula exactM31SourceOps := by
      calc
        x = cm31ExactToLimbs (cm31LimbsToExact x) :=
          (cm31ExactToLimbs_toExact x).symm
        _ = cm31ExactToLimbs 0 := by rw [hx]
        _ = cm31ZeroFormula exactM31SourceOps :=
          cm31_zeroFormula_eq_toLimbs_zero.symm
    rw [if_pos hx]
    simp only [cm31FormulaOps, cm31TryInvFormula, hxwire, if_pos,
      Option.map_none]
  · have hxwire : x ≠ cm31ZeroFormula exactM31SourceOps := by
      intro h
      apply hx
      rw [h]
      exact exact_cm31_zero
    let normWire := exactM31SourceOps.add
      (exactM31SourceOps.mul (x 0) (x 0))
      (exactM31SourceOps.mul (x 1) (x 1))
    have hnorm : m31ResidueEquiv normWire =
        QuadraticAlgebra.norm (cm31LimbsToExact x) := by
      simp [normWire, cm31LimbsToExact, QuadraticAlgebra.norm_def]
    have hnorm_ne : m31ResidueEquiv normWire ≠ 0 := by
      rw [hnorm]
      intro h
      apply hx
      exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h
    rw [if_neg hx]
    simp only [cm31FormulaOps, cm31TryInvFormula, hxwire, if_false]
    have htry : exactM31SourceOps.tryInv normWire =
        some (m31ResidueEquiv.symm ((m31ResidueEquiv normWire)⁻¹)) := by
      change (if m31ResidueEquiv normWire = 0 then none
        else some (m31ResidueEquiv.symm ((m31ResidueEquiv normWire)⁻¹))) = _
      rw [if_neg hnorm_ne]
    rw [htry]
    simp only [Option.map_some]
    congr 1
    ext <;>
      simp [cm31LimbsToExact, normWire, hnorm,
        QuadraticAlgebra.re_inv, QuadraticAlgebra.im_inv,
        QuadraticAlgebra.norm_def] <;> ring

theorem exact_cm31_tryInv_some (x : CM31Limbs)
    (hx : cm31LimbsToExact x ≠ 0) :
    (cm31FormulaOps exactM31SourceOps).tryInv x =
      some (cm31ExactToLimbs (cm31LimbsToExact x)⁻¹) := by
  have h := exact_cm31_tryInv x
  rw [if_neg hx] at h
  cases hopt : (cm31FormulaOps exactM31SourceOps).tryInv x with
  | none => simp [hopt] at h
  | some value =>
      have hvalue : cm31LimbsToExact value = (cm31LimbsToExact x)⁻¹ := by
        simpa [hopt] using h
      congr 1
      calc
        value = cm31ExactToLimbs (cm31LimbsToExact value) :=
          (cm31ExactToLimbs_toExact value).symm
        _ = cm31ExactToLimbs (cm31LimbsToExact x)⁻¹ := by rw [hvalue]

/-! ## QM31 source formulas -/

def lowCM31 (x : QM31Limbs) : CM31Limbs := ![x 0, x 1]
def highCM31 (x : QM31Limbs) : CM31Limbs := ![x 2, x 3]
def joinCM31 (x y : CM31Limbs) : QM31Limbs := ![x 0, x 1, y 0, y 1]

@[simp] theorem join_low_high (x : QM31Limbs) :
    joinCM31 (lowCM31 x) (highCM31 x) = x := by
  funext i
  fin_cases i <;> rfl

def qm31ZeroFormula (c : CM31SourceOps) : QM31Limbs :=
  joinCM31 c.zero c.zero
def qm31OneFormula (c : CM31SourceOps) : QM31Limbs :=
  joinCM31 c.one c.zero
def qm31AddFormula (c : CM31SourceOps) (x y : QM31Limbs) : QM31Limbs :=
  joinCM31 (c.add (lowCM31 x) (lowCM31 y))
    (c.add (highCM31 x) (highCM31 y))
def qm31SubFormula (c : CM31SourceOps) (x y : QM31Limbs) : QM31Limbs :=
  joinCM31 (c.sub (lowCM31 x) (lowCM31 y))
    (c.sub (highCM31 x) (highCM31 y))
def qm31NegFormula (c : CM31SourceOps) (x : QM31Limbs) : QM31Limbs :=
  joinCM31 (c.neg (lowCM31 x)) (c.neg (highCM31 x))

/-- Literal three-CM31-product QM31 Karatsuba graph. -/
def qm31MulFormula (c : CM31SourceOps) (x y : QM31Limbs) : QM31Limbs :=
  let m0 := c.mul (lowCM31 x) (lowCM31 y)
  let m1 := c.mul (highCM31 x) (highCM31 y)
  let m2 := c.mul (c.add (lowCM31 x) (highCM31 x))
    (c.add (lowCM31 y) (highCM31 y))
  joinCM31 (c.add m0 (c.mulByR m1)) (c.sub (c.sub m2 m0) m1)

/-- Literal optimized seven-base-product QM31 square graph. -/
def qm31SquareFormula (c : CM31SourceOps) (x : QM31Limbs) : QM31Limbs :=
  let c0Square := c.square (lowCM31 x)
  let c1Square := c.square (highCM31 x)
  let cross := c.mul (lowCM31 x) (highCM31 x)
  joinCM31 (c.add c0Square (c.mulByR c1Square)) (c.add cross cross)

/-- Literal safe form of the deployed quadratic-extension inversion graph. -/
def qm31TryInvFormula (c : CM31SourceOps) (x : QM31Limbs) : Option QM31Limbs :=
  if x = qm31ZeroFormula c then none
  else
    let norm := c.sub (c.square (lowCM31 x))
      (c.mulByR (c.square (highCM31 x)))
    (c.tryInv norm).map fun nInv =>
      joinCM31 (c.mul (lowCM31 x) nInv)
        (c.mul (c.neg (highCM31 x)) nInv)

structure QM31SourceOps where
  zero : QM31Limbs
  one : QM31Limbs
  add : QM31Limbs → QM31Limbs → QM31Limbs
  sub : QM31Limbs → QM31Limbs → QM31Limbs
  neg : QM31Limbs → QM31Limbs
  mul : QM31Limbs → QM31Limbs → QM31Limbs
  square : QM31Limbs → QM31Limbs
  tryInv : QM31Limbs → Option QM31Limbs

def qm31FormulaOps (c : CM31SourceOps) : QM31SourceOps where
  zero := qm31ZeroFormula c
  one := qm31OneFormula c
  add := qm31AddFormula c
  sub := qm31SubFormula c
  neg := qm31NegFormula c
  mul := qm31MulFormula c
  square := qm31SquareFormula c
  tryInv := qm31TryInvFormula c

/-- Exact Rust/source equality for every deployed QM31 formula, including the
optimized square rather than generic multiplication. -/
def RustQM31FormulasMatch (c : CM31SourceOps) (rust : QM31SourceOps) : Prop :=
  rust = qm31FormulaOps c

theorem qm31Formulas_nonvacuous (c : CM31SourceOps) :
    RustQM31FormulasMatch c (qm31FormulaOps c) := rfl

@[simp] theorem lowCM31_toExact (x : QM31Limbs) :
    cm31LimbsToExact (lowCM31 x) = (limbsToQM31Exact x).re := by
  ext <;> simp [cm31LimbsToExact, lowCM31, limbsToQM31Exact]

@[simp] theorem highCM31_toExact (x : QM31Limbs) :
    cm31LimbsToExact (highCM31 x) = (limbsToQM31Exact x).im := by
  ext <;> simp [cm31LimbsToExact, highCM31, limbsToQM31Exact]

theorem joinCM31_toExact (x y : CM31Limbs) :
    limbsToQM31Exact (joinCM31 x y) =
      (⟨cm31LimbsToExact x, cm31LimbsToExact y⟩ : QM31Exact) := by
  ext <;> simp [limbsToQM31Exact, joinCM31, cm31LimbsToExact]

theorem exact_qm31_zero :
    limbsToQM31Exact (qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).zero = 0 := by
  rw [show (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero =
      joinCM31 (cm31FormulaOps exactM31SourceOps).zero
        (cm31FormulaOps exactM31SourceOps).zero by rfl,
    joinCM31_toExact, exact_cm31_zero]
  rfl

theorem exact_qm31_one :
    limbsToQM31Exact (qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).one = 1 := by
  rw [show (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).one =
      joinCM31 (cm31FormulaOps exactM31SourceOps).one
        (cm31FormulaOps exactM31SourceOps).zero by rfl,
    joinCM31_toExact, exact_cm31_one, exact_cm31_zero]
  rfl

theorem exact_qm31_add (x y : QM31Limbs) :
    limbsToQM31Exact ((qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).add x y) =
      limbsToQM31Exact x + limbsToQM31Exact y := by
  rw [show (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).add x y =
      joinCM31
        ((cm31FormulaOps exactM31SourceOps).add (lowCM31 x) (lowCM31 y))
        ((cm31FormulaOps exactM31SourceOps).add (highCM31 x) (highCM31 y)) by rfl,
    joinCM31_toExact, exact_cm31_add, exact_cm31_add]
  ext <;> simp

theorem exact_qm31_sub (x y : QM31Limbs) :
    limbsToQM31Exact ((qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).sub x y) =
      limbsToQM31Exact x - limbsToQM31Exact y := by
  rw [show (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).sub x y =
      joinCM31
        ((cm31FormulaOps exactM31SourceOps).sub (lowCM31 x) (lowCM31 y))
        ((cm31FormulaOps exactM31SourceOps).sub (highCM31 x) (highCM31 y)) by rfl,
    joinCM31_toExact, exact_cm31_sub, exact_cm31_sub]
  ext <;> simp

theorem exact_qm31_neg (x : QM31Limbs) :
    limbsToQM31Exact ((qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).neg x) =
      -limbsToQM31Exact x := by
  rw [show (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).neg x =
      joinCM31
        ((cm31FormulaOps exactM31SourceOps).neg (lowCM31 x))
        ((cm31FormulaOps exactM31SourceOps).neg (highCM31 x)) by rfl,
    joinCM31_toExact, exact_cm31_neg, exact_cm31_neg]
  ext <;> simp

theorem exact_qm31_mul (x y : QM31Limbs) :
    limbsToQM31Exact ((qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).mul x y) =
      limbsToQM31Exact x * limbsToQM31Exact y := by
  rw [← qm31Karatsuba_eq_mul]
  simp only [qm31FormulaOps, qm31MulFormula]
  rw [joinCM31_toExact]
  simp only [exact_cm31_add, exact_cm31_sub, exact_cm31_mul,
    exact_cm31_mulByR, lowCM31_toExact, highCM31_toExact]
  simp [qm31Karatsuba, cm31Karatsuba_eq_mul, cm31MulByR_eq]

theorem exact_qm31_square (x : QM31Limbs) :
    limbsToQM31Exact ((qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).square x) =
      limbsToQM31Exact x * limbsToQM31Exact x := by
  rw [← qm31Square_eq_sq]
  simp only [qm31FormulaOps, qm31SquareFormula]
  rw [joinCM31_toExact]
  simp only [exact_cm31_add, exact_cm31_square, exact_cm31_mulByR,
    exact_cm31_mul, lowCM31_toExact, highCM31_toExact]
  apply QuadraticAlgebra.ext
  · simp [qm31Square, cm31Square_eq_sq, cm31MulByR_eq]
  · simp [qm31Square, cm31Karatsuba_eq_mul]
    ring

theorem qm31_zeroFormula_eq_toLimbs_zero :
    qm31ZeroFormula (cm31FormulaOps exactM31SourceOps) =
      qm31ExactToLimbs 0 := by
  apply qm31ExactLimbEquiv.injective
  change limbsToQM31Exact
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero =
    limbsToQM31Exact (qm31ExactToLimbs 0)
  rw [exact_qm31_zero, limbsToQM31Exact_qm31ExactToLimbs]

theorem exact_qm31_tryInv (x : QM31Limbs) :
    ((qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).tryInv x).map
        limbsToQM31Exact =
      if limbsToQM31Exact x = 0 then none
      else some (limbsToQM31Exact x)⁻¹ := by
  by_cases hx : limbsToQM31Exact x = 0
  · have hxwire : x = qm31ZeroFormula
        (cm31FormulaOps exactM31SourceOps) := by
      calc
        x = qm31ExactToLimbs (limbsToQM31Exact x) :=
          (qm31ExactToLimbs_limbsToQM31Exact x).symm
        _ = qm31ExactToLimbs 0 := by rw [hx]
        _ = qm31ZeroFormula (cm31FormulaOps exactM31SourceOps) :=
          qm31_zeroFormula_eq_toLimbs_zero.symm
    rw [if_pos hx]
    simp only [qm31FormulaOps, qm31TryInvFormula, hxwire, if_pos,
      Option.map_none]
  · have hxwire : x ≠ qm31ZeroFormula
        (cm31FormulaOps exactM31SourceOps) := by
      intro h
      apply hx
      rw [h]
      exact exact_qm31_zero
    let normWire := (cm31FormulaOps exactM31SourceOps).sub
      ((cm31FormulaOps exactM31SourceOps).square (lowCM31 x))
      ((cm31FormulaOps exactM31SourceOps).mulByR
        ((cm31FormulaOps exactM31SourceOps).square (highCM31 x)))
    have hnorm : cm31LimbsToExact normWire =
        QuadraticAlgebra.norm (limbsToQM31Exact x) := by
      simp only [normWire]
      rw [exact_cm31_sub, exact_cm31_square, exact_cm31_mulByR,
        exact_cm31_square, lowCM31_toExact, highCM31_toExact]
      simp [QuadraticAlgebra.norm_def]
      ring
    have hnorm_ne : cm31LimbsToExact normWire ≠ 0 := by
      rw [hnorm]
      intro h
      apply hx
      exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h
    have hcmInv := exact_cm31_tryInv_some normWire hnorm_ne
    rw [if_neg hx]
    simp only [qm31FormulaOps, qm31TryInvFormula, hxwire, if_false]
    change Option.map limbsToQM31Exact
      (Option.map
        (fun nInv => joinCM31
          ((cm31FormulaOps exactM31SourceOps).mul (lowCM31 x) nInv)
          ((cm31FormulaOps exactM31SourceOps).mul
            ((cm31FormulaOps exactM31SourceOps).neg (highCM31 x)) nInv))
        ((cm31FormulaOps exactM31SourceOps).tryInv normWire)) = _
    rw [hcmInv]
    simp only [Option.map_some]
    congr 1
    rw [joinCM31_toExact, exact_cm31_mul, exact_cm31_mul,
      exact_cm31_neg, cm31LimbsToExact_toLimbs, lowCM31_toExact,
      highCM31_toExact, hnorm]
    apply QuadraticAlgebra.ext
    · simp [QuadraticAlgebra.re_inv, QuadraticAlgebra.norm_def]
      ring
    · simp [QuadraticAlgebra.im_inv, QuadraticAlgebra.norm_def]
      ring

/-! ## Algebraic composition into the deployment seam -/

/-- The byte/assembly functions remain a separate code-model equality. -/
def RustQM31AssemblyCodecFunctionsMatch
    (rustAssemble : QM31Limbs → QM31Exact)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact) : Prop :=
  rustAssemble = limbsToQM31Exact ∧
  rustEncode = encodeQM31ExactLE ∧
  rustDecode = decodeQM31ExactLE

/-- Strengthened source conclusion.  Its first conjunct is the pre-existing
deployment seam; the final two conjuncts retain subtraction and the optimized
square as explicit, testable facts. -/
def RustQM31CompleteSourceFunctionsMatch
    (rustAssemble : QM31Limbs → QM31Exact)
    (q : QM31SourceOps)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact) : Prop :=
  RustQM31SourceFunctionsMatch rustAssemble q.zero q.one q.add q.mul q.neg
      q.tryInv rustEncode rustDecode ∧
  (∀ a b, limbsToQM31Exact (q.sub a b) =
    limbsToQM31Exact a - limbsToQM31Exact b) ∧
  (∀ a, limbsToQM31Exact (q.square a) =
    limbsToQM31Exact a * limbsToQM31Exact a)

private theorem option_map_equiv_injective {α β : Type*} (e : α ≃ β) :
    Function.Injective (fun x : Option α => x.map e) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some yv => simp at h
  | some xv =>
      cases y with
      | none => simp at h
      | some yv =>
          simp only [Option.map_some, Option.some.injEq] at h
          exact congrArg some (e.injective h)

theorem exact_formula_zero_eq_limbZero :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero = limbZero := by
  apply qm31ExactLimbEquiv.injective
  simp [qm31ExactLimbEquiv, exact_qm31_zero, limbZero]

theorem exact_formula_one_eq_limbOne :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).one = limbOne := by
  apply qm31ExactLimbEquiv.injective
  simp [qm31ExactLimbEquiv, exact_qm31_one, limbOne]

theorem exact_formula_add_eq_limbAdd :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).add = limbAdd := by
  funext x y
  apply qm31ExactLimbEquiv.injective
  simp [qm31ExactLimbEquiv, exact_qm31_add, limbAdd]

theorem exact_formula_mul_eq_limbMul :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).mul = limbMul := by
  funext x y
  apply qm31ExactLimbEquiv.injective
  simp [qm31ExactLimbEquiv, exact_qm31_mul, limbMul,
    qm31Karatsuba_eq_mul]

theorem exact_formula_neg_eq_limbNeg :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).neg = limbNeg := by
  funext x
  apply qm31ExactLimbEquiv.injective
  simp [qm31ExactLimbEquiv, exact_qm31_neg, limbNeg]

theorem limbTryInv_map_exact (x : QM31Limbs) :
    (limbTryInv x).map limbsToQM31Exact =
      if limbsToQM31Exact x = 0 then none
      else some (limbsToQM31Exact x)⁻¹ := by
  by_cases h : limbsToQM31Exact x = 0
  · simp [limbTryInv, qm31TryInv_eq, h]
  · simp [limbTryInv, qm31TryInv_eq, h]

theorem exact_formula_tryInv_eq_limbTryInv :
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).tryInv =
      limbTryInv := by
  funext x
  apply option_map_equiv_injective qm31ExactLimbEquiv
  change Option.map limbsToQM31Exact
      ((qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).tryInv x) =
    Option.map limbsToQM31Exact (limbTryInv x)
  rw [exact_qm31_tryInv, limbTryInv_map_exact]

/-- Pure algebraic lifting: local base/CM/QM source equalities imply the old
source-function seam plus the formerly omitted subtraction and optimized
square facts. -/
theorem formulaFidelity_lifts_completeSourceFunctions
    (m : M31SourceOps) (c : CM31SourceOps) (q : QM31SourceOps)
    (rustAssemble : QM31Limbs → QM31Exact)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact)
    (hm : RustCanonicalM31PrimitivesMatch m)
    (hc : RustCM31FormulasMatch m c)
    (hq : RustQM31FormulasMatch c q)
    (hwire : RustQM31AssemblyCodecFunctionsMatch rustAssemble rustEncode
      rustDecode) :
    RustQM31CompleteSourceFunctionsMatch rustAssemble q rustEncode
      rustDecode := by
  rcases hm with ⟨hz, ho, ha, hs, hmul, hn, hi⟩
  have hmEq : m = exactM31SourceOps := by
    cases m
    simp_all
  subst m
  subst c
  subst q
  rcases hwire with ⟨rfl, rfl, rfl⟩
  refine ⟨?_, exact_qm31_sub, exact_qm31_square⟩
  exact ⟨rfl, exact_formula_zero_eq_limbZero,
    exact_formula_one_eq_limbOne, exact_formula_add_eq_limbAdd,
    exact_formula_mul_eq_limbMul, exact_formula_neg_eq_limbNeg,
    exact_formula_tryInv_eq_limbTryInv, rfl, rfl⟩

/-- The strengthened formula seam implies the exact deployment representation
bundle while retaining the subtraction/square guarantees in the conclusion. -/
theorem formulaFidelity_lifts_deploymentRepresentation
    (m : M31SourceOps) (c : CM31SourceOps) (q : QM31SourceOps)
    (rustAssemble : QM31Limbs → QM31Exact)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact)
    (hm : RustCanonicalM31PrimitivesMatch m)
    (hc : RustCM31FormulasMatch m c)
    (hq : RustQM31FormulasMatch c q)
    (hwire : RustQM31AssemblyCodecFunctionsMatch rustAssemble rustEncode
      rustDecode) :
    DeployedQM31RepresentationMatches qm31ExactLimbEquiv rustAssemble
        (rustEncode ∘ rustAssemble)
        (fun bytes => (rustDecode bytes).map qm31ExactLimbEquiv.symm)
        q.zero q.one q.add q.mul q.neg q.tryInv ∧
      (∀ a b, limbsToQM31Exact (q.sub a b) =
        limbsToQM31Exact a - limbsToQM31Exact b) ∧
      (∀ a, limbsToQM31Exact (q.square a) =
        limbsToQM31Exact a * limbsToQM31Exact a) := by
  have hcomplete := formulaFidelity_lifts_completeSourceFunctions m c q
    rustAssemble rustEncode rustDecode hm hc hq hwire
  exact ⟨deployedRepresentationMatches_of_sourceFunctions rustAssemble q.zero
    q.one q.add q.mul q.neg q.tryInv rustEncode rustDecode hcomplete.1,
    hcomplete.2.1, hcomplete.2.2⟩

theorem completeSourceFunctions_nonvacuous :
    RustQM31CompleteSourceFunctionsMatch limbsToQM31Exact
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps))
      encodeQM31ExactLE decodeQM31ExactLE :=
  formulaFidelity_lifts_completeSourceFunctions exactM31SourceOps
    (cm31FormulaOps exactM31SourceOps)
    (qm31FormulaOps (cm31FormulaOps exactM31SourceOps))
    limbsToQM31Exact encodeQM31ExactLE decodeQM31ExactLE
    canonicalM31Primitives_nonvacuous (cm31Formulas_nonvacuous _)
    (qm31Formulas_nonvacuous _) ⟨rfl, rfl, rfl⟩

/-! ## Negative teeth -/

/-- A base implementation whose subtraction always returns zero. -/
def wrongM31SubOps : M31SourceOps :=
  { exactM31SourceOps with sub := fun _ _ => exactM31SourceOps.zero }

theorem wrong_base_subtraction_breaks_primitive_interface :
    ¬ RustCanonicalM31PrimitivesMatch wrongM31SubOps := by
  rintro ⟨_, _, _, hsub, _, _, _⟩
  have tooth := congrFun (congrFun hsub exactM31SourceOps.one)
    exactM31SourceOps.zero
  apply_fun m31ResidueEquiv at tooth
  simp [wrongM31SubOps, exactM31SourceOps] at tooth

/-- A top-level source with subtraction replaced by constant zero. -/
def wrongSubQM31Ops : QM31SourceOps :=
  { qm31FormulaOps (cm31FormulaOps exactM31SourceOps) with
    sub := fun _ _ => (qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).zero }

/-- A top-level source with the optimized square replaced by constant zero. -/
def wrongSquareQM31Ops : QM31SourceOps :=
  { qm31FormulaOps (cm31FormulaOps exactM31SourceOps) with
    square := fun _ => (qm31FormulaOps
      (cm31FormulaOps exactM31SourceOps)).zero }

theorem wrong_subtraction_breaks_complete_source :
    ¬ RustQM31CompleteSourceFunctionsMatch limbsToQM31Exact wrongSubQM31Ops
      encodeQM31ExactLE decodeQM31ExactLE := by
  intro h
  have tooth := h.2.1 limbOne limbZero
  rw [show wrongSubQM31Ops.sub limbOne limbZero =
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero by rfl,
    exact_qm31_zero] at tooth
  simp [limbOne, limbZero] at tooth

theorem wrong_optimized_square_breaks_complete_source :
    ¬ RustQM31CompleteSourceFunctionsMatch limbsToQM31Exact wrongSquareQM31Ops
      encodeQM31ExactLE decodeQM31ExactLE := by
  intro h
  have tooth := h.2.2 limbOne
  rw [show wrongSquareQM31Ops.square limbOne =
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero by rfl,
    exact_qm31_zero] at tooth
  simp [limbOne] at tooth

theorem wrong_subtraction_breaks_qm31_formula_interface :
    ¬ RustQM31FormulasMatch (cm31FormulaOps exactM31SourceOps)
      wrongSubQM31Ops := by
  intro h
  have hsub := congrArg QM31SourceOps.sub h
  have tooth := congrFun (congrFun hsub limbOne) limbZero
  apply_fun limbsToQM31Exact at tooth
  rw [show wrongSubQM31Ops.sub limbOne limbZero =
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero by rfl,
    exact_qm31_zero, exact_qm31_sub] at tooth
  simp [limbOne, limbZero] at tooth

theorem wrong_square_breaks_qm31_formula_interface :
    ¬ RustQM31FormulasMatch (cm31FormulaOps exactM31SourceOps)
      wrongSquareQM31Ops := by
  intro h
  have hsquare := congrArg QM31SourceOps.square h
  have tooth := congrFun hsquare limbOne
  apply_fun limbsToQM31Exact at tooth
  rw [show wrongSquareQM31Ops.square limbOne =
      (qm31FormulaOps (cm31FormulaOps exactM31SourceOps)).zero by rfl,
    exact_qm31_zero, exact_qm31_square] at tooth
  simp [limbOne] at tooth

/-! ## Axiom audit -/

#print axioms canonicalM31Primitives_nonvacuous
#print axioms exact_cm31_mul
#print axioms exact_cm31_square
#print axioms exact_cm31_mulByR
#print axioms exact_cm31_tryInv
#print axioms exact_qm31_mul
#print axioms exact_qm31_square
#print axioms exact_qm31_tryInv
#print axioms formulaFidelity_lifts_completeSourceFunctions
#print axioms formulaFidelity_lifts_deploymentRepresentation
#print axioms completeSourceFunctions_nonvacuous
#print axioms wrong_base_subtraction_breaks_primitive_interface
#print axioms wrong_subtraction_breaks_complete_source
#print axioms wrong_optimized_square_breaks_complete_source
#print axioms wrong_subtraction_breaks_qm31_formula_interface
#print axioms wrong_square_breaks_qm31_formula_interface

end AspisV5ComponentCQM31RustFormulaSeam
