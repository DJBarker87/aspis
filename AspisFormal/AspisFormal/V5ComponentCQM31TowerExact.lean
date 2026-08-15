import AspisFormal.V5ComponentCQM31Representation
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- Kernel reduction of the two concrete M31 non-residue certificates needs the
-- same enlarged recursion stack as the existing 31-fold circle-order check.
set_option maxRecDepth 20000

/-!
# v5 Component C: exact deployed QM31 tower

This leaf replaces the cardinality-only `P^4` representation by the literal
field tower used by `aspis-core/src/field.rs`:

* `M31Exact = ZMod (2^31-1)`;
* `CM31Exact = M31Exact[i]/(i^2+1)`;
* `QM31Exact = CM31Exact[u]/(u^2-(2+i))`.

`QuadraticAlgebra R a 0` is the explicit pair representation in which the
second basis element squares to `a`.  Consequently the definitions below are
not abstract quotient representatives: their four coordinates are literally
Rust's `(c0.a,c0.b,c1.a,c1.b)` coordinates.

The two field facts are proved, rather than assumed.  `-1` is a nonsquare in
M31 because `P = 3 mod 4`; if `2+i` were a square in CM31, its norm `5` would
be a square in M31, contradicting quadratic reciprocity.  The Karatsuba and
inverse formulas are then checked against the field operations.

This leaf proves the mathematical tower and exposes the source-function bundle
needed by the existing deployment ledger.  It does not claim that bundle covers
every optimized Rust entry point.  The complete executable formula boundary,
including base subtraction and optimized QM31 square, is defined separately in
`V5ComponentCQM31RustFormulaSeam`.  No cryptographic assumption and no arbitrary
cardinality bijection occurs here.
-/

namespace AspisV5ComponentCQM31TowerExact

open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation

abbrev P : Nat := 2147483647

instance m31PrimeFact : Fact P.Prime := ⟨by norm_num [P]⟩

/-- The exact mathematical M31 field. -/
abbrev M31Exact := ZMod P

/-- `-1` is not a square modulo the deployed Mersenne prime. -/
theorem m31_neg_one_not_isSquare : ¬ IsSquare (-1 : M31Exact) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  norm_num [P]

/-- One square-and-multiply step for the exponent recurrence
`e_(k+1)=2*e_k+1`. -/
def fivePowStep (z : M31Exact) : M31Exact := z * z * 5

/-- Thirty iterations compute exponent `2^30-1`, using only thirty concrete
field squarings/multiplications in the kernel. -/
theorem fivePowStep_iterate (k : Nat) :
    fivePowStep^[k] 1 = (5 : M31Exact) ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      unfold fivePowStep
      calc
        (5 : M31Exact) ^ (2 ^ n - 1) * 5 ^ (2 ^ n - 1) * 5 =
            5 ^ ((2 ^ n - 1) + (2 ^ n - 1)) * 5 := by rw [pow_add]
        _ = 5 ^ ((2 ^ n - 1) + (2 ^ n - 1) + 1) := by
          simpa using
            (pow_add (5 : M31Exact)
              ((2 ^ n - 1) + (2 ^ n - 1)) 1).symm
        _ = 5 ^ (2 ^ (n + 1) - 1) := by
          congr 1
          rw [pow_succ]
          have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          omega

/-- The concrete Euler certificate: `5^(P/2) != 1`. -/
theorem five_euler_certificate : (5 : M31Exact) ^ (P / 2) ≠ 1 := by
  rw [show P / 2 = 2 ^ 30 - 1 by norm_num [P], ← fivePowStep_iterate 30]
  decide

/-- `5` is not a square modulo `P`, by Euler's criterion and the kernel-checked
30-step certificate above. -/
theorem m31_five_not_isSquare : ¬ IsSquare (5 : M31Exact) := by
  rw [ZMod.euler_criterion P (by decide)]
  exact five_euler_certificate

/-- Exact deployed complex extension: `i^2 = -1`. -/
abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

instance cm31Rootless : Fact
    (∀ r : M31Exact, r ^ 2 ≠ (-1 : M31Exact) + 0 * r) := ⟨by
  intro r hr
  apply m31_neg_one_not_isSquare
  refine ⟨r, ?_⟩
  simpa [pow_two] using hr.symm
⟩

/-- The literal non-residue `R = 2+i` from the Rust source. -/
def qm31R : CM31Exact := ⟨2, 1⟩

@[simp] theorem qm31R_re : qm31R.re = 2 := rfl
@[simp] theorem qm31R_im : qm31R.im = 1 := rfl

theorem cm31_norm_qm31R : QuadraticAlgebra.norm qm31R = (5 : M31Exact) := by
  norm_num [qm31R, QuadraticAlgebra.norm_def]

/-- `2+i` is a nonsquare in CM31: the norm of a square is a square, while
`Norm(2+i)=5` is a nonsquare in M31. -/
theorem cm31_qm31R_not_isSquare : ¬ IsSquare qm31R := by
  rintro ⟨z, hz⟩
  apply m31_five_not_isSquare
  refine ⟨QuadraticAlgebra.norm z, ?_⟩
  calc
    (5 : M31Exact) = QuadraticAlgebra.norm qm31R := cm31_norm_qm31R.symm
    _ = QuadraticAlgebra.norm (z * z) := congrArg QuadraticAlgebra.norm hz
    _ = QuadraticAlgebra.norm z * QuadraticAlgebra.norm z :=
      QuadraticAlgebra.norm.map_mul z z

instance qm31Rootless : Fact
    (∀ z : CM31Exact, z ^ 2 ≠ qm31R + 0 * z) := ⟨by
  intro z hz
  apply cm31_qm31R_not_isSquare
  refine ⟨z, ?_⟩
  simpa [pow_two] using hz.symm
⟩

/-- Exact deployed quartic extension: `u^2 = 2+i`. -/
abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

/-! ## Literal tower coordinates -/

/-- Exact canonical-residue equivalence.  Unlike `Fintype.equivOfCardEq`,
this is the standard ring equivalence `Fin P ≃ ZMod P`. -/
def m31ResidueEquiv : M31Value ≃+* M31Exact := ZMod.finEquiv P

/-- Four canonical M31 residues in Rust field order. -/
def limbsToQM31Exact (x : QM31Limbs) : QM31Exact :=
  ⟨⟨m31ResidueEquiv (x 0), m31ResidueEquiv (x 1)⟩,
   ⟨m31ResidueEquiv (x 2), m31ResidueEquiv (x 3)⟩⟩

/-- Recover the four canonical residues in `(c0.a,c0.b,c1.a,c1.b)` order. -/
def qm31ExactToLimbs (x : QM31Exact) : QM31Limbs :=
  ![m31ResidueEquiv.symm x.re.re,
    m31ResidueEquiv.symm x.re.im,
    m31ResidueEquiv.symm x.im.re,
    m31ResidueEquiv.symm x.im.im]

@[simp] theorem qm31ExactToLimbs_limbsToQM31Exact (x : QM31Limbs) :
    qm31ExactToLimbs (limbsToQM31Exact x) = x := by
  funext j
  fin_cases j <;> simp [qm31ExactToLimbs, limbsToQM31Exact]

@[simp] theorem limbsToQM31Exact_qm31ExactToLimbs (x : QM31Exact) :
    limbsToQM31Exact (qm31ExactToLimbs x) = x := by
  ext <;> simp [qm31ExactToLimbs, limbsToQM31Exact]

/-- The exact, computable four-limb equivalence. -/
def qm31ExactLimbEquiv : QM31Limbs ≃ QM31Exact where
  toFun := limbsToQM31Exact
  invFun := qm31ExactToLimbs
  left_inv := qm31ExactToLimbs_limbsToQM31Exact
  right_inv := limbsToQM31Exact_qm31ExactToLimbs

@[simp] theorem qm31ExactLimbEquiv_apply (x : QM31Limbs) :
    qm31ExactLimbEquiv x = limbsToQM31Exact x := rfl

@[simp] theorem qm31ExactLimbEquiv_symm_apply (x : QM31Exact) :
    qm31ExactLimbEquiv.symm x = qm31ExactToLimbs x := rfl

noncomputable instance cm31ExactFintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact) (QuadraticAlgebra.equivProd (-1) 0).symm

noncomputable instance qm31ExactFintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact) (QuadraticAlgebra.equivProd qm31R 0).symm

/-- The literal deployed tower has exactly four M31 coordinates. -/
theorem qm31Exact_card : Fintype.card QM31Exact = P ^ 4 := by
  calc
    Fintype.card QM31Exact = Fintype.card QM31Limbs :=
      Fintype.card_congr qm31ExactLimbEquiv.symm
    _ = P ^ 4 := qm31Limbs_card

/-- The exact-tower analogue of the old cardinality-only sampler theorem. -/
theorem successfulExactQM31FreeCoordinates_areIndependentUniform :
    AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform
      (successfulComponentCFreeCoordinateLaw qm31ExactLimbEquiv) :=
  successfulComponentCFreeCoordinateLaw_isIndependentUniform qm31ExactLimbEquiv

/-- Literal-`u32` Component-C sampling, assembled into the exact deployed
tower, is uniform on the encoder kernel.  No representation equivalence is a
caller premise. -/
theorem successfulExactQM31RawU32KernelLaw_eq_uniform
    (ell : (Fin 1024 → QM31Exact) →ₗ[QM31Exact] QM31Exact)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    (((successfulComponentCRawU32BlockLaw.map componentCFlatToCoordinates).map
        (componentCCoordinateRepresentationEquiv qm31ExactLimbEquiv)).map
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)) =
      PMF.uniformOfFintype (LinearMap.ker ell) := by
  rw [successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw]
  exact successfulComponentCKernelLaw_eq_uniform_under_representation
    qm31ExactLimbEquiv ell pivot hpivot

/-- Exact tower-aware 16-byte encoder. -/
def encodeQM31ExactLE (x : QM31Exact) : QM31Bytes :=
  encodeQM31LE (qm31ExactLimbEquiv.symm x)

/-- Exact tower-aware 16-byte decoder. -/
def decodeQM31ExactLE (bytes : QM31Bytes) : Option QM31Exact :=
  (decodeQM31LE bytes).map qm31ExactLimbEquiv

theorem decodeQM31ExactLE_encodeQM31ExactLE (x : QM31Exact) :
    decodeQM31ExactLE (encodeQM31ExactLE x) = some x := by
  simp [decodeQM31ExactLE, encodeQM31ExactLE, decodeQM31LE_encodeQM31LE]

/-! ## Exact CM31 kernels -/

/-- Rust's three-product CM31 Karatsuba formula. -/
def cm31Karatsuba (x y : CM31Exact) : CM31Exact :=
  let m0 := x.re * y.re
  let m1 := x.im * y.im
  let m2 := (x.re + x.im) * (y.re + y.im)
  ⟨m0 - m1, m2 - m0 - m1⟩

theorem cm31Karatsuba_eq_mul (x y : CM31Exact) :
    cm31Karatsuba x y = x * y := by
  ext <;> simp [cm31Karatsuba] <;> ring

/-- Rust's two-product complex squaring formula. -/
def cm31Square (x : CM31Exact) : CM31Exact :=
  ⟨(x.re + x.im) * (x.re - x.im), 2 * (x.re * x.im)⟩

theorem cm31Square_eq_sq (x : CM31Exact) : cm31Square x = x * x := by
  ext <;> simp [cm31Square] <;> ring

/-- Multiplication by the deployed non-residue `(2+i)`. -/
def cm31MulByR (x : CM31Exact) : CM31Exact :=
  ⟨2 * x.re - x.im, x.re + 2 * x.im⟩

theorem cm31MulByR_eq (x : CM31Exact) : cm31MulByR x = qm31R * x := by
  ext <;> simp [cm31MulByR, qm31R] <;> ring

/-! ## Exact QM31 kernels -/

/-- Rust's nested Karatsuba QM31 multiplication formula. -/
def qm31Karatsuba (x y : QM31Exact) : QM31Exact :=
  let m0 := cm31Karatsuba x.re y.re
  let m1 := cm31Karatsuba x.im y.im
  let m2 := cm31Karatsuba (x.re + x.im) (y.re + y.im)
  ⟨m0 + cm31MulByR m1, m2 - m0 - m1⟩

theorem qm31Karatsuba_eq_mul (x y : QM31Exact) :
    qm31Karatsuba x y = x * y := by
  ext <;>
    simp [qm31Karatsuba, cm31Karatsuba_eq_mul, cm31MulByR_eq] <;>
    ring

/-- Rust's seven-base-product specialized QM31 square. -/
def qm31Square (x : QM31Exact) : QM31Exact :=
  ⟨cm31Square x.re + cm31MulByR (cm31Square x.im),
   2 * cm31Karatsuba x.re x.im⟩

theorem qm31Square_eq_sq (x : QM31Exact) : qm31Square x = x * x := by
  ext <;>
    simp [qm31Square, cm31Square_eq_sq, cm31MulByR_eq,
      cm31Karatsuba_eq_mul, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat] <;>
    ring

/-- Rust's exact `try_inv`: reject zero, otherwise use
`(a+bu)^-1=(a-bu)/(a^2-(2+i)b^2)`. -/
def qm31TryInv (x : QM31Exact) : Option QM31Exact :=
  if x = 0 then none
  else
    let n := cm31Square x.re - cm31MulByR (cm31Square x.im)
    let nInv := n⁻¹
    some ⟨cm31Karatsuba x.re nInv, cm31Karatsuba (-x.im) nInv⟩

theorem qm31TryInv_eq (x : QM31Exact) :
    qm31TryInv x = if x = 0 then none else some x⁻¹ := by
  by_cases hx : x = 0
  · simp [qm31TryInv, hx]
  · simp only [qm31TryInv, hx, if_false]
    congr 1
    ext <;>
      simp [cm31Square_eq_sq, cm31MulByR_eq, cm31Karatsuba_eq_mul,
        QuadraticAlgebra.re_inv, QuadraticAlgebra.im_inv,
        QuadraticAlgebra.norm_def] <;>
      ring

/-! ## Arithmetic transported to the literal four-limb wire representation -/

def limbZero : QM31Limbs := qm31ExactLimbEquiv.symm 0
def limbOne : QM31Limbs := qm31ExactLimbEquiv.symm 1
def limbAdd (x y : QM31Limbs) : QM31Limbs :=
  qm31ExactLimbEquiv.symm (qm31ExactLimbEquiv x + qm31ExactLimbEquiv y)
def limbNeg (x : QM31Limbs) : QM31Limbs :=
  qm31ExactLimbEquiv.symm (-qm31ExactLimbEquiv x)
def limbMul (x y : QM31Limbs) : QM31Limbs :=
  qm31ExactLimbEquiv.symm (qm31Karatsuba (qm31ExactLimbEquiv x) (qm31ExactLimbEquiv y))
def limbTryInv (x : QM31Limbs) : Option QM31Limbs :=
  (qm31TryInv (qm31ExactLimbEquiv x)).map qm31ExactLimbEquiv.symm

/-- The previously named arithmetic seam is fully instantiable by the exact
tower and the literal deployed formulas. -/
theorem exactTowerArithmeticMatches :
    RustQM31TowerArithmeticMatches qm31ExactLimbEquiv limbZero limbOne
      limbAdd limbMul limbNeg limbTryInv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [limbZero]
  · simp [limbOne]
  · intro a b
    simp [limbAdd]
  · intro a b
    simp [limbMul, qm31Karatsuba_eq_mul]
  · intro a
    simp [limbNeg]
  · intro a
    by_cases h : qm31ExactLimbEquiv a = 0
    · simp [limbTryInv, qm31TryInv_eq]
    · simp [limbTryInv, qm31TryInv_eq]

/-- The sampler assembler is now the explicit four-limb tower equivalence,
not a cardinality-selected bijection. -/
theorem exactTowerSamplerAssemblyMatches :
    RustQM31SamplerAssemblyMatches qm31ExactLimbEquiv limbsToQM31Exact := rfl

/-! ## Deployment-ledger source bundle -/

/-- Exact pure-function correspondence required by the existing deployment
representation bundle.  This deliberately does not pretend to bind the entire
Rust field API: subtraction and the optimized square are absent from that older
bundle and are retained explicitly by `V5ComponentCQM31RustFormulaSeam`. -/
def RustQM31SourceFunctionsMatch
    (rustAssemble : QM31Limbs → QM31Exact)
    (rustZero rustOne : QM31Limbs)
    (rustAdd rustMul : QM31Limbs → QM31Limbs → QM31Limbs)
    (rustNeg : QM31Limbs → QM31Limbs)
    (rustTryInv : QM31Limbs → Option QM31Limbs)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact) : Prop :=
  rustAssemble = limbsToQM31Exact ∧
  rustZero = limbZero ∧ rustOne = limbOne ∧
  rustAdd = limbAdd ∧ rustMul = limbMul ∧ rustNeg = limbNeg ∧
  rustTryInv = limbTryInv ∧
  rustEncode = encodeQM31ExactLE ∧ rustDecode = decodeQM31ExactLE

/-! ## Axiom audit -/

#print axioms m31_neg_one_not_isSquare
#print axioms m31_five_not_isSquare
#print axioms cm31_qm31R_not_isSquare
#print axioms qm31ExactToLimbs_limbsToQM31Exact
#print axioms limbsToQM31Exact_qm31ExactToLimbs
#print axioms qm31Exact_card
#print axioms successfulExactQM31FreeCoordinates_areIndependentUniform
#print axioms successfulExactQM31RawU32KernelLaw_eq_uniform
#print axioms decodeQM31ExactLE_encodeQM31ExactLE
#print axioms cm31Karatsuba_eq_mul
#print axioms cm31Square_eq_sq
#print axioms cm31MulByR_eq
#print axioms qm31Karatsuba_eq_mul
#print axioms qm31Square_eq_sq
#print axioms qm31TryInv_eq
#print axioms exactTowerArithmeticMatches
#print axioms exactTowerSamplerAssemblyMatches

end AspisV5ComponentCQM31TowerExact
