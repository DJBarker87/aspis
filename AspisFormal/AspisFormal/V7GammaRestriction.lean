import AspisFormal.V5ComponentCQM31TowerExact
import AspisFormal.V7SplitTensorProfile
import Mathlib.Data.Nat.Bitwise

/-!
# Exact V7 gamma restriction

This leaf proves the 26+3 split-tensor identity in the literal deployed M31 /
QM31 tower.  Stage A uses lane point `(gamma,gamma^2,...,gamma^16)`.
Stage B uses low bits for `(1,i,u,iu)`, high bits for the three QM31 lanes,
and lane point `(i,u,gamma,gamma^2)`.
-/

namespace AspisV7GammaRestriction

open AspisV5ComponentCQM31TowerExact

set_option maxRecDepth 20000

abbrev F := M31Exact
abbrev K := QM31Exact

def liftBase (x : F) : K := ⟨⟨x, 0⟩, 0⟩

def qm31I : K := ⟨⟨0, 1⟩, 0⟩
def qm31U : K := ⟨0, 1⟩
def qm31IU : K := ⟨0, ⟨0, 1⟩⟩

def qm31Basis : Fin 4 → K := ![1, qm31I, qm31U, qm31IU]

theorem qm31IU_eq_mul : qm31IU = qm31I * qm31U := by
  rw [← qm31Karatsuba_eq_mul]
  ext <;>
    simp [qm31IU, qm31I, qm31U, qm31Karatsuba, cm31Karatsuba,
      cm31MulByR, qm31R, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

def fromBaseLimbs (limbs : Fin 4 → F) : K :=
  ⟨⟨limbs 0, limbs 1⟩, ⟨limbs 2, limbs 3⟩⟩

def scaleBasis (x : F) : Fin 4 → K :=
  ![⟨⟨x, 0⟩, 0⟩, ⟨⟨0, x⟩, 0⟩, ⟨0, ⟨x, 0⟩⟩, ⟨0, ⟨0, x⟩⟩]

theorem scaleBasis_eq_mul (x : F) (basis : Fin 4) :
    scaleBasis x basis = liftBase x * qm31Basis basis := by
  rw [← qm31Karatsuba_eq_mul]
  fin_cases basis <;>
    ext <;>
    simp [scaleBasis, liftBase, qm31Basis, qm31I, qm31U, qm31IU,
      qm31Karatsuba, cm31Karatsuba, cm31MulByR, qm31R,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The mathematical basis order is exactly Rust's
`(c0.a,c0.b,c1.a,c1.b) = (1,i,u,iu)`. -/
theorem fromBaseLimbs_eq_basis_sum (limbs : Fin 4 → F) :
    fromBaseLimbs limbs = ∑ basis : Fin 4, liftBase (limbs basis) * qm31Basis basis := by
  calc
    fromBaseLimbs limbs = ∑ basis : Fin 4, scaleBasis (limbs basis) basis := by
      rw [Fin.sum_univ_four]
      ext <;> simp [fromBaseLimbs, scaleBasis]
    _ = ∑ basis : Fin 4, liftBase (limbs basis) * qm31Basis basis := by
      apply Finset.sum_congr rfl
      intro basis _
      exact scaleBasis_eq_mul (limbs basis) basis

def genericStageALanePoint [CommRing R] (gamma : R) (bit : Fin 5) : R :=
  gamma ^ (2 ^ bit.val)

theorem genericStageALanePoint_eq_vector [CommRing R] (gamma : R) :
    genericStageALanePoint gamma =
      ![gamma, gamma ^ 2, gamma ^ 4, gamma ^ 8, gamma ^ 16] := by
  funext bit
  fin_cases bit <;> norm_num [genericStageALanePoint]

def genericStageABooleanWeight [CommRing R] (gamma : R) (lane : Fin 26) : R :=
  ∏ bit : Fin 5,
    if lane.val.testBit bit.val then genericStageALanePoint gamma bit else 1

set_option maxHeartbeats 1000000 in
theorem genericStageABooleanWeight_eq_pow [CommRing R] (gamma : R) (lane : Fin 26) :
    genericStageABooleanWeight gamma lane = gamma ^ lane.val := by
  fin_cases lane <;>
    norm_num [genericStageABooleanWeight, genericStageALanePoint,
      Fin.prod_univ_five, Nat.testBit_eq_decide_div_mod_eq] <;> ring

def stageALanePoint (gamma : K) : Fin 5 → K := genericStageALanePoint gamma

def stageABooleanWeight (gamma : K) (lane : Fin 26) : K :=
  genericStageABooleanWeight gamma lane

/-- The little-endian five-bit lane point evaluates lane `ell` to
`gamma^ell` for every real Stage-A lane. -/
theorem stageABooleanWeight_eq_pow (gamma : K) (lane : Fin 26) :
    stageABooleanWeight gamma lane = gamma ^ lane.val :=
  genericStageABooleanWeight_eq_pow gamma lane

def stageATensorRestriction (source : Fin 26 → F) (gamma : K) : K :=
  ∑ lane : Fin 26, stageABooleanWeight gamma lane * liftBase (source lane)

def stageADirectRestriction (source : Fin 26 → F) (gamma : K) : K :=
  ∑ lane : Fin 26, gamma ^ lane.val * liftBase (source lane)

theorem stageA_restrict_gamma (source : Fin 26 → F) (gamma : K) :
    stageATensorRestriction source gamma = stageADirectRestriction source gamma := by
  simp [stageATensorRestriction, stageADirectRestriction, stageABooleanWeight_eq_pow]

def genericStageBBasisPoint [CommMonoid R] (i u : R) : Fin 2 → R := ![i, u]

def genericStageBSourcePoint [CommRing R] (gamma : R) : Fin 2 → R := ![gamma, gamma ^ 2]

def genericStageBBasisWeight [CommMonoid R] (i u : R) (basis : Fin 4) : R :=
  ∏ bit : Fin 2,
    if basis.val.testBit bit.val then genericStageBBasisPoint i u bit else 1

def genericStageBSourceWeight [CommRing R] (gamma : R) (lane : Fin 3) : R :=
  ∏ bit : Fin 2,
    if lane.val.testBit bit.val then genericStageBSourcePoint gamma bit else 1

theorem genericStageBBasisWeight_eq [CommMonoid R] (i u : R) (basis : Fin 4) :
    genericStageBBasisWeight i u basis = ![1, i, u, i * u] basis := by
  fin_cases basis <;>
    norm_num [genericStageBBasisWeight, genericStageBBasisPoint,
      Fin.prod_univ_two, Nat.testBit_eq_decide_div_mod_eq]

theorem genericStageBSourceWeight_eq_pow [CommRing R] (gamma : R) (lane : Fin 3) :
    genericStageBSourceWeight gamma lane = gamma ^ lane.val := by
  fin_cases lane <;>
    norm_num [genericStageBSourceWeight, genericStageBSourcePoint,
      Fin.prod_univ_two, Nat.testBit_eq_decide_div_mod_eq]

def stageBBasisPoint : Fin 2 → K := genericStageBBasisPoint qm31I qm31U

def stageBSourcePoint (gamma : K) : Fin 2 → K := genericStageBSourcePoint gamma

def stageBBasisWeight (basis : Fin 4) : K :=
  genericStageBBasisWeight qm31I qm31U basis

def stageBSourceWeight (gamma : K) (lane : Fin 3) : K :=
  genericStageBSourceWeight gamma lane

theorem stageBBasisWeight_eq (basis : Fin 4) :
    stageBBasisWeight basis = qm31Basis basis :=
  genericStageBBasisWeight_eq qm31I qm31U basis

theorem stageBSourceWeight_eq_pow (gamma : K) (lane : Fin 3) :
    stageBSourceWeight gamma lane = gamma ^ lane.val :=
  genericStageBSourceWeight_eq_pow gamma lane

def stageBTensorRestriction (limbs : Fin 3 → Fin 4 → F) (gamma : K) : K :=
  ∑ lane : Fin 3, stageBSourceWeight gamma lane *
    (∑ basis : Fin 4, liftBase (limbs lane basis) * stageBBasisWeight basis)

def stageBDirectRestriction (source : Fin 3 → K) (gamma : K) : K :=
  ∑ lane : Fin 3, gamma ^ lane.val * source lane

theorem stageB_restrict_gamma (limbs : Fin 3 → Fin 4 → F) (gamma : K) :
    stageBTensorRestriction limbs gamma =
      stageBDirectRestriction (fun lane => fromBaseLimbs (limbs lane)) gamma := by
  simp only [stageBTensorRestriction, stageBDirectRestriction,
    stageBSourceWeight_eq_pow, stageBBasisWeight_eq]
  apply Finset.sum_congr rfl
  intro lane _
  rw [← fromBaseLimbs_eq_basis_sum]

def splitTensorRestriction
    (stageA : Fin 26 → F) (stageBLimbs : Fin 3 → Fin 4 → F) (gamma : K) : K :=
  stageATensorRestriction stageA gamma +
    gamma ^ 26 * stageBTensorRestriction stageBLimbs gamma

def width29Batch
    (stageA : Fin 26 → F) (stageB : Fin 3 → K) (gamma : K) : K :=
  (∑ lane : Fin 26, gamma ^ lane.val * liftBase (stageA lane)) +
    ∑ lane : Fin 3, gamma ^ (26 + lane.val) * stageB lane

/-- The staged tensor representation is exactly the frozen V6 degree-28
width-29 gamma batch; no cryptographic assumption occurs in this identity. -/
theorem splitTensor_eq_width29Batch
    (stageA : Fin 26 → F) (stageBLimbs : Fin 3 → Fin 4 → F) (gamma : K) :
    splitTensorRestriction stageA stageBLimbs gamma =
      width29Batch stageA (fun lane => fromBaseLimbs (stageBLimbs lane)) gamma := by
  rw [splitTensorRestriction, stageA_restrict_gamma, stageB_restrict_gamma]
  simp only [width29Batch, stageADirectRestriction, stageBDirectRestriction]
  apply congrArg (fun tail : K =>
    (∑ lane : Fin 26, gamma ^ lane.val * liftBase (stageA lane)) + tail)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lane _
  simp [pow_add, mul_assoc]

end AspisV7GammaRestriction
