import AspisFormal.V7GammaRestriction

/-!
# Published code-switch interfaces for Aspis V7

This module records the finite predicates found in the V7 paper audit.  It does
not import a paper theorem as an axiom.  In particular it proves that the
current 32/16-to-4 two-source proposal is not a direct instance of SwitchFold
Theorem 2, then states the exact transcript and low-degree identity interface
which the selected fallback must discharge.
-/

namespace AspisV7PublishedCodeSwitchInterfaces

/-! ## Necessary finite shape of SwitchFold Theorem 2 -/

/-- The finite dimension equalities which are necessary (but not sufficient)
for the one-source `C^t -> C'^t` switch in SwitchFold Theorem 2. -/
def SwitchFoldTheorem2FiniteShape
    (sourceInterleave targetInterleave sourceDimension targetDimension : Nat) : Prop :=
  sourceInterleave = targetInterleave /\
    sourceDimension = sourceInterleave * targetDimension

def stageAInterleave : Nat := 32
def stageBInterleave : Nat := 16
def targetBaseLimbInterleave : Nat := 4

/-- The target keeps four M31 limbs, so the Stage-A 32-limb source cannot have
the theorem's unchanged interleave width, for any code dimensions. -/
theorem no_stageA_direct_switchFold_shape (k k' : Nat) :
    ¬ SwitchFoldTheorem2FiniteShape
      stageAInterleave targetBaseLimbInterleave k k' := by
  norm_num [SwitchFoldTheorem2FiniteShape, stageAInterleave,
    targetBaseLimbInterleave]

/-- The same obstruction holds for the Stage-B 16-limb source. -/
theorem no_stageB_direct_switchFold_shape (k k' : Nat) :
    ¬ SwitchFoldTheorem2FiniteShape
      stageBInterleave targetBaseLimbInterleave k k' := by
  norm_num [SwitchFoldTheorem2FiniteShape, stageBInterleave,
    targetBaseLimbInterleave]

def switchFoldSourceCommitments : Nat := 1
def v7SourceCommitments : Nat := 2
def switchFoldGeneratorMatrixOracleRequirements : Nat := 1
def v7PreferredGeneratorMatrixOracles : Nat := 0

theorem source_commitment_count_mismatch :
    v7SourceCommitments ≠ switchFoldSourceCommitments := by decide

theorem generator_matrix_oracle_missing :
    v7PreferredGeneratorMatrixOracles ≠
      switchFoldGeneratorMatrixOracleRequirements := by decide

/-! ## One gamma is not a uniform Freivalds vector -/

section PowerVector

variable {K : Type*} [Field K]

def gammaPowerVector (width : Nat) (gamma : K) : Fin width -> K :=
  fun lane => gamma ^ lane.val

theorem gammaPowerVector_first (width : Nat) (hwidth : 0 < width) (gamma : K) :
    gammaPowerVector width gamma (Fin.mk 0 hwidth) = 1 := by
  simp [gammaPowerVector]

/-- Already at width 32, a powers-of-one-gamma vector cannot cover the uniform
vector space required by the direct Freivalds step: the zero vector has no
preimage because coordinate zero is fixed to one. -/
theorem stageA_gamma_power_vector_not_surjective :
    ¬ Function.Surjective (gammaPowerVector (K := K) stageAInterleave) := by
  intro hsurjective
  obtain ⟨gamma, hgamma⟩ := hsurjective (fun _ => (0 : K))
  let first : Fin stageAInterleave :=
    ⟨0, by norm_num [stageAInterleave]⟩
  have hfirst : gammaPowerVector stageAInterleave gamma first = (0 : K) :=
    congrFun hgamma first
  simpa [gammaPowerVector, first] using hfirst

end PowerVector

/-! ## Selected degree-corrected fallback interface -/

def rowVariables : Nat := 10

abbrev RowPoint (K : Type*) := Fin rowVariables -> K

section Fallback

variable {K : Type*} [Field K]

def fallbackDiscrepancy
    (stageA stageB target : RowPoint K -> K) (gamma : K) : RowPoint K -> K :=
  fun row => target row - stageA row - gamma ^ 26 * stageB row

def FallbackIdentityAt
    (stageA stageB target : RowPoint K -> K) (gamma : K) (row : RowPoint K) : Prop :=
  target row = stageA row + gamma ^ 26 * stageB row

theorem fallbackIdentityAt_iff_discrepancy_zero
    (stageA stageB target : RowPoint K -> K) (gamma : K) (row : RowPoint K) :
    FallbackIdentityAt stageA stageB target gamma row <->
      fallbackDiscrepancy stageA stageB target gamma row = 0 := by
  simp only [FallbackIdentityAt, fallbackDiscrepancy]
  constructor <;> intro h
  · rw [h]
    ring
  · calc
      target row =
          (target row - stageA row - gamma ^ 26 * stageB row) +
            stageA row + gamma ^ 26 * stageB row := by ring
      _ = stageA row + gamma ^ 26 * stageB row := by rw [h]; ring

/-- Exact finite predicate required from the multivariate
Schwartz--Zippel instantiation.  For ten row variables and total degree `d`, a
nonzero discrepancy has at most `d * |K|^9` zeros.  This file names the
predicate; the concrete Phase-4 polynomial supplies and proves it. -/
def TenVariableSchwartzZippelBound
    [Fintype K] [DecidableEq K] (totalDegree : Nat)
    (discrepancy : RowPoint K -> K) : Prop :=
  discrepancy ≠ 0 ->
    (Finset.univ.filter fun row => discrepancy row = 0).card <=
      totalDegree * Fintype.card K ^ (rowVariables - 1)

/-- The knowledge-sound PCS contract needed by the fallback.  `bound` means
that acceptance binds all three authenticated openings to the three extracted
low-degree row functions; `degreeCorrected` excludes the unsupported released
S-two list-regime shortcut documented in the audit. -/
structure DegreeCorrectedFallbackPCSContract
    (Commitment Opening : Type*) where
  bound : Commitment -> Opening ->
    (RowPoint K -> K) -> (RowPoint K -> K) -> (RowPoint K -> K) -> Prop
  degreeCorrected : Prop

end Fallback

/-! ## Fiat--Shamir causality -/

def stageARootRound : Nat := 0
def stageBRootRound : Nat := 1
def gammaRound : Nat := 2
def targetRootRound : Nat := 3
def freshRowPointRound : Nat := 4
def openingChallengeRound : Nat := 5

theorem fallback_transcript_order :
    stageARootRound < gammaRound /\
    stageBRootRound < gammaRound /\
    gammaRound < targetRootRound /\
    targetRootRound < freshRowPointRound /\
    freshRowPointRound < openingChallengeRound := by
  decide

/-! ## Audit -/

#print axioms no_stageA_direct_switchFold_shape
#print axioms no_stageB_direct_switchFold_shape
#print axioms source_commitment_count_mismatch
#print axioms generator_matrix_oracle_missing
#print axioms stageA_gamma_power_vector_not_surjective
#print axioms fallbackIdentityAt_iff_discrepancy_zero
#print axioms fallback_transcript_order

end AspisV7PublishedCodeSwitchInterfaces
