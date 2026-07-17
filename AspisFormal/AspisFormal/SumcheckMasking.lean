import Mathlib
import AspisFormal.CoreHidingPMF

/-!
# Sumcheck masking by a precommitted random oracle

This file isolates the algebra behind the v5 sumcheck mask. It models a table
`F : Fin n → K`, a uniformly random mask table `R`, and the challenge mixture

`Q = R + η F`.

The mask oracle and its claimed sum must be fixed before `η` is sampled. This
is the self-reduction used by the cited zero-knowledge sumcheck constructions;
it is not the same as sampling ten unrelated zero-sum round polynomials. The
commitment encoding and hash are deliberately outside this finite model.

The results below establish the following facts in the Lean kernel.

* If `F` sums to zero, then the joint distribution of `sum R` and any
  deterministic observation of `Q` is independent of `F`.
* If the honest mask-sum claim is used and `η ≠ 0`, acceptance of the mixed sum
  forces `F` to sum to zero.
* More generally, for fixed `F`, `R`, and a claimed sum, a false original sum
  can satisfy the mixed sum equation for at most one value of `η`.

The first item covers the serialized sumcheck transcript because Fiat--Shamir
replay is a deterministic function of `Q` once the hash function and public
context are fixed. It deliberately does **not** cover a joint view that also
contains any observation of `R`, including its commitment root or correlated
PCS openings. Binding those values and the component-(A) masked evaluations to
a published simulator remains a named v5 wire obligation; no claim about that
joint view is made here.
-/

open scoped BigOperators ENNReal

namespace AspisSumcheckMasking

variable {K : Type*} [Field K] {n : ℕ}

/-- Sum of a table over its finite index set. -/
def tableSum (f : Fin n → K) : K := ∑ i, f i

/-- The challenge mixture of a real summand and a precommitted mask oracle. -/
def maskedOracle (eta : K) (real mask : Fin n → K) : Fin n → K :=
  mask + eta • real

/-- The mixed table sums to `sum(mask) + eta * sum(real)`. -/
theorem tableSum_maskedOracle (eta : K) (real mask : Fin n → K) :
    tableSum (maskedOracle eta real mask)
      = tableSum mask + eta * tableSum real := by
  simp [tableSum, maskedOracle, Finset.sum_add_distrib, Finset.mul_sum]

/-- With the honest mask-sum claim and a nonzero challenge, an accepted mixed
sum implies that the original summand has sum zero. -/
theorem original_sum_eq_zero_of_mixed_sum
    (eta : K) (real mask : Fin n → K) (heta : eta ≠ 0)
    (hclaim : tableSum (maskedOracle eta real mask) = tableSum mask) :
    tableSum real = 0 := by
  rw [tableSum_maskedOracle] at hclaim
  have hzero : eta * tableSum real = 0 := by
    linear_combination hclaim
  exact (mul_eq_zero.mp hzero).resolve_left heta

/-- For fixed pre-challenge data, a false original sum can make the mixed sum
equal a claimed value for at most one challenge. -/
theorem accepting_challenge_unique
    (real mask : Fin n → K) (beta eta₁ eta₂ : K)
    (hreal : tableSum real ≠ 0)
    (h₁ : tableSum (maskedOracle eta₁ real mask) = beta)
    (h₂ : tableSum (maskedOracle eta₂ real mask) = beta) :
    eta₁ = eta₂ := by
  rw [tableSum_maskedOracle] at h₁ h₂
  have hzero : (eta₁ - eta₂) * tableSum real = 0 := by
    linear_combination h₁ - h₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hreal)

section Distribution

variable [Fintype K]

/-- A full uniform mask makes the entire mixed oracle independent of the real
summand. This is the identity-map instance of `CoreHidingPMF`. -/
theorem maskedOracle_pmf_indep
    (eta : K) (real₁ real₂ : Fin n → K) :
    (PMF.uniformOfFintype (Fin n → K)).map (fun mask => maskedOracle eta real₁ mask)
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => maskedOracle eta real₂ mask) := by
  classical
  simpa [maskedOracle, add_comm] using
    (view_pmf_indep_of_witness (LinearMap.id)
      (Function.surjective_id : Function.Surjective (LinearMap.id :
        (Fin n → K) →ₗ[K] (Fin n → K)))
      (eta • real₁) (eta • real₂))

/-- Applying any deterministic transcript or observation function preserves
the witness-independent distribution. -/
theorem observed_maskedOracle_pmf_indep
    {View : Type*} (observe : (Fin n → K) → View)
    (eta : K) (real₁ real₂ : Fin n → K) :
    (PMF.uniformOfFintype (Fin n → K)).map
        (fun mask => observe (maskedOracle eta real₁ mask))
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => observe (maskedOracle eta real₂ mask)) := by
  classical
  have h := congrArg (fun distribution : PMF (Fin n → K) => distribution.map observe)
    (maskedOracle_pmf_indep eta real₁ real₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- The public mask-sum claim together with any deterministic transcript of the
mixed oracle is witness-independent when the real summand sums to zero.

For a valid summand, `sum(mask) = sum(mask + eta * real)`, so the whole pair is
a deterministic observation of the uniformly shifted mixed oracle. -/
theorem maskSum_and_observation_pmf_indep
    {View : Type*} (observe : (Fin n → K) → View)
    (eta : K) (real₁ real₂ : Fin n → K)
    (hreal₁ : tableSum real₁ = 0) (hreal₂ : tableSum real₂ = 0) :
    (PMF.uniformOfFintype (Fin n → K)).map
        (fun mask => (tableSum mask, observe (maskedOracle eta real₁ mask)))
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => (tableSum mask, observe (maskedOracle eta real₂ mask))) := by
  classical
  let view : (Fin n → K) → K × View := fun mixed => (tableSum mixed, observe mixed)
  have h₁ : (fun mask => (tableSum mask, observe (maskedOracle eta real₁ mask)))
      = (fun mask => view (maskedOracle eta real₁ mask)) := by
    funext mask
    simp [view, tableSum_maskedOracle, hreal₁]
  have h₂ : (fun mask => (tableSum mask, observe (maskedOracle eta real₂ mask)))
      = (fun mask => view (maskedOracle eta real₂ mask)) := by
    funext mask
    simp [view, tableSum_maskedOracle, hreal₂]
  rw [h₁, h₂]
  exact observed_maskedOracle_pmf_indep view eta real₁ real₂

end Distribution

end AspisSumcheckMasking

#print axioms AspisSumcheckMasking.tableSum_maskedOracle
#print axioms AspisSumcheckMasking.original_sum_eq_zero_of_mixed_sum
#print axioms AspisSumcheckMasking.accepting_challenge_unique
#print axioms AspisSumcheckMasking.maskedOracle_pmf_indep
#print axioms AspisSumcheckMasking.observed_maskedOracle_pmf_indep
#print axioms AspisSumcheckMasking.maskSum_and_observation_pmf_indep
