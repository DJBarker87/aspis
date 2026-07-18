import AspisFormal.V5RankOneOpeningHiding
import AspisFormal.V5InactiveClaimMasking
import AspisFormal.V5CompactTerminalOptimized

/-!
# Joint hiding of the carried copy-inactive claim given the terminal opening

`V5InactiveClaimMasking` proves a scalar one-time-pad statement: with a uniform
pivot and a nonzero lane coefficient `gammaB`, the released copy-inactive claim
`base + gammaB * pivot` has a law independent of the witness base.  That
statement treats the carried claim **in isolation**.  The v5 verifier, however,
also sees the authenticated terminal opening, and the terminal value and the
carried claim are functionals of the **same** mask assignment — they are
correlated, and modelling them as two independently padded scalars would be
wrong.  This file proves the joint statements.

Setting: a finite field `K`, a finite `K`-module `M` (the mask space), the
authenticated terminal functional `terminal : M →ₗ[K] K`, the carried
inactive-claim functional `inactive : M →ₗ[K] K`, and a lane coefficient
`gammaB : K` with the explicit hypothesis `gammaB ≠ 0`.  The released joint
view of a mask `m` is the pair

  `(terminal m, base + gammaB * inactive m)`

with `base : K` the witness-dependent part of the carried claim.  Both
coordinates are evaluated at the **one** sampled mask; the correlation between
the terminal opening and the carried claim is carried by the sampling model,
not assumed away.

Statements proved.

1. **Kernel-witness ⟺ restricted surjectivity**
   (`inactive_on_ker_surjective_iff_kernel_witness`).  For the scalar target
   `K`, the pivot-shaped fact "some point of `LinearMap.ker terminal` is not
   annihilated by `inactive`" is *equivalent* to surjectivity of `inactive`
   restricted to `LinearMap.ker terminal` (one nonvanishing point scales onto
   every target).  The surjectivity side is the running hypothesis below; the
   equivalence is exported so the pivot facts can discharge it.

2. **Joint hiding, kernel-shift model**
   (`terminalOpening_hides_carriedClaim_on_ker`).  Fix the revealed terminal
   value `t`, two witnesses `m₁ m₂` with `terminal mᵢ = t`, and two witness
   bases `base₁ base₂`.  Randomising by one uniform `k` in
   `LinearMap.ker terminal`, the joint view
   `(terminal (mᵢ + k), baseᵢ + gammaB * inactive (mᵢ + k))` has the same
   `PMF` for `i = 1, 2`.  Route: `released_view_indep_on_ker` (the engine of
   `V5RankOneOpeningHiding.terminalOpening_hides_released_view`) instantiated
   with the scaled released map `pivotMap gammaB ∘ₗ inactive`, with
   `gammaB ≠ 0` carrying surjectivity through the scaling.

3. **Joint hiding, conditional-fibre model**
   (`terminalOpening_hides_carriedClaim`, the headline).  The same conclusion
   with the mask sampled uniformly from the affine fibre `{m // terminal m = t}`
   — the honest model of "condition on the authenticated terminal opening
   being `t`" — transported from statement 2 by `kerFibreEquiv`.  Hiding of
   the carried claim survives conditioning on the terminal opening.

4. **Pivot connection** (`inactive_on_ker_surjective_of_pivot`,
   `terminalOpening_hides_carriedClaim_of_pivot`).  The named hypotheses
   `hpivot_ker : terminal pivotWitness = 0` and
   `hpivot_inactive : inactive pivotWitness ≠ 0` — "the reserved pivot
   coordinate lies in the terminal functional's kernel and feeds the inactive
   claim" — imply the surjectivity hypothesis via statement 1, hence the joint
   hiding.  At this abstract level neither pivot fact is proved; for the
   transcribed deployed covector, `hpivot_ker` is discharged in section 8
   below (`terminalDotFunctional_pivot_eq_zero`, the row-993
   terminal-weight-zero fact), while `hpivot_inactive` remains supplied by the
   fixture layout (the pivot coordinate enters the inactive claim with the
   lane coefficient; see section 10).

5. **Non-vacuity** (`terminalOpening_hides_carriedClaim_instantiable`, and
   `_zmod`).  A concrete instantiation `M = Fin 2 → K`, `terminal` the first
   coordinate, `inactive` the second, `pivotWitness = ![0, 1]` satisfies every
   hypothesis, including over the concrete finite field `ZMod p`.

6. **Named unresolved interfaces** (`Prop` definitions, **not** proved):
   commitment binding of the pivot coordinate, deployed-terminal
   correspondence, post-commitment sampling of the nonzero `gammaB`, and
   exactness of the released-view serialization.

7. **The joint law under the single shared pivot scalar**
   (`sharedPivotView_law`, `sharedPivotView_pmf_indep`,
   `sharedPivotView_pmf_indep_of_fresh`, `terminal_inactive_pair_law`,
   `terminal_inactive_pair_pmf_indep`, `sharedPivotView_carried_marginal`).
   One uniform scalar `p` is drawn once, and the whole view
   `p ↦ (terminal (m + p • k), inactive (m + p • k), released (m + p • k))`
   is pushed forward through it: the same reused pivot coordinate feeds the
   authenticated terminal opening, the carried inactive claim, and the rest of
   the released view.  The exact joint law is computed: `terminal k = 0` pins
   the terminal coordinate at `t`, `inactive k ≠ 0` makes the inactive
   coordinate uniform, and the residual coordinate stays correlated with the
   inactive coordinate through the shared sample, with slope
   `(inactive k)⁻¹ • released k`.  Witness-independence of the joint law holds
   exactly on the correlation invariant
   `released m - ((inactive k)⁻¹ * inactive m) • released k`; for a fresh
   pivot (`released k = 0`) this collapses to equality of residual views.  The
   inactive marginal of the joint law is literally the
   `V5InactiveClaimMasking.carriedClaim` one-time-pad law.

8. **Kernel-pivot bridge and the full triple**
   (`prodKer_surjective_of_kernel_pivot`,
   `terminalOpening_inactiveClaim_joint_hiding`).  A pivot in the terminal
   kernel with `inactive k ≠ 0` that the residual view does not read
   (`released k = 0`) upgrades the released-only restricted surjectivity used
   by `terminalOpening_hides_released_view` to joint `(inactive, released)`
   restricted surjectivity.  Hence the full triple view
   `u ↦ (terminal (m + u), inactive (m + u), released (m + u))`, under one
   uniform draw `u` from `LinearMap.ker terminal` feeding all three
   coordinates, is witness-independent on the fibre `terminal m = t`, for
   witnesses differing arbitrarily in inactive and residual components.

9. **Row-993 connection to the deployed compact terminal covector**
   (`pivotRow`, `terminalWeights_pivotRow_eq_zero`, `terminalDotFunctional`,
   `terminalDotFunctional_pivot_eq_zero`,
   `represented1024_optimizedInit_pivotRow_eq_zero`, and the `deployed_*`
   theorems).  Row 993 is the reserved pivot coordinate; its weight in the
   transcribed covector `terminalWeights` is proved zero, so the row-993 basis
   direction lies in the kernel of the deployed terminal functional —
   `hpivot_ker` / `terminal k = 0` is discharged, not assumed, for the
   transcription, and the fact is transported through the proved non-`rfl`
   optimized-evaluator correspondence of `V5CompactTerminalOptimized` to the
   deployed state machine's initial represented covector.

10. **Non-vacuity of the added layers** (`example_restricted_surjective`,
    `joint_triple_hypotheses_instantiable`, `joint_hiding_nonvacuous`,
    `sharedPivot_hiding_nonvacuous`).  `M = Fin 3 → K` with the three
    coordinate projections and pivot `![0, 1, 0]` satisfies every premise of
    the shared-pivot and full-triple theorems simultaneously.

11. **Lane-coefficient discharge wrappers**
    (`PivotCoefficientIsGammaB`, `pivot_inactive_nonzero_of_gammaB`,
    `deployed_joint_hiding_from_gammaB`).  The named interface "the carried
    claim reads the pivot with coefficient exactly `gammaB`" plus the
    `gammaB ≠ 0` hypothesis discharge `hpivot_inactive`; the deployed capstone
    consumes them with the proved row-993 kernel fact.

**Scope of the claim.**  Everything proved here is linear algebra over a finite
field plus finite uniform-`PMF` reasoning.  Nothing is claimed about any
deployed commitment scheme, hash, transcript ordering, or serialization; every
such edge enters as an explicit named hypothesis or as one of the unresolved
interface `Prop`s.  Statements 1–8, 10 and 11 are independent of
`AspisFormal.V5CompactTerminalOptimized`; statement 9 imports it, after
checking in this session that it compiles cleanly, that every theorem it
exports reports axioms within `{propext, Classical.choice, Quot.sound}`, and
that its optimized-evaluator theorem
`optimizedCompactFinalDot_eq_compactComponentBFinalDot` is not provable by
`rfl` (the definitional-equality check fails), so the correspondence is a real
theorem, not a definitional restatement.  The identification of the Lean
transcriptions with the compiled Rust remains that module's named
`RustCompactFoldModel` / `QM31FieldModel` interface obligations.
-/

open scoped ENNReal

namespace AspisV5InactiveClaimJointHiding

open AspisV5RankOneOpeningHiding AspisV5InactiveClaimMasking

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-! ## 1. Kernel-witness ⟺ restricted surjectivity

For the scalar codomain `K`, surjectivity of `inactive` restricted to
`LinearMap.ker terminal` is equivalent to the existence of one kernel point on
which `inactive` does not vanish: scaling that single point hits every target.
The right-hand side is the hypothesis consumed by the hiding engine; the
left-hand side is the shape in which the pivot facts arrive. -/

/-- **One nonvanishing kernel point ⟺ the restricted inactive functional is
surjective.**  Forward: scale the witness `k` by `v * (inactive k)⁻¹` to hit
any target `v` (the kernel is closed under scaling).  Backward: a preimage of
`1` is a nonvanishing kernel point. -/
theorem inactive_on_ker_surjective_iff_kernel_witness
    (terminal inactive : M →ₗ[K] K) :
    (∃ k ∈ LinearMap.ker terminal, inactive k ≠ 0) ↔
      Function.Surjective (inactive ∘ₗ (LinearMap.ker terminal).subtype) := by
  constructor
  · rintro ⟨k, hk, hne⟩ v
    refine ⟨⟨(v * (inactive k)⁻¹) • k, Submodule.smul_mem _ _ hk⟩, ?_⟩
    show inactive ((v * (inactive k)⁻¹) • k) = v
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  · intro hsurj
    obtain ⟨k, hk⟩ := hsurj 1
    refine ⟨(k : M), k.2, ?_⟩
    have hk' : inactive (k : M) = 1 := hk
    rw [hk']
    exact one_ne_zero

/-! ## 2. The pivot connection into the surjectivity hypothesis -/

/-- **The pivot facts imply the running surjectivity hypothesis.**  The two
named hypotheses are exactly the facts the surrounding development owes:

* `hpivot_ker : terminal pivotWitness = 0` — the reserved Component-B pivot
  coordinate has terminal weight zero.  At this abstract level it is a named
  hypothesis; for the transcribed deployed covector it is discharged by the
  row-993 terminal-weight-zero fact `terminalDotFunctional_pivot_eq_zero`
  proved in section 8 below.
* `hpivot_inactive : inactive pivotWitness ≠ 0` — the pivot coordinate enters
  the carried inactive claim.  Expected from the fixture layout, where the
  pivot coordinate appears in the inactive-claim functional with the nonzero
  lane coefficient; see the discharge wrapper in section 10.

Neither fact is proved at this abstract level. -/
theorem inactive_on_ker_surjective_of_pivot
    (terminal inactive : M →ₗ[K] K) (pivotWitness : M)
    (hpivot_ker : terminal pivotWitness = 0)
    (hpivot_inactive : inactive pivotWitness ≠ 0) :
    Function.Surjective (inactive ∘ₗ (LinearMap.ker terminal).subtype) :=
  (inactive_on_ker_surjective_iff_kernel_witness terminal inactive).mp
    ⟨pivotWitness, LinearMap.mem_ker.mpr hpivot_ker, hpivot_inactive⟩

/-! ## 3. Joint hiding of the carried claim given the terminal opening

The released claim is `base + gammaB * inactive m`, i.e.
`carriedClaim base gammaB (inactive m)` in the vocabulary of
`V5InactiveClaimMasking`; the alignment is definitional
(`carriedClaim_of_inactive`).  The joint view pairs it with the terminal value
of the **same** mask. -/

/-- **Definitional alignment with the scalar file.**  The joint statements
below speak about `base + gammaB * inactive m`; this is literally
`V5InactiveClaimMasking.carriedClaim` evaluated at the inactive functional's
value on the mask, so the scalar one-time-pad statement and the joint
statement are about the same released quantity.  (This lemma is definitional
by design — it is the naming bridge, not a hiding claim.) -/
theorem carriedClaim_of_inactive (base gammaB : K) (inactive : M →ₗ[K] K) (m : M) :
    carriedClaim base gammaB (inactive m) = base + gammaB * inactive m := rfl

/-- **Scaling by the nonzero lane coefficient preserves restricted
surjectivity.**  This is the only place `gammaB ≠ 0` is consumed: the released
map fed to the hiding engine is `pivotMap gammaB ∘ₗ inactive`, and a preimage
of `gammaB⁻¹ * v` under the restricted `inactive` is a preimage of `v` under
the scaled map. -/
theorem scaled_inactive_on_ker_surjective
    (terminal inactive : M →ₗ[K] K) (gammaB : K) (hgammaB : gammaB ≠ 0)
    (hsurj : Function.Surjective (inactive ∘ₗ (LinearMap.ker terminal).subtype)) :
    Function.Surjective
      ((pivotMap gammaB ∘ₗ inactive) ∘ₗ (LinearMap.ker terminal).subtype) := by
  intro v
  obtain ⟨k, hk⟩ := hsurj (gammaB⁻¹ * v)
  refine ⟨k, ?_⟩
  have hk' : inactive (k : M) = gammaB⁻¹ * v := hk
  show gammaB * inactive (k : M) = v
  rw [hk', mul_inv_cancel_left₀ hgammaB]

/-- **Factoring the joint view through the constant terminal coordinate.**  On
the kernel coset of a witness `m` with `terminal m = t`, the joint view is the
scalar released view `base + gammaB * inactive m + (pivotMap gammaB ∘ₗ inactive) k`
post-composed with the deterministic pairing `x ↦ (t, x)`.  This is where the
correlation is handled: the terminal coordinate of the joint pair is not an
independently masked value but the value of `terminal` at the same sample,
constantly `t` because the sample stays inside the fibre. -/
theorem jointView_factor
    (terminal inactive : M →ₗ[K] K) (gammaB : K) {t : K} (m : M)
    (hm : terminal m = t) (base : K) :
    (fun k : LinearMap.ker terminal =>
        (terminal (m + (k : M)), base + gammaB * inactive (m + (k : M))))
      = (fun x : K => (t, x)) ∘
        (fun k : LinearMap.ker terminal =>
          base + gammaB * inactive m + (pivotMap gammaB ∘ₗ inactive) (k : M)) := by
  funext k
  have hk : terminal (k : M) = 0 := LinearMap.mem_ker.mp k.2
  simp only [Function.comp_apply, LinearMap.comp_apply, pivotMap_apply, map_add, hk, hm,
    add_zero, mul_add, add_assoc]

section Distribution

variable [Fintype K] [DecidableEq K] [Fintype M]

/-- **Joint hiding given the terminal opening, kernel-shift model.**  Fix the
revealed terminal value `t`.  For any two witnesses `m₁ m₂` realising it and
any two witness bases `base₁ base₂`, randomising by **one** uniform
`k ∈ LinearMap.ker terminal` makes the joint released view

  `(terminal (mᵢ + k), baseᵢ + gammaB * inactive (mᵢ + k))`

— terminal opening and carried claim evaluated at the same mask — identically
distributed for `i = 1, 2`, provided `inactive` restricted to
`LinearMap.ker terminal` is surjective (equivalently, by
`inactive_on_ker_surjective_iff_kernel_witness`, provided some kernel point
feeds the inactive claim) and `gammaB ≠ 0`. -/
theorem terminalOpening_hides_carriedClaim_on_ker
    (terminal inactive : M →ₗ[K] K) (gammaB : K) (hgammaB : gammaB ≠ 0)
    (hsurj : Function.Surjective (inactive ∘ₗ (LinearMap.ker terminal).subtype))
    (t : K) (m₁ m₂ : M) (h₁ : terminal m₁ = t) (h₂ : terminal m₂ = t)
    (base₁ base₂ : K) :
    (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun k : LinearMap.ker terminal =>
          (terminal (m₁ + (k : M)), base₁ + gammaB * inactive (m₁ + (k : M))))
      = (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun k : LinearMap.ker terminal =>
          (terminal (m₂ + (k : M)), base₂ + gammaB * inactive (m₂ + (k : M)))) := by
  have hview := released_view_indep_on_ker terminal (pivotMap gammaB ∘ₗ inactive)
    (scaled_inactive_on_ker_surjective terminal inactive gammaB hgammaB hsurj)
    (base₁ + gammaB * inactive m₁) (base₂ + gammaB * inactive m₂)
  rw [jointView_factor terminal inactive gammaB m₁ h₁ base₁,
    jointView_factor terminal inactive gammaB m₂ h₂ base₂,
    ← PMF.map_comp, ← PMF.map_comp]
  exact congrArg (fun q : PMF K => q.map (fun x : K => (t, x))) hview

/-- **Joint hiding given the terminal opening, conditional-fibre model (the
main theorem).**  Sample the mask uniformly from the affine fibre
`{m // terminal m = t}` — the honest model of conditioning on the
authenticated terminal opening being `t` — and release the joint pair

  `(terminal m, base + gammaB * inactive m)`

with both coordinates evaluated at the one sampled mask.  For any two witness
bases `base₁ base₂` the joint law is the same, provided `inactive` restricted
to `LinearMap.ker terminal` is surjective and `gammaB ≠ 0`.  Hiding of the
carried copy-inactive claim therefore survives conditioning on the terminal
opening; the correlation between the two released values (functionals of the
same mask) is inside the model, not assumed independent.  Transport from the
kernel-shift model is `kerFibreEquiv` + `uniform_map_equiv`. -/
theorem terminalOpening_hides_carriedClaim
    (terminal inactive : M →ₗ[K] K) (gammaB : K) (hgammaB : gammaB ≠ 0)
    (hsurj : Function.Surjective (inactive ∘ₗ (LinearMap.ker terminal).subtype))
    (t : K) [hfib : Nonempty {m : M // terminal m = t}] (base₁ base₂ : K) :
    (PMF.uniformOfFintype {m : M // terminal m = t}).map
        (fun m : {m : M // terminal m = t} =>
          (terminal (m : M), base₁ + gammaB * inactive (m : M)))
      = (PMF.uniformOfFintype {m : M // terminal m = t}).map
        (fun m : {m : M // terminal m = t} =>
          (terminal (m : M), base₂ + gammaB * inactive (m : M))) := by
  obtain ⟨⟨m_t, ht⟩⟩ := id hfib
  have huni : PMF.uniformOfFintype {m : M // terminal m = t}
      = (PMF.uniformOfFintype (LinearMap.ker terminal)).map
          (kerFibreEquiv terminal t m_t ht) :=
    (uniform_map_equiv (kerFibreEquiv terminal t m_t ht)).symm
  have hcomp : ∀ base : K,
      ((fun m : {m : M // terminal m = t} =>
          (terminal (m : M), base + gammaB * inactive (m : M))) ∘
        (kerFibreEquiv terminal t m_t ht))
      = fun k : LinearMap.ker terminal =>
          (terminal (m_t + (k : M)), base + gammaB * inactive (m_t + (k : M))) := by
    intro base
    funext k
    show (terminal ((k : M) + m_t), base + gammaB * inactive ((k : M) + m_t))
        = (terminal (m_t + (k : M)), base + gammaB * inactive (m_t + (k : M)))
    rw [add_comm (k : M) m_t]
  rw [huni, PMF.map_comp, PMF.map_comp, hcomp base₁, hcomp base₂]
  exact terminalOpening_hides_carriedClaim_on_ker terminal inactive gammaB hgammaB hsurj
    t m_t m_t ht ht base₁ base₂

/-- **The main theorem from the pivot facts.**  The named hypotheses
`hpivot_ker` and `hpivot_inactive` (see `inactive_on_ker_surjective_of_pivot`
for their provenance and expected discharge) imply the joint hiding of the
carried claim given the terminal opening. -/
theorem terminalOpening_hides_carriedClaim_of_pivot
    (terminal inactive : M →ₗ[K] K) (gammaB : K) (hgammaB : gammaB ≠ 0)
    (pivotWitness : M)
    (hpivot_ker : terminal pivotWitness = 0)
    (hpivot_inactive : inactive pivotWitness ≠ 0)
    (t : K) [Nonempty {m : M // terminal m = t}] (base₁ base₂ : K) :
    (PMF.uniformOfFintype {m : M // terminal m = t}).map
        (fun m : {m : M // terminal m = t} =>
          (terminal (m : M), base₁ + gammaB * inactive (m : M)))
      = (PMF.uniformOfFintype {m : M // terminal m = t}).map
        (fun m : {m : M // terminal m = t} =>
          (terminal (m : M), base₂ + gammaB * inactive (m : M))) :=
  terminalOpening_hides_carriedClaim terminal inactive gammaB hgammaB
    (inactive_on_ker_surjective_of_pivot terminal inactive pivotWitness
      hpivot_ker hpivot_inactive)
    t base₁ base₂

end Distribution

/-! ## 4. Non-vacuity

The hypotheses are jointly satisfiable: over any finite field, the mask space
`Fin 2 → K` with `terminal` the first coordinate, `inactive` the second, and
`pivotWitness = ![0, 1]` satisfies `terminal pivotWitness = 0`,
`inactive pivotWitness ≠ 0`, and every fibre of `terminal` is nonempty. -/

/-- Every fibre of the first-coordinate functional on `Fin 2 → K` is nonempty:
`![t, 0]` realises the terminal value `t`. -/
instance projZeroFibre_nonempty {K : Type*} [Field K] (t : K) :
    Nonempty {m : Fin 2 → K // (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) m = t} :=
  ⟨⟨![t, 0], by simp⟩⟩

/-- **Non-vacuity of the main theorem.**  The concrete instantiation
`M = Fin 2 → K`, `terminal = proj 0`, `inactive = proj 1`,
`pivotWitness = ![0, 1]` satisfies every hypothesis of
`terminalOpening_hides_carriedClaim_of_pivot`, so the joint-hiding conclusion
holds for it: the statement is not vacuous. -/
theorem terminalOpening_hides_carriedClaim_instantiable
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (gammaB : K) (hgammaB : gammaB ≠ 0) (t base₁ base₂ : K) :
    (PMF.uniformOfFintype
        {m : Fin 2 → K // (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) m = t}).map
        (fun m : {m : Fin 2 → K // (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) m = t} =>
          ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) (m : Fin 2 → K),
            base₁ + gammaB * (LinearMap.proj 1 : (Fin 2 → K) →ₗ[K] K) (m : Fin 2 → K)))
      = (PMF.uniformOfFintype
        {m : Fin 2 → K // (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) m = t}).map
        (fun m : {m : Fin 2 → K // (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) m = t} =>
          ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) (m : Fin 2 → K),
            base₂ + gammaB * (LinearMap.proj 1 : (Fin 2 → K) →ₗ[K] K) (m : Fin 2 → K))) :=
  terminalOpening_hides_carriedClaim_of_pivot
    (LinearMap.proj 0) (LinearMap.proj 1) gammaB hgammaB
    ![0, 1] (by simp) (by simp) t base₁ base₂

/-- **Non-vacuity over a concrete finite field.**  The typeclass hypotheses
`[Field K] [Fintype K] [DecidableEq K]` are themselves satisfiable: specialise
to `ZMod p` for a prime `p`. -/
theorem terminalOpening_hides_carriedClaim_instantiable_zmod
    (p : ℕ) [Fact p.Prime]
    (gammaB : ZMod p) (hgammaB : gammaB ≠ 0) (t base₁ base₂ : ZMod p) :
    (PMF.uniformOfFintype
        {m : Fin 2 → ZMod p //
          (LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) m = t}).map
        (fun m : {m : Fin 2 → ZMod p //
            (LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) m = t} =>
          ((LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) (m : Fin 2 → ZMod p),
            base₁ + gammaB *
              (LinearMap.proj 1 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) (m : Fin 2 → ZMod p)))
      = (PMF.uniformOfFintype
        {m : Fin 2 → ZMod p //
          (LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) m = t}).map
        (fun m : {m : Fin 2 → ZMod p //
            (LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) m = t} =>
          ((LinearMap.proj 0 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) (m : Fin 2 → ZMod p),
            base₂ + gammaB *
              (LinearMap.proj 1 : (Fin 2 → ZMod p) →ₗ[ZMod p] ZMod p) (m : Fin 2 → ZMod p))) :=
  terminalOpening_hides_carriedClaim_instantiable gammaB hgammaB t base₁ base₂

/-! ## 5. Named unresolved interfaces

The theorems above close the mathematical gap only.  The following `Prop`s are
the remaining, deliberately **unproved** edges between the mathematics and the
deployed system.  Each is a definition, not a theorem: nothing here discharges
them.  They are named so that later modules (or an audit) can point at exactly
which edge they close. -/

/-- **Unresolved interface: the pre-challenge commitment binds the pivot
coordinate.**  Two mask assignments with the same pre-challenge commitment
have the same pivot coordinate.  This is the binding fact that stops a prover
from choosing the pivot after seeing `gammaB`; it is owed by the commitment
layer in the injective-commitment model of
`AspisFormal.V5SumcheckTranscriptBinding` (compare
`componentBState_eq_of_injective_commitment` there), or computationally by its
`ComponentBComputationalBinding` game.  Not proved here. -/
def PivotBoundByPreChallengeCommitment
    {Commitment MaskAssignment K : Type*}
    (commit : MaskAssignment → Commitment)
    (pivotCoordinate : MaskAssignment → K) : Prop :=
  ∀ a₁ a₂ : MaskAssignment, commit a₁ = commit a₂ →
    pivotCoordinate a₁ = pivotCoordinate a₂

/-- **Unresolved interface: the deployed verifier's terminal functional is the
Lean `terminal`.**  The functional the deployed verifier actually evaluates on
the mask assignment agrees pointwise with the linear map `terminal` used in
the theorems above.  Rust/verifier correspondence; not proved here. -/
def DeployedTerminalMatchesModel
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (deployedTerminal : M → K) (terminal : M →ₗ[K] K) : Prop :=
  ∀ m : M, deployedTerminal m = terminal m

/-- **Unresolved interface: the deployed `gammaB` is the nonzero Component-B
lane coefficient sampled after the pivot commitment.**  The lane coefficient
the deployed verifier uses equals the model's `gammaB`, is derived from a
transcript state that already contains the pivot commitment (so the pivot
cannot depend on it), and is nonzero.  The nonzeroness half instantiates the
explicit `gammaB ≠ 0` hypothesis of the theorems above; the derivation half is
transcript-schedule correspondence (compare the `FiatShamirSchedule` model in
`AspisFormal.V5SumcheckTranscriptBinding`).  Not proved here. -/
def GammaBIsPostCommitmentLaneCoefficient
    {K Commitment : Type*} [Field K]
    (deriveLaneCoefficient : Commitment → K)
    (pivotCommitment : Commitment) (gammaB : K) : Prop :=
  deriveLaneCoefficient pivotCommitment = gammaB ∧ gammaB ≠ 0

/-- **Unresolved interface: the released-view serialization is exactly the
joint pair.**  The bytes the prover releases for this opening are an injective
encoding of exactly the pair `(t, claim)` — the authenticated terminal value
and the carried inactive claim — with no coordinate duplicated under a second
encoding and none omitted.  If the serialization leaked any further functional
of the same mask, the two-coordinate joint view analysed above would not be
the whole released view, and the hiding theorem would not apply to the
deployed byte stream.  Serialization correspondence; not proved here. -/
def ReleasedViewSerializesExactlyTheJointPair
    {K Bytes : Type*}
    (encodePair : K × K → Bytes)
    (releasedBytes : Bytes) (t claim : K) : Prop :=
  Function.Injective encodePair ∧ releasedBytes = encodePair (t, claim)

/-! ## 6. The joint view under the single shared pivot scalar

`V5InactiveClaimMasking` reserves ONE fresh mask coordinate.  The honest model
of that reservation is a single uniform scalar `p` scaling a fixed pivot
direction `k : M`, with every revealed value evaluated on the same masked
vector `m + p • k`.  Nothing is padded independently: the terminal opening,
the carried inactive claim, and the rest of the released view are three
functionals of one sample. -/

section SharedPivot

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The joint released view under ONE draw of the pivot scalar `p`: the
authenticated terminal opening, the carried copy-inactive claim, and the rest
of the released view, all evaluated on the same masked witness `m + p • k`.
The single `p` feeds every coordinate. -/
def sharedPivotView (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k m : M)
    (p : K) : K × K × V :=
  (terminal (m + p • k), inactive (m + p • k), released (m + p • k))

/-- Deterministic skeleton of the shared-pivot view: with the pivot in the
terminal kernel, the terminal coordinate is pinned at `t`, the inactive
coordinate is the scalar one-time pad `inactive m + inactive k * p`, and the
residual view moves along `released k`.  All three coordinates are driven by
the same `p`. -/
theorem sharedPivotView_apply (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V)
    (k m : M) (t : K) (hk : terminal k = 0) (hm : terminal m = t) (p : K) :
    sharedPivotView terminal inactive released k m p
      = (t, inactive m + inactive k * p, released m + p • released k) := by
  simp only [sharedPivotView, map_add, map_smul, smul_eq_mul, hk, hm, mul_zero, add_zero,
    mul_comm p (inactive k)]

/-- The affine reparametrisation `p ↦ base + gamma * p` of the pivot line: a
bijection of `K` whenever `gamma ≠ 0`.  Realises "the released inactive claim
determines the pivot sample". -/
def pivotReparam (base gamma : K) (hgamma : gamma ≠ 0) : K ≃ K where
  toFun p := base + gamma * p
  invFun c := gamma⁻¹ * (c - base)
  left_inv p := by
    show gamma⁻¹ * (base + gamma * p - base) = p
    rw [add_sub_cancel_left, inv_mul_cancel_left₀ hgamma]
  right_inv c := by
    show base + gamma * (gamma⁻¹ * (c - base)) = c
    rw [mul_inv_cancel_left₀ hgamma, add_sub_cancel]

theorem pivotReparam_apply (base gamma : K) (hgamma : gamma ≠ 0) (p : K) :
    pivotReparam base gamma hgamma p = base + gamma * p := rfl

section SharedPivotDistribution

variable [Fintype K]

/-- **The exact joint law under the single shared pivot.**  Pushing the
uniform pivot law through the shared-pivot view gives: terminal coordinate
degenerate at `t`, inactive coordinate uniform, and residual coordinate the
affine function of the *same* sample with slope `(inactive k)⁻¹ • released k`
— the residual correlation between the carried claim and the rest of the
view.  The witness enters only through the intercept
`released m - ((inactive k)⁻¹ * inactive m) • released k`. -/
theorem sharedPivotView_law (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V)
    (k m : M) (t : K) (hk : terminal k = 0) (hgamma : inactive k ≠ 0)
    (hm : terminal m = t) :
    (PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m)
      = (PMF.uniformOfFintype K).map (fun c : K =>
          (t, c, (released m - ((inactive k)⁻¹ * inactive m) • released k)
            + ((inactive k)⁻¹ * c) • released k)) := by
  have hfun : sharedPivotView terminal inactive released k m
      = (fun c : K =>
          (t, c, (released m - ((inactive k)⁻¹ * inactive m) • released k)
            + ((inactive k)⁻¹ * c) • released k))
        ∘ ⇑(pivotReparam (inactive m) (inactive k) hgamma) := by
    funext p
    simp only [Function.comp_apply, pivotReparam_apply,
      sharedPivotView_apply terminal inactive released k m t hk hm p, Prod.mk.injEq]
    refine ⟨trivial, trivial, ?_⟩
    rw [mul_add, inv_mul_cancel_left₀ hgamma, add_smul]
    abel
  rw [hfun, ← PMF.map_comp, uniform_map_equiv]

/-- **Joint hiding under the single shared pivot, general correlated form.**
Two witnesses with the same authenticated terminal value and the same
correlation invariant `released m - ((inactive k)⁻¹ * inactive m) • released k`
produce identical joint laws for the triple (terminal opening, carried
inactive claim, residual view) under one shared uniform pivot.  The
hypotheses are exactly the pivot-kernel fact and the nonzero pivot
coefficient; no coordinate is masked separately. -/
theorem sharedPivotView_pmf_indep (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V)
    (k : M) (t : K) (m₁ m₂ : M) (hk : terminal k = 0) (hgamma : inactive k ≠ 0)
    (h₁ : terminal m₁ = t) (h₂ : terminal m₂ = t)
    (hcarried : released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
      = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k) :
    (PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m₁)
      = (PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m₂) := by
  rw [sharedPivotView_law terminal inactive released k m₁ t hk hgamma h₁,
    sharedPivotView_law terminal inactive released k m₂ t hk hgamma h₂, hcarried]

/-- **Joint hiding under the single shared pivot, fresh-pivot form.**  If the
pivot is a fresh coordinate that the residual released view does not read
(`released k = 0`), the correlation invariant collapses to the residual view
itself: any two witnesses that agree on the residual released view and the
terminal value have identical joint laws, however much their inactive base
claims differ.  This is the v5 configuration: the reserved Component-B pivot
row feeds only the terminal covector (with weight zero) and the carried
inactive claim. -/
theorem sharedPivotView_pmf_indep_of_fresh (terminal inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (t : K) (m₁ m₂ : M) (hk : terminal k = 0)
    (hgamma : inactive k ≠ 0) (hfresh : released k = 0) (h₁ : terminal m₁ = t)
    (h₂ : terminal m₂ = t) (hreleased : released m₁ = released m₂) :
    (PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m₁)
      = (PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m₂) := by
  refine sharedPivotView_pmf_indep terminal inactive released k t m₁ m₂ hk hgamma h₁ h₂ ?_
  rw [hfresh, smul_zero, smul_zero, sub_zero, sub_zero, hreleased]

/-- **The revealed pair.**  The joint law of the authenticated terminal
opening and the carried inactive claim under the shared pivot is exactly
`(t, uniform)`: the terminal coordinate is a constant function of the same
sample that makes the inactive coordinate uniform.  In particular the pair
law carries no witness information at all beyond `t`. -/
theorem terminal_inactive_pair_law (terminal inactive : M →ₗ[K] K) (k m : M) (t : K)
    (hk : terminal k = 0) (hgamma : inactive k ≠ 0) (hm : terminal m = t) :
    (PMF.uniformOfFintype K).map
        (fun p : K => (terminal (m + p • k), inactive (m + p • k)))
      = (PMF.uniformOfFintype K).map (fun c : K => (t, c)) := by
  have hfun : (fun p : K => (terminal (m + p • k), inactive (m + p • k)))
      = (fun c : K => (t, c)) ∘ ⇑(pivotReparam (inactive m) (inactive k) hgamma) := by
    funext p
    simp only [Function.comp_apply, pivotReparam_apply, map_add, map_smul, smul_eq_mul, hk,
      mul_zero, add_zero, hm, mul_comm p (inactive k)]
  rw [hfun, ← PMF.map_comp, uniform_map_equiv]

/-- Witness-independence of the revealed pair, immediate from the exact pair
law. -/
theorem terminal_inactive_pair_pmf_indep (terminal inactive : M →ₗ[K] K) (k : M) (t : K)
    (m₁ m₂ : M) (hk : terminal k = 0) (hgamma : inactive k ≠ 0) (h₁ : terminal m₁ = t)
    (h₂ : terminal m₂ = t) :
    (PMF.uniformOfFintype K).map
        (fun p : K => (terminal (m₁ + p • k), inactive (m₁ + p • k)))
      = (PMF.uniformOfFintype K).map
        (fun p : K => (terminal (m₂ + p • k), inactive (m₂ + p • k))) := by
  rw [terminal_inactive_pair_law terminal inactive k m₁ t hk hgamma h₁,
    terminal_inactive_pair_law terminal inactive k m₂ t hk hgamma h₂]

/-- The inactive-coordinate marginal of the shared-pivot view is exactly the
scalar one-time-pad law of `V5InactiveClaimMasking.carriedClaim`: the joint
statements refine that file's scalar statement rather than replacing it. -/
theorem sharedPivotView_carried_marginal (terminal inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m : M) :
    ((PMF.uniformOfFintype K).map (sharedPivotView terminal inactive released k m)).map
        (fun view => view.2.1)
      = (PMF.uniformOfFintype K).map (carriedClaim (inactive m) (inactive k)) := by
  rw [PMF.map_comp]
  congr 1
  funext p
  show inactive (m + p • k) = carriedClaim (inactive m) (inactive k) p
  rw [map_add, map_smul, smul_eq_mul]
  show inactive m + p * inactive k = inactive m + inactive k * p
  rw [mul_comm]

end SharedPivotDistribution

end SharedPivot

/-! ## 7. The kernel-pivot bridge and the full triple -/

section KernelTriple

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **The kernel pivot upgrades released-only surjectivity to joint
surjectivity.**  If the pivot `k` lies in `LinearMap.ker terminal`, carries a
nonzero inactive coefficient, and is fresh for the residual view
(`released k = 0`), then surjectivity of `released` restricted to the terminal
kernel — the exact hypothesis of `terminalOpening_hides_released_view` —
upgrades to surjectivity of the joint restricted map
`m ↦ (inactive m, released m)`.  Proof: hit the residual target with the old
hypothesis, then correct the inactive coordinate along the pivot, which moves
neither the terminal value nor the residual view. -/
theorem prodKer_surjective_of_kernel_pivot (terminal inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (hk : terminal k = 0) (hgamma : inactive k ≠ 0)
    (hfresh : released k = 0)
    (hrel : Function.Surjective (released ∘ₗ (LinearMap.ker terminal).subtype)) :
    Function.Surjective ((inactive.prod released) ∘ₗ (LinearMap.ker terminal).subtype) := by
  rintro ⟨c, v⟩
  obtain ⟨u, hu⟩ := hrel v
  have hval : released (u : M) = v := hu
  set s : K := (c - inactive (u : M)) * (inactive k)⁻¹ with hs
  refine ⟨⟨(u : M) + s • k, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, map_add, map_smul, hk, smul_zero, add_zero]
    exact LinearMap.mem_ker.mp u.2
  · show (inactive ((u : M) + s • k), released ((u : M) + s • k)) = (c, v)
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [map_add, map_smul, smul_eq_mul, hs, mul_assoc, inv_mul_cancel₀ hgamma, mul_one,
        add_sub_cancel]
    · rw [map_add, map_smul, hfresh, smul_zero, add_zero]
      exact hval

/-- **The full-triple joint theorem.**  Fix the authenticated terminal opening
to `t`.  One uniform mask draw `u` from `LinearMap.ker terminal` feeds the
terminal opening, the carried copy-inactive claim, and the rest of the
released view simultaneously; the three revealed coordinates are functions of
the same masked vector `mᵢ + u`, so every correlation between them is
retained.  Under the pivot facts (`terminal k = 0`, `inactive k ≠ 0`,
`released k = 0`) and the released-only restricted surjectivity already used
by the rank-one opening theorem, the joint law is independent of which
witness realises the terminal value `t`.  The witnesses may differ
arbitrarily in their inactive and residual components. -/
theorem terminalOpening_inactiveClaim_joint_hiding {V : Type*} [AddCommGroup V]
    [Module K V] [Fintype K] [DecidableEq K] [Fintype M] [FiniteDimensional K V]
    (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k : M)
    (hk : terminal k = 0) (hgamma : inactive k ≠ 0) (hfresh : released k = 0)
    (hrel : Function.Surjective (released ∘ₗ (LinearMap.ker terminal).subtype))
    (t : K) (m₁ m₂ : M) (h₁ : terminal m₁ = t) (h₂ : terminal m₂ = t) :
    (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun u : LinearMap.ker terminal =>
          (terminal (m₁ + (u : M)), inactive (m₁ + (u : M)), released (m₁ + (u : M))))
      = (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun u : LinearMap.ker terminal =>
          (terminal (m₂ + (u : M)), inactive (m₂ + (u : M)), released (m₂ + (u : M)))) := by
  have h := terminalOpening_hides_released_view terminal (inactive.prod released)
    (prodKer_surjective_of_kernel_pivot terminal inactive released k hk hgamma hfresh hrel)
    t m₁ m₂ h₁ h₂
  simpa only [LinearMap.coe_prod, Function.prod_apply] using h

end KernelTriple

/-! ## 8. Row-993 connection to the deployed compact terminal covector -/

section DeployedConnection

open AspisV5CompactTerminal

/-- Row 993: the reserved fresh pivot coordinate of the deployed 1,024-row
component-B layout (row 992 is the initial-state row; the coefficient blocks
end at row 987). -/
def pivotRow : Row := ⟨993, by omega⟩

/-- **The transcribed terminal covector has weight zero at the pivot row.**
Row 993 is neither the initial row 992 nor any coefficient row
`32 * selector + degree`: selectors are at most 30 and stored degrees below
28, so coefficient rows stop at 987. -/
theorem terminalWeights_pivotRow_eq_zero (point : Round → K) (scale : K) :
    terminalWeights point scale pivotRow = 0 := by
  classical
  have hne : pivotRow ≠ initialRow := by decide
  simp only [terminalWeights, Pi.add_apply, Finset.sum_apply, basis]
  rw [if_neg hne, zero_add]
  refine Finset.sum_eq_zero fun index _ => if_neg fun hEq => ?_
  have hval : (pivotRow : ℕ) = 32 * blockSelector index.1 + (index.2 : ℕ) := by
    rw [hEq, coefficientRow_val]
  have hp : (pivotRow : ℕ) = 993 := rfl
  have hsel := blockSelector_le_thirty index.1
  have hdeg : (index.2 : ℕ) < 28 := index.2.isLt
  omega

/-- The deployed compact component-B terminal check, packaged as the linear
functional `message ↦ dot (terminalWeights point scale) message` on the
1,024-row message space (spelled as the covector-weighted sum of coordinate
projections; `terminalDotFunctional_apply` restates it as the `dot`). -/
def terminalDotFunctional (point : Round → K) (scale : K) : (Row → K) →ₗ[K] K :=
  ∑ row, terminalWeights point scale row • LinearMap.proj row

theorem terminalDotFunctional_apply (point : Round → K) (scale : K) (message : Row → K) :
    terminalDotFunctional point scale message
      = dot (terminalWeights point scale) message := by
  simp only [terminalDotFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, dot]

/-- **The pivot direction lies in the kernel of the deployed terminal
functional.**  This discharges `hpivot_ker` / `terminal k = 0` for the
transcribed covector: it is proved from the layout, not assumed. -/
theorem terminalDotFunctional_pivot_eq_zero (point : Round → K) (scale : K) :
    terminalDotFunctional point scale (basis pivotRow 1) = 0 := by
  rw [terminalDotFunctional_apply, dot_basis_right, terminalWeights_pivotRow_eq_zero,
    zero_mul]

/-- The deployed *optimized* evaluator's initial machine state also represents
weight zero at the pivot row: row 993 has no register in the state machine.
Obtained by transporting `terminalWeights_pivotRow_eq_zero` through the proved
(non-`rfl`) correspondence `represented1024_optimizedInit_eq_terminalWeights`
of `V5CompactTerminalOptimized`. -/
theorem represented1024_optimizedInit_pivotRow_eq_zero (point : Fin 10 → K) (scale : K) :
    AspisV5CompactTerminalOptimized.represented1024
      (AspisV5CompactTerminalOptimized.optimizedInit point scale) pivotRow = 0 := by
  rw [AspisV5CompactTerminalOptimized.represented1024_optimizedInit_eq_terminalWeights]
  exact terminalWeights_pivotRow_eq_zero point scale

/- From here on the terminal functional participates only through its proved
interface lemmas; its 1,024-term body is sealed against definitional
unfolding so that instance unification never evaluates it. -/
attribute [irreducible] terminalDotFunctional

/-- The conditional-fibre pair theorem (statement 3) instantiated at the
deployed terminal functional with the row-993 pivot direction: `hpivot_ker`
is supplied by `terminalDotFunctional_pivot_eq_zero`.  The nonzero pivot
coefficient stays an explicit named hypothesis. -/
theorem deployed_terminalOpening_hides_carriedClaim [Fintype K] [DecidableEq K]
    (point : Round → K) (scale : K) (inactive : (Row → K) →ₗ[K] K) (gammaB : K)
    (hgammaB : gammaB ≠ 0) (hpivot_inactive : inactive (basis pivotRow 1) ≠ 0) (t : K)
    [Nonempty {m : Row → K // terminalDotFunctional point scale m = t}]
    (base₁ base₂ : K) :
    (PMF.uniformOfFintype {m : Row → K // terminalDotFunctional point scale m = t}).map
        (fun m : {m : Row → K // terminalDotFunctional point scale m = t} =>
          (terminalDotFunctional point scale (m : Row → K),
            base₁ + gammaB * inactive (m : Row → K)))
      = (PMF.uniformOfFintype {m : Row → K // terminalDotFunctional point scale m = t}).map
        (fun m : {m : Row → K // terminalDotFunctional point scale m = t} =>
          (terminalDotFunctional point scale (m : Row → K),
            base₂ + gammaB * inactive (m : Row → K))) :=
  @terminalOpening_hides_carriedClaim_of_pivot K (Row → K) _ _ _ _ _ _
    (terminalDotFunctional point scale) inactive gammaB hgammaB (basis pivotRow 1)
    (terminalDotFunctional_pivot_eq_zero point scale) hpivot_inactive t _ base₁ base₂

/-- The full-triple joint theorem (statement 8) instantiated at the deployed
terminal functional with the row-993 pivot direction: `terminal k = 0` is
supplied by `terminalDotFunctional_pivot_eq_zero`.  The nonzero pivot
coefficient, pivot freshness for the residual view, and restricted
surjectivity remain explicit named hypotheses. -/
theorem deployed_terminalOpening_inactiveClaim_joint_hiding {V : Type*} [AddCommGroup V]
    [Module K V] [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    (point : Round → K) (scale : K) (inactive : (Row → K) →ₗ[K] K)
    (released : (Row → K) →ₗ[K] V) (hgamma : inactive (basis pivotRow 1) ≠ 0)
    (hfresh : released (basis pivotRow 1) = 0)
    (hrel : Function.Surjective
      (released ∘ₗ (LinearMap.ker (terminalDotFunctional point scale)).subtype))
    (t : K) (m₁ m₂ : Row → K) (h₁ : terminalDotFunctional point scale m₁ = t)
    (h₂ : terminalDotFunctional point scale m₂ = t) :
    (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₁ + (u : Row → K)),
            inactive (m₁ + (u : Row → K)), released (m₁ + (u : Row → K))))
      = (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₂ + (u : Row → K)),
            inactive (m₂ + (u : Row → K)), released (m₂ + (u : Row → K)))) :=
  @terminalOpening_inactiveClaim_joint_hiding K (Row → K) _ _ _ V _ _ _ _ _ _
    (terminalDotFunctional point scale) inactive released (basis pivotRow 1)
    (terminalDotFunctional_pivot_eq_zero point scale) hgamma hfresh hrel t m₁ m₂ h₁ h₂

/-- The exact revealed-pair law (statement 7) at the deployed terminal
functional: one shared scalar pivot at row 993 pins the authenticated
terminal opening at `t` and makes the carried inactive claim uniform,
jointly. -/
theorem deployed_sharedPivot_pair_law [Fintype K] (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (hgamma : inactive (basis pivotRow 1) ≠ 0) (t : K)
    (m : Row → K) (hm : terminalDotFunctional point scale m = t) :
    (PMF.uniformOfFintype K).map
        (fun p : K => (terminalDotFunctional point scale (m + p • basis pivotRow 1),
          inactive (m + p • basis pivotRow 1)))
      = (PMF.uniformOfFintype K).map (fun c : K => (t, c)) :=
  terminal_inactive_pair_law (terminalDotFunctional point scale) inactive
    (basis pivotRow 1) m t (terminalDotFunctional_pivot_eq_zero point scale) hgamma hm

end DeployedConnection

/-! ## 9. Non-vacuity of the added layers

Mask space `Fin 3 → K`; `terminal`, `inactive`, `released` are the three
coordinate projections; the pivot is `![0, 1, 0]`.  Every premise of the
shared-pivot and full-triple theorems holds simultaneously for this model. -/

section TripleNonVacuity

/-- The restricted-surjectivity hypothesis is satisfiable: with
`terminal = proj 0` and `released = proj 2` on `Fin 3 → K`, the joint map is
surjective, hence so is the restriction to the terminal kernel. -/
theorem example_restricted_surjective :
    Function.Surjective ((LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) ∘ₗ
      (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K)).subtype) := by
  apply releasedKer_surjective_of_prod_surjective
  intro pair
  exact ⟨![pair.1, 0, pair.2], rfl⟩

/-- **Every premise of the full-triple theorem, instantiated at once.**  The
pivot facts, freshness, restricted surjectivity, and the two fibre conditions
all hold for the concrete projections, pivot `![0, 1, 0]`, and witnesses
`![t, a₁, b₁]`, `![t, a₂, b₂]`. -/
theorem joint_triple_hypotheses_instantiable (t a₁ a₂ b₁ b₂ : K) :
    (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] = 0
      ∧ (LinearMap.proj 1 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] ≠ 0
      ∧ (LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] = 0
      ∧ Function.Surjective ((LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) ∘ₗ
          (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K)).subtype)
      ∧ (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) ![t, a₁, b₁] = t
      ∧ (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) ![t, a₂, b₂] = t :=
  ⟨rfl, one_ne_zero, rfl, example_restricted_surjective, rfl, rfl⟩

/-- **Non-vacuity of the full-triple theorem.**  All hypotheses hold for the
concrete projections and pivot `![0, 1, 0]`, for any two witnesses
`![t, a₁, b₁]`, `![t, a₂, b₂]` sharing only the terminal value: the joint
triple law is witness-independent for them. -/
theorem joint_hiding_nonvacuous [Fintype K] [DecidableEq K] (t a₁ a₂ b₁ b₂ : K) :
    (PMF.uniformOfFintype (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K))).map
        (fun u : LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) =>
          ((LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) (![t, a₁, b₁] + (u : Fin 3 → K)),
            (LinearMap.proj 1 : (Fin 3 → K) →ₗ[K] K) (![t, a₁, b₁] + (u : Fin 3 → K)),
            (LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) (![t, a₁, b₁] + (u : Fin 3 → K))))
      = (PMF.uniformOfFintype (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K))).map
        (fun u : LinearMap.ker (LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) =>
          ((LinearMap.proj 0 : (Fin 3 → K) →ₗ[K] K) (![t, a₂, b₂] + (u : Fin 3 → K)),
            (LinearMap.proj 1 : (Fin 3 → K) →ₗ[K] K) (![t, a₂, b₂] + (u : Fin 3 → K)),
            (LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) (![t, a₂, b₂] + (u : Fin 3 → K)))) :=
  @terminalOpening_inactiveClaim_joint_hiding K (Fin 3 → K) _ _ _ K _ _ _ _ _ _
    (LinearMap.proj 0) (LinearMap.proj 1) (LinearMap.proj 2) ![0, 1, 0] rfl one_ne_zero
    rfl example_restricted_surjective t ![t, a₁, b₁] ![t, a₂, b₂] rfl rfl

/-- **Non-vacuity of the shared-scalar-pivot theorems.**  The fresh-pivot
joint independence holds for the concrete projections, pivot `![0, 1, 0]`,
and witnesses `![t, a₁, b]`, `![t, a₂, b]` differing exactly in the inactive
base claim. -/
theorem sharedPivot_hiding_nonvacuous [Fintype K] (t a₁ a₂ b : K) :
    (PMF.uniformOfFintype K).map
        (sharedPivotView (LinearMap.proj 0) (LinearMap.proj 1)
          (LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] ![t, a₁, b])
      = (PMF.uniformOfFintype K).map
        (sharedPivotView (LinearMap.proj 0) (LinearMap.proj 1)
          (LinearMap.proj 2 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] ![t, a₂, b]) :=
  sharedPivotView_pmf_indep_of_fresh (LinearMap.proj 0) (LinearMap.proj 1)
    (LinearMap.proj 2) ![0, 1, 0] t ![t, a₁, b] ![t, a₂, b] rfl one_ne_zero rfl rfl rfl rfl

end TripleNonVacuity

/-! ## 10. Lane-coefficient discharge wrappers -/

section GammaBDischarge

/-- **Named interface: the carried claim reads the pivot with coefficient
exactly `gammaB`.**  Deployment correspondence between the inactive-claim
functional and the lane layout; not proved here. -/
def PivotCoefficientIsGammaB (inactive : M →ₗ[K] K) (pivotWitness : M)
    (gammaB : K) : Prop :=
  inactive pivotWitness = gammaB

/-- The two named lane facts — the pivot coefficient is `gammaB` and `gammaB`
is nonzero — discharge `hpivot_inactive`. -/
theorem pivot_inactive_nonzero_of_gammaB (inactive : M →ₗ[K] K) (pivotWitness : M)
    (gammaB : K) (hcoeff : PivotCoefficientIsGammaB inactive pivotWitness gammaB)
    (hgammaB : gammaB ≠ 0) : inactive pivotWitness ≠ 0 := by
  rw [PivotCoefficientIsGammaB] at hcoeff
  rw [hcoeff]
  exact hgammaB

open AspisV5CompactTerminal in
/-- **Deployed capstone.**  The full-triple joint hiding at the transcribed
terminal covector, with the row-993 kernel fact *proved*
(`terminalDotFunctional_pivot_eq_zero`) and the nonzero pivot coefficient
supplied through the named lane interfaces (`PivotCoefficientIsGammaB` and
`gammaB ≠ 0`, the nonzeroness half of
`GammaBIsPostCommitmentLaneCoefficient`).  Commitment binding of the pivot
(`PivotBoundByPreChallengeCommitment`) and serialization exactness
(`ReleasedViewSerializesExactlyTheJointPair`) remain free-standing named
obligations. -/
theorem deployed_joint_hiding_from_gammaB {V : Type*} [AddCommGroup V] [Module K V]
    [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    (point : Round → K) (scale : K) (inactive : (Row → K) →ₗ[K] K)
    (released : (Row → K) →ₗ[K] V) (gammaB : K)
    (hcoeff : PivotCoefficientIsGammaB inactive (basis pivotRow 1) gammaB)
    (hgammaB : gammaB ≠ 0) (hfresh : released (basis pivotRow 1) = 0)
    (hrel : Function.Surjective
      (released ∘ₗ (LinearMap.ker (terminalDotFunctional point scale)).subtype))
    (t : K) (m₁ m₂ : Row → K) (h₁ : terminalDotFunctional point scale m₁ = t)
    (h₂ : terminalDotFunctional point scale m₂ = t) :
    (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₁ + (u : Row → K)),
            inactive (m₁ + (u : Row → K)), released (m₁ + (u : Row → K))))
      = (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₂ + (u : Row → K)),
            inactive (m₂ + (u : Row → K)), released (m₂ + (u : Row → K)))) :=
  @terminalOpening_inactiveClaim_joint_hiding K (Row → K) _ _ _ V _ _ _ _ _ _
    (terminalDotFunctional point scale) inactive released (basis pivotRow 1)
    (terminalDotFunctional_pivot_eq_zero point scale)
    (pivot_inactive_nonzero_of_gammaB inactive (basis pivotRow 1) gammaB hcoeff hgammaB)
    hfresh hrel t m₁ m₂ h₁ h₂

/-- The lane interfaces are satisfiable (`proj 1`, pivot `![0, 1, 0]`,
`gammaB = 1`), so the discharge wrappers are not vacuous. -/
theorem pivotCoefficient_interface_nonvacuous {K : Type*} [Field K] :
    PivotCoefficientIsGammaB (LinearMap.proj 1 : (Fin 3 → K) →ₗ[K] K) ![0, 1, 0] 1 :=
  rfl

end GammaBDischarge

/-! ## Axiom audit -/

#print axioms inactive_on_ker_surjective_iff_kernel_witness
#print axioms inactive_on_ker_surjective_of_pivot
#print axioms carriedClaim_of_inactive
#print axioms scaled_inactive_on_ker_surjective
#print axioms jointView_factor
#print axioms terminalOpening_hides_carriedClaim_on_ker
#print axioms terminalOpening_hides_carriedClaim
#print axioms terminalOpening_hides_carriedClaim_of_pivot
#print axioms projZeroFibre_nonempty
#print axioms terminalOpening_hides_carriedClaim_instantiable
#print axioms terminalOpening_hides_carriedClaim_instantiable_zmod
#print axioms PivotBoundByPreChallengeCommitment
#print axioms DeployedTerminalMatchesModel
#print axioms GammaBIsPostCommitmentLaneCoefficient
#print axioms ReleasedViewSerializesExactlyTheJointPair
#print axioms sharedPivotView
#print axioms sharedPivotView_apply
#print axioms pivotReparam
#print axioms sharedPivotView_law
#print axioms sharedPivotView_pmf_indep
#print axioms sharedPivotView_pmf_indep_of_fresh
#print axioms terminal_inactive_pair_law
#print axioms terminal_inactive_pair_pmf_indep
#print axioms sharedPivotView_carried_marginal
#print axioms prodKer_surjective_of_kernel_pivot
#print axioms terminalOpening_inactiveClaim_joint_hiding
#print axioms pivotRow
#print axioms terminalWeights_pivotRow_eq_zero
#print axioms terminalDotFunctional
#print axioms terminalDotFunctional_apply
#print axioms terminalDotFunctional_pivot_eq_zero
#print axioms represented1024_optimizedInit_pivotRow_eq_zero
#print axioms deployed_terminalOpening_hides_carriedClaim
#print axioms deployed_terminalOpening_inactiveClaim_joint_hiding
#print axioms deployed_sharedPivot_pair_law
#print axioms example_restricted_surjective
#print axioms joint_triple_hypotheses_instantiable
#print axioms joint_hiding_nonvacuous
#print axioms sharedPivot_hiding_nonvacuous
#print axioms PivotCoefficientIsGammaB
#print axioms pivot_inactive_nonzero_of_gammaB
#print axioms deployed_joint_hiding_from_gammaB
#print axioms pivotCoefficient_interface_nonvacuous

end AspisV5InactiveClaimJointHiding
