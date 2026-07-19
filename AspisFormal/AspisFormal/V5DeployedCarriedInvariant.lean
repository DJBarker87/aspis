import Mathlib

/-!
# The capstone-v2 premise `hCarriedB` as a finite kernel certificate

`V5ConditionalHidingCapstoneV2.conditional_complete_view_hiding_v2` consumes
one Component-B premise that no theorem in this repository discharges for the
deployed artefacts: the correlated invariant

  `hCarriedB : releasedB mB₁ - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB`
  `          = releasedB mB₂ - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB`

(the shape is transcribed verbatim from that file; this module imports only
Mathlib and re-derives everything it needs).  This module reduces that
premise, for all witness pairs at once, to an exact finite obligation a
deployment audit can check: a chosen spanning generator list together with `d` vector
equations `Q (gens i) = 0` for the corrected released map

  `Q m = released m - ((inactive k)⁻¹ * inactive m) • released k`.

Contents, all kernel-checked with axioms within
`{propext, Classical.choice, Quot.sound}`:

1. `corrected_eq_iff_diff_zero` / `corrected_eq_iff_mem_ker`: the pairwise
   invariant `Q m₁ = Q m₂` is exactly `Q (m₂ - m₁) = 0`, i.e. membership of
   the difference in `ker Q`.
2. `carriedInvariant_forall_iff_le_ker`: the invariant holds for *every*
   pair with difference in a legal-difference submodule `ΔB` **iff**
   `ΔB ≤ ker Q`.  Both directions: the obligation is exact, not merely
   sufficient.
3. `gens_check_iff_le_ker`: for any family spanning `ΔB`, checking
   `Q (gens i) = 0` on the generators is sufficient **and** complete for
   `ΔB ≤ ker Q`.
4. `CarriedCertificate` + `carriedInvariant_of_certificate` /
   `certificate_of_le_ker`: the `Fin d` certificate `Prop` and its checker.
   The certificate asserts nothing about surjectivity and nothing about
   freshness; it contains exactly the spanning and vanishing facts consumed
   by the checker.
5. `correctedReleased_of_fresh`, `le_ker_of_fresh`,
   `carriedInvariant_of_fresh`: the fresh-pivot route `released k = 0` is
   only a corollary (`Q = released` under freshness).  The `ZMod 2` model
   `egCertificate` / `egBeyondFresh` has `released k = 1 ≠ 0`, a generator
   outside the pivot line, and a legal pair on which the *raw* residual view
   differs — the certificate route reaches strictly beyond freshness.
6. `egNegativeModel`: with a legal-difference space **not** contained in
   `ker Q`, a concrete pair with difference in it violates `hCarriedB` and
   the shared-pivot joint laws are distinct `PMF`s
   (`jointLaws_differ_of_corrected_ne`: the corrected value is computable
   from the joint view, so the invariant is an observable — necessary, not
   just sufficient).

## Deployed inspection (READ-ONLY; feature-gated v5 candidate artefacts)

The Rust below is the v5 *candidate*: `v5_spend_messages.rs` states it "is
not a complete v5 proof builder" and carries
`V5_CU_STRESS_ONLY_STATUS = "CU stress only: … no v5 security claim is made"`
(`crates/aspis-prover/src/v5_spend_messages.rs:14-17, 88-89`).  Every claim
here is a citation, not a formalisation.

**The pivot.**  Row 993 is the dependent balancing coordinate of the B lane:
`V5StructuredBLane::encode` writes
`values[993] = -Σ_{copy-inactive rows} values[row]`
(`crates/aspis-prover/src/v5_spend_messages.rs:97, 269-301`, pivot write at
`294-296`; host fixture `crates/aspis-prover/src/v5_b_structured_rank.rs:34,
185`).  Row 993 is itself copy-inactive
(`v5_b_structured_rank.rs:270`; verifier-side group table
`programs/aspis-verifier/src/v5_cu_probe.rs:144-148`, row 993 ∈ group 6,
mask `0xffff`).  So `inactive (e₉₉₃) = 1` for the binary copy-inactive
covector, and one unit of the B-lane row-993 cell enters the γ-combined
message with lane coefficient `γ^17`
(`v5_spend_messages.rs:557-583`, `powers[16 + 1]`, `V5_COMPONENT_B_LANE = 1`
at line 64).

**Released functionals that read row 993** (`released (e₉₉₃) ≠ 0`
generically — freshness fails, which is why the v2 premise is `hCarriedB`):

* the three per-lane multilinear claims of the B lane at `z`,
  `successor(z)`, `xor12(z)` —
  `crates/aspis-prover/src/v5_split_layer_zero.rs:196`
  (`multilinear_eval_extension`); a multilinear `eq` covector at a generic
  point weights every row, including 993; released on the wire claims table
  and absorbed pre-κ (`crates/aspis-prover/src/v5_real_host_proof.rs:595-598`);
* the released carried inactive claim: the γ-combined message summed over
  the copy-inactive rows, which include 993
  (`crates/aspis-prover/src/v5_real_host_proof.rs:627-636`);
* the PCS layer-zero C2 query openings: opened B-lane codeword values read
  row 993 through the circle-encoder row basis
  (host enumeration of the released view: 72 raw openings + 3 MLE values +
  1 dense terminal = 76 functionals,
  `crates/aspis-prover/src/v5_b_structured_rank.rs:314-382`).

**Not a reader**: the structured terminal covector is zero at and beyond
row 993 (`v5_split_layer_zero.rs:153-171` writes only row 992 and the ten
28-coefficient blocks; asserted `v5_b_structured_rank.rs:247`; pinned
on-chain `programs/aspis-verifier/src/v5_cu_probe.rs:2884, 2895`; the
fenced standalone-dot path additionally skips the pivot row,
`v5_cu_probe.rs:1692-1703`).  This is the deployed side of the capstone's
`hB_pivot_ker` (`terminalB kB = 0`), not of `hCarriedB`.

**Corrected covectors.**  No corrected released functionals exist in the
Rust.  With `inactive (e₉₉₃) = 1` the correction is
`φ ↦ φ - φ(e₉₉₃) · (copy-inactive sum)` per released functional `φ`; this
subtraction is performed nowhere in the deployed code — it is exactly the
Lean-side object `correctedReleased` below.

**Legal-difference space `ΔB`: ABSENT.**  No executable legal-difference
space exists for the B lane.  The Component-C modules disclaim one
explicitly (`crates/aspis-prover/src/v5_component_c_fmat.rs:9`,
`v5_component_c_emat.rs:7`: "This file defines no legal-difference space,
`Delta`, C-DEC certificate, …"); nothing B-side defines one either.  The
nearest artefacts — the linear serializer `V5StructuredBLane::encode`
(271 mask-state + 255 pad free coordinates) and the test-only pad-basis
directions `encode_pad_basis` (`v5_b_structured_rank.rs:190-199`, each
`e_{224+p}` with a `-e₉₉₃` compensation when the pad row is copy-inactive) —
are not designated as the witness-difference space the hiding statement
quantifies over, and the released covectors are transcript-parametric
(`z`-dependent MLE weights, schedule-dependent query positions).  Honest
consequence: no concrete finite matrix can be transcribed today, `ΔB` is
not invented here, and the deployed obligation is stated as the named
interface `UnmetDeployment.DeployedCarriedCertificateInterface` (a `Prop`,
not proved) consumed by the conditional checker
`UnmetDeployment.deployed_carried_invariant_of_interface`.

**One sufficient artifact to close the interface**: (i) a transcription of the
deployed residual released view as `releasedB : MB →ₗ[K] VB` on the
1024-row B-lane space at pinned transcript parameters, with the binary
copy-inactive covector as `inactiveB` and `kB = e₉₉₃`; (ii) a finite
generator list `gens : Fin d → MB` with a kernel-checked
`Submodule.span K (Set.range gens) = ΔB` designating the legal B-lane
witness differences the protocol quantifies over; (iii) the `d`
kernel-checked equations `correctedReleased inactiveB releasedB kB (gens i)
= 0`.  For this chosen spanning-family presentation, items (ii)--(iii) are a
sound-and-complete check of the kernel containment.  Other presentations of
the same containment (for example, a direct proof) are not ruled out.

**Headline.**  Everything deployed-facing in this module is conditional.
Neither the real deployed released map nor legal-difference generators are
present as artefacts, so this module asserts **no** deployed applicability:
it proves that *if* the named interface is discharged, the capstone-v2
premise `hCarriedB` follows for every quantified pair.  Exactness is claimed
only for the finite generator check relative to its supplied spanning family,
not for this particular deployment-interface packaging globally.
-/

namespace AspisV5DeployedCarriedInvariant

section CorrectedMap

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-! ## 1. The corrected released map `Q` -/

/-- The corrected released map
`Q m = released m - ((inactive k)⁻¹ * inactive m) • released k`, packaged as
a `LinearMap`.  This is the unique linear map agreeing with `released` on
`ker inactive` and killing the pivot direction `k` (when `inactive k ≠ 0`);
the capstone-v2 premise `hCarriedB` is precisely the statement that `Q`
takes equal values on the two witnesses. -/
def correctedReleased (inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k : M) :
    M →ₗ[K] V :=
  released - LinearMap.smulRight ((inactive k)⁻¹ • inactive) (released k)

@[simp] theorem correctedReleased_apply (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m : M) :
    correctedReleased inactive released k m
      = released m - ((inactive k)⁻¹ * inactive m) • released k := by
  simp [correctedReleased, smul_eq_mul]

/-- The capstone-v2 premise `hCarriedB` for a pair, in its verbatim spelling,
is exactly equality of the corrected released map on the pair.  This is the
naming bridge between the deployed premise and the kernel obligation. -/
theorem carriedInvariant_iff_corrected_eq (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m₁ m₂ : M) :
    (released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
        = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k)
      ↔ correctedReleased inactive released k m₁
          = correctedReleased inactive released k m₂ := by
  rw [correctedReleased_apply, correctedReleased_apply]

/-- With a nonzero pivot coefficient the corrected map kills the pivot
direction: the correction subtracts exactly the pivot's residual image. -/
theorem correctedReleased_pivot (inactive : M →ₗ[K] K) (released : M →ₗ[K] V)
    {k : M} (hk : inactive k ≠ 0) :
    correctedReleased inactive released k k = 0 := by
  rw [correctedReleased_apply, inv_mul_cancel₀ hk, one_smul, sub_self]

/-! ## 2. Item 1: the pairwise invariant is kernel membership of the
difference -/

/-- **Item 1a.**  `hCarriedB` for the pair `(m₁, m₂)` — that is,
`Q m₁ = Q m₂` — holds iff the corrected map vanishes on the difference. -/
theorem corrected_eq_iff_diff_zero (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m₁ m₂ : M) :
    correctedReleased inactive released k m₁
        = correctedReleased inactive released k m₂
      ↔ correctedReleased inactive released k (m₂ - m₁) = 0 := by
  rw [map_sub, sub_eq_zero, eq_comm]

/-- **Item 1b.**  Equivalently: the difference lies in `ker Q`. -/
theorem corrected_eq_iff_mem_ker (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m₁ m₂ : M) :
    correctedReleased inactive released k m₁
        = correctedReleased inactive released k m₂
      ↔ m₂ - m₁ ∈ LinearMap.ker (correctedReleased inactive released k) := by
  rw [LinearMap.mem_ker]
  exact corrected_eq_iff_diff_zero inactive released k m₁ m₂

/-! ## 3. Item 2: quantifying over a legal-difference submodule -/

/-- **Item 2 (kernel form).**  The invariant holds for *every* pair whose
difference lies in `ΔB` iff `ΔB ≤ ker Q`.  The forward direction
instantiates the pair `(0, d)`; the backward direction is item 1.  Both
directions hold: the containment is the exact obligation, not an
over-approximation. -/
theorem carried_forall_iff_le_ker (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (ΔB : Submodule K M) :
    (∀ m₁ m₂ : M, m₂ - m₁ ∈ ΔB →
        correctedReleased inactive released k m₁
          = correctedReleased inactive released k m₂)
      ↔ ΔB ≤ LinearMap.ker (correctedReleased inactive released k) := by
  constructor
  · intro h d hd
    have h0 := h 0 d (by simpa using hd)
    exact LinearMap.mem_ker.mpr (h0.symm.trans (map_zero _))
  · intro hle m₁ m₂ hd
    exact (corrected_eq_iff_mem_ker inactive released k m₁ m₂).mpr (hle hd)

/-- **Item 2 (verbatim form).**  The same equivalence with the left side
spelled exactly as the capstone-v2 premise `hCarriedB`. -/
theorem carriedInvariant_forall_iff_le_ker (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (ΔB : Submodule K M) :
    (∀ m₁ m₂ : M, m₂ - m₁ ∈ ΔB →
        released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
          = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k)
      ↔ ΔB ≤ LinearMap.ker (correctedReleased inactive released k) := by
  simp only [carriedInvariant_iff_corrected_eq]
  exact carried_forall_iff_le_ker inactive released k ΔB

/-! ## 4. Item 3: the generator check is sound and complete -/

/-- **Item 3.**  If `gens` spans `ΔB`, then checking `Q (gens i) = 0` on the
generators is **sufficient and complete** for `ΔB ≤ ker Q`: the forward
direction is `Submodule.span_le` (kernels are submodules), the backward
direction evaluates the containment on each generator.  Thus this is an
exact check for the chosen spanning family.  The family may contain zero,
duplicate, or linearly dependent generators, so no generator-level
irredundancy is claimed. -/
theorem gens_check_iff_le_ker {ι : Type*} (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (ΔB : Submodule K M) (gens : ι → M)
    (hspan : Submodule.span K (Set.range gens) = ΔB) :
    (∀ i, correctedReleased inactive released k (gens i) = 0)
      ↔ ΔB ≤ LinearMap.ker (correctedReleased inactive released k) := by
  constructor
  · intro hchk
    rw [← hspan, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    simpa using hchk i
  · intro hle i
    exact LinearMap.mem_ker.mp
      (hle (hspan ▸ Submodule.subset_span (Set.mem_range_self i)))

/-- **The exactness headline.**  Composing items 2 and 3: for a spanning
family, the capstone-v2 premise `hCarriedB` over all legal pairs is
*equivalent* to the finite generator check for that chosen spanning family. -/
theorem carriedInvariant_forall_iff_gens_check {ι : Type*}
    (inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k : M)
    (ΔB : Submodule K M) (gens : ι → M)
    (hspan : Submodule.span K (Set.range gens) = ΔB) :
    (∀ m₁ m₂ : M, m₂ - m₁ ∈ ΔB →
        released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
          = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k)
      ↔ ∀ i, correctedReleased inactive released k (gens i) = 0 :=
  (carriedInvariant_forall_iff_le_ker inactive released k ΔB).trans
    (gens_check_iff_le_ker inactive released k ΔB gens hspan).symm

/-! ## 5. Item 4: the finite certificate -/

/-- **Item 4: the finite certificate.**  A `Fin d` generator list spanning
`ΔB` together with the `d` checked equations `Q (gens i) = 0`.  This `Prop`
asserts **no** surjectivity of any map and **no** pivot freshness
(`released k = 0` appears nowhere).  For the supplied spanning family,
`carriedInvariant_forall_iff_gens_check` proves that its two conjuncts are a
sound-and-complete check of the capstone-v2 premise over `ΔB`.  This does not
claim that the chosen generator list is irredundant or that this is a globally
minimal deployment interface. -/
def CarriedCertificate (inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k : M)
    {d : ℕ} (gens : Fin d → M) (ΔB : Submodule K M) : Prop :=
  Submodule.span K (Set.range gens) = ΔB
    ∧ ∀ i : Fin d, correctedReleased inactive released k (gens i) = 0

/-- **The checker (soundness).**  A certificate yields the capstone-v2
premise `hCarriedB`, in its verbatim spelling, for every pair whose
difference lies in `ΔB`. -/
theorem carriedInvariant_of_certificate {inactive : M →ₗ[K] K}
    {released : M →ₗ[K] V} {k : M} {d : ℕ} {gens : Fin d → M}
    {ΔB : Submodule K M}
    (hcert : CarriedCertificate inactive released k gens ΔB) :
    ∀ m₁ m₂ : M, m₂ - m₁ ∈ ΔB →
      released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
        = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k :=
  (carriedInvariant_forall_iff_gens_check inactive released k ΔB gens
    hcert.1).mpr hcert.2

/-- **Completeness.**  Any spanning family of a legal-difference space
contained in `ker Q` passes the check: certificates exist whenever the
obligation holds, so demanding a certificate loses no generality. -/
theorem certificate_of_le_ker {inactive : M →ₗ[K] K} {released : M →ₗ[K] V}
    {k : M} {d : ℕ} {gens : Fin d → M} {ΔB : Submodule K M}
    (hspan : Submodule.span K (Set.range gens) = ΔB)
    (hle : ΔB ≤ LinearMap.ker (correctedReleased inactive released k)) :
    CarriedCertificate inactive released k gens ΔB :=
  ⟨hspan, (gens_check_iff_le_ker inactive released k ΔB gens hspan).mpr hle⟩

/-! ## 6. Item 5: pivot freshness is only a corollary -/

/-- **Freshness collapses the correction.**  If the residual view does not
read the pivot (`released k = 0`), the corrected map *is* the released map.
The certificate route therefore contains the fresh route as the special
case in which the correction term is identically zero. -/
theorem correctedReleased_of_fresh (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k : M) (hfresh : released k = 0) :
    correctedReleased inactive released k = released := by
  ext m
  rw [correctedReleased_apply, hfresh, smul_zero, sub_zero]

/-- **Fresh-pivot corollary (kernel form).**  Under freshness, the
obligation `ΔB ≤ ker Q` is just `ΔB ≤ ker released`. -/
theorem le_ker_of_fresh {inactive : M →ₗ[K] K} {released : M →ₗ[K] V}
    {k : M} (hfresh : released k = 0) {ΔB : Submodule K M}
    (hraw : ΔB ≤ LinearMap.ker released) :
    ΔB ≤ LinearMap.ker (correctedReleased inactive released k) := by
  rw [correctedReleased_of_fresh inactive released k hfresh]
  exact hraw

/-- **Fresh-pivot corollary (pairwise form).**  Freshness plus raw
residual-view agreement gives the verbatim invariant — the v1 route,
re-derived here to certify it is strictly a special case of the
certificate route (the model below is outside its reach). -/
theorem carriedInvariant_of_fresh (inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m₁ m₂ : M) (hfresh : released k = 0)
    (hraw : released m₁ = released m₂) :
    released m₁ - ((inactive k)⁻¹ * inactive m₁) • released k
      = released m₂ - ((inactive k)⁻¹ * inactive m₂) • released k := by
  rw [hfresh, smul_zero, smul_zero, sub_zero, sub_zero, hraw]

/-! ## 7. The invariant is an observable of the shared-pivot joint law

Machinery for item 6.  `sharedPivotViewShape` transcribes the shape of
`AspisV5InactiveClaimJointHiding.sharedPivotView` (read, not imported): the
triple (terminal, inactive claim, residual view) under one draw of the
pivot scalar.  The discriminator lemma shows the corrected value
`Q m` is computable from any point of the view's orbit, so two witnesses
with `Q m₁ ≠ Q m₂` have *distinct joint laws*: the correlated invariant is
necessary, not merely sufficient, and a failed certificate is a real leak,
not a lost proof. -/

/-- The joint released view under one draw of the pivot scalar `p`
(the transcribed shape of `sharedPivotView`). -/
def sharedPivotViewShape (terminal inactive : M →ₗ[K] K)
    (released : M →ₗ[K] V) (k m : M) (p : K) : K × K × V :=
  (terminal (m + p • k), inactive (m + p • k), released (m + p • k))

/-- Point masses are distinct at distinct points. -/
theorem pmf_pure_inj {α : Type*} {x y : α} (h : PMF.pure x = PMF.pure y) :
    x = y := by
  by_contra hxy
  have hx := congrArg (fun q : PMF α => q x) h
  rw [PMF.pure_apply, PMF.pure_apply, if_pos rfl, if_neg hxy] at hx
  exact one_ne_zero hx

/-- **The discriminator.**  Subtracting `(inactive k)⁻¹ · (inactive claim)`
times the pivot's residual image from the residual coordinate of the
shared-pivot view returns the constant `Q m`: the pivot scalar cancels.
Pushing the joint law through this function is the point mass at `Q m`. -/
theorem sharedPivotViewShape_map_discriminator [Fintype K]
    (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k m : M)
    (hk : inactive k ≠ 0) :
    ((PMF.uniformOfFintype K).map
          (sharedPivotViewShape terminal inactive released k m)).map
        (fun v : K × K × V => v.2.2 - ((inactive k)⁻¹ * v.2.1) • released k)
      = PMF.pure (correctedReleased inactive released k m) := by
  have hfun : (fun v : K × K × V =>
        v.2.2 - ((inactive k)⁻¹ * v.2.1) • released k)
        ∘ sharedPivotViewShape terminal inactive released k m
      = fun _ : K => correctedReleased inactive released k m := by
    funext p
    show released (m + p • k)
        - ((inactive k)⁻¹ * inactive (m + p • k)) • released k
      = correctedReleased inactive released k m
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, mul_add,
      mul_left_comm, inv_mul_cancel₀ hk, mul_one, add_smul,
      correctedReleased_apply]
    abel
  rw [PMF.map_comp, hfun]
  exact PMF.map_const _ _

/-- **Failed invariant ⇒ distinct joint laws.**  If the corrected values of
two witnesses differ, the shared-pivot joint laws differ: the adversary
computes `Q m` from the released triple and distinguishes.  (Consumes the
nonzero pivot coefficient `hk`; the terminal functional participates only
through the view.) -/
theorem jointLaws_differ_of_corrected_ne [Fintype K]
    (terminal inactive : M →ₗ[K] K) (released : M →ₗ[K] V) (k m₁ m₂ : M)
    (hk : inactive k ≠ 0)
    (hne : correctedReleased inactive released k m₁
      ≠ correctedReleased inactive released k m₂) :
    (PMF.uniformOfFintype K).map
        (sharedPivotViewShape terminal inactive released k m₁)
      ≠ (PMF.uniformOfFintype K).map
        (sharedPivotViewShape terminal inactive released k m₂) := by
  intro hcontra
  apply hne
  have h₁ := sharedPivotViewShape_map_discriminator terminal inactive
    released k m₁ hk
  have h₂ := sharedPivotViewShape_map_discriminator terminal inactive
    released k m₂ hk
  rw [hcontra, h₂] at h₁
  exact (pmf_pure_inj h₁).symm

end CorrectedMap

/-! ## 8. Item 5 model: the certificate route reaches beyond freshness

`K = ZMod 2`, `M = Fin 4 → ZMod 2`, `V = ZMod 2`, with the Component-B
shape of the capstone-v2 example (terminal = row 0, inactive claim = row 1,
residual view reads rows 2 and 3, pivot read by the residual view).  The
pivot `![0, 1, 1, 0]` has `released k = 1 ≠ 0`, the legal-difference space
is spanned by the pivot together with `![0, 1, 0, 1]` — which is **not** a
pivot multiple and on which the raw residual view is nonzero — and the
`d = 2` certificate closes.  Both fresh-corollary premises fail on this
data, exactly as in `capstone_v2_beyond_fresh`. -/

section Models

abbrev egK : Type := ZMod 2
abbrev egM : Type := Fin 4 → ZMod 2

/-- Model terminal functional: row 0. -/
def egTerminal : egM →ₗ[egK] egK := LinearMap.proj (0 : Fin 4)

/-- Model inactive-claim functional: row 1. -/
def egInactive : egM →ₗ[egK] egK := LinearMap.proj (1 : Fin 4)

/-- Model residual released view: reads rows 2 and 3. -/
def egReleased : egM →ₗ[egK] egK :=
  (LinearMap.proj (2 : Fin 4) : egM →ₗ[egK] egK) + LinearMap.proj (3 : Fin 4)

/-- Model pivot: read by the inactive claim (row 1) *and* by the residual
view (row 2) — not fresh. -/
def egPivot : egM := ![0, 1, 1, 0]

/-- Model legal-difference generators: the pivot itself and a second
direction outside the pivot line that the raw residual view reads. -/
def egGens : Fin 2 → egM := ![![0, 1, 1, 0], ![0, 1, 0, 1]]

/-- The model legal-difference space: the span of the generators. -/
def egΔB : Submodule egK egM := Submodule.span egK (Set.range egGens)

/-- The `d = 2` certificate for the model: the span condition is
definitional and both generator checks are kernel computations. -/
theorem egCertificate :
    CarriedCertificate egInactive egReleased egPivot egGens egΔB := by
  refine ⟨rfl, fun i => ?_⟩
  fin_cases i <;> decide +kernel

/-- The generators preserve the terminal fibre: the model's legal
differences are not excluded by the authenticated-terminal layer. -/
theorem egGens_terminal_fibre : ∀ i, egTerminal (egGens i) = 0 := by decide

/-- **Item 5 non-vacuity package: strictly beyond freshness.**  The pivot
is read by the residual view (`released k = 1 ≠ 0`), the raw residual view
separates a legal pair (`released (gens 1) ≠ released 0`), the second
generator is not a pivot multiple (so the containment is not the automatic
`Q k = 0` fact), and still `ΔB ≤ ker Q`: the certificate does real work
that neither fresh-corollary premise could do. -/
theorem egBeyondFresh :
    egReleased egPivot ≠ 0
      ∧ egReleased (egGens 1) ≠ egReleased (0 : egM)
      ∧ egGens 1 ∉ Submodule.span egK {egPivot}
      ∧ egΔB ≤ LinearMap.ker
          (correctedReleased egInactive egReleased egPivot) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rw [Submodule.mem_span_singleton]
    decide
  · exact (gens_check_iff_le_ker egInactive egReleased egPivot egΔB egGens
      rfl).mp egCertificate.2

/-- The capstone-v2 premise `hCarriedB`, in its verbatim spelling, for
*every* pair of model witnesses with difference in `egΔB` — produced by the
checker from the certificate. -/
theorem egCarriedAllPairs :
    ∀ m₁ m₂ : egM, m₂ - m₁ ∈ egΔB →
      egReleased m₁ - ((egInactive egPivot)⁻¹ * egInactive m₁)
          • egReleased egPivot
        = egReleased m₂ - ((egInactive egPivot)⁻¹ * egInactive m₂)
          • egReleased egPivot :=
  carriedInvariant_of_certificate egCertificate

/-- A concrete legal pair `(0, gens 1)` on which the *raw* residual view
differs (`0 ≠ 1`) while the corrected invariant agrees: the exact pair
shape that the fresh route cannot reach and the certificate route covers. -/
theorem egPair_carried :
    egReleased (0 : egM) - ((egInactive egPivot)⁻¹ * egInactive (0 : egM))
        • egReleased egPivot
      = egReleased (egGens 1) - ((egInactive egPivot)⁻¹
          * egInactive (egGens 1)) • egReleased egPivot :=
  egCarriedAllPairs 0 (egGens 1)
    (by rw [sub_zero]; exact Submodule.subset_span (Set.mem_range_self (1 : Fin 2)))

/-! ## 9. Item 6: the negative model

Same layout, but the legal-difference space is replaced by the span of
`![0, 0, 1, 0]` — a direction that preserves the terminal fibre but is NOT
in `ker Q`.  The pair `(0, ![0, 0, 1, 0])` has its difference in the space,
`hCarriedB` fails for it, and the shared-pivot joint laws are distinct
`PMF`s.  The certificate is load-bearing: without `ΔB ≤ ker Q` the
invariant and the laws genuinely break. -/

/-- The negative-model difference direction: terminal-fibre-preserving,
outside `ker Q`. -/
def egBad : egM := ![0, 0, 1, 0]

/-- The negative-model legal-difference space. -/
def egΔBad : Submodule egK egM := Submodule.span egK {egBad}

/-- **Item 6 negative package.**  For the pair `(0, egBad)`: the terminal
fibre is shared (the failure is not excluded by the binding layer), the
difference lies in `egΔBad`, the verbatim `hCarriedB` is FALSE, the
kernel containment fails, and the two shared-pivot joint laws are distinct
probability mass functions. -/
theorem egNegativeModel :
    egTerminal (0 : egM) = egTerminal egBad
      ∧ egBad - 0 ∈ egΔBad
      ∧ ¬ (egReleased (0 : egM) - ((egInactive egPivot)⁻¹
              * egInactive (0 : egM)) • egReleased egPivot
            = egReleased egBad - ((egInactive egPivot)⁻¹
              * egInactive egBad) • egReleased egPivot)
      ∧ ¬ egΔBad ≤ LinearMap.ker
          (correctedReleased egInactive egReleased egPivot)
      ∧ (PMF.uniformOfFintype egK).map
            (sharedPivotViewShape egTerminal egInactive egReleased egPivot
              (0 : egM))
          ≠ (PMF.uniformOfFintype egK).map
            (sharedPivotViewShape egTerminal egInactive egReleased egPivot
              egBad) := by
  refine ⟨by decide, ?_, by decide, ?_, ?_⟩
  · rw [sub_zero]
    exact Submodule.mem_span_singleton_self egBad
  · intro hle
    exact absurd
      (LinearMap.mem_ker.mp (hle (Submodule.mem_span_singleton_self egBad)))
      (by decide)
  · exact jointLaws_differ_of_corrected_ne egTerminal egInactive egReleased
      egPivot 0 egBad (by decide) (by decide)

end Models

/-! ## 10. The deployed obligation as a named interface

`ΔB` is absent from the deployed Rust (module docstring), so nothing here
is discharged.  The interface packages one sufficient finite artifact; the
checker consumes it and emits the capstone-v2 premise `hCarriedB` — the
same `Prop` as `UnmetDeployment.DeployedCarriedInvariantCorrespondence` of
the capstone file — for every quantified pair, phrased on the opaque
deployed-side objects. -/

namespace UnmetDeployment

variable {K : Type*} [Field K]
variable {MB : Type*} [AddCommGroup MB] [Module K MB]
variable {VB : Type*} [AddCommGroup VB] [Module K VB]

/-- **UNRESOLVED INTERFACE (not proved) — the deployed correlated-invariant
certificate.**  `rustReleased` and `rustInactive` stand for the deployed
residual released view and copy-inactive functional
(`v5_split_layer_zero.rs:176-212`, `v5_real_host_proof.rs:627-636`;
`kB` is intended as the row-993 unit direction of
`V5StructuredBLane::encode`, `v5_spend_messages.rs:294-296`), and
`rustLegalPairs` for the witness pairs the deployed hiding statement
quantifies over.  The four conjuncts form one sufficient artifact: (i)/(ii)
transcription of the released and inactive functionals as the Lean linear
maps, (iii) coverage of the deployed pair quantification by `ΔB`, (iv) the
finite `CarriedCertificate`.  No theorem in this repository discharges any
conjunct for the deployed artefacts.  The exactness results above apply to
the chosen spanning-family certificate; they do not claim that this four-part
interface is globally minimal or exclude a direct containment proof. -/
def DeployedCarriedCertificateInterface (rustReleased : MB → VB)
    (rustInactive : MB → K) (rustLegalPairs : Set (MB × MB))
    (inactiveB : MB →ₗ[K] K) (releasedB : MB →ₗ[K] VB) (kB : MB)
    {d : ℕ} (gens : Fin d → MB) (ΔB : Submodule K MB) : Prop :=
  (∀ m : MB, rustReleased m = releasedB m)
    ∧ (∀ m : MB, rustInactive m = inactiveB m)
    ∧ (∀ p ∈ rustLegalPairs, p.2 - p.1 ∈ ΔB)
    ∧ CarriedCertificate inactiveB releasedB kB gens ΔB

/-- **The conditional checker.**  Given the interface — and only given it —
every deployed witness pair satisfies the capstone-v2 premise `hCarriedB`
in its verbatim spelling, stated on the opaque deployed-side objects.  This
is a conditional theorem consuming the certificate, not a deployed-
applicability claim: with the interface undischarged it asserts nothing
about the deployed byte stream. -/
theorem deployed_carried_invariant_of_interface {rustReleased : MB → VB}
    {rustInactive : MB → K} {rustLegalPairs : Set (MB × MB)}
    {inactiveB : MB →ₗ[K] K} {releasedB : MB →ₗ[K] VB} {kB : MB} {d : ℕ}
    {gens : Fin d → MB} {ΔB : Submodule K MB}
    (h : DeployedCarriedCertificateInterface rustReleased rustInactive
      rustLegalPairs inactiveB releasedB kB gens ΔB) :
    ∀ p ∈ rustLegalPairs,
      rustReleased p.1 - ((rustInactive kB)⁻¹ * rustInactive p.1)
          • rustReleased kB
        = rustReleased p.2 - ((rustInactive kB)⁻¹ * rustInactive p.2)
          • rustReleased kB := by
  obtain ⟨hrel, hina, hcov, hcert⟩ := h
  intro p hp
  simp only [hrel, hina]
  exact carriedInvariant_of_certificate hcert p.1 p.2 (hcov p hp)

end UnmetDeployment

/-! ## Axiom audit -/

#print axioms correctedReleased
#print axioms correctedReleased_apply
#print axioms carriedInvariant_iff_corrected_eq
#print axioms correctedReleased_pivot
#print axioms corrected_eq_iff_diff_zero
#print axioms corrected_eq_iff_mem_ker
#print axioms carried_forall_iff_le_ker
#print axioms carriedInvariant_forall_iff_le_ker
#print axioms gens_check_iff_le_ker
#print axioms carriedInvariant_forall_iff_gens_check
#print axioms CarriedCertificate
#print axioms carriedInvariant_of_certificate
#print axioms certificate_of_le_ker
#print axioms correctedReleased_of_fresh
#print axioms le_ker_of_fresh
#print axioms carriedInvariant_of_fresh
#print axioms sharedPivotViewShape
#print axioms pmf_pure_inj
#print axioms sharedPivotViewShape_map_discriminator
#print axioms jointLaws_differ_of_corrected_ne
#print axioms egTerminal
#print axioms egInactive
#print axioms egReleased
#print axioms egPivot
#print axioms egGens
#print axioms egΔB
#print axioms egCertificate
#print axioms egGens_terminal_fibre
#print axioms egBeyondFresh
#print axioms egCarriedAllPairs
#print axioms egPair_carried
#print axioms egBad
#print axioms egΔBad
#print axioms egNegativeModel
#print axioms UnmetDeployment.DeployedCarriedCertificateInterface
#print axioms UnmetDeployment.deployed_carried_invariant_of_interface

end AspisV5DeployedCarriedInvariant
