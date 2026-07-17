import Mathlib
import AspisFormal.CoreHiding
import AspisFormal.MaskingHiding
import AspisFormal.CircleVandermondeGeneral

/-!
# Layer 3 (START): binding the abstract hiding lemma to the ACTUAL circle construction

This file makes an honest *start* on the hardest, still-open part of the Aspis
hiding formalization: connecting the abstract, matrix-agnostic hiding lemma
(`MaskingHiding.view_indep_of_det_ne_zero`, valid for an **arbitrary** square
matrix `M`) to the **concrete** circle mask-evaluation matrix
(`AspisLivenessGeneral.circleMatrixGen`) and to the released view declared in the
paper (`def:spend-complete-view`, `eq:affine-field-view`).

It is deliberately split into three honest pieces:

1. **A genuine in-kernel win (Step 1).**  We instantiate the arbitrary-`M`
   hiding lemma at the *specific* matrix `M = circleMatrixGen K m` evaluated at a
   Fiat–Shamir schedule.  This yields a kernel-checked theorem
   (`circleMask_hides_witness`) that Aspis's circle mask matrix — not an
   arbitrary matrix — hides the witness whenever the emitted schedule is
   nonsingular (`det ≠ 0`).  We also show this is **non-vacuous**: at a grid
   schedule with distinct nodes the evaluated circle matrix is provably
   nonsingular (`circleMatrixGen_eval_grid_det_ne_zero`), so hiding holds
   unconditionally there (`circleMask_hides_witness_grid`).  All sorry-free.

2. **The released-view interface (Step 2).**  A Lean `structure`
   (`ReleasedView`) capturing the shape of `def:spend-complete-view`: the count
   of released non-hash field coordinates, the ideal mask-coordinate count, the
   public mask map `A`, the witness-dependent shift `b(w)`, and the affine view
   `Y = A·R + b(w)` of `eq:affine-field-view`.

3. **The faithfulness obligations, stated as EXPLICIT hypotheses, NOT proofs
   (Step 3).**  A `structure` (`FaithfulCircleView`) bundling the three
   currently-unproved obligations that would tie the abstract model to the
   deployed Rust prover.  A theorem (`faithful_view_hides_witness`) then
   discharges the *conclusion* — the real released view has witness-independent
   fibre counts — *given* that interface, via Step 1.  This is honest: the
   security conclusion is proved conditionally, and the condition is exactly the
   remaining obligation, explicitly named. No `sorry`, no faked
   "matrix = transcript" equality.

See the closing `## Remaining obligations` section for a plain-words statement of
what is proved in-kernel here versus what still requires either an exhaustive
symbolic check of the prover output or a proof-assistant model of the Rust.
-/

open MvPolynomial Matrix AspisLivenessGeneral

namespace AspisViewBinding

variable {K : Type*} [Field K]

/-! ## Step 1 — abstract hiding lemma, instantiated at the concrete circle matrix

`MaskingHiding.view_indep_of_det_ne_zero` holds for an arbitrary square matrix.
Here we pin `M` to `circleMatrixGen K m` *evaluated at a concrete schedule*
`f : Fin (2·(2m)) → K`.  This is the paper's `A_{s_fs}`: the symbolic circle
mask-evaluation matrix specialized to the emitted Fiat–Shamir schedule `s_fs`.
The mask coordinates `R` live in the field `K`; the schedule coordinates have
been evaluated away. -/

/-- **Step 1 (the real in-kernel win).**  Aspis's *circle* mask matrix
(`circleMatrixGen K m`), evaluated at a schedule `f` at which it is nonsingular,
hides the witness: for any two witness shifts `w₁, w₂` and any fixed released
view `y`, the mask fibre cardinalities agree.

This is `MaskingHiding.view_indep_of_det_ne_zero` specialized from "arbitrary `M`"
to the concrete circle matrix.  The hypothesis `hf` is precisely the per-schedule
liveness fact whose failure probability `AspisLivenessGeneral.circle_schedule_fail_le`
bounds (Layer 2b). -/
theorem circleMask_hides_witness {m : ℕ}
    (f : Fin (2 * (2 * m)) → K)
    (hf : ((circleMatrixGen K m).map (eval f)).det ≠ 0)
    (w₁ w₂ y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K //
        w₁ + Matrix.mulVecLin ((circleMatrixGen K m).map (eval f)) R = y}
      = Nat.card {R : Fin (2 * m) → K //
        w₂ + Matrix.mulVecLin ((circleMatrixGen K m).map (eval f)) R = y} :=
  view_indep_of_det_ne_zero ((circleMatrixGen K m).map (eval f)) hf w₁ w₂ y

/-- **Non-vacuity of Step 1: the evaluated circle matrix at a grid schedule is
nonsingular.**  At the grid witness `circleWitness` on `m` distinct nodes `ν`,
the circle mask-evaluation matrix reindexes to `fromBlocks V 0 V V` with
`V = vandermonde ν`, so its determinant is `(det V)² ≠ 0` (nodes distinct ⇒
Vandermonde nonsingular).  This is the same block computation that
`AspisLivenessGeneral.circleMatrixGen_det_ne_zero` uses to prove the *symbolic*
determinant is not identically zero; here we record the *evaluated* value at the
concrete grid schedule, which is what Step 1 consumes. -/
theorem circleMatrixGen_eval_grid_det_ne_zero {m : ℕ} (hm : 0 < m)
    (ν : Fin m → K) (hν : Function.Injective ν) :
    ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))).det ≠ 0 := by
  set A : Matrix (Fin m) (Fin m) K := Matrix.vandermonde ν with hA
  have hsub : ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))).submatrix
      (blockEquiv m) (blockEquiv m) = fromBlocks A 0 A A := by
    ext r c
    rcases r with k | k <;> rcases c with l | l
    · rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₁₁,
        blockEquiv_inl_val, blockEquiv_inl_val, if_pos l.2, hA, Matrix.vandermonde_apply,
        show (⟨k.1 % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext (Nat.mod_eq_of_lt k.2)]
    · rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        blockEquiv_inl_val, blockEquiv_inr_val, if_neg (by omega : ¬ m + l.1 < m),
        if_pos k.2, mul_zero]
    · have hmodk : (m + k.1) % m = k.1 := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt k.2
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₂₁,
        blockEquiv_inr_val, blockEquiv_inl_val, if_pos l.2, hA, Matrix.vandermonde_apply,
        show (⟨(m + k.1) % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext hmodk]
    · have hmodk : (m + k.1) % m = k.1 := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt k.2
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₂₂,
        blockEquiv_inr_val, blockEquiv_inr_val, if_neg (by omega : ¬ m + l.1 < m),
        if_neg (by omega : ¬ m + k.1 < m), mul_one, hA, Matrix.vandermonde_apply,
        show (⟨(m + k.1) % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext hmodk,
        show m + l.1 - m = l.1 from by omega]
  have hdet : ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))).det
      = A.det * A.det := by
    rw [← Matrix.det_submatrix_equiv_self (blockEquiv m)
        ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))),
      hsub, Matrix.det_fromBlocks_zero₁₂]
  rw [hdet]
  have hV : A.det ≠ 0 := by rw [hA]; exact (Matrix.det_vandermonde_ne_zero_iff).mpr hν
  exact mul_ne_zero hV hV

/-- **Step 1, unconditional at a grid schedule (given distinct nodes).**  Combining
the two facts above: on `m` distinct nodes the circle mask matrix hides the
witness with no residual hypothesis.  A concrete, kernel-checked witness that
Step 1 is not vacuous. -/
theorem circleMask_hides_witness_grid {m : ℕ} (hm : 0 < m)
    (ν : Fin m → K) (hν : Function.Injective ν)
    (w₁ w₂ y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K //
        w₁ + Matrix.mulVecLin
          ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))) R = y}
      = Nat.card {R : Fin (2 * m) → K //
        w₂ + Matrix.mulVecLin
          ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))) R = y} :=
  circleMask_hides_witness (circleWitness K m hm ν)
    (circleMatrixGen_eval_grid_det_ne_zero hm ν hν) w₁ w₂ y

/-! ## Step 2 — the released-view interface (`def:spend-complete-view`)

`def:spend-complete-view` declares the *complete* released non-hash field view,
and `eq:affine-field-view` states it has the affine form `Y = A·R + b(w)`.  We
capture exactly that shape — no more.  This is a data interface, not a claim:
it does not assert that any particular `A`/`b` are the deployed ones (that is
Step 3). -/

/-- The declared complete affine released view of `eq:affine-field-view`,
`Y_{s_fs}(w,R) = A_{s_fs}·R + b_{s_fs}(w)`, as a data structure over a field `K`
of split coordinates and a witness type `W`.

* `n`        — number of released non-hash field coordinates in the declared view;
* `numMask`  — number `m` of ideal independent mask coordinates `R ∈ Kᵐ`;
* `maskMap`  — the public matrix `A_{s_fs}` (frozen layout × schedule);
* `witShift` — the witness-dependent part `b_{s_fs}(w)`.

The affine view itself is `view`.  Nothing here is proved; it only fixes shape. -/
structure ReleasedView (K : Type*) [Field K] (W : Type*) where
  /-- number of released non-hash field coordinates (the declared view's width). -/
  n : ℕ
  /-- number `m` of ideal independent mask coordinates. -/
  numMask : ℕ
  /-- the public mask map `A_{s_fs}` determined by the frozen layout and schedule. -/
  maskMap : Matrix (Fin n) (Fin numMask) K
  /-- the witness-dependent shift `b_{s_fs}(w)`. -/
  witShift : W → (Fin n → K)

/-- The affine released view `Y = A·R + b(w)` of `eq:affine-field-view`. -/
def ReleasedView.view {K : Type*} [Field K] {W : Type*} (V : ReleasedView K W)
    (w : W) (R : Fin V.numMask → K) : Fin V.n → K :=
  V.witShift w + Matrix.mulVecLin V.maskMap R

/-! ## Step 3 — the faithfulness obligations, as an explicit interface

The following structure bundles the obligations that would bind the abstract
model to the deployed circle construction and Rust prover.  **Each field is a
hypothesis the eventual implementation must supply; none is proved here.**  This
is the honest encoding of items 5–6: instead of manufacturing a theorem
"Lean matrix = Rust transcript", we name that correspondence as an interface. -/

/-- **Faithfulness interface (the remaining, unproved obligations).**

For leakage budget `b = 2m`, witness type `W`, and an emitted schedule, this
bundles what must hold for the deployed circle prover to be modelled by
`circleMatrixGen`.  It is a *hypothesis carrier*, not a theorem:

* `sched`              — the emitted Fiat–Shamir circle schedule `s_fs` (its
                          `2·(2m)` coordinate variables), evaluated into `K`;
* `realView`           — the ACTUAL complete released non-hash field view of the
                          honest prover, as a function of witness and mask coords
                          (in the real system this is produced by the Rust
                          transcript; here it is an opaque function);
* `view_is_circle_affine` — **obligations (a) + (b), unproved.**  The real complete
                          view equals `A_{s_fs}·R + b(w)` where `A_{s_fs}` is the
                          deployed circle matrix at the emitted schedule
                          (obligation (a): the mask map *is* `circleMatrixGen`),
                          and equality of the FULL `realView` encodes that no
                          witness-dependent coordinate is omitted (obligation (b));
* `good`               — **obligation (c-liveness), unproved for a fixed deployment.**
                          the emitted schedule is `Good_spend`: the circle matrix
                          at `sched` is nonsingular.

Obligation (c-uniformity) — that the mask coordinates `R` are independent and
uniform — is captured *structurally*: `realView` is quantified over the full
product `Fin (2m) → K` with the counting measure, which is exactly "independent
uniform mask coordinates".  The theorem below therefore needs no extra field for
it. -/
structure FaithfulCircleView (K : Type*) [Field K] (W : Type*) (m : ℕ) where
  /-- the emitted Fiat–Shamir circle schedule `s_fs`, evaluated into `K`. -/
  sched : Fin (2 * (2 * m)) → K
  /-- the witness-dependent shift `b_{s_fs}(w)` of the deployed view. -/
  witShift : W → (Fin (2 * m) → K)
  /-- the ACTUAL complete released non-hash field view (opaque; the Rust transcript). -/
  realView : W → (Fin (2 * m) → K) → (Fin (2 * m) → K)
  /-- **Obligations (a)+(b), UNPROVED.** the real complete view is the affine map
  with mask matrix = the deployed circle matrix at the emitted schedule, and this
  equality of the full view asserts no witness-dependent coordinate is omitted. -/
  view_is_circle_affine : ∀ (w : W) (R : Fin (2 * m) → K),
      realView w R
        = witShift w + Matrix.mulVecLin ((circleMatrixGen K m).map (eval sched)) R
  /-- **Obligation (c-liveness), UNPROVED for a fixed deployment.** the emitted
  schedule is `Good_spend`: the circle matrix at `sched` is nonsingular. -/
  good : ((circleMatrixGen K m).map (eval sched)).det ≠ 0

/-- **Step 3 conclusion — the deployed released view hides the witness, GIVEN the
faithfulness interface.**

If `F : FaithfulCircleView K W m` supplies the (unproved) obligations that the
real complete view is the circle-affine map at a `Good_spend` schedule, then the
real view's mask fibre cardinalities are witness-independent — the perfect-hiding
statement a simulator needs.  The conclusion is discharged entirely from the
interface via Step 1 (`circleMask_hides_witness`); no obligation is faked. -/
theorem faithful_view_hides_witness {W : Type*} {m : ℕ}
    (F : FaithfulCircleView K W m) (w₁ w₂ : W) (y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K // F.realView w₁ R = y}
      = Nat.card {R : Fin (2 * m) → K // F.realView w₂ R = y} := by
  simp only [F.view_is_circle_affine]
  exact circleMask_hides_witness F.sched F.good (F.witShift w₁) (F.witShift w₂) y

/-! ## Remaining obligations (the multi-week frontier)

What is **proved in-kernel here** (sorry-free, axioms `[propext,
Classical.choice, Quot.sound]`):

* `circleMask_hides_witness` — the ARBITRARY-`M` hiding lemma, specialized to the
  concrete matrix `circleMatrixGen K m` evaluated at a schedule: given `det ≠ 0`,
  the *circle* mask matrix hides the witness.  This is the genuine "abstract →
  concrete" step.
* `circleMatrixGen_eval_grid_det_ne_zero` — that concrete matrix really is
  nonsingular at a grid schedule with distinct nodes; so
* `circleMask_hides_witness_grid` — hiding holds unconditionally there.
* `faithful_view_hides_witness` — the deployed view hides the witness *given* the
  faithfulness interface.

What remains **stated only as explicit interface hypotheses** (the fields of
`FaithfulCircleView`), awaiting the Rust binding — NONE proved here:

* (a) `view_is_circle_affine`'s "`A_{s_fs} = circleMatrixGen` at the emitted
  schedule": that the deployed prover's mask map really is the circle
  mask-evaluation matrix on the frozen layout.  Closing it requires an exhaustive
  symbolic reconstruction of the prover's linear map from the frozen layout at the
  deployed schedule (the `Good_spend` gate of `def:spend-complete-view`), matched
  coordinate-by-coordinate against `circleMatrixGen`.
* (b) `view_is_circle_affine`'s completeness: that `realView` is the COMPLETE
  released non-hash field view of `def:spend-complete-view` — every
  witness-dependent released coordinate present, nothing omitted.  Closing it
  requires enumerating the released field coordinates of the actual serialization
  and proving the enumeration exhaustive.
* (c-liveness) `good` for a *fixed* deployment: that the specific emitted schedule
  is nonsingular.  In-kernel we bound how *often* a random schedule fails
  (`AspisLivenessGeneral.circle_schedule_fail_le`) and exhibit nonsingular
  schedules (`circleMatrixGen_eval_grid_det_ne_zero`), but certifying one fixed
  deployed schedule is a per-run check.
* (c-uniformity): that the mask coordinates are independent and uniform.  Modelled
  structurally (counting measure over the full product `Fin (2m) → K`); a
  distributional (`PMF`) upgrade tying counts to sampling probabilities is not
  formalized (`CoreHiding`/`MaskingHiding` prove equal *cardinalities* only).

Closing (a) and (b) is the frontier: it needs either an exhaustive symbolic check
of the prover output at the frozen layout, or a proof-assistant model of the Rust
transcript in `crates/aspis-core/src/statement_hiding.rs` /
`state_only_hiding.rs`.  This file's contribution is to make that frontier
*precise* — the missing facts are exactly the named fields of
`FaithfulCircleView` — and to discharge everything downstream of them in-kernel. -/

end AspisViewBinding

#print axioms AspisViewBinding.circleMask_hides_witness
#print axioms AspisViewBinding.circleMatrixGen_eval_grid_det_ne_zero
#print axioms AspisViewBinding.circleMask_hides_witness_grid
#print axioms AspisViewBinding.faithful_view_hides_witness
