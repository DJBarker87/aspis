import Mathlib
import AspisFormal.CoreHidingPMF

/-!
# v5 selection hiding: the three-branch least-good selector and the cap-17 retry/abort

**Position in the argument.**  The v5 spend IOP-to-NARG reduction is the vanilla
Chiesa–Yogev compilation (Theorem 26.2.1) plus one bespoke prover-side device: on
every attempt the deployed prover derives three query-branch schedules from one
common transcript state, evaluates the public `GoodSpend` predicate on all three,
serializes only the least-good branch (the least selector index whose schedule is
good), retries the whole attempt when all three are bad, and aborts after 17
completed attempts (`crates/aspis-prover/src/state_only_good_spend.rs`:
`evaluate_all_and_choose_least_parallel` selects
`decisions.iter().position(accepted)`, with `SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS = 17`
and three query candidates).  This selection is schedule-dependent and prover-side;
it is not part of the vanilla IOP covered by Theorem 26.2.1, so its
witness-independence is a separate obligation that sits on top of that theorem.
This file discharges exactly that layer: the paper's Lemma "Selection and
cap-exhaustion law" (`lem:selection-hiding-abort` in
`paper/aspis-spend/sections/hiding.tex`), stated abstractly and proved as exact
`PMF` equalities.

**The model.**  Over abstract `Schedule`, witness `W` and `View` types, an attempt
draws a schedule triple `s : Fin 3 → Schedule` from a law `schedLaw` that does not
read the witness, computes `select Good s` (the least branch index whose schedule
satisfies the public predicate `Good : Schedule → Bool`), and, if a branch is
selected, releases the selector, the selected schedule and one sample of that
branch's view law `branchView sel (s sel) w`; on all-bad it retries, up to
`spendRetryCap = 17` attempts, after which it emits the abort symbol `none`.  The
finite-field layer instantiates each branch view as an affine masked vector view
over a finite field `K` (reusing `CoreHidingPMF.view_pmf_indep_of_witness`).

**What is proved.**
1. `attemptLaw_witness_indep`: if each branch's released view law is
   witness-independent on every *good* schedule, the selected (least-good) released
   object of one attempt has a witness-independent law.  The selection rule reads
   only `Good`, a public function of the schedule, never the witness.
2. `composedLaw_witness_indep`: the same through the bounded retry, for any cap;
   `spendComposedLaw_witness_indep` pins the deployed cap 17.
   `composedLaw_map_publicPart` shows the joint law of retry count, selector,
   selected schedule and the abort event equals `composedPublicLaw`, a distribution
   whose definition consumes only `Good` and `schedLaw` — witness-freeness of the
   retry/abort layer is visible in its type.  `composedPublicLaw_apply_none` and
   `composedLaw_apply_none` compute the abort mass as
   `attemptAllBadProb ^ fuel`, a function of the schedule law alone.
3. Non-vacuity: a concrete bundle (`toyGood`, `toySchedLaw`, `toyMaskMap`,
   `toyWitnessShift`) over `K = ZMod 3` in which the premises hold, the all-bad
   probability is exactly `8⁻¹` (so selection, retry and abort all occur with
   positive probability), and — sharper — the branch views on *bad* schedules leak
   the witness (`toy_bad_branch_leaks`), yet the composed law is witness-free
   because bad schedules are never selected: the good-schedule conditioning in the
   hypothesis is doing real work.
4. Negative test: with a witness-dependent predicate in place of `Good`
   (`leakGood`), fully hiding branch views and a fixed schedule law, the attempt
   law and the composed law both differ across witnesses
   (`witness_dependent_good_breaks_attempt_hiding`,
   `witness_dependent_good_breaks_composed_hiding`): the "public schedule
   predicate only" hypothesis is load-bearing.

**What is not proved.**  No random-oracle or EPRO layer: the schedule-triple law
is a parameter that does not read the witness — in the paper this is the
lazy-programming coupling conditioned on no adversarial prequery and no
programmed-state collision.  Nothing here identifies the abstract branch views
with the deployed Rust transcript (that is the complete-view obligation ledger of
`V5CompleteView.lean`), and the wall-clock deadline lemma of the paper
(`lem:deadline-hiding-abort`) is out of scope.
-/

open scoped ENNReal

namespace AspisV5SelectionHidingAbort

/-! ## The deployed q3 selector -/

section Selector

variable {Schedule : Type*}

/-- **The deployed least-good selection rule.**  `select Good s` is the least
branch index whose schedule satisfies the public predicate `Good`, and `none` when
all three branches are bad.  This is `decisions.iter().position(accepted)` from
`evaluate_all_and_choose_least_parallel` for the three query candidates.  Its type
records the load-bearing fact of the whole file: the rule consumes a predicate of
the *schedule* only — no witness, mask, salt or retry-derived secret appears. -/
def select (Good : Schedule → Bool) (s : Fin 3 → Schedule) : Option (Fin 3) :=
  if Good (s 0) then some 0
    else if Good (s 1) then some 1
      else if Good (s 2) then some 2
        else none

/-- A selected branch has a good schedule.  This is the reason the per-branch
hiding hypothesis is only ever needed on good schedules. -/
theorem good_of_select_eq_some {Good : Schedule → Bool} {s : Fin 3 → Schedule}
    {sel : Fin 3} (h : select Good s = some sel) : Good (s sel) = true := by
  unfold select at h
  split_ifs at h with h0 h1 h2
  · obtain rfl := Option.some.inj h
    exact h0
  · obtain rfl := Option.some.inj h
    exact h1
  · obtain rfl := Option.some.inj h
    exact h2

/-- `select` returns `none` exactly on the all-bad event: every one of the three
branch schedules is rejected by `Good`.  This is the per-attempt retry event. -/
theorem select_eq_none_iff {Good : Schedule → Bool} {s : Fin 3 → Schedule} :
    select Good s = none ↔ ∀ sel, Good (s sel) = false := by
  constructor
  · intro h sel
    unfold select at h
    split_ifs at h with h0 h1 h2
    simp only [Bool.not_eq_true] at h0 h1 h2
    fin_cases sel
    · exact h0
    · exact h1
    · exact h2
  · intro h
    simp [select, h 0, h 1, h 2]

/-- The selected branch is the *least* good one: every branch strictly below the
selected index is bad.  This pins the "least" in least-good against the deployed
`position(accepted)` rule. -/
theorem select_least {Good : Schedule → Bool} {s : Fin 3 → Schedule} {sel : Fin 3}
    (hsel : select Good s = some sel) {sel' : Fin 3} (hlt : sel' < sel) :
    Good (s sel') = false := by
  unfold select at hsel
  split_ifs at hsel with h0 h1 h2
  · obtain rfl := Option.some.inj hsel
    fin_cases sel' <;> simp at hlt
  · obtain rfl := Option.some.inj hsel
    simp only [Bool.not_eq_true] at h0
    fin_cases sel'
    · exact h0
    · simp at hlt
    · simp at hlt
  · obtain rfl := Option.some.inj hsel
    simp only [Bool.not_eq_true] at h0 h1
    fin_cases sel'
    · exact h0
    · exact h1
    · simp at hlt

/-- Checking the selected branch and the strictly earlier prefix is exactly
equivalent to recomputing the full least-good selector.  In particular, later
branches are logically irrelevant to verifier acceptance once `sel` is fixed.
This is the formal justification for the verifier's prefix-only CU path. -/
theorem select_eq_some_iff_prefix {Good : Schedule → Bool}
    {s : Fin 3 → Schedule} {sel : Fin 3} :
    select Good s = some sel ↔
      Good (s sel) = true ∧
        ∀ sel' : Fin 3, sel' < sel → Good (s sel') = false := by
  constructor
  · intro hsel
    exact ⟨good_of_select_eq_some hsel,
      fun _ hlt => select_least hsel hlt⟩
  · rintro ⟨hgood, hbefore⟩
    fin_cases sel
    · have hgood0 : Good (s 0) = true := by simpa using hgood
      simp [select, hgood0]
    · have hzero : Good (s 0) = false := hbefore 0 (by decide)
      have hgood1 : Good (s 1) = true := by simpa using hgood
      simp [select, hzero, hgood1]
    · have hzero : Good (s 0) = false := hbefore 0 (by decide)
      have hone : Good (s 1) = false := hbefore 1 (by decide)
      have hgood2 : Good (s 2) = true := by simpa using hgood
      simp [select, hzero, hone, hgood2]

end Selector

/-! ## One attempt: per-good-schedule hiding lifts through least-good selection -/

section SelectedView

variable {Schedule W View : Type*}

/-- The released object of one attempt on schedule triple `s`: the least-good
selector together with its schedule and one sample of the selected branch's view
law, or `none` on the all-bad event.  Only the selected branch is released — the
two unselected branch views are never sampled, matching the deployed serializer
which emits exactly one branch's opening sections. -/
noncomputable def attemptRelease (Good : Schedule → Bool)
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) (s : Fin 3 → Schedule) :
    PMF (Option (Fin 3 × Schedule × View)) :=
  (select Good s).elim (PMF.pure none)
    fun sel => (branchView sel (s sel) w).map fun v => some (sel, s sel, v)

/-- The law of one attempt: draw the schedule triple from `schedLaw`, then release
the least-good branch.  `schedLaw` is a parameter with no witness argument — the
paper's witness-independent joint schedule law under lazy random-oracle
programming. -/
noncomputable def attemptLaw (Good : Schedule → Bool) (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) :
    PMF (Option (Fin 3 × Schedule × View)) :=
  schedLaw.bind (attemptRelease Good branchView w)

/-- **Per-schedule hiding lifts through least-good selection.**  If each branch's
released view law is witness-independent on every good schedule, then the released
object of one attempt — least-good selector, selected schedule, selected view, or
the all-bad symbol — has the same `PMF` for any two witnesses.  The proof is a
per-schedule case split on `select Good s`: on `none` both sides are the retry
symbol, and on `some sel` the schedule is good by `good_of_select_eq_some`, so the
hypothesis applies.  The selection rule itself depends only on `Good`, a public
function of the schedule, never on the witness. -/
theorem attemptLaw_witness_indep (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w₁ w₂ : W)
    (hview : ∀ (sel : Fin 3) (σ : Schedule), Good σ = true →
      branchView sel σ w₁ = branchView sel σ w₂) :
    attemptLaw Good schedLaw branchView w₁ = attemptLaw Good schedLaw branchView w₂ := by
  unfold attemptLaw
  congr 1
  funext s
  unfold attemptRelease
  cases hsel : select Good s with
  | none => rfl
  | some sel =>
      simp only [Option.elim_some]
      rw [hview sel (s sel) (good_of_select_eq_some hsel)]

end SelectedView

/-! ## Bounded retry and the cap-17 abort -/

section RetryAbort

variable {Schedule W View : Type*}

/-- The bounded-retry composed law.  `fuel` is the number of attempts still
allowed and `used` the number of attempts already failed (the released retry
count).  Each attempt draws a fresh schedule triple; a selected branch releases
`some (used, sel, s sel, v)` and stops; all-bad consumes one unit of fuel and
retries; exhausted fuel emits the abort symbol `none`.  Attempts are independent:
the paper's fresh attempt entropy and fresh burned nonce. -/
noncomputable def composedLaw (Good : Schedule → Bool) (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) :
    ℕ → ℕ → PMF (Option (ℕ × Fin 3 × Schedule × View))
  | 0 => fun _ => PMF.pure none
  | fuel + 1 => fun used =>
      schedLaw.bind fun s =>
        (select Good s).elim (composedLaw Good schedLaw branchView w fuel (used + 1))
          fun sel => (branchView sel (s sel) w).map fun v => some (used, sel, s sel, v)

/-- Exhausted fuel is the abort symbol. -/
theorem composedLaw_zero (Good : Schedule → Bool) (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) (used : ℕ) :
    composedLaw Good schedLaw branchView w 0 used = PMF.pure none := rfl

/-- One unfolding of the retry recursion. -/
theorem composedLaw_succ (Good : Schedule → Bool) (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) (fuel used : ℕ) :
    composedLaw Good schedLaw branchView w (fuel + 1) used
      = schedLaw.bind fun s =>
          (select Good s).elim (composedLaw Good schedLaw branchView w fuel (used + 1))
            fun sel => (branchView sel (s sel) w).map fun v => some (used, sel, s sel, v) := rfl

/-- **Retry and abort preserve selection hiding.**  Under the same per-good-schedule
hypothesis as `attemptLaw_witness_indep`, the full bounded-retry transcript law —
retry count, least-good selector, selected schedule, selected view, and the
cap-exhaustion abort symbol — is the same `PMF` for any two witnesses, for every
fuel bound and failed-attempt count.  Induction on the fuel; each attempt is the
one-attempt case split again. -/
theorem composedLaw_witness_indep (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w₁ w₂ : W)
    (hview : ∀ (sel : Fin 3) (σ : Schedule), Good σ = true →
      branchView sel σ w₁ = branchView sel σ w₂)
    (fuel used : ℕ) :
    composedLaw Good schedLaw branchView w₁ fuel used
      = composedLaw Good schedLaw branchView w₂ fuel used := by
  induction fuel generalizing used with
  | zero => rfl
  | succ n ih =>
      rw [composedLaw_succ, composedLaw_succ]
      congr 1
      funext s
      cases hsel : select Good s with
      | none =>
          simp only [Option.elim_none]
          exact ih (used + 1)
      | some sel =>
          simp only [Option.elim_some]
          rw [hview sel (s sel) (good_of_select_eq_some hsel)]

/-- The public part of a released composed transcript: retry count, selector and
selected schedule, with the view discarded; the abort symbol is kept. -/
def publicPart : Option (ℕ × Fin 3 × Schedule × View) → Option (ℕ × Fin 3 × Schedule) :=
  Option.map fun out => (out.1, out.2.1, out.2.2.1)

/-- The law of the public part, built from `Good` and `schedLaw` alone.  Its type
is the witness-freeness claim for the selection/retry/abort metadata: no witness
and no branch-view family appear among its arguments. -/
noncomputable def composedPublicLaw (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule)) :
    ℕ → ℕ → PMF (Option (ℕ × Fin 3 × Schedule))
  | 0 => fun _ => PMF.pure none
  | fuel + 1 => fun used =>
      schedLaw.bind fun s =>
        (select Good s).elim (composedPublicLaw Good schedLaw fuel (used + 1))
          fun sel => PMF.pure (some (used, sel, s sel))

/-- Exhausted fuel is the abort symbol (public projection). -/
theorem composedPublicLaw_zero (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule)) (used : ℕ) :
    composedPublicLaw Good schedLaw 0 used = PMF.pure none := rfl

/-- One unfolding of the public retry recursion. -/
theorem composedPublicLaw_succ (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule)) (fuel used : ℕ) :
    composedPublicLaw Good schedLaw (fuel + 1) used
      = schedLaw.bind fun s =>
          (select Good s).elim (composedPublicLaw Good schedLaw fuel (used + 1))
            fun sel => PMF.pure (some (used, sel, s sel)) := rfl

/-- **The selection/retry/abort metadata is witness-free by construction.**  For
*every* witness and every branch-view family, the pushforward of the composed law
along `publicPart` is `composedPublicLaw`, a distribution defined from `Good` and
`schedLaw` alone.  This is the paper lemma's first sentence — the Good bits, the
least-good selector, the first good completed attempt and the all-bad/abort bit
have a joint law that consumes no witness — in type-level form. -/
theorem composedLaw_map_publicPart (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) (fuel used : ℕ) :
    (composedLaw Good schedLaw branchView w fuel used).map publicPart
      = composedPublicLaw Good schedLaw fuel used := by
  induction fuel generalizing used with
  | zero =>
      rw [composedLaw_zero, composedPublicLaw_zero, PMF.pure_map]
      rfl
  | succ n ih =>
      rw [composedLaw_succ, composedPublicLaw_succ, PMF.map_bind]
      congr 1
      funext s
      cases hsel : select Good s with
      | none =>
          simp only [Option.elim_none]
          exact ih (used + 1)
      | some sel =>
          simp only [Option.elim_some]
          rw [PMF.map_comp]
          have hconst : publicPart ∘ (fun v : View => some (used, sel, s sel, v))
              = Function.const View (some (used, sel, s sel)) := rfl
          rw [hconst, PMF.map_const]

/-- The per-attempt all-bad probability: the `schedLaw`-mass of the event that all
three branch schedules are rejected by `Good` (`select_eq_none_iff`).  A function
of the public schedule law and predicate only. -/
noncomputable def attemptAllBadProb (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule)) : ℝ≥0∞ :=
  ∑' s, if select Good s = none then schedLaw s else 0

/-- **The abort mass is a public quantity.**  The cap-exhaustion symbol carries
mass `attemptAllBadProb ^ fuel` under the public law: attempts are independent and
abort is exactly `fuel` consecutive all-bad events.  No conditioning or division
by a success probability occurs — abort is retained in the output space. -/
theorem composedPublicLaw_apply_none (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule)) (fuel used : ℕ) :
    composedPublicLaw Good schedLaw fuel used none
      = attemptAllBadProb Good schedLaw ^ fuel := by
  induction fuel generalizing used with
  | zero =>
      rw [composedPublicLaw_zero, pow_zero]
      exact PMF.pure_apply_self none
  | succ n ih =>
      rw [composedPublicLaw_succ, PMF.bind_apply]
      have hpt : ∀ s : Fin 3 → Schedule,
          schedLaw s * ((select Good s).elim (composedPublicLaw Good schedLaw n (used + 1))
              fun sel => PMF.pure (some (used, sel, s sel))) none
            = (if select Good s = none then schedLaw s else 0)
                * attemptAllBadProb Good schedLaw ^ n := by
        intro s
        cases hsel : select Good s with
        | none =>
            simp only [Option.elim_none]
            rw [ih (used + 1)]
            simp
        | some sel => simp
      rw [tsum_congr hpt, ENNReal.tsum_mul_right, pow_succ']
      rfl

/-- Discarding the view does not move mass off the abort symbol: the composed law
and its public projection agree at `none`. -/
theorem map_publicPart_apply_none (p : PMF (Option (ℕ × Fin 3 × Schedule × View))) :
    p.map publicPart none = p none := by
  rw [PMF.map_apply]
  refine (tsum_eq_single none fun out hout => ?_).trans ?_
  · cases out with
    | none => exact absurd rfl hout
    | some out => simp [publicPart]
  · simp [publicPart]

/-- **The retry/abort event is witness-independent, with an explicit formula.**
For every witness and every branch-view family, the composed law gives the abort
symbol mass `attemptAllBadProb ^ fuel` — a function of `Good` and `schedLaw`
alone.  Combines the public projection with the public abort mass. -/
theorem composedLaw_apply_none (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) (fuel used : ℕ) :
    composedLaw Good schedLaw branchView w fuel used none
      = attemptAllBadProb Good schedLaw ^ fuel := by
  rw [← map_publicPart_apply_none, composedLaw_map_publicPart,
    composedPublicLaw_apply_none]

/-- The deployed retry cap: at most 17 completed attempts per proof
(`SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS`). -/
def spendRetryCap : ℕ := 17

/-- The cap is 17, pinned. -/
theorem spendRetryCap_eq : spendRetryCap = 17 := rfl

/-- The deployed composed law: bounded retry at cap 17, starting from zero failed
attempts. -/
noncomputable def spendComposedLaw (Good : Schedule → Bool) (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) :
    PMF (Option (ℕ × Fin 3 × Schedule × View)) :=
  composedLaw Good schedLaw branchView w spendRetryCap 0

/-- **The selection-hiding-abort lemma at the deployed cap.**  Per-good-schedule
witness-independence of the branch views makes the entire cap-17 released
transcript law — retry count, least-good selector, selected schedule, selected
view, abort — identical for any two witnesses. -/
theorem spendComposedLaw_witness_indep (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w₁ w₂ : W)
    (hview : ∀ (sel : Fin 3) (σ : Schedule), Good σ = true →
      branchView sel σ w₁ = branchView sel σ w₂) :
    spendComposedLaw Good schedLaw branchView w₁
      = spendComposedLaw Good schedLaw branchView w₂ :=
  composedLaw_witness_indep Good schedLaw branchView w₁ w₂ hview spendRetryCap 0

/-- The deployed cap-17 abort mass, as a public formula. -/
theorem spendComposedLaw_apply_none (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → W → PMF View) (w : W) :
    spendComposedLaw Good schedLaw branchView w none
      = attemptAllBadProb Good schedLaw ^ 17 :=
  composedLaw_apply_none Good schedLaw branchView w spendRetryCap 0

end RetryAbort

/-! ## Affine masked branch views over a finite field -/

section AffineBranches

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {Schedule W : Type*} {m v : ℕ}

/-- A branch view family in the shape supplied by the vanilla per-branch argument:
on branch `sel` with schedule `σ`, sample a uniform mask over the finite field `K`
and release the witness contribution shifted by the (schedule-dependent) linear
mask image. -/
noncomputable def affineBranchView
    (maskMap : Fin 3 → Schedule → (Fin m → K) →ₗ[K] (Fin v → K))
    (witnessShift : Fin 3 → Schedule → W → Fin v → K)
    (sel : Fin 3) (σ : Schedule) (w : W) : PMF (Fin v → K) :=
  (PMF.uniformOfFintype (Fin m → K)).map
    fun R => witnessShift sel σ w + maskMap sel σ R

/-- A surjective mask map makes the affine branch view witness-independent on its
schedule: `CoreHidingPMF.view_pmf_indep_of_witness` applied branchwise. -/
theorem affineBranchView_witness_indep
    (maskMap : Fin 3 → Schedule → (Fin m → K) →ₗ[K] (Fin v → K))
    (witnessShift : Fin 3 → Schedule → W → Fin v → K)
    (sel : Fin 3) (σ : Schedule) (hσ : Function.Surjective (maskMap sel σ))
    (w₁ w₂ : W) :
    affineBranchView maskMap witnessShift sel σ w₁
      = affineBranchView maskMap witnessShift sel σ w₂ :=
  view_pmf_indep_of_witness (maskMap sel σ) hσ
    (witnessShift sel σ w₁) (witnessShift sel σ w₂)

/-- **The finite-field composed statement.**  If the mask map is surjective on
every *good* schedule — surjectivity on bad schedules is not required, because
`select` never releases a bad branch — then the deployed cap-17 selection law over
the affine branch views is witness-independent.  This is the seam with the vanilla
reduction: Theorem 26.2.1's per-branch affine hiding premise enters here, and the
selection/retry/abort device on top of it adds no witness dependence. -/
theorem spendComposedLaw_affine_witness_indep (Good : Schedule → Bool)
    (schedLaw : PMF (Fin 3 → Schedule))
    (maskMap : Fin 3 → Schedule → (Fin m → K) →ₗ[K] (Fin v → K))
    (witnessShift : Fin 3 → Schedule → W → Fin v → K)
    (hsurj : ∀ (sel : Fin 3) (σ : Schedule), Good σ = true →
      Function.Surjective (maskMap sel σ))
    (w₁ w₂ : W) :
    spendComposedLaw Good schedLaw (affineBranchView maskMap witnessShift) w₁
      = spendComposedLaw Good schedLaw (affineBranchView maskMap witnessShift) w₂ :=
  spendComposedLaw_witness_indep Good schedLaw (affineBranchView maskMap witnessShift)
    w₁ w₂ fun sel σ hσ =>
      affineBranchView_witness_indep maskMap witnessShift sel σ (hsurj sel σ hσ) w₁ w₂

end AffineBranches

/-! ## Non-vacuity: a concrete bundle over `ZMod 3` where the premises hold -/

section ToyInstance

/-- Toy public predicate: the schedule is one bit and is good iff it is `true`. -/
def toyGood : Bool → Bool := fun σ => σ

/-- Toy schedule law: uniform over the eight branch-schedule triples. -/
noncomputable def toySchedLaw : PMF (Fin 3 → Bool) := PMF.uniformOfFintype (Fin 3 → Bool)

/-- Toy mask map over `K = ZMod 3`: the identity (surjective) on good schedules,
the zero map (maximally non-hiding) on bad schedules.  The zero arm makes the
good-schedule conditioning in the surjectivity hypothesis genuinely load-bearing:
the premise would be false without it. -/
def toyMaskMap : Fin 3 → Bool → (Fin 1 → ZMod 3) →ₗ[ZMod 3] (Fin 1 → ZMod 3) :=
  fun _ σ => if σ = true then LinearMap.id else 0

/-- Toy witness contribution: the witness itself, on every branch and schedule. -/
def toyWitnessShift : Fin 3 → Bool → ZMod 3 → Fin 1 → ZMod 3 :=
  fun _ _ w _ => w

/-- The toy branch-view family assembled from the affine layer. -/
noncomputable def toyBranchView : Fin 3 → Bool → ZMod 3 → PMF (Fin 1 → ZMod 3) :=
  affineBranchView toyMaskMap toyWitnessShift

/-- The toy premises hold: on every good schedule the mask map is surjective. -/
theorem toy_surjective (sel : Fin 3) (σ : Bool) (hσ : toyGood σ = true) :
    Function.Surjective (toyMaskMap sel σ) := by
  have hσ' : σ = true := hσ
  subst hσ'
  intro y
  refine ⟨y, ?_⟩
  simp [toyMaskMap]

/-- **Non-vacuity of the whole bundle.**  The composed cap-17 selection law of the
toy instance is witness-independent, by the finite-field composed theorem with the
premises discharged above. -/
theorem toy_spend_composed_witness_indep (w₁ w₂ : ZMod 3) :
    spendComposedLaw toyGood toySchedLaw toyBranchView w₁
      = spendComposedLaw toyGood toySchedLaw toyBranchView w₂ :=
  spendComposedLaw_affine_witness_indep toyGood toySchedLaw toyMaskMap toyWitnessShift
    toy_surjective w₁ w₂

/-- On a *bad* toy schedule the branch view is the deterministic witness: the zero
mask arm hides nothing. -/
theorem toy_bad_branch_view (sel : Fin 3) (w : ZMod 3) :
    toyBranchView sel false w = PMF.pure fun _ => w := by
  unfold toyBranchView affineBranchView
  have hconst : (fun R : Fin 1 → ZMod 3 => toyWitnessShift sel false w + toyMaskMap sel false R)
      = Function.const (Fin 1 → ZMod 3) fun _ => w := by
    funext R i
    simp [toyWitnessShift, toyMaskMap]
  rw [hconst, PMF.map_const]

/-- The toy branch views on bad schedules *leak the witness*: the per-branch
hiding premise genuinely fails off the good event, yet
`toy_spend_composed_witness_indep` holds — the selector never releases a bad
branch, so the good-schedule conditioning carries the whole statement. -/
theorem toy_bad_branch_leaks (sel : Fin 3) :
    toyBranchView sel false 0 ≠ toyBranchView sel false 1 := by
  rw [toy_bad_branch_view sel 0, toy_bad_branch_view sel 1]
  intro h
  have hne : (fun _ : Fin 1 => (0 : ZMod 3)) ≠ fun _ => (1 : ZMod 3) := by
    intro hc
    exact absurd (congrFun hc 0) (by decide)
  have h0 := congrArg (fun p : PMF (Fin 1 → ZMod 3) => p fun _ => (0 : ZMod 3)) h
  simp only [PMF.pure_apply_self, PMF.pure_apply_of_ne _ _ hne] at h0
  exact one_ne_zero h0

/-- The deployed least-good rule on concrete toy schedules: branch 0 wins whenever
good, branch 1 wins when 0 is bad, branch 2 when 0 and 1 are bad, and the all-bad
triple retries.  Matches the Rust test
`manager_evaluates_all_three_and_selects_least_good`. -/
theorem toy_select_examples :
    select toyGood ![true, true, true] = some 0 ∧
      select toyGood ![false, true, true] = some 1 ∧
        select toyGood ![false, false, true] = some 2 ∧
          select toyGood ![false, false, false] = none := by
  decide

/-- The toy all-bad probability is exactly `8⁻¹`: of the eight uniform schedule
triples only the all-`false` one is rejected on all three branches.  Selection,
retry and cap-17 abort all occur with positive probability, so the composed
theorems above are exercised on a non-degenerate process. -/
theorem toy_attempt_all_bad_prob : attemptAllBadProb toyGood toySchedLaw = 8⁻¹ := by
  have hsingle : ∀ s : Fin 3 → Bool, s ≠ (fun _ => false) →
      (if select toyGood s = none then toySchedLaw s else 0) = 0 := by
    intro s hs
    have hcond : ¬select toyGood s = none := by
      intro hnone
      exact hs (funext fun i => select_eq_none_iff.mp hnone i)
    rw [if_neg hcond]
  have hstep : attemptAllBadProb toyGood toySchedLaw
      = if select toyGood (fun _ : Fin 3 => false) = none
          then toySchedLaw fun _ => false else 0 :=
    tsum_eq_single _ hsingle
  rw [hstep, if_pos (by decide)]
  unfold toySchedLaw
  rw [PMF.uniformOfFintype_apply]
  norm_num [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The toy abort event is neither impossible nor certain: the retry/abort branch
of the composed law is genuinely exercised. -/
theorem toy_all_bad_prob_nondegenerate :
    attemptAllBadProb toyGood toySchedLaw ≠ 0
      ∧ attemptAllBadProb toyGood toySchedLaw ≠ 1 := by
  rw [toy_attempt_all_bad_prob]
  constructor
  · simp
  · rw [ne_eq, ENNReal.inv_eq_one]
    norm_num

/-- The toy cap-17 abort mass, computed: `8⁻¹ ^ 17`, for every witness. -/
theorem toy_spend_abort_prob (w : ZMod 3) :
    spendComposedLaw toyGood toySchedLaw toyBranchView w none = 8⁻¹ ^ 17 := by
  unfold spendComposedLaw
  rw [composedLaw_apply_none, toy_attempt_all_bad_prob, spendRetryCap_eq]

end ToyInstance

/-! ## Negative test: the public-predicate hypothesis is load-bearing -/

section NegativeTest

/-- A *witness-dependent* predicate in the selector slot: it ignores the schedule
and accepts iff the witness bit is `true`.  This is exactly what the deployed
`GoodSpend` is forbidden from doing. -/
def leakGood (w : Bool) : Unit → Bool := fun _ => w

/-- Deterministic schedule law for the counterexample. -/
noncomputable def leakSchedLaw : PMF (Fin 3 → Unit) := PMF.pure fun _ => ()

/-- Fully hiding branch views: every branch releases the constant view.  The
per-branch hypothesis of the positive theorems holds in its strongest form. -/
noncomputable def leakBranchView : Fin 3 → Unit → Bool → PMF Unit := fun _ _ _ => PMF.pure ()

/-- The counterexample's branch views are witness-independent on every schedule
(not only good ones), so only the predicate's witness dependence is in play. -/
theorem leakBranchView_witness_indep (sel : Fin 3) (σ : Unit) (w₁ w₂ : Bool) :
    leakBranchView sel σ w₁ = leakBranchView sel σ w₂ := rfl

/-- With witness bit `true` the leaky selector always selects branch 0, so the
attempt never aborts. -/
theorem leak_attempt_apply_none_true :
    attemptLaw (leakGood true) leakSchedLaw leakBranchView true none = 0 := by
  unfold attemptLaw leakSchedLaw
  rw [PMF.pure_bind]
  unfold attemptRelease
  have hsel : select (leakGood true) (fun _ : Fin 3 => ()) = some 0 := rfl
  rw [hsel]
  simp [leakBranchView, PMF.pure_map]

/-- With witness bit `false` the leaky selector rejects every branch, so the
attempt aborts with certainty. -/
theorem leak_attempt_apply_none_false :
    attemptLaw (leakGood false) leakSchedLaw leakBranchView false none = 1 := by
  unfold attemptLaw leakSchedLaw
  rw [PMF.pure_bind]
  unfold attemptRelease
  have hsel : select (leakGood false) (fun _ : Fin 3 => ()) = none := rfl
  rw [hsel]
  simp

/-- **The negative test at the attempt level.**  The branch views satisfy the
hiding premise on every schedule, the schedule law is fixed, and still the
selected-view laws of the two witnesses differ — because the predicate in the
selector slot reads the witness.  The "public function of the schedule only"
hypothesis on `Good` is therefore load-bearing, not decorative. -/
theorem witness_dependent_good_breaks_attempt_hiding :
    (∀ (sel : Fin 3) (σ : Unit) (w₁ w₂ : Bool),
        leakBranchView sel σ w₁ = leakBranchView sel σ w₂)
      ∧ attemptLaw (leakGood true) leakSchedLaw leakBranchView true
          ≠ attemptLaw (leakGood false) leakSchedLaw leakBranchView false := by
  refine ⟨leakBranchView_witness_indep, fun h => ?_⟩
  have h0 := leak_attempt_apply_none_true
  rw [h] at h0
  exact zero_ne_one (h0.symm.trans leak_attempt_apply_none_false)

/-- With witness bit `true` no attempt is ever all-bad. -/
theorem leak_all_bad_prob_true : attemptAllBadProb (leakGood true) leakSchedLaw = 0 := by
  unfold attemptAllBadProb
  have hpt : ∀ s : Fin 3 → Unit,
      (if select (leakGood true) s = none then leakSchedLaw s else 0) = 0 := by
    intro s
    have hcond : ¬select (leakGood true) s = none := by
      have hsel : select (leakGood true) s = some 0 := rfl
      rw [hsel]
      simp
    rw [if_neg hcond]
  rw [tsum_congr hpt, tsum_zero]

/-- With witness bit `false` every attempt is all-bad. -/
theorem leak_all_bad_prob_false : attemptAllBadProb (leakGood false) leakSchedLaw = 1 := by
  unfold attemptAllBadProb
  have hpt : ∀ s : Fin 3 → Unit,
      (if select (leakGood false) s = none then leakSchedLaw s else 0) = leakSchedLaw s :=
    fun s => if_pos rfl
  rw [tsum_congr hpt]
  exact PMF.tsum_coe leakSchedLaw

/-- **The negative test at the composed cap-17 level.**  With the witness-reading
predicate, one witness never aborts and the other aborts with certainty, so the
composed transcript laws differ.  Computed through the abort-mass formula
`composedLaw_apply_none`, whose hypotheses do not constrain the predicate's
provenance. -/
theorem witness_dependent_good_breaks_composed_hiding :
    spendComposedLaw (leakGood true) leakSchedLaw leakBranchView true
      ≠ spendComposedLaw (leakGood false) leakSchedLaw leakBranchView false := by
  intro h
  have hTrue : spendComposedLaw (leakGood true) leakSchedLaw leakBranchView true none = 0 := by
    unfold spendComposedLaw
    rw [composedLaw_apply_none, leak_all_bad_prob_true]
    exact zero_pow (by decide)
  have hFalse :
      spendComposedLaw (leakGood false) leakSchedLaw leakBranchView false none = 1 := by
    unfold spendComposedLaw
    rw [composedLaw_apply_none, leak_all_bad_prob_false, one_pow]
  rw [h] at hTrue
  exact zero_ne_one (hTrue.symm.trans hFalse)

end NegativeTest

end AspisV5SelectionHidingAbort

#print axioms AspisV5SelectionHidingAbort.good_of_select_eq_some
#print axioms AspisV5SelectionHidingAbort.select_eq_none_iff
#print axioms AspisV5SelectionHidingAbort.select_least
#print axioms AspisV5SelectionHidingAbort.select_eq_some_iff_prefix
#print axioms AspisV5SelectionHidingAbort.attemptLaw_witness_indep
#print axioms AspisV5SelectionHidingAbort.composedLaw_witness_indep
#print axioms AspisV5SelectionHidingAbort.composedLaw_map_publicPart
#print axioms AspisV5SelectionHidingAbort.composedPublicLaw_apply_none
#print axioms AspisV5SelectionHidingAbort.composedLaw_apply_none
#print axioms AspisV5SelectionHidingAbort.spendComposedLaw_witness_indep
#print axioms AspisV5SelectionHidingAbort.spendComposedLaw_apply_none
#print axioms AspisV5SelectionHidingAbort.spendComposedLaw_affine_witness_indep
#print axioms AspisV5SelectionHidingAbort.toy_spend_composed_witness_indep
#print axioms AspisV5SelectionHidingAbort.toy_bad_branch_leaks
#print axioms AspisV5SelectionHidingAbort.toy_select_examples
#print axioms AspisV5SelectionHidingAbort.toy_attempt_all_bad_prob
#print axioms AspisV5SelectionHidingAbort.toy_spend_abort_prob
#print axioms AspisV5SelectionHidingAbort.witness_dependent_good_breaks_attempt_hiding
#print axioms AspisV5SelectionHidingAbort.witness_dependent_good_breaks_composed_hiding
