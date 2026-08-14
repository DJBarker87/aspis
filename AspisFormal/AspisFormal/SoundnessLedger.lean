import Mathlib
import AspisFormal.CircleFibreRoots
import AspisFormal.CircleGroupOrder

/-!
# Kernel-checked soundness ledger arithmetic

This file pulls the *arithmetic* facts of the Aspis-spend soundness
finite-parameter check (`tools/verify_soundness_params.py`) into the Lean
kernel, so fewer important numbers rest only on the Python calculation.
It is a companion to `SoundnessParams.lean` (which kernel-checks the
Johnson-threshold `ρ ≤ α²` and the cap `A = ⌊αN⌋ = 6082`); here we cover the
event-degree table, the per-event Schwartz–Zippel / MCA probability bounds, the
batch and four fold-round bounds (via rational sandwiches of the square roots),
the OOD list-union and raw-query bounds, and the coarse event-union / ×3
whole-ledger floor.

## Scope, stated honestly

* Every constant below is a Lean literal.  As in `SoundnessParams.lean`, nothing
  here proves these equal the constants compiled into the Rust verifier; this is
  math about the *intended* parameters.
* The imported theorems themselves (Stwo Johnson list decoding, the
  Bordage/Haböck polynomial-generator MCA theorem, the WHIR fold-list
  commutation, and the BCS/Fiat–Shamir transform) are **cited, not proved**.  We
  reproduce only the finite-parameter arithmetic the script re-derives.
* The exact decimal bit-values the script prints (e.g. `107.3160201143554`) need
  `Real.logb`; we instead prove the security-meaningful **floor** bound
  `probability ≤ 2^(-k)` for the integer `k = ⌊bits⌋`, which is what the ledger
  is defended on.  These are strictly weaker only in that they drop a fractional
  bit of margin.
* **Fibre-root distinctness (Check 4) is kernel-checked and bridged below:**
  `CircleFibreRoots.lean` proves the `π(x)=2x²−1` ramification and that the
  deployed exponents `2¹²+2¹⁴j` are pairwise non-±-congruent and nonzero mod
  `2³¹`; `CircleGroupOrder.lean` proves the x-collision criterion and
  `orderOf g = 2³¹` on the concrete circle group — structurally, no brute
  force.  Section 4 composes the two into `circle_fibre_root_conditions`,
  stated on the deployed group itself, with the former `SameXCoord` interface
  hypothesis discharged by the theorem `sameXCoord_exp`.
* **Not covered here (remains Python-only):** the exact
  `Real.logb`-based BCS work-normalized endpoints (101.75 / 106.79 / final
  100.16 bits, Check 5b), which mix `Real.logb` with additive `2^(-256)` terms.
  We instead kernel-check the *coarse event-union* `≤ 2^(-106)` and its `×3`
  inflation `≤ 2^(-104)`; the further BCS work-normalization erosion down to the
  ~100-bit release endpoint stays Python-verified.

Field size is `|K| = P⁴` with `P = 2³¹ − 1` (QM31 over M31).  Event
probabilities are `numerator / |K|` (Schwartz–Zippel) or the stated closed
forms; each theorem asserts `probability ≤ 2^(-k)`.
-/

namespace AspisSoundnessLedger

/-- QM31 field size `|K| = P⁴`, `P = 2³¹ − 1`. -/
noncomputable def FIELD : ℝ := (2 ^ 31 - 1) ^ 4

lemma FIELD_pos : (0 : ℝ) < FIELD := by unfold FIELD; positivity

/-! ## 1. Rate and domain (layout constants) -/

theorem message_dim : (2 : ℕ) ^ 10 = 1024 := by decide
theorem domain_symbols : (2 : ℕ) ^ 19 = 524288 := by decide
theorem inverse_rate : (2 : ℕ) ^ 19 / 2 ^ 10 = 512 := by decide
theorem query_fibers : (2 : ℕ) ^ 17 = 131072 := by decide
/-- Rate `ρ = 2¹⁰ / 2¹⁹ = 1/512`. -/
theorem rate_rho : (1024 : ℚ) / 524288 = 1 / 512 := by norm_num

/-! ## 2. Johnson agreement cap  (independent re-derivation of `SoundnessParams`)

`α = (1 + 1/2m)√ρ` with `m = 10`, `ρ = 1/512`, `N = 2¹⁷`; the cap is
`A = ⌊αN⌋ = 6082`. -/

/-- `√ρ`, `ρ = 1/512`. -/
noncomputable def sqrtRho : ℝ := Real.sqrt (1 / 512)
/-- Johnson agreement fraction `α = (21/20)·√ρ`. -/
noncomputable def alpha : ℝ := (21 / 20) * sqrtRho

private lemma sqrtRho_sq : sqrtRho ^ 2 = 1 / 512 := Real.sq_sqrt (by norm_num)
private lemma sqrtRho_nonneg : (0 : ℝ) ≤ sqrtRho := Real.sqrt_nonneg _

/-- Agreement cap `⌊α·N⌋ = 6082`: we prove `6082 ≤ α·131072 < 6083`. -/
theorem johnson_cap : (6082 : ℝ) ≤ alpha * 131072 ∧ alpha * 131072 < 6083 := by
  have h := sqrtRho_sq
  have hnn := sqrtRho_nonneg
  unfold alpha
  constructor <;> nlinarith [h, hnn]

/-! ## 3. Regime membership (proven Johnson, not capacity) -/

/-- `ρ < √ρ`: the agreement floor sits strictly above the capacity value. -/
theorem rho_lt_sqrtRho : (1 / 512 : ℝ) < sqrtRho := by
  have h := sqrtRho_sq; have hnn := sqrtRho_nonneg; nlinarith [h, hnn]

/-- `√ρ ≤ α`: agreement is at or above the *proven* Johnson list-decoding
threshold (equivalently `1 − α ≤ 1 − √ρ`), so soundness does not rely on the
capacity conjecture. -/
theorem sqrtRho_le_alpha : sqrtRho ≤ alpha := by
  unfold alpha; nlinarith [sqrtRho_nonneg]

/-- `ρ < α`: proximity `1 − α` is strictly inside the capacity radius `1 − ρ`. -/
theorem rho_lt_alpha : (1 / 512 : ℝ) < alpha :=
  lt_of_lt_of_le rho_lt_sqrtRho sqrtRho_le_alpha

/-! ## 4. Circle fibre-root conditions (Check 4) — kernel-checked bridge

The script (Check 4) walks all `2¹⁷ = 131072` arity-four fibre roots
`t = 2x² − 1` on the deployed M31 circle and checks two finite conditions: the
roots are pairwise distinct and none equals `1`.  Both are now kernel-checked
structurally (no `native_decide`, no 131072-way enumeration), split across two
imported files and composed here:

* `CircleGroupOrder.lean` builds the M31 circle group concretely, proves the
  x-collision criterion `x(P) = x(Q) ⟺ Q = P ∨ Q = P⁻¹`, pins the deployed
  generator's order (`orderOf_g : orderOf g = 2³¹`, kernel `decide` on a
  31-fold repeated squaring), and combines the two into `sameXCoord_exp`:
  `x(g^a) = x(g^b) ⟺ a ≡ ±b (mod 2³¹)`.
* `CircleFibreRoots.lean` proves by 2-adic valuation (`omega`) that the
  deployed doubled exponents `dⱼ = 2¹² + 2¹⁴·j`, `j < 2¹⁷`, are pairwise
  non-`±`-congruent and nonzero mod `2³¹` (`fiber_roots_distinct`,
  `fiber_root_ne_one`), stated over its `SameXCoord` collision interface.

The bridge theorem composes them: on the deployed circle group itself, the
fibre-root values `tⱼ = x(g^{dⱼ})` are pairwise distinct field elements and
none equals `1`.  `sameXCoord_exp` discharges the `SameXCoord` interface
hypothesis, so no geometric assumption remains in the statement.  Named
residues, for scope honesty: that `tⱼ` is the verifier's root of the `j`-th
fibre representative — `π(x(g^{eⱼ})) = x(g^{2eⱼ})`, `eⱼ = 2¹¹ + 2¹³·j` — is
the circle doubling formula recorded with the deployed walk constants in
`CircleFibreRoots.lean`'s header, and the exact circle cardinality `|C| = 2³¹`
remains the named interface `CircleCardInterface` in `CircleGroupOrder.lean`
(needed by no theorem here). -/

open AspisCircleFibreRoots AspisCircleGroupOrder in
/-- **Check 4, bridged.**  On the deployed M31 circle group with generator
`g = (2, 1268011823)`: the `2¹⁷` fibre-root values `x(g^{2¹² + 2¹⁴·j})` are
pairwise distinct, and none equals `1` (the ramified root value, the
x-coordinate of the identity).  Proved by composing `fiber_roots_distinct` /
`fiber_root_ne_one` (exponent arithmetic mod `2³¹`) with the proved x-collision
criterion `sameXCoord_exp` — no re-derivation, no enumeration. -/
theorem circle_fibre_root_conditions :
    (∀ i < 2 ^ 17, ∀ j < 2 ^ 17,
        X (g ^ fiberRootExp i) = X (g ^ fiberRootExp j) → i = j) ∧
    ∀ j < 2 ^ 17, X (g ^ fiberRootExp j) ≠ 1 := by
  constructor
  · intro i hi j hj hx
    exact fiber_roots_distinct i j hi hj ((sameXCoord_exp _ _).mp hx)
  · intro j hj hx
    have h0 : X (g ^ (0 : ℤ)) = 1 := by rw [zpow_zero]; exact one_re
    exact fiber_root_ne_one j hj
      ((sameXCoord_exp (fiberRootExp j) 0).mp (hx.trans h0.symm))

/-! ## 5a. Ledger event degrees (integer identities) -/

/-- Width-29 batch degree: `D` lane lifts `γ²⁷` to `γ²⁸`, i.e. `27 + 1 = 28`. -/
theorem deg_batch : 27 + 1 = 28 := by decide
/-- Three-point nonzero-γ numerator: `D` lifts `29 → 30`. -/
theorem deg_three_point : 29 + 1 = 30 := by decide
/-- Inactive-copy nonzero-γ numerator: `27 → 28`. -/
theorem deg_inactive : 27 + 1 = 28 := by decide
/-- Atomic tuple-compression degree `183 · 17 = 3111`. -/
theorem deg_tuple : 183 * 17 = 3111 := by decide
/-- Atomic copy/range-pole degree `4 · (183 + 1024) = 4828`. -/
theorem deg_poles : 4 * (183 + 1024) = 4828 := by decide
/-- Ten degree-27 zerocheck rounds: `10 · 27 = 270`. -/
theorem deg_ten_rounds : 10 * 27 = 270 := by decide

/-! ## 5a′. MCA generator hypothesis (width-29 scalar-powers generator) -/

/-- The generator width is 29. -/
theorem generator_width : (Finset.range 29).card = 29 := by decide
/-- `G`-lane exponent index 27 and `D`-lane index 28 are among the 29
exponents `γ⁰..γ²⁸`, and are distinct — the plain scalar-powers generator that
meets the MCA generator hypothesis. -/
theorem generator_indices :
    27 ∈ Finset.range 29 ∧ 28 ∈ Finset.range 29 ∧ (27 : ℕ) ≠ 28 := by decide

/-! ## 5b. Per-event Schwartz–Zippel / MCA probability bounds

Each event probability is `degree / |K|` (or `degree / (|K|−1)` for the
nonzero-γ / nonzero-η events).  We prove `probability ≤ 2^(-⌊bits⌋)`. -/

/-- Numeric term `24/|K| ≤ 2^(-119)`, intended as four degree-six
relation-sumcheck round errors.  This theorem proves only the arithmetic.  The
custom V5 argument that each bad claimed evaluation reaches one of those four
nonzero degree-six differences is a separate soundness obligation.  In
particular, this term does not itself cover adaptive cancellation through the
eight sequential OOD mix challenges or select one fixed member of the FRI
list.  The older release label “24 relation OOD mixers” is therefore
misleading: V5 has eight OOD mix challenges, not twenty-four. -/
theorem sz_relation_mixers : (24 : ℝ) / FIELD ≤ 1 / 2 ^ 119 := by
  unfold FIELD; norm_num
/-- Atomic θ-collision (deg 24): `24/|K| ≤ 2^(-119)`. -/
theorem sz_theta : (24 : ℝ) / FIELD ≤ 1 / 2 ^ 119 := by
  unfold FIELD; norm_num
/-- Nonzero-γ three-point batch (deg 30): `30/(|K|−1) ≤ 2^(-119)`. -/
theorem sz_three_point : (30 : ℝ) / (FIELD - 1) ≤ 1 / 2 ^ 119 := by
  unfold FIELD; norm_num
/-- Inactive-copy nonzero-γ (deg 28): `28/(|K|−1) ≤ 2^(-119)`. -/
theorem sz_inactive : (28 : ℝ) / (FIELD - 1) ≤ 1 / 2 ^ 119 := by
  unfold FIELD; norm_num
/-- Atomic tuple compression (deg 3111): `3111/|K| ≤ 2^(-112)`. -/
theorem sz_tuple : (3111 : ℝ) / FIELD ≤ 1 / 2 ^ 112 := by
  unfold FIELD; norm_num
/-- Atomic copy/range poles (deg 4828): `4828/|K| ≤ 2^(-111)`. -/
theorem sz_poles : (4828 : ℝ) / FIELD ≤ 1 / 2 ^ 111 := by
  unfold FIELD; norm_num
/-- Zerocheck equality point (deg 10): `10/|K| ≤ 2^(-120)`. -/
theorem sz_zerocheck_eq : (10 : ℝ) / FIELD ≤ 1 / 2 ^ 120 := by
  unfold FIELD; norm_num
/-- Zero-sum `H1` helper (deg 1): `1/|K| ≤ 2^(-123)`. -/
theorem sz_zero_sum : (1 : ℝ) / FIELD ≤ 1 / 2 ^ 123 := by
  unfold FIELD; norm_num
/-- Ten degree-27 zerocheck rounds (deg 270): `270/|K| ≤ 2^(-115)`. -/
theorem sz_ten_rounds : (270 : ℝ) / FIELD ≤ 1 / 2 ^ 115 := by
  unfold FIELD; norm_num
/-- Nonzero-η for the original mask: `1/(|K|−1) ≤ 2^(-123)`. -/
theorem sz_nonzero_eta : (1 : ℝ) / (FIELD - 1) ≤ 1 / 2 ^ 123 := by
  unfold FIELD; norm_num

/-! ## 5c. Two-sample OOD list union

`Σ_root  (240·239/2)·(root/(|K| − P²))²` over the root caps `[1024,255,63,15]`,
`P² = (2³¹−1)²`.  We prove `≤ 2^(-213)`. -/

theorem ood_list_union :
    ((240 * 239 / 2) * ((1024 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
      + (240 * 239 / 2) * ((255 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
      + (240 * 239 / 2) * ((63 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
      + (240 * 239 / 2) * ((15 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2)
      ≤ 1 / 2 ^ 213 := by
  unfold FIELD; norm_num

/-! ## 5d. Raw one-branch final `q18` miss

`(∏_{i=0}^{17} (A−i)/(N−i)) · 2^(-32)` with `A = 6082`, `N = 131072`.  We prove
`≤ 2^(-111)`. -/

theorem raw_query_miss :
    ((6082 : ℝ) / 131072) * (6081 / 131071) * (6080 / 131070) * (6079 / 131069)
      * (6078 / 131068) * (6077 / 131067) * (6076 / 131066) * (6075 / 131065)
      * (6074 / 131064) * (6073 / 131063) * (6072 / 131062) * (6071 / 131061)
      * (6070 / 131060) * (6069 / 131059) * (6068 / 131058) * (6067 / 131057)
      * (6066 / 131056) * (6065 / 131055) / 2 ^ 32 ≤ 1 / 2 ^ 111 := by
  norm_num

/-! ## 5e. Batch and fold-round bounds (MCA numerators with square roots)

The width-29 batch and the four WHIR fold rounds share one shape: with
`ℓ = (m + 1/2)/√ρ`, the event probability is

  `deg · ℓ · ((2ℓ⁴/3)·ρ + 1) · symbols / |K| / 2^work`.

Since `ℓ = (m+1/2)/√ρ` the numerator is `R/√ρ` with `R` rational, so the
probability is *decreasing* in `√ρ`; lower-bounding `√ρ ≥ l` by an explicit
rational `l` with `l² ≤ ρ` turns the bound into a rational inequality. -/

/-- Master bound for a square-root MCA/batch event: given a rational lower
bound `l ≤ √rr`, the event probability is `≤ 2^(-target)`. -/
theorem sqrt_event_bound
    (coeff mh rr symbols l : ℝ) (work target : ℕ)
    (hrr : 0 < rr) (hl : 0 < l) (hl2 : l ^ 2 ≤ rr)
    (hfin : (coeff * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols) * 2 ^ target
              ≤ l * FIELD * 2 ^ work) :
    coeff * (mh / Real.sqrt rr)
        * ((2 * (mh / Real.sqrt rr) ^ 4 / 3) * rr + 1) * symbols / FIELD / 2 ^ work
      ≤ 1 / 2 ^ target := by
  set s := Real.sqrt rr with hs
  have hs2 : s ^ 2 = rr := Real.sq_sqrt hrr.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hrr
  have hsl : l ≤ s := by nlinarith [sq_nonneg (s - l)]
  have hs4 : s ^ 4 = rr ^ 2 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
  have e4 : (mh / s) ^ 4 = mh ^ 4 / rr ^ 2 := by rw [div_pow, hs4]
  have enum : coeff * (mh / s) * ((2 * (mh / s) ^ 4 / 3) * rr + 1) * symbols
      = (coeff * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols) / s := by
    rw [e4]; field_simp
  rw [enum]
  set R := coeff * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols with hRdef
  have hFpos := FIELD_pos
  have key : R * 2 ^ target ≤ s * FIELD * 2 ^ work := by
    have h1 : l * FIELD * 2 ^ work ≤ s * FIELD * 2 ^ work :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsl hFpos.le) (by positivity)
    linarith [hfin]
  have hden : (0 : ℝ) < s * FIELD * 2 ^ work := mul_pos (mul_pos hspos hFpos) (by positivity)
  have hrw : R / s / FIELD / 2 ^ work = R / (s * FIELD * 2 ^ work) := by
    rw [div_div, div_div]; ring_nf
  rw [hrw, div_le_div_iff₀ hden (by positivity)]
  nlinarith [key]

/-- Width-29 polynomial batch (deg 28, `ρ = 1/512`, `2¹⁹` symbols, +37 work):
`≤ 2^(-107)`. -/
theorem batch_bound :
    (28 : ℝ) * ((21 / 2) / Real.sqrt (1 / 512))
      * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1) * 524288
      / FIELD / 2 ^ 37 ≤ 1 / 2 ^ 107 :=
  sqrt_event_bound 28 (21 / 2) (1 / 512) 524288 (4419417 / 100000000) 37 107
    (by norm_num) (by norm_num) (by norm_num) (by unfold FIELD; norm_num)

/-- Fold round 0 (deg 3, `m = 10`, `ρ = 255/131072`, `2¹⁷` symbols, +34): `≤ 2^(-109)`. -/
theorem fold0_bound :
    (3 : ℝ) * ((21 / 2) / Real.sqrt (255 / 131072))
      * ((2 * ((21 / 2) / Real.sqrt (255 / 131072)) ^ 4 / 3) * (255 / 131072) + 1) * 131072
      / FIELD / 2 ^ 34 ≤ 1 / 2 ^ 109 :=
  sqrt_event_bound 3 (21 / 2) (255 / 131072) 131072 (4410777 / 100000000) 34 109
    (by norm_num) (by norm_num) (by norm_num) (by unfold FIELD; norm_num)

/-- Fold round 1 (deg 3, `m = 9`, `ρ = 63/32768`, `2¹⁵` symbols, +33): `≤ 2^(-111)`. -/
theorem fold1_bound :
    (3 : ℝ) * ((19 / 2) / Real.sqrt (63 / 32768))
      * ((2 * ((19 / 2) / Real.sqrt (63 / 32768)) ^ 4 / 3) * (63 / 32768) + 1) * 32768
      / FIELD / 2 ^ 33 ≤ 1 / 2 ^ 111 :=
  sqrt_event_bound 3 (19 / 2) (63 / 32768) 32768 (2192377 / 50000000) 33 111
    (by norm_num) (by norm_num) (by norm_num) (by unfold FIELD; norm_num)

/-- Fold round 2 (deg 3, `m = 6`, `ρ = 15/8192`, `2¹³` symbols, +30): `≤ 2^(-112)`. -/
theorem fold2_bound :
    (3 : ℝ) * ((13 / 2) / Real.sqrt (15 / 8192))
      * ((2 * ((13 / 2) / Real.sqrt (15 / 8192)) ^ 4 / 3) * (15 / 8192) + 1) * 8192
      / FIELD / 2 ^ 30 ≤ 1 / 2 ^ 112 :=
  sqrt_event_bound 3 (13 / 2) (15 / 8192) 8192 (2139541 / 50000000) 30 112
    (by norm_num) (by norm_num) (by norm_num) (by unfold FIELD; norm_num)

/-- Fold round 3 (deg 3, `m = 3`, `ρ = 3/2048`, `2¹¹` symbols, +25): `≤ 2^(-113)`. -/
theorem fold3_bound :
    (3 : ℝ) * ((7 / 2) / Real.sqrt (3 / 2048))
      * ((2 * ((7 / 2) / Real.sqrt (3 / 2048)) ^ 4 / 3) * (3 / 2048) + 1) * 2048
      / FIELD / 2 ^ 25 ≤ 1 / 2 ^ 113 :=
  sqrt_event_bound 3 (7 / 2) (3 / 2048) 2048 (3827327 / 100000000) 25 113
    (by norm_num) (by norm_num) (by norm_num) (by unfold FIELD; norm_num)

/-! ## 5f. Event-union arithmetic

Given the per-event probability bounds above, the union bound `P(∪Eᵢ) ≤ ΣP(Eᵢ)`
(a standard fact, not re-proved) reduces the ledger endpoints to rational sums of
the per-event upper bounds. -/

/-- Four-fold WHIR union: the sum of the fold-round upper bounds is `≤ 2^(-108)`.
Combined with `fold0..3_bound` this bounds the four-fold union event. -/
theorem fold_union :
    (1 / 2 ^ 109 + 1 / 2 ^ 111 + 1 / 2 ^ 112 + 1 / 2 ^ 113 : ℝ) ≤ 1 / 2 ^ 108 := by
  norm_num

/-- Coarse whole-ledger event union: the sum of all sixteen per-event upper
bounds (batch 107, four-fold union 108, raw-query 111, OOD 213, and the twelve
local / reserve terms) is `≤ 2^(-106)`. -/
theorem coarse_event_union :
    (1 / 2 ^ 107 + 1 / 2 ^ 108 + 1 / 2 ^ 111 + 1 / 2 ^ 213
      + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 112
      + 1 / 2 ^ 111 + 1 / 2 ^ 119 + 1 / 2 ^ 120 + 1 / 2 ^ 123
      + 1 / 2 ^ 123 + 1 / 2 ^ 115 + 1 / 2 ^ 124 + 1 / 2 ^ 128 : ℝ)
      ≤ 1 / 2 ^ 106 := by
  norm_num

/-- The `×3` whole-ledger inflation of the coarse union is `≤ 2^(-104)`.  (The
further BCS work-normalization erosion down to the ~100-bit release endpoint
mixes `Real.logb` with additive `2^(-256)` terms and stays Python-verified.) -/
theorem coarse_union_times_three :
    3 * (1 / 2 ^ 107 + 1 / 2 ^ 108 + 1 / 2 ^ 111 + 1 / 2 ^ 213
      + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 112
      + 1 / 2 ^ 111 + 1 / 2 ^ 119 + 1 / 2 ^ 120 + 1 / 2 ^ 123
      + 1 / 2 ^ 123 + 1 / 2 ^ 115 + 1 / 2 ^ 124 + 1 / 2 ^ 128 : ℝ)
      ≤ 1 / 2 ^ 104 := by
  norm_num

end AspisSoundnessLedger

-- Axiom audit: every theorem must rest only on [propext, Classical.choice, Quot.sound].
#print axioms AspisSoundnessLedger.johnson_cap
#print axioms AspisSoundnessLedger.rho_lt_alpha
#print axioms AspisSoundnessLedger.circle_fibre_root_conditions
#print axioms AspisSoundnessLedger.deg_tuple
#print axioms AspisSoundnessLedger.generator_indices
#print axioms AspisSoundnessLedger.sz_relation_mixers
#print axioms AspisSoundnessLedger.sz_nonzero_eta
#print axioms AspisSoundnessLedger.ood_list_union
#print axioms AspisSoundnessLedger.raw_query_miss
#print axioms AspisSoundnessLedger.batch_bound
#print axioms AspisSoundnessLedger.fold0_bound
#print axioms AspisSoundnessLedger.fold3_bound
#print axioms AspisSoundnessLedger.coarse_event_union
#print axioms AspisSoundnessLedger.coarse_union_times_three
