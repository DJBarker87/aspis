import AspisFormal.SoundnessLedger

/-!
# Kernel-checked BCS work-normalized soundness endpoint (Check 5b)

`SoundnessLedger.lean` kernel-checks the *interactive* soundness floor: the
coarse whole-ledger event union `≤ 2^(-106)` (`coarse_event_union`) and its `×3`
selector inflation `≤ 2^(-104)` (`coarse_union_times_three`).  Its docstring
records that the remaining step — the BCS/Fiat–Shamir *work-normalized release*
endpoint (the `~100.16`-bit figure `tools/verify_soundness_params.py` prints in
its `[5b]` block) — stays Python-only, because it mixes `Real.logb` with additive
`2^(-256)` terms.  This file moves that endpoint into the kernel.

## What the Python checker does (`bcs_work_normalized_bits` + `check_union_and_floor`)

With `eps_round` the interactive round-soundness error, the adversary's
random-oracle query budget `T`, the cited BCS extractor work factor `R = 32`, and
the random-oracle capacity `Λ = 256`, the BCS transform gives a soundness error

  `eps_bcs(T) = (1 + R/T)·eps_round + 3·(T + 1/T)·2^(-Λ)`.

The release figure is `3 · eps_bcs` (the `×3` whole-ledger selector inflation),
evaluated at the worst endpoint of the adversary budget `T ∈ [1, 2^128]`.  The
worst endpoint is `T = 1`, where `(1 + R/T) = 33` and `3·(1 + R/T) = 99`, and the
Python prints `100.16` bits, i.e. release error `≤ 2^(-100.16)`.

## The cited interface (named, not re-proved)

`bcsError` below is the *arithmetic form* of the BCS transform soundness bound
[Ben-Sasson–Chiesa–Spooner, *Interactive Oracle Proofs* — state-restoration
soundness composed with the random-oracle extractor].  We take this functional
form as given and prove **only its arithmetic consequence** at the pinned
constants; we do not re-prove the BCS extractor theorem.  The cited numbers are
the named constants `R_BCS = 32`, `roCapErr = 2^(-256)` (Λ = 256), and the
whole-ledger `selectorInflation = 3`.  They enter every theorem as *explicit
hypotheses* `R ≤ R_BCS`, `capErr ≤ roCapErr` (monotone: larger is worse), never as
silent literals.

## An honest arithmetic finding

The ledger's *floored* endpoints are too coarse to survive the work-normalization.
Amplifying the interactive floor by the `T = 1` BCS factor and the `×3` inflation
multiplies the error by `99`, and `99` costs `log₂ 99 ≈ 6.63` bits — more than the
`~0.5` bits the ledger already rounded away when it floored each per-event bit to
an integer.  Concretely `99·2^(-106) = 2^(-99.37)` and `33·2^(-104) = 2^(-98.96)`,
both **above** `2^(-100)` (`coarse_floor_insufficient`,
`floor_times_three_insufficient` below).  So one cannot reach the `≥ 100`-bit
release endpoint from `coarse_event_union` / `coarse_union_times_three` alone.
We therefore re-derive the *tight* (un-floored) union `roundError ≤ unionBound`
with `unionBound = 2^(-106.72)` — tight enough that `99·unionBound + 2^(-256)`
terms stay `≤ 2^(-100)`.  Only the five `Real.sqrt` events (the width-29 batch and
the four WHIR fold rounds) need new tight bounds; the fourteen exact-rational
events reuse the ledger's own per-event theorems verbatim.

## Scope, stated honestly

* As in the ledger, every constant is a Lean literal; nothing here proves these
  equal the constants compiled into the Rust verifier.
* The `2^(-256)` additive terms are **kept**, not dropped: they appear in
  `bcsError` and are carried (bounded by `9·(2^128 + 1)·2^(-256) ≤ 2^(-124)`,
  `bcs_additive_le`) through to the final inequality.
* We prove the security-meaningful integer endpoint `error ≤ 2^(-100)` /
  `min-entropy ≥ 100` bits.  The Python's exact figure is `100.16`; our
  `unionBound = 2^(-106.72)` under-approximates the true union `2^(-106.79)` by
  `~0.07` bits, and the `≥ 100`-bit endpoint drops the remaining `0.16` fractional
  bit of margin — exactly as the ledger drops fractional bits for its integer
  floors.  This is an honest rational under-approximation of `100.16`, still
  `≥ 100`.
-/

namespace AspisWorkNormalizedEndpoint

open AspisSoundnessLedger

/-! ## 1. The cited BCS interface (named constants, not re-proved) -/

/-- Cited BCS/Fiat–Shamir extractor work factor `R = 32` — the `R` in the
`(1 + R/T)` round-to-standard-soundness loss.  Taken from the BCS transform, not
derived here. -/
def R_BCS : ℝ := 32

/-- Cited random-oracle capacity term `2^(-Λ)` with `Λ = 256` — the base of the
additive soundness terms in the BCS bound.  Taken as cited. -/
noncomputable def roCapErr : ℝ := 1 / 2 ^ 256

/-- Whole-ledger selector inflation `×3` (three spend selectors share one
transcript); a union bound, applied after work-normalization. -/
def selectorInflation : ℝ := 3

/-- **Cited BCS interface (functional form, not re-proved).**  The BCS/Fiat–Shamir
work-normalized soundness error as an explicit function of the interactive round
error `epsRound`, the adversary random-oracle query budget `T`, the extractor
work factor `R`, and the capacity term `capErr = 2^(-Λ)`.  This mirrors
`bcs_work_normalized_bits` in `tools/verify_soundness_params.py`:
`eps_bcs = (1 + R/T)·eps_round + 3·(T + 1/T)·2^(-Λ)`. -/
noncomputable def bcsError (epsRound T R capErr : ℝ) : ℝ :=
  (1 + R / T) * epsRound + 3 * (T + 1 / T) * capErr

/-! ## 2. A tight rational bound for a square-root (batch / fold) event

Companion to the ledger's `sqrt_event_bound`, which concludes `≤ 1/2^target` for
an *integer* `target`.  For the work-normalization we need bounds tighter than an
integer power of two, so we generalise the conclusion to an arbitrary rational
`q`.  Given the same rational lower bound `l ≤ √rr` on the square root, the event
probability `R/(√rr · |K| · 2^work)` is `≤ q` whenever `R ≤ q · (l · |K| · 2^work)`. -/
theorem sqrt_event_le
    (coeff mh rr symbols l q : ℝ) (work : ℕ)
    (hrr : 0 < rr) (hl : 0 < l) (hl2 : l ^ 2 ≤ rr) (hq : 0 ≤ q)
    (hfin : coeff * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols
              ≤ q * (l * FIELD * 2 ^ work)) :
    coeff * (mh / Real.sqrt rr)
        * ((2 * (mh / Real.sqrt rr) ^ 4 / 3) * rr + 1) * symbols / FIELD / 2 ^ work
      ≤ q := by
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
  have hden : (0 : ℝ) < s * FIELD * 2 ^ work :=
    mul_pos (mul_pos hspos hFpos) (by positivity)
  have hrw : R / s / FIELD / 2 ^ work = R / (s * FIELD * 2 ^ work) := by
    rw [div_div, div_div]; ring_nf
  rw [hrw, div_le_iff₀ hden]
  have hmono : l * FIELD * 2 ^ work ≤ s * FIELD * 2 ^ work :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsl hFpos.le) (by positivity)
  have step : q * (l * FIELD * 2 ^ work) ≤ q * (s * FIELD * 2 ^ work) :=
    mul_le_mul_of_nonneg_left hmono hq
  linarith [hfin, step]

/-! ## 3. The interactive soundness round error (the tight union)

`roundError` is the sum of all nineteen individual event probabilities — the
*true* whole-ledger union, the object the ledger's `coarse_event_union` bounds by
the (too coarse) integer floor `2^(-106)`.  We reuse the ledger's per-event
expressions verbatim so the terms are literally the same objects. -/

/-- Width-29 polynomial batch event (deg 28, `ρ = 1/512`, `2¹⁹` symbols, +37
work).  Same expression as `AspisSoundnessLedger.batch_bound`. -/
noncomputable def batchTerm : ℝ :=
  (28 : ℝ) * ((21 / 2) / Real.sqrt (1 / 512))
    * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1) * 524288
    / FIELD / 2 ^ 37

/-- WHIR fold round 0.  Same expression as `AspisSoundnessLedger.fold0_bound`. -/
noncomputable def fold0Term : ℝ :=
  (3 : ℝ) * ((21 / 2) / Real.sqrt (255 / 131072))
    * ((2 * ((21 / 2) / Real.sqrt (255 / 131072)) ^ 4 / 3) * (255 / 131072) + 1) * 131072
    / FIELD / 2 ^ 34

/-- WHIR fold round 1.  Same expression as `AspisSoundnessLedger.fold1_bound`. -/
noncomputable def fold1Term : ℝ :=
  (3 : ℝ) * ((19 / 2) / Real.sqrt (63 / 32768))
    * ((2 * ((19 / 2) / Real.sqrt (63 / 32768)) ^ 4 / 3) * (63 / 32768) + 1) * 32768
    / FIELD / 2 ^ 33

/-- WHIR fold round 2.  Same expression as `AspisSoundnessLedger.fold2_bound`. -/
noncomputable def fold2Term : ℝ :=
  (3 : ℝ) * ((13 / 2) / Real.sqrt (15 / 8192))
    * ((2 * ((13 / 2) / Real.sqrt (15 / 8192)) ^ 4 / 3) * (15 / 8192) + 1) * 8192
    / FIELD / 2 ^ 30

/-- WHIR fold round 3.  Same expression as `AspisSoundnessLedger.fold3_bound`. -/
noncomputable def fold3Term : ℝ :=
  (3 : ℝ) * ((7 / 2) / Real.sqrt (3 / 2048))
    * ((2 * ((7 / 2) / Real.sqrt (3 / 2048)) ^ 4 / 3) * (3 / 2048) + 1) * 2048
    / FIELD / 2 ^ 25

/-- Raw one-branch final `q18` miss.  Same expression as
`AspisSoundnessLedger.raw_query_miss`. -/
noncomputable def rawTerm : ℝ :=
  ((6082 : ℝ) / 131072) * (6081 / 131071) * (6080 / 131070) * (6079 / 131069)
    * (6078 / 131068) * (6077 / 131067) * (6076 / 131066) * (6075 / 131065)
    * (6074 / 131064) * (6073 / 131063) * (6072 / 131062) * (6071 / 131061)
    * (6070 / 131060) * (6069 / 131059) * (6068 / 131058) * (6067 / 131057)
    * (6066 / 131056) * (6065 / 131055) / 2 ^ 32

/-- Two-sample OOD list union.  Same expression as
`AspisSoundnessLedger.ood_list_union`. -/
noncomputable def oodTerm : ℝ :=
  (240 * 239 / 2) * ((1024 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
    + (240 * 239 / 2) * ((255 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
    + (240 * 239 / 2) * ((63 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2
    + (240 * 239 / 2) * ((15 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2

/-- The interactive whole-ledger soundness round error `eps_round^(0)`: the sum of
all nineteen event probabilities.  This is the tight union that
`AspisSoundnessLedger.coarse_event_union` bounds by the integer floor `2^(-106)`;
here we keep it un-floored so it survives the work-normalization. -/
noncomputable def roundError : ℝ :=
  batchTerm + fold0Term + fold1Term + fold2Term + fold3Term
    + rawTerm + oodTerm
    + 24 / FIELD + 24 / FIELD + 30 / (FIELD - 1) + 28 / (FIELD - 1)
    + 3111 / FIELD + 4828 / FIELD + 10 / FIELD + 1 / FIELD + 1 / (FIELD - 1)
    + 270 / FIELD
    + 1 / 2 ^ 124 + 1 / 2 ^ 128

/-- The tight dyadic union upper bound `unionBound = 2^(-106.72)`: the five
`Real.sqrt` events bounded by tight small-numerator dyadics, the fourteen exact
events bounded by the ledger's own per-event theorems.  Its `-log₂` is `106.72`,
strictly above the `100 + log₂ 99 = 106.629` threshold the release endpoint needs. -/
noncomputable def unionBound : ℝ :=
  3291 / 2 ^ 119 + 2837 / 2 ^ 121 + 3502 / 2 ^ 123 + 2260 / 2 ^ 124 + 2288 / 2 ^ 125
    + 1 / 2 ^ 111 + 1 / 2 ^ 213
    + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119
    + 1 / 2 ^ 112 + 1 / 2 ^ 111 + 1 / 2 ^ 120 + 1 / 2 ^ 123 + 1 / 2 ^ 123
    + 1 / 2 ^ 115
    + 1 / 2 ^ 124 + 1 / 2 ^ 128

/-! ### 3a. Per-event tight bounds -/

/-- Batch event `≤ 3291/2^119 ≈ 2^(-107.316)` (tight; the ledger's floor is the
looser `2^(-107)`). -/
theorem batchTerm_le : batchTerm ≤ 3291 / 2 ^ 119 := by
  unfold batchTerm
  exact sqrt_event_le 28 (21 / 2) (1 / 512) 524288 (4419417 / 100000000)
    (3291 / 2 ^ 119) 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold FIELD; norm_num)

/-- Fold round 0 `≤ 2837/2^121 ≈ 2^(-109.530)` (tight). -/
theorem fold0Term_le : fold0Term ≤ 2837 / 2 ^ 121 := by
  unfold fold0Term
  exact sqrt_event_le 3 (21 / 2) (255 / 131072) 131072 (4410777 / 100000000)
    (2837 / 2 ^ 121) 34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold FIELD; norm_num)

/-- Fold round 1 `≤ 3502/2^123 ≈ 2^(-111.226)` (tight). -/
theorem fold1Term_le : fold1Term ≤ 3502 / 2 ^ 123 := by
  unfold fold1Term
  exact sqrt_event_le 3 (19 / 2) (63 / 32768) 32768 (2192377 / 50000000)
    (3502 / 2 ^ 123) 33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold FIELD; norm_num)

/-- Fold round 2 `≤ 2260/2^124 ≈ 2^(-112.858)` (tight). -/
theorem fold2Term_le : fold2Term ≤ 2260 / 2 ^ 124 := by
  unfold fold2Term
  exact sqrt_event_le 3 (13 / 2) (15 / 8192) 8192 (2139541 / 50000000)
    (2260 / 2 ^ 124) 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold FIELD; norm_num)

/-- Fold round 3 `≤ 2288/2^125 ≈ 2^(-113.840)` (tight). -/
theorem fold3Term_le : fold3Term ≤ 2288 / 2 ^ 125 := by
  unfold fold3Term
  exact sqrt_event_le 3 (7 / 2) (3 / 2048) 2048 (3827327 / 100000000)
    (2288 / 2 ^ 125) 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold FIELD; norm_num)

/-- The tight union bound holds: `roundError ≤ unionBound`.  Combines the five
tight square-root bounds above with the ledger's fourteen exact per-event
theorems (`raw_query_miss`, `ood_list_union`, and the `sz_*` Schwartz–Zippel
bounds), plus the two policy reserves. -/
theorem roundError_le_unionBound : roundError ≤ unionBound := by
  unfold roundError unionBound
  linarith [batchTerm_le, fold0Term_le, fold1Term_le, fold2Term_le, fold3Term_le,
    (show rawTerm ≤ 1 / 2 ^ 111 by unfold rawTerm; exact raw_query_miss),
    (show oodTerm ≤ 1 / 2 ^ 213 by unfold oodTerm; exact ood_list_union),
    sz_relation_mixers, sz_theta, sz_three_point, sz_inactive, sz_tuple, sz_poles,
    sz_zerocheck_eq, sz_zero_sum, sz_nonzero_eta, sz_ten_rounds]

/-- The interactive round error is strictly positive (it contains the strictly
positive reserve `2^(-128)` and every other term is nonnegative). -/
theorem roundError_pos : 0 < roundError := by
  have hF : (0 : ℝ) < FIELD := FIELD_pos
  have hF1 : (0 : ℝ) < FIELD - 1 := by unfold FIELD; norm_num
  have hFo : (0 : ℝ) < FIELD - (2 ^ 31 - 1) ^ 2 := by unfold FIELD; norm_num
  have hbatch : 0 ≤ batchTerm := by unfold batchTerm; unfold FIELD; positivity
  have hf0 : 0 ≤ fold0Term := by unfold fold0Term; unfold FIELD; positivity
  have hf1 : 0 ≤ fold1Term := by unfold fold1Term; unfold FIELD; positivity
  have hf2 : 0 ≤ fold2Term := by unfold fold2Term; unfold FIELD; positivity
  have hf3 : 0 ≤ fold3Term := by unfold fold3Term; unfold FIELD; positivity
  have hraw : 0 ≤ rawTerm := by unfold rawTerm; positivity
  have hood : 0 ≤ oodTerm := by
    unfold oodTerm
    have h1 : (0 : ℝ) ≤ (240 * 239 / 2) * ((1024 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (240 * 239 / 2) * ((255 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h3 : (0 : ℝ) ≤ (240 * 239 / 2) * ((63 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h4 : (0 : ℝ) ≤ (240 * 239 / 2) * ((15 : ℝ) / (FIELD - (2 ^ 31 - 1) ^ 2)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    linarith [h1, h2, h3, h4]
  have hf1d : (0 : ℝ) ≤ 30 / (FIELD - 1) := div_nonneg (by norm_num) hF1.le
  have hf1e : (0 : ℝ) ≤ 28 / (FIELD - 1) := div_nonneg (by norm_num) hF1.le
  have hf1f : (0 : ℝ) ≤ 1 / (FIELD - 1) := div_nonneg (by norm_num) hF1.le
  have hd24 : (0 : ℝ) ≤ 24 / FIELD := div_nonneg (by norm_num) hF.le
  have hd3111 : (0 : ℝ) ≤ 3111 / FIELD := div_nonneg (by norm_num) hF.le
  have hd4828 : (0 : ℝ) ≤ 4828 / FIELD := div_nonneg (by norm_num) hF.le
  have hd10 : (0 : ℝ) ≤ 10 / FIELD := div_nonneg (by norm_num) hF.le
  have hd1 : (0 : ℝ) ≤ 1 / FIELD := div_nonneg (by norm_num) hF.le
  have hd270 : (0 : ℝ) ≤ 270 / FIELD := div_nonneg (by norm_num) hF.le
  unfold roundError
  have hsha : (0 : ℝ) < 1 / 2 ^ 128 := by norm_num
  have hpos124 : (0 : ℝ) ≤ 1 / 2 ^ 124 := by norm_num
  linarith [hbatch, hf0, hf1, hf2, hf3, hraw, hood, hf1d, hf1e, hf1f, hd24,
    hd3111, hd4828, hd10, hd1, hd270, hsha, hpos124]

/-! ## 4. The floors are too coarse — why the tight union is required

These two facts document the honest finding: the ledger's *floored* endpoints,
amplified by the work-normalization, land **above** `2^(-100)`.  The endpoint can
therefore not be obtained from `coarse_event_union` / `coarse_union_times_three`
alone; the tight `roundError ≤ unionBound` above is what makes it go through. -/

/-- The coarse interactive floor `2^(-106)`, times the `T = 1` BCS factor `33` and
the `×3` inflation (`= 99`), exceeds `2^(-100)`: `2^(-100) < 99·2^(-106)`. -/
theorem coarse_floor_insufficient : (1 : ℝ) / 2 ^ 100 < 99 * (1 / 2 ^ 106) := by
  norm_num

/-- The already-inflated floor `2^(-104)`, times the `T = 1` BCS factor `33`,
exceeds `2^(-100)`: `2^(-100) < 33·2^(-104)`. -/
theorem floor_times_three_insufficient : (1 : ℝ) / 2 ^ 100 < 33 * (1 / 2 ^ 104) := by
  norm_num

/-- The carried `2^(-256)` additive mass over the whole budget `T ∈ [1, 2^128]`
is negligible: `9·(2^128 + 1)·2^(-256) ≤ 2^(-124)`.  Kept explicitly, not dropped. -/
theorem bcs_additive_le :
    9 * (2 ^ 128 + 1) * (1 / 2 ^ 256) ≤ (1 : ℝ) / 2 ^ 124 := by
  norm_num

/-! ## 5. The work-normalized release endpoint -/

/-- **Work-normalized release endpoint (the arithmetic core).**  For *any*
interactive round error `epsRound ≤ unionBound`, any cited BCS work factor
`R ≤ R_BCS = 32`, any capacity term `capErr ≤ roCapErr = 2^(-256)`, and any
adversary random-oracle query budget `T ∈ [1, 2^128]`, the `×3` whole-ledger
work-normalized soundness error is `≤ 2^(-100)`.

The `2^(-256)` additive terms of `bcsError` are carried through, bounded over the
whole budget by `9·(2^128 + 1)·2^(-256)`; the worst budget is `T = 1`, where
`3·(1 + R/T) = 99`. -/
theorem work_normalized_endpoint
    (epsRound R capErr T : ℝ)
    (hround0 : 0 ≤ epsRound) (hround : epsRound ≤ unionBound)
    (_hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation * bcsError epsRound T R capErr ≤ 1 / 2 ^ 100 := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hRT : R / T ≤ 32 := by
    rw [div_le_iff₀ hTpos]; unfold R_BCS at hR; nlinarith [hR, hT1]
  have h1T : 1 / T ≤ 1 := by rw [div_le_one hTpos]; exact hT1
  have hcap' : capErr ≤ 1 / 2 ^ 256 := by unfold roCapErr at hcap; exact hcap
  -- first summand of `bcsError`
  have hA : (1 + R / T) * epsRound ≤ 33 * unionBound := by
    have h1 : (1 + R / T) * epsRound ≤ 33 * epsRound :=
      mul_le_mul_of_nonneg_right (by linarith [hRT]) hround0
    have h2 : 33 * epsRound ≤ 33 * unionBound := by linarith [hround]
    linarith [h1, h2]
  -- second summand of `bcsError`
  have hB : 3 * (T + 1 / T) * capErr ≤ 3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    have hTsum : T + 1 / T ≤ 2 ^ 128 + 1 := by linarith [hTmax, h1T]
    have h1 : 3 * (T + 1 / T) * capErr ≤ 3 * (2 ^ 128 + 1) * capErr :=
      mul_le_mul_of_nonneg_right (by linarith [hTsum]) hcapnn
    have h2 : 3 * (2 ^ 128 + 1) * capErr ≤ 3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) :=
      mul_le_mul_of_nonneg_left hcap' (by positivity)
    linarith [h1, h2]
  have hbcs : bcsError epsRound T R capErr
      ≤ 33 * unionBound + 3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    unfold bcsError; linarith [hA, hB]
  have hfinal : selectorInflation * bcsError epsRound T R capErr
      ≤ selectorInflation * (33 * unionBound + 3 * (2 ^ 128 + 1) * (1 / 2 ^ 256)) :=
    mul_le_mul_of_nonneg_left hbcs (by unfold selectorInflation; norm_num)
  refine le_trans hfinal ?_
  unfold selectorInflation unionBound
  norm_num

/-- The endpoint at the *actual* interactive round error `roundError`: the `×3`
work-normalized soundness error of the whole ledger is `≤ 2^(-100)`. -/
theorem release_endpoint
    (R capErr T : ℝ)
    (hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation * bcsError roundError T R capErr ≤ 1 / 2 ^ 100 :=
  work_normalized_endpoint roundError R capErr T roundError_pos.le
    roundError_le_unionBound hRnn hR hcapnn hcap hT1 hTmax

/-- **Min-entropy reading (via `Real.logb`).**  The whole-ledger work-normalized
release soundness has at least `100` bits of security: for the cited BCS
constants (`R ≤ 32`, `capErr ≤ 2^(-256)`) and any adversary budget
`T ∈ [1, 2^128]`,

  `100 ≤ -log₂ (3 · bcsError roundError T R capErr)`. -/
theorem release_min_entropy_ge
    (R capErr T : ℝ)
    (hRnn : 0 ≤ R) (hR : R ≤ R_BCS)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    100 ≤ - Real.logb 2 (selectorInflation * bcsError roundError T R capErr) := by
  set E := selectorInflation * bcsError roundError T R capErr with hE
  have hle : E ≤ 1 / 2 ^ 100 :=
    release_endpoint R capErr T hRnn hR hcapnn hcap hT1 hTmax
  -- `E > 0`
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hEpos : 0 < E := by
    rw [hE]; unfold selectorInflation bcsError
    have h1 : 0 < (1 + R / T) * roundError := by
      apply mul_pos _ roundError_pos
      have : 0 ≤ R / T := div_nonneg hRnn hTpos.le
      linarith
    have h2 : 0 ≤ 3 * (T + 1 / T) * capErr := by
      have : 0 ≤ T + 1 / T := by positivity
      positivity
    nlinarith [h1, h2]
  -- monotonicity of `log`, then `logb`
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hval : Real.logb 2 ((1 : ℝ) / 2 ^ 100) = -100 := by
    rw [Real.logb, show (1 : ℝ) / 2 ^ 100 = ((2 : ℝ) ^ 100)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow, neg_div, mul_div_assoc, div_self hlog2, mul_one]
    norm_num
  have hmono : Real.logb 2 E ≤ Real.logb 2 ((1 : ℝ) / 2 ^ 100) := by
    rw [Real.logb, Real.logb]
    exact div_le_div_of_nonneg_right (Real.log_le_log hEpos hle) hlog2pos.le
  rw [hval] at hmono
  linarith [hmono]

end AspisWorkNormalizedEndpoint

-- Axiom audit: every exported theorem must rest only on
-- [propext, Classical.choice, Quot.sound].
#print axioms AspisWorkNormalizedEndpoint.sqrt_event_le
#print axioms AspisWorkNormalizedEndpoint.batchTerm_le
#print axioms AspisWorkNormalizedEndpoint.fold0Term_le
#print axioms AspisWorkNormalizedEndpoint.fold1Term_le
#print axioms AspisWorkNormalizedEndpoint.fold2Term_le
#print axioms AspisWorkNormalizedEndpoint.fold3Term_le
#print axioms AspisWorkNormalizedEndpoint.roundError_le_unionBound
#print axioms AspisWorkNormalizedEndpoint.roundError_pos
#print axioms AspisWorkNormalizedEndpoint.coarse_floor_insufficient
#print axioms AspisWorkNormalizedEndpoint.floor_times_three_insufficient
#print axioms AspisWorkNormalizedEndpoint.bcs_additive_le
#print axioms AspisWorkNormalizedEndpoint.work_normalized_endpoint
#print axioms AspisWorkNormalizedEndpoint.release_endpoint
#print axioms AspisWorkNormalizedEndpoint.release_min_entropy_ge
