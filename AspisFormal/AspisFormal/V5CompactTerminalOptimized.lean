import AspisFormal.V5CompactTerminal

/-!
# The deployed optimized compact component-B terminal evaluator

`V5CompactTerminal` works with the dense spelling of the component-B terminal
check: four `dualFold4` applications to the sparse 1,024-row `terminalWeights`
covector, followed by a four-value dot.  The deployed Rust evaluator
(`CompactBTerminalWeights` in `programs/aspis-verifier/src/v5_cu_probe.rs`,
the mode-9/tag-67 `FourClaimsCompact` path) never materialises those 1,024
values.  It carries ten structured blocks — a running scale, two power
registers advanced by repeated squaring, and the five-bit block selector from
`[0, 1, 2, 3, 4, 5, 6, 28, 29, 30]` — plus one `delta_scale` register for the
initial-state row 992, and updates them through four hand-scheduled fold
transitions before scattering into four final weights.

This module models that state machine as an independent definition,
`optimizedCompactFinalDot`, built only from the block-selector table and the
terminal point.  It never mentions `terminalWeights`, `dualFold4`, or any
other dense-side value.  The exported theorems then prove, in the kernel, that
after `k` optimized folds the sparse vector represented by the machine state
equals the `k`-fold dense partial fold of `terminalWeights`, and hence that
the deployed evaluator's final dot equals the dense four-fold terminal
evaluation.  Row 993 is the inactive dependent pivot: it carries weight zero
in `terminalWeights` and correspondingly has no register in the machine.

The identification of the Lean transition functions with the executable Rust
`CompactBTerminalWeights::new`/`fold`/`final_weights`/`dot` bodies is a named
executable-correspondence obligation, recorded in the final section of this
docstring; it is an interface assumption, not a theorem of this module.  The
same applies to the arithmetic of `QM31` being a field of characteristic
`≠ 2`: the theorems take the corresponding hypothesis on the abstract field.

## Interface obligations (assumed, not proved here)

* `RustCompactFoldModel`: `optimizedInit`, `optimizedFoldZero`,
  `optimizedFoldOne`, `optimizedFoldTwo`, `optimizedFoldThree`,
  `optimizedFinalWeights`, and the final dot are transcriptions of
  `CompactBTerminalWeights::{new, fold, final_weights, dot}`; the Rust
  `half()` is multiplication by the inverse of two.  No Lean theorem relates
  the transcription to the compiled program.
* `QM31FieldModel`: the concrete coefficient field satisfies the `Field` and
  `(2 : K) ≠ 0` hypotheses used below.
-/

open scoped BigOperators

namespace AspisV5CompactTerminalOptimized

open AspisV5SumcheckCommitment
open AspisV5CompactTerminal

/-- One structured block of the deployed evaluator: the running scale, the two
power registers (`z, z²` before fold zero, `z⁴, z⁸` before fold one, then the
folded upper-half weight and a spent register), and the five-bit selector.
Mirrors the Rust `CompactBTerminalBlock`. -/
structure OptimizedBlock (K : Type*) where
  scale : K
  powerLo : K
  powerHi : K
  selector : ℕ

/-- Full state of the deployed evaluator: ten structured blocks plus the
row-992 initial-state scale.  Mirrors the Rust `CompactBTerminalWeights`
(the `folds` counter is externalised into the four transition functions). -/
structure OptimizedState (K : Type*) where
  blocks : Fin 10 → OptimizedBlock K
  deltaScale : K

section Model

variable {K : Type*} [Field K]

/-- `count` repeated halvings, the exact loop shape used by the Rust
`CompactBTerminalWeights::new` scale table. -/
def iteratedHalf (count : ℕ) (value : K) : K :=
  (fun current : K ↦ current / 2)^[count] value

/-- Initial state derived from the ten-coordinate terminal point and the lane
scale: block `round` holds `scale` halved `9 - round` times, the point powers
`z, z²`, and its selector; the delta register holds the row-992 weight,
one further halving of block zero's scale.  Mirrors
`CompactBTerminalWeights::new`. -/
def optimizedInit (point : Fin 10 → K) (scale : K) : OptimizedState K where
  blocks := fun round ↦
    { scale := iteratedHalf (9 - (round : ℕ)) scale
      powerLo := point round
      powerHi := point round ^ 2
      selector := blockSelector round }
  deltaScale := iteratedHalf 9 scale / 2

/-- Fold zero (`self.folds = 0`): every block multiplies its scale by
`(1 + α³z + α²z² + αz³) / 4` and advances the power registers by repeated
squaring to `z⁴, z⁸`; the delta register is multiplied by `1 / 4`. -/
def optimizedFoldZero (alpha : K) (state : OptimizedState K) : OptimizedState K where
  blocks := fun round ↦
    let block := state.blocks round
    let newPowerLo := block.powerHi ^ 2
    { scale := block.scale *
        ((1 + (alpha ^ 3 * block.powerLo + alpha ^ 2 * block.powerHi +
          alpha * (block.powerHi * block.powerLo))) / 4)
      powerLo := newPowerLo
      powerHi := newPowerLo ^ 2
      selector := block.selector }
  deltaScale := state.deltaScale * (1 / 4)

/-- Fold one (`self.folds = 1`): the lower factor `(1 + α³z⁴ + α²z⁸ + αz¹²)/4`
scales the surviving 0–3 chunk, while `powerLo` is repurposed to carry the
folded upper half `z¹⁶(1 + α³z⁴ + α²z⁸)/4` of the truncated degree block
(the 28th–31st coefficients are the fixed zeros, so the upper chunk has only
three live positions); the delta register is multiplied by `1 / 4`. -/
def optimizedFoldOne (alpha : K) (state : OptimizedState K) : OptimizedState K where
  blocks := fun round ↦
    let block := state.blocks round
    { scale := block.scale *
        ((1 + (alpha ^ 3 * block.powerLo + alpha ^ 2 * block.powerHi +
          alpha * (block.powerHi * block.powerLo))) / 4)
      powerLo := block.scale *
        (block.powerHi ^ 2 *
          (1 + (alpha ^ 3 * block.powerLo + alpha ^ 2 * block.powerHi)) / 4)
      powerHi := 0
      selector := block.selector }
  deltaScale := state.deltaScale * (1 / 4)

/-- Fold two (`self.folds = 2`): selector bit zero decides whether the block's
two surviving chunk weights sit at even positions (multipliers `1, α³`) or odd
positions (multipliers `α², α`) of the arity-four fold; the result replaces
the scale and the upper register is spent.  The delta register is multiplied
by `α² / 4`. -/
def optimizedFoldTwo (alpha : K) (state : OptimizedState K) : OptimizedState K where
  blocks := fun round ↦
    let block := state.blocks round
    { scale :=
        (if block.selector % 2 = 0 then
          block.scale + alpha ^ 3 * block.powerLo
        else
          alpha ^ 2 * block.scale + alpha * block.powerLo) / 4
      powerLo := 0
      powerHi := block.powerHi
      selector := block.selector }
  deltaScale := state.deltaScale * (alpha ^ 2 / 4)

/-- Fold three (`self.folds = 3`): selector bits one and two select the final
fold multiplier `1, α³, α², α`; the delta register is multiplied by `α / 4`. -/
def optimizedFoldThree (alpha : K) (state : OptimizedState K) : OptimizedState K where
  blocks := fun round ↦
    let block := state.blocks round
    { scale := block.scale *
        ((if block.selector / 2 % 4 = 0 then 1
          else if block.selector / 2 % 4 = 1 then alpha ^ 3
          else if block.selector / 2 % 4 = 2 then alpha ^ 2
          else alpha) / 4)
      powerLo := block.powerLo
      powerHi := block.powerHi
      selector := block.selector }
  deltaScale := state.deltaScale * (alpha / 4)

/-- A single sparse coordinate, indexed by its numeric position.  Positions at
or beyond `n` denote the zero vector, so no bound bookkeeping is needed. -/
def indicator {n : ℕ} (position : ℕ) (value : K) : Fin n → K :=
  fun query ↦ if (query : ℕ) = position then value else 0

/-- The four final weights produced by the deployed evaluator: each block
scatters its scale into slot `selector / 8`, and the delta register lands in
slot 3.  Mirrors `CompactBTerminalWeights::final_weights`. -/
def optimizedFinalWeights (state : OptimizedState K) : Fin 4 → K :=
  (∑ round : Fin 10,
    indicator ((state.blocks round).selector / 8) (state.blocks round).scale) +
    indicator 3 state.deltaScale

/-- The deployed fold schedule: initialisation followed by the four fold
transitions with the transcript challenges in order. -/
def optimizedRun (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) :
    OptimizedState K :=
  optimizedFoldThree (alphas 3)
    (optimizedFoldTwo (alphas 2)
      (optimizedFoldOne (alphas 1)
        (optimizedFoldZero (alphas 0) (optimizedInit point scale))))

/-- The deployed optimized compact component-B terminal evaluation: run the
state machine, then dot the four final weights against the final
coefficients.  Mirrors `CompactBTerminalWeights::dot`.  This definition is
independent of the dense `terminalWeights`/`dualFold4` side. -/
def optimizedCompactFinalDot (point : Fin 10 → K) (scale : K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K) : K :=
  ∑ index, optimizedFinalWeights (optimizedRun point scale alphas) index *
    finalValues index

/-- The power registers of the initial state satisfy the repeated-squaring
invariant `powerHi = powerLo²`. -/
theorem optimizedInit_powerHi (point : Fin 10 → K) (scale : K) :
    ∀ round, ((optimizedInit point scale).blocks round).powerHi =
      ((optimizedInit point scale).blocks round).powerLo ^ 2 :=
  fun _ ↦ rfl

/-- Fold zero preserves the repeated-squaring invariant `powerHi = powerLo²`. -/
theorem optimizedFoldZero_powerHi (alpha : K) (state : OptimizedState K) :
    ∀ round, ((optimizedFoldZero alpha state).blocks round).powerHi =
      ((optimizedFoldZero alpha state).blocks round).powerLo ^ 2 :=
  fun _ ↦ rfl

end Model

section Bridging

variable {K : Type*} [Field K]

/-- Division by the true field element `4` is multiplication by the dense
side's `quarter`, under the characteristic guard. -/
theorem div_four_eq_quarter_mul (h2 : (2 : K) ≠ 0) (value : K) :
    value / 4 = quarter * value := by
  have h4 : (4 : K) ≠ 0 := by
    have hfour : (4 : K) = 2 * 2 := by norm_num
    rw [hfour]
    exact mul_ne_zero h2 h2
  show value / 4 = half * half * value
  show value / 4 = (2 : K)⁻¹ * (2 : K)⁻¹ * value
  field_simp
  ring

/-- Iterated halving is multiplication by the matching power of `half`. -/
theorem iteratedHalf_eq_mul_half_pow (count : ℕ) (value : K) :
    iteratedHalf count value = value * half ^ count := by
  induction count with
  | zero => simp [iteratedHalf]
  | succ n ih =>
      have step : iteratedHalf (n + 1) value = iteratedHalf n value / 2 := by
        simp only [iteratedHalf, Function.iterate_succ_apply']
      rw [step, ih, pow_succ, div_eq_mul_inv, mul_assoc]
      rfl

private theorem indicator_val_eq_basis (row : Fin 1024) (value : K) :
    (indicator ((row : Fin 1024) : ℕ) value : Fin 1024 → K) = basis row value := by
  funext query
  simp [indicator, basis, Fin.ext_iff]

private theorem indicator_add {n : ℕ} (position : ℕ) (left right : K) :
    (indicator position left : Fin n → K) + indicator position right =
      indicator position (left + right) := by
  funext query
  simp only [Pi.add_apply, indicator]
  by_cases h : (query : ℕ) = position
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- The dual-fold multiplier attached to each in-chunk slot. -/
private def foldCoefficient (alpha : K) (slot : ℕ) : K :=
  if slot = 0 then 1
  else if slot = 1 then alpha ^ 3
  else if slot = 2 then alpha ^ 2
  else alpha

private theorem foldCoefficient_zero (alpha : K) : foldCoefficient alpha 0 = 1 := rfl

private theorem foldCoefficient_one (alpha : K) :
    foldCoefficient alpha 1 = alpha ^ 3 := rfl

private theorem foldCoefficient_two (alpha : K) :
    foldCoefficient alpha 2 = alpha ^ 2 := rfl

private theorem foldCoefficient_three (alpha : K) :
    foldCoefficient alpha 3 = alpha := rfl

private theorem dualFold4_zero {n : ℕ} (alpha : K) :
    dualFold4 (n := n) alpha (0 : Fin (4 * n) → K) = 0 := by
  funext chunk
  simp [dualFold4]

private theorem dualFold4_add {n : ℕ} (alpha : K) (left right : Fin (4 * n) → K) :
    dualFold4 alpha (left + right) = dualFold4 alpha left + dualFold4 alpha right := by
  funext chunk
  simp only [dualFold4, Pi.add_apply]
  ring

private theorem dualFold4_sum {n : ℕ} {I : Type*} (alpha : K) (s : Finset I)
    (family : I → Fin (4 * n) → K) :
    dualFold4 alpha (∑ index ∈ s, family index) =
      ∑ index ∈ s, dualFold4 alpha (family index) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dualFold4_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dualFold4_add, ih]

/-- One dense dual fold moves a single sparse coordinate from `position` to
`position / 4`, scaled by `quarter` and the slot multiplier of
`position % 4`. -/
private theorem dualFold4_indicator {n : ℕ} (alpha : K) (position : ℕ) (value : K) :
    dualFold4 (n := n) alpha (indicator position value) =
      indicator (position / 4)
        (quarter * (foldCoefficient alpha (position % 4) * value)) := by
  funext chunk
  simp only [dualFold4, indicator]
  by_cases hc : (chunk : ℕ) = position / 4
  · have hsplit : position % 4 = 0 ∨ position % 4 = 1 ∨ position % 4 = 2 ∨
        position % 4 = 3 := by omega
    rcases hsplit with h | h | h | h
    · rw [h, foldCoefficient_zero,
        if_pos (show 4 * (chunk : ℕ) = position by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 1 = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 2 = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 3 = position) by omega), if_pos hc]
      ring
    · rw [h, foldCoefficient_one,
        if_neg (show ¬(4 * (chunk : ℕ) = position) by omega),
        if_pos (show 4 * (chunk : ℕ) + 1 = position by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 2 = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 3 = position) by omega), if_pos hc]
      ring
    · rw [h, foldCoefficient_two,
        if_neg (show ¬(4 * (chunk : ℕ) = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 1 = position) by omega),
        if_pos (show 4 * (chunk : ℕ) + 2 = position by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 3 = position) by omega), if_pos hc]
      ring
    · rw [h, foldCoefficient_three,
        if_neg (show ¬(4 * (chunk : ℕ) = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 1 = position) by omega),
        if_neg (show ¬(4 * (chunk : ℕ) + 2 = position) by omega),
        if_pos (show 4 * (chunk : ℕ) + 3 = position by omega), if_pos hc]
      ring
  · rw [if_neg (show ¬(4 * (chunk : ℕ) = position) by omega),
      if_neg (show ¬(4 * (chunk : ℕ) + 1 = position) by omega),
      if_neg (show ¬(4 * (chunk : ℕ) + 2 = position) by omega),
      if_neg (show ¬(4 * (chunk : ℕ) + 3 = position) by omega), if_neg hc]
    ring

private theorem sum_range_chunk4 {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (count : ℕ) :
    ∑ index ∈ Finset.range (4 * count), f index =
      ∑ chunk ∈ Finset.range count,
        (f (4 * chunk) + f (4 * chunk + 1) + f (4 * chunk + 2) + f (4 * chunk + 3)) := by
  induction count with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih,
        show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ,
        show (4 * n + 1 + 1 : ℕ) = 4 * n + 2 by ring,
        show (4 * n + 1 + 1 + 1 : ℕ) = 4 * n + 3 by ring]
      abel

private theorem sum_range_28_chunk4 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ index ∈ Finset.range 28, f index =
      ∑ chunk ∈ Finset.range 7,
        (f (4 * chunk) + f (4 * chunk + 1) + f (4 * chunk + 2) + f (4 * chunk + 3)) := by
  rw [show (28 : ℕ) = 4 * 7 by norm_num]
  exact sum_range_chunk4 f 7

private theorem sum_range_seven {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ index ∈ Finset.range 7, f index =
      (f 0 + f 1 + f 2 + f 3) + (f 4 + f 5 + f 6) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  abel

end Bridging

section Represented

variable {K : Type*} [Field K]

/-- The 1,024-row vector represented by a machine state before any fold:
block `round` populates rows `32·selector + degree` with the geometric
progression `scale · powerLo^degree` over the 28 stored degrees, and the
delta register sits at row 992.  Rows 993 (the inactive pivot) and every
block tail offset 28–31 are zero. -/
def represented1024 (state : OptimizedState K) : Fin 1024 → K :=
  (∑ round : Fin 10, ∑ degree ∈ Finset.range 28,
    indicator (32 * (state.blocks round).selector + degree)
      ((state.blocks round).scale * (state.blocks round).powerLo ^ degree)) +
    indicator 992 state.deltaScale

/-- The 256-row vector represented after fold zero: seven surviving chunks per
block, geometric in the advanced register `z⁴`, and the delta at chunk 248. -/
def represented256 (state : OptimizedState K) : Fin 256 → K :=
  (∑ round : Fin 10, ∑ chunk ∈ Finset.range 7,
    indicator (8 * (state.blocks round).selector + chunk)
      ((state.blocks round).scale * (state.blocks round).powerLo ^ chunk)) +
    indicator 248 state.deltaScale

/-- The 64-row vector represented after fold one: the folded lower half in
`scale` at chunk `2·selector`, the folded upper half in `powerLo` at chunk
`2·selector + 1`, and the delta at chunk 62. -/
def represented64 (state : OptimizedState K) : Fin 64 → K :=
  (∑ round : Fin 10,
    (indicator (2 * (state.blocks round).selector) (state.blocks round).scale +
      indicator (2 * (state.blocks round).selector + 1) (state.blocks round).powerLo)) +
    indicator 62 state.deltaScale

/-- The 16-row vector represented after fold two: one weight per block at
chunk `selector / 2` (adjacent selectors now share a chunk additively), and
the delta at chunk 15. -/
def represented16 (state : OptimizedState K) : Fin 16 → K :=
  (∑ round : Fin 10,
    indicator ((state.blocks round).selector / 2) (state.blocks round).scale) +
    indicator 15 state.deltaScale

end Represented

section Correspondence

variable {K : Type*} [Field K]

/-- Initialisation is exact: the machine state represents precisely the public
geometric covector `terminalWeights`. -/
theorem represented1024_optimizedInit_eq_terminalWeights
    (point : Fin 10 → K) (scale : K) :
    represented1024 (optimizedInit point scale) = terminalWeights point scale := by
  simp only [represented1024, optimizedInit, terminalWeights]
  conv_lhs => rw [add_comm]
  congr 1
  · rw [show (992 : ℕ) = ((initialRow : Fin 1024) : ℕ) from rfl, indicator_val_eq_basis]
    congr 1
    rw [iteratedHalf_eq_mul_half_pow, div_eq_mul_inv, mul_assoc]
    show scale * (half ^ 9 * half) = scale * half ^ 10
    rw [← pow_succ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun round _ ↦ ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun degree _ ↦ ?_
    rw [show 32 * blockSelector round + (degree : ℕ) =
        ((coefficientRow (round, degree) : Fin 1024) : ℕ) from rfl,
      indicator_val_eq_basis, iteratedHalf_eq_mul_half_pow]

/-- Fold-zero invariant, generically: one optimized fold-zero transition acts
on the represented vector exactly as one dense dual fold, provided the power
registers satisfy the repeated-squaring invariant. -/
theorem represented256_optimizedFoldZero (h2 : (2 : K) ≠ 0) (alpha : K)
    (state : OptimizedState K)
    (hpow : ∀ round, (state.blocks round).powerHi = (state.blocks round).powerLo ^ 2) :
    represented256 (optimizedFoldZero alpha state) =
      dualFold4 (n := 256) alpha (represented1024 state) := by
  have hdivq : ∀ x : K, x / 4 = quarter * x := div_four_eq_quarter_mul h2
  simp only [represented1024, represented256, optimizedFoldZero]
  rw [dualFold4_add, dualFold4_sum]
  congr 1
  · refine Finset.sum_congr rfl fun round _ ↦ ?_
    rw [sum_range_28_chunk4, dualFold4_sum]
    refine Finset.sum_congr rfl fun chunk _ ↦ ?_
    rw [dualFold4_add, dualFold4_add, dualFold4_add, dualFold4_indicator,
      dualFold4_indicator, dualFold4_indicator, dualFold4_indicator]
    have e0 : (32 * (state.blocks round).selector + 4 * chunk) / 4 =
        8 * (state.blocks round).selector + chunk := by omega
    have e1 : (32 * (state.blocks round).selector + (4 * chunk + 1)) / 4 =
        8 * (state.blocks round).selector + chunk := by omega
    have e2 : (32 * (state.blocks round).selector + (4 * chunk + 2)) / 4 =
        8 * (state.blocks round).selector + chunk := by omega
    have e3 : (32 * (state.blocks round).selector + (4 * chunk + 3)) / 4 =
        8 * (state.blocks round).selector + chunk := by omega
    have m0 : (32 * (state.blocks round).selector + 4 * chunk) % 4 = 0 := by omega
    have m1 : (32 * (state.blocks round).selector + (4 * chunk + 1)) % 4 = 1 := by omega
    have m2 : (32 * (state.blocks round).selector + (4 * chunk + 2)) % 4 = 2 := by omega
    have m3 : (32 * (state.blocks round).selector + (4 * chunk + 3)) % 4 = 3 := by omega
    rw [e0, e1, e2, e3, m0, m1, m2, m3, foldCoefficient_zero, foldCoefficient_one,
      foldCoefficient_two, foldCoefficient_three, indicator_add, indicator_add,
      indicator_add]
    congr 1
    rw [hpow round, hdivq]
    ring
  · rw [dualFold4_indicator, show (992 : ℕ) / 4 = 248 from by norm_num,
      show (992 : ℕ) % 4 = 0 from by norm_num, foldCoefficient_zero]
    congr 1
    rw [hdivq]
    ring

/-- Fold-one invariant, generically: the second optimized transition acts on
the represented 256-vector exactly as one dense dual fold. -/
theorem represented64_optimizedFoldOne (h2 : (2 : K) ≠ 0) (alpha : K)
    (state : OptimizedState K)
    (hpow : ∀ round, (state.blocks round).powerHi = (state.blocks round).powerLo ^ 2) :
    represented64 (optimizedFoldOne alpha state) =
      dualFold4 (n := 64) alpha (represented256 state) := by
  have hdivq : ∀ x : K, x / 4 = quarter * x := div_four_eq_quarter_mul h2
  simp only [represented256, represented64, optimizedFoldOne]
  rw [dualFold4_add, dualFold4_sum]
  congr 1
  · refine Finset.sum_congr rfl fun round _ ↦ ?_
    rw [sum_range_seven, dualFold4_add, dualFold4_add, dualFold4_add, dualFold4_add,
      dualFold4_add, dualFold4_add, dualFold4_indicator, dualFold4_indicator,
      dualFold4_indicator, dualFold4_indicator, dualFold4_indicator,
      dualFold4_indicator, dualFold4_indicator]
    have e0 : (8 * (state.blocks round).selector + 0) / 4 =
        2 * (state.blocks round).selector := by omega
    have e1 : (8 * (state.blocks round).selector + 1) / 4 =
        2 * (state.blocks round).selector := by omega
    have e2 : (8 * (state.blocks round).selector + 2) / 4 =
        2 * (state.blocks round).selector := by omega
    have e3 : (8 * (state.blocks round).selector + 3) / 4 =
        2 * (state.blocks round).selector := by omega
    have e4 : (8 * (state.blocks round).selector + 4) / 4 =
        2 * (state.blocks round).selector + 1 := by omega
    have e5 : (8 * (state.blocks round).selector + 5) / 4 =
        2 * (state.blocks round).selector + 1 := by omega
    have e6 : (8 * (state.blocks round).selector + 6) / 4 =
        2 * (state.blocks round).selector + 1 := by omega
    have m0 : (8 * (state.blocks round).selector + 0) % 4 = 0 := by omega
    have m1 : (8 * (state.blocks round).selector + 1) % 4 = 1 := by omega
    have m2 : (8 * (state.blocks round).selector + 2) % 4 = 2 := by omega
    have m3 : (8 * (state.blocks round).selector + 3) % 4 = 3 := by omega
    have m4 : (8 * (state.blocks round).selector + 4) % 4 = 0 := by omega
    have m5 : (8 * (state.blocks round).selector + 5) % 4 = 1 := by omega
    have m6 : (8 * (state.blocks round).selector + 6) % 4 = 2 := by omega
    rw [e0, e1, e2, e3, e4, e5, e6, m0, m1, m2, m3, m4, m5, m6]
    simp only [foldCoefficient_zero, foldCoefficient_one, foldCoefficient_two,
      foldCoefficient_three]
    rw [indicator_add, indicator_add, indicator_add, indicator_add, indicator_add]
    congr 1
    · congr 1
      rw [hpow round, hdivq]
      ring
    · congr 1
      rw [hpow round, hdivq]
      ring
  · rw [dualFold4_indicator, show (248 : ℕ) / 4 = 62 from by norm_num,
      show (248 : ℕ) % 4 = 0 from by norm_num, foldCoefficient_zero]
    congr 1
    rw [hdivq]
    ring

/-- Fold-two invariant, generically: the third optimized transition acts on
the represented 64-vector exactly as one dense dual fold; selector parity
selects the even or odd pair of slot multipliers. -/
theorem represented16_optimizedFoldTwo (h2 : (2 : K) ≠ 0) (alpha : K)
    (state : OptimizedState K) :
    represented16 (optimizedFoldTwo alpha state) =
      dualFold4 (n := 16) alpha (represented64 state) := by
  have hdivq : ∀ x : K, x / 4 = quarter * x := div_four_eq_quarter_mul h2
  simp only [represented64, represented16, optimizedFoldTwo]
  rw [dualFold4_add, dualFold4_sum]
  congr 1
  · refine Finset.sum_congr rfl fun round _ ↦ ?_
    rw [dualFold4_add, dualFold4_indicator, dualFold4_indicator]
    have e0 : 2 * (state.blocks round).selector / 4 =
        (state.blocks round).selector / 2 := by omega
    have e1 : (2 * (state.blocks round).selector + 1) / 4 =
        (state.blocks round).selector / 2 := by omega
    rcases (show (state.blocks round).selector % 2 = 0 ∨
        (state.blocks round).selector % 2 = 1 by omega) with hpar | hpar
    · have m0 : 2 * (state.blocks round).selector % 4 = 0 := by omega
      have m1 : (2 * (state.blocks round).selector + 1) % 4 = 1 := by omega
      rw [e0, e1, m0, m1, foldCoefficient_zero, foldCoefficient_one, indicator_add,
        if_pos hpar]
      congr 1
      rw [hdivq]
      ring
    · have m0 : 2 * (state.blocks round).selector % 4 = 2 := by omega
      have m1 : (2 * (state.blocks round).selector + 1) % 4 = 3 := by omega
      rw [e0, e1, m0, m1, foldCoefficient_two, foldCoefficient_three, indicator_add,
        if_neg (show ¬((state.blocks round).selector % 2 = 0) by omega)]
      congr 1
      rw [hdivq]
      ring
  · rw [dualFold4_indicator, show (62 : ℕ) / 4 = 15 from by norm_num,
      show (62 : ℕ) % 4 = 2 from by norm_num, foldCoefficient_two]
    congr 1
    rw [hdivq]
    ring

/-- Fold-three invariant, generically: the fourth optimized transition acts on
the represented 16-vector exactly as one dense dual fold, producing the four
final weights; selector bits one and two select the slot multiplier. -/
theorem optimizedFinalWeights_optimizedFoldThree (h2 : (2 : K) ≠ 0) (alpha : K)
    (state : OptimizedState K) :
    optimizedFinalWeights (optimizedFoldThree alpha state) =
      dualFold4 (n := 4) alpha (represented16 state) := by
  have hdivq : ∀ x : K, x / 4 = quarter * x := div_four_eq_quarter_mul h2
  simp only [represented16, optimizedFinalWeights, optimizedFoldThree]
  rw [dualFold4_add, dualFold4_sum]
  simp_rw [dualFold4_indicator]
  congr 1
  · refine Finset.sum_congr rfl fun round _ ↦ ?_
    have e : (state.blocks round).selector / 2 / 4 =
        (state.blocks round).selector / 8 := by omega
    rcases (show (state.blocks round).selector / 2 % 4 = 0 ∨
        (state.blocks round).selector / 2 % 4 = 1 ∨
        (state.blocks round).selector / 2 % 4 = 2 ∨
        (state.blocks round).selector / 2 % 4 = 3 by omega) with h | h | h | h
    · rw [e, h, foldCoefficient_zero, if_pos (show (0 : ℕ) = 0 by omega)]
      congr 1
      rw [hdivq]
      ring
    · rw [e, h, foldCoefficient_one, if_neg (show ¬((1 : ℕ) = 0) by omega),
        if_pos (show (1 : ℕ) = 1 by omega)]
      congr 1
      rw [hdivq]
      ring
    · rw [e, h, foldCoefficient_two, if_neg (show ¬((2 : ℕ) = 0) by omega),
        if_neg (show ¬((2 : ℕ) = 1) by omega), if_pos (show (2 : ℕ) = 2 by omega)]
      congr 1
      rw [hdivq]
      ring
    · rw [e, h, foldCoefficient_three, if_neg (show ¬((3 : ℕ) = 0) by omega),
        if_neg (show ¬((3 : ℕ) = 1) by omega), if_neg (show ¬((3 : ℕ) = 2) by omega)]
      congr 1
      rw [hdivq]
      ring
  · rw [show (15 : ℕ) / 4 = 3 from by norm_num,
      show (15 : ℕ) % 4 = 3 from by norm_num, foldCoefficient_three]
    congr 1
    rw [hdivq]
    ring

/-- State invariant after fold zero of the deployed run: the represented
256-vector is exactly one dense dual fold of `terminalWeights`. -/
theorem represented256_afterFoldZero_eq_one_dense_dual_fold (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) :
    represented256 (optimizedFoldZero (alphas 0) (optimizedInit point scale)) =
      dualFold4 (n := 256) (alphas 0) (terminalWeights point scale) := by
  rw [represented256_optimizedFoldZero h2 (alphas 0) (optimizedInit point scale)
      (optimizedInit_powerHi point scale),
    represented1024_optimizedInit_eq_terminalWeights]

/-- State invariant after fold one of the deployed run: the represented
64-vector is exactly two dense dual folds of `terminalWeights`. -/
theorem represented64_afterFoldOne_eq_two_dense_dual_folds (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) :
    represented64 (optimizedFoldOne (alphas 1)
        (optimizedFoldZero (alphas 0) (optimizedInit point scale))) =
      dualFold4 (n := 64) (alphas 1)
        (dualFold4 (n := 256) (alphas 0) (terminalWeights point scale)) := by
  rw [represented64_optimizedFoldOne h2 (alphas 1)
      (optimizedFoldZero (alphas 0) (optimizedInit point scale))
      (optimizedFoldZero_powerHi (alphas 0) (optimizedInit point scale)),
    represented256_afterFoldZero_eq_one_dense_dual_fold h2 point scale alphas]

/-- State invariant after fold two of the deployed run: the represented
16-vector is exactly three dense dual folds of `terminalWeights`. -/
theorem represented16_afterFoldTwo_eq_three_dense_dual_folds (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) :
    represented16 (optimizedFoldTwo (alphas 2)
        (optimizedFoldOne (alphas 1)
          (optimizedFoldZero (alphas 0) (optimizedInit point scale)))) =
      dualFold4 (n := 16) (alphas 2)
        (dualFold4 (n := 64) (alphas 1)
          (dualFold4 (n := 256) (alphas 0) (terminalWeights point scale))) := by
  rw [represented16_optimizedFoldTwo h2 (alphas 2)
      (optimizedFoldOne (alphas 1)
        (optimizedFoldZero (alphas 0) (optimizedInit point scale))),
    represented64_afterFoldOne_eq_two_dense_dual_folds h2 point scale alphas]

/-- State invariant after fold three of the deployed run: the four final
weights are exactly the four dense dual folds of `terminalWeights`. -/
theorem optimizedFinalWeights_afterFoldThree_eq_fourDualFolds (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) :
    optimizedFinalWeights (optimizedRun point scale alphas) =
      fourDualFolds alphas (terminalWeights point scale) := by
  simp only [optimizedRun]
  rw [optimizedFinalWeights_optimizedFoldThree h2 (alphas 3)
      (optimizedFoldTwo (alphas 2)
        (optimizedFoldOne (alphas 1)
          (optimizedFoldZero (alphas 0) (optimizedInit point scale)))),
    represented16_afterFoldTwo_eq_three_dense_dual_folds h2 point scale alphas]
  rfl

/-- Principal theorem: the deployed optimized compact component-B terminal
evaluator computes the same value as the dense four-fold terminal — four
`dualFold4` applications to `terminalWeights` followed by the four-value
dot. -/
theorem optimizedCompactFinalDot_eq_fourDenseDualFolds (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) (finalValues : Fin 4 → K) :
    optimizedCompactFinalDot point scale alphas finalValues =
      compactFinalDot alphas (terminalWeights point scale) finalValues := by
  simp only [optimizedCompactFinalDot, compactFinalDot]
  rw [optimizedFinalWeights_afterFoldThree_eq_fourDualFolds h2 point scale alphas]

/-- The deployed evaluator agrees with the audited dense spelling
`compactComponentBFinalDot` of the compact component-B terminal check. -/
theorem optimizedCompactFinalDot_eq_compactComponentBFinalDot (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale : K) (alphas : Fin 4 → K) (finalValues : Fin 4 → K) :
    optimizedCompactFinalDot point scale alphas finalValues =
      compactComponentBFinalDot point scale alphas finalValues :=
  optimizedCompactFinalDot_eq_fourDenseDualFolds h2 point scale alphas finalValues

/-- Once the ordinary relation sumcheck has carried the initial row-dot claim
to the final four values — the same explicit hypothesis as in the dense
module, neither dropped nor weakened — the deployed optimized terminal check
authenticates exactly the ten-round component-B recurrence. -/
theorem optimizedCompactFinalDot_eq_tenRoundTerminal_of_relation (h2 : (2 : K) ≠ 0)
    (point : Fin 10 → K) (scale initial : K) (tails : Fin 10 → Fin 27 → K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K)
    (relation_carried :
      compactComponentBFinalDot point scale alphas finalValues =
        dot (terminalWeights point scale) (rowMessage initial tails)) :
    optimizedCompactFinalDot point scale alphas finalValues =
      scale * tenRoundTerminal initial tails point := by
  rw [optimizedCompactFinalDot_eq_compactComponentBFinalDot h2 point scale alphas
      finalValues]
  exact compactComponentBFinalDot_eq_tenRoundTerminal_of_relation point scale initial
    tails alphas finalValues relation_carried

end Correspondence

end AspisV5CompactTerminalOptimized

#print axioms AspisV5CompactTerminalOptimized.optimizedInit_powerHi
#print axioms AspisV5CompactTerminalOptimized.optimizedFoldZero_powerHi
#print axioms AspisV5CompactTerminalOptimized.div_four_eq_quarter_mul
#print axioms AspisV5CompactTerminalOptimized.iteratedHalf_eq_mul_half_pow
#print axioms AspisV5CompactTerminalOptimized.represented1024_optimizedInit_eq_terminalWeights
#print axioms AspisV5CompactTerminalOptimized.represented256_optimizedFoldZero
#print axioms AspisV5CompactTerminalOptimized.represented64_optimizedFoldOne
#print axioms AspisV5CompactTerminalOptimized.represented16_optimizedFoldTwo
#print axioms AspisV5CompactTerminalOptimized.optimizedFinalWeights_optimizedFoldThree
#print axioms AspisV5CompactTerminalOptimized.represented256_afterFoldZero_eq_one_dense_dual_fold
#print axioms AspisV5CompactTerminalOptimized.represented64_afterFoldOne_eq_two_dense_dual_folds
#print axioms AspisV5CompactTerminalOptimized.represented16_afterFoldTwo_eq_three_dense_dual_folds
#print axioms AspisV5CompactTerminalOptimized.optimizedFinalWeights_afterFoldThree_eq_fourDualFolds
#print axioms AspisV5CompactTerminalOptimized.optimizedCompactFinalDot_eq_fourDenseDualFolds
#print axioms AspisV5CompactTerminalOptimized.optimizedCompactFinalDot_eq_compactComponentBFinalDot
#print axioms AspisV5CompactTerminalOptimized.optimizedCompactFinalDot_eq_tenRoundTerminal_of_relation
