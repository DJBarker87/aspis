import Mathlib

/-!
# Exact Guruswami--Sudan list cap for the four committed V5 FRI layers

This file checks only the finite arithmetic behind the release's list cap
`240`.  It instantiates equations (73)--(74) of the S-two soundness analysis:

`m(r) = max (ceil (sqrt r / (2 * (alpha - sqrt r)))) 3`

and

`ell(r) = (m(r) + 1/2) / sqrt r`.

The common agreement fraction is
`alpha = (21/20) * sqrt (1/512)`.  The four committed layers have distance
complements `1/512`, `255/131072`, `63/32768`, and `15/8192`.  Lean proves
that the formula chooses multiplicities `10`, `10`, `9`, and `6`, and that
all four resulting real list-size bounds are strictly below `240`.

This arithmetic does not prove that Tag-67 acceptance produces a coherent FRI
candidate list, nor that a single list factor rather than a product of list
factors is appropriate.  Those are separate protocol arguments.
-/

namespace AspisV5FriListCap

/-- Distance complement for the initial circle-code layer. -/
noncomputable def circleRate : ℝ := 1 / 512

/-- Distance complements for the three committed line-code layers. -/
noncomputable def lineRate0 : ℝ := 255 / 131072
noncomputable def lineRate1 : ℝ := 63 / 32768
noncomputable def lineRate2 : ℝ := 15 / 8192

/-- The release's agreement fraction `1 - theta`. -/
noncomputable def agreement : ℝ := (21 / 20) * Real.sqrt circleRate

/-- The quantity rounded up in the Guruswami--Sudan multiplicity formula. -/
noncomputable def multiplicityRatio (rate : ℝ) : ℝ :=
  Real.sqrt rate / (2 * (agreement - Real.sqrt rate))

/-- Equation (74), including its lower bound of three. -/
noncomputable def multiplicity (rate : ℝ) : ℕ :=
  max ⌈multiplicityRatio rate⌉₊ 3

/-- Equation (73), with the multiplicity selected by equation (74). -/
noncomputable def listBound (rate : ℝ) : ℝ :=
  ((multiplicity rate : ℝ) + 1 / 2) / Real.sqrt rate

private theorem circleRate_pos : 0 < circleRate := by
  norm_num [circleRate]

private theorem lineRate0_pos : 0 < lineRate0 := by
  norm_num [lineRate0]

private theorem lineRate1_pos : 0 < lineRate1 := by
  norm_num [lineRate1]

private theorem lineRate2_pos : 0 < lineRate2 := by
  norm_num [lineRate2]

private theorem sqrt_circle_sq : Real.sqrt circleRate ^ 2 = circleRate :=
  Real.sq_sqrt circleRate_pos.le

private theorem sqrt_line0_sq : Real.sqrt lineRate0 ^ 2 = lineRate0 :=
  Real.sq_sqrt lineRate0_pos.le

private theorem sqrt_line1_sq : Real.sqrt lineRate1 ^ 2 = lineRate1 :=
  Real.sq_sqrt lineRate1_pos.le

private theorem sqrt_line2_sq : Real.sqrt lineRate2 ^ 2 = lineRate2 :=
  Real.sq_sqrt lineRate2_pos.le

private theorem sqrt_circle_pos : 0 < Real.sqrt circleRate :=
  Real.sqrt_pos.2 circleRate_pos

private theorem sqrt_line0_pos : 0 < Real.sqrt lineRate0 :=
  Real.sqrt_pos.2 lineRate0_pos

private theorem sqrt_line1_pos : 0 < Real.sqrt lineRate1 :=
  Real.sqrt_pos.2 lineRate1_pos

private theorem sqrt_line2_pos : 0 < Real.sqrt lineRate2 :=
  Real.sqrt_pos.2 lineRate2_pos

private theorem sqrt_line0_lt_agreement : Real.sqrt lineRate0 < agreement := by
  have hc := sqrt_circle_sq
  have h0 := sqrt_line0_sq
  have hcp := sqrt_circle_pos
  have h0p := sqrt_line0_pos
  unfold agreement circleRate lineRate0 at *
  nlinarith

private theorem sqrt_line1_lt_agreement : Real.sqrt lineRate1 < agreement := by
  have hc := sqrt_circle_sq
  have h1 := sqrt_line1_sq
  have hcp := sqrt_circle_pos
  have h1p := sqrt_line1_pos
  unfold agreement circleRate lineRate1 at *
  nlinarith

private theorem sqrt_line2_lt_agreement : Real.sqrt lineRate2 < agreement := by
  have hc := sqrt_circle_sq
  have h2 := sqrt_line2_sq
  have hcp := sqrt_circle_pos
  have h2p := sqrt_line2_pos
  unfold agreement circleRate lineRate2 at *
  nlinarith

/-- At the initial circle layer, the multiplicity ratio is exactly ten. -/
theorem circle_multiplicity_ratio : multiplicityRatio circleRate = 10 := by
  have hs := sqrt_circle_pos.ne'
  unfold multiplicityRatio agreement
  field_simp
  ring

/-- The first line layer's ratio lies in `(9, 10]`, so its ceiling is ten. -/
theorem line0_multiplicity_ratio :
    9 < multiplicityRatio lineRate0 ∧ multiplicityRatio lineRate0 ≤ 10 := by
  have hden : 0 < 2 * (agreement - Real.sqrt lineRate0) := by
    nlinarith [sqrt_line0_lt_agreement]
  constructor
  · rw [show multiplicityRatio lineRate0 =
        Real.sqrt lineRate0 / (2 * (agreement - Real.sqrt lineRate0)) by rfl]
    rw [lt_div_iff₀ hden]
    have hc := sqrt_circle_sq
    have h0 := sqrt_line0_sq
    have hcp := sqrt_circle_pos
    have h0p := sqrt_line0_pos
    unfold agreement circleRate lineRate0 at *
    nlinarith
  · rw [show multiplicityRatio lineRate0 =
        Real.sqrt lineRate0 / (2 * (agreement - Real.sqrt lineRate0)) by rfl]
    rw [div_le_iff₀ hden]
    have hc := sqrt_circle_sq
    have h0 := sqrt_line0_sq
    have hcp := sqrt_circle_pos
    have h0p := sqrt_line0_pos
    unfold agreement circleRate lineRate0 at *
    nlinarith

/-- The second line layer's ratio lies in `(8, 9]`, so its ceiling is nine. -/
theorem line1_multiplicity_ratio :
    8 < multiplicityRatio lineRate1 ∧ multiplicityRatio lineRate1 ≤ 9 := by
  have hden : 0 < 2 * (agreement - Real.sqrt lineRate1) := by
    nlinarith [sqrt_line1_lt_agreement]
  constructor
  · rw [show multiplicityRatio lineRate1 =
        Real.sqrt lineRate1 / (2 * (agreement - Real.sqrt lineRate1)) by rfl]
    rw [lt_div_iff₀ hden]
    have hc := sqrt_circle_sq
    have h1 := sqrt_line1_sq
    have hcp := sqrt_circle_pos
    have h1p := sqrt_line1_pos
    unfold agreement circleRate lineRate1 at *
    nlinarith
  · rw [show multiplicityRatio lineRate1 =
        Real.sqrt lineRate1 / (2 * (agreement - Real.sqrt lineRate1)) by rfl]
    rw [div_le_iff₀ hden]
    have hc := sqrt_circle_sq
    have h1 := sqrt_line1_sq
    have hcp := sqrt_circle_pos
    have h1p := sqrt_line1_pos
    unfold agreement circleRate lineRate1 at *
    nlinarith

/-- The third line layer's ratio lies in `(5, 6]`, so its ceiling is six. -/
theorem line2_multiplicity_ratio :
    5 < multiplicityRatio lineRate2 ∧ multiplicityRatio lineRate2 ≤ 6 := by
  have hden : 0 < 2 * (agreement - Real.sqrt lineRate2) := by
    nlinarith [sqrt_line2_lt_agreement]
  constructor
  · rw [show multiplicityRatio lineRate2 =
        Real.sqrt lineRate2 / (2 * (agreement - Real.sqrt lineRate2)) by rfl]
    rw [lt_div_iff₀ hden]
    have hc := sqrt_circle_sq
    have h2 := sqrt_line2_sq
    have hcp := sqrt_circle_pos
    have h2p := sqrt_line2_pos
    unfold agreement circleRate lineRate2 at *
    nlinarith
  · rw [show multiplicityRatio lineRate2 =
        Real.sqrt lineRate2 / (2 * (agreement - Real.sqrt lineRate2)) by rfl]
    rw [div_le_iff₀ hden]
    have hc := sqrt_circle_sq
    have h2 := sqrt_line2_sq
    have hcp := sqrt_circle_pos
    have h2p := sqrt_line2_pos
    unfold agreement circleRate lineRate2 at *
    nlinarith

/-- Equation (74) selects the deployed multiplicities `10, 10, 9, 6`. -/
theorem deployed_multiplicities :
    multiplicity circleRate = 10 ∧
    multiplicity lineRate0 = 10 ∧
    multiplicity lineRate1 = 9 ∧
    multiplicity lineRate2 = 6 := by
  have hcceil : ⌈multiplicityRatio circleRate⌉₊ = 10 := by
    rw [circle_multiplicity_ratio]
    norm_num
  have h0ceil : ⌈multiplicityRatio lineRate0⌉₊ = 10 := by
    apply (Nat.ceil_eq_iff (by decide)).2
    simpa using line0_multiplicity_ratio
  have h1ceil : ⌈multiplicityRatio lineRate1⌉₊ = 9 := by
    apply (Nat.ceil_eq_iff (by decide)).2
    simpa using line1_multiplicity_ratio
  have h2ceil : ⌈multiplicityRatio lineRate2⌉₊ = 6 := by
    apply (Nat.ceil_eq_iff (by decide)).2
    simpa using line2_multiplicity_ratio
  simp [multiplicity, hcceil, h0ceil, h1ceil, h2ceil]

private theorem circle_list_bound_lt :
    ((10 : ℝ) + 1 / 2) / Real.sqrt circleRate < 240 := by
  rw [div_lt_iff₀ sqrt_circle_pos]
  have hs := sqrt_circle_sq
  have hp := sqrt_circle_pos
  unfold circleRate at *
  nlinarith

private theorem line0_list_bound_lt :
    ((10 : ℝ) + 1 / 2) / Real.sqrt lineRate0 < 240 := by
  rw [div_lt_iff₀ sqrt_line0_pos]
  have hs := sqrt_line0_sq
  have hp := sqrt_line0_pos
  unfold lineRate0 at *
  nlinarith

private theorem line1_list_bound_lt :
    ((9 : ℝ) + 1 / 2) / Real.sqrt lineRate1 < 240 := by
  rw [div_lt_iff₀ sqrt_line1_pos]
  have hs := sqrt_line1_sq
  have hp := sqrt_line1_pos
  unfold lineRate1 at *
  nlinarith

private theorem line2_list_bound_lt :
    ((6 : ℝ) + 1 / 2) / Real.sqrt lineRate2 < 240 := by
  rw [div_lt_iff₀ sqrt_line2_pos]
  have hs := sqrt_line2_sq
  have hp := sqrt_line2_pos
  unfold lineRate2 at *
  nlinarith

/-- All four S-two equation-(73) list bounds are strictly below `240`. -/
theorem all_committed_list_bounds_lt_240 :
    listBound circleRate < 240 ∧
    listBound lineRate0 < 240 ∧
    listBound lineRate1 < 240 ∧
    listBound lineRate2 < 240 := by
  rcases deployed_multiplicities with ⟨hc, h0, h1, h2⟩
  simp only [listBound, hc, h0, h1, h2]
  exact ⟨circle_list_bound_lt, line0_list_bound_lt,
    line1_list_bound_lt, line2_list_bound_lt⟩

/-- A single public cap convenient for later finite-family theorems. -/
theorem each_committed_list_bound_le_240
    (rate : ℝ)
    (hrate : rate = circleRate ∨ rate = lineRate0 ∨
      rate = lineRate1 ∨ rate = lineRate2) :
    listBound rate ≤ 240 := by
  rcases all_committed_list_bounds_lt_240 with ⟨hc, h0, h1, h2⟩
  rcases hrate with rfl | rfl | rfl | rfl <;> linarith

#print axioms circle_multiplicity_ratio
#print axioms line0_multiplicity_ratio
#print axioms line1_multiplicity_ratio
#print axioms line2_multiplicity_ratio
#print axioms deployed_multiplicities
#print axioms all_committed_list_bounds_lt_240
#print axioms each_committed_list_bound_le_240

end AspisV5FriListCap
