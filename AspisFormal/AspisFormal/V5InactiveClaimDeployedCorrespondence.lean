import AspisFormal.V5InactiveClaimJointHiding

/-!
# Deployed correspondence for the v5 inactive-claim (Component B) pivot

`V5InactiveClaimJointHiding` leaves four named deployed interfaces open:
`PivotCoefficientIsGammaB`, `GammaBIsPostCommitmentLaneCoefficient`,
the residual-view freshness hypothesis `released (basis pivotRow 1) = 0`, and
`ReleasedViewSerializesExactlyTheJointPair`.  This module answers, against the
deployed Rust, which of those obligations the current Lean layout definitions
can discharge, discharges what is dischargeable, and names the smallest exact
missing Rust-binding premise for each remainder.  No abstract hiding lemma is
added; every theorem here is either a fact about the real transcribed layout
(`Row`, `terminalWeights`, `rowMessage`, `terminalDotFunctional`,
`represented1024`) or a conversion between named premises and the existing
interfaces.

## Verdicts

**Question 1 (pivot coefficient).**  Not derivable from the current layout
definitions: no Lean definition of the deployed copy-inactive functional
exists, so `inactive` is a free variable and `inactive (basis pivotRow 1)`
has no computable value.  The deployed functional is the *binary* row mask
`atomic_state_only_copy_inactive_row_masks_v3()`
(`crates/aspis-statement/src/atomic_state_only_terminal.rs:115-122`): every
row absent from `COMPILED_ATOMIC_COPY_ACTIVE_ROWS`
(`crates/aspis-statement/src/atomic_state_only_terminal_constants.rs:6`,
210 entries, largest entry 866, row 993 absent) carries coefficient exactly
`QM31::ONE`, because `WeightAccumulator::add_grouped_64x16_binary_masks_deferred`
(`crates/aspis-core/src/sumcheck.rs:272-298`) installs unit weights; the
verifier consumes it at `programs/aspis-verifier/src/v5_cu_probe.rs:1086` and
the prover sums the same rows at
`crates/aspis-prover/src/v5_real_host_proof.rs:627-633`.  So on the combined
1,024-row space the pivot coefficient is `1`, not a transcript scalar; the
smallest missing premise is `DeployedInactiveCovectorIsUnitAtPivotRow` below.
Given that single premise, `PivotCoefficientIsGammaB` is *proved* here (at
`gammaB = 1` for the unit pivot and at `gammaB = c` for every scaled pivot),
and the `gammaB ≠ 0` obligation of the deployed capstone collapses to
`one_ne_zero` — the capstone fires with no lane-coefficient bound at all
(`deployed_joint_hiding_of_binary_mask`).  The γB *lane power* is a distinct,
finer fact: one unit of the pivot **cell** (row 993 of the Component-B lane)
enters the combined row value with coefficient `γ^17`, because the B message
is C2 lane 1 after 16 C1 lanes (`V5_COMPONENT_B_LANE = 1`,
`crates/aspis-prover/src/v5_spend_messages.rs:64`; `V5_C1_LANES = 16`,
lines 61 and 103; power assignment `powers[16 + j]` in
`gamma_combine_v5_values`, lines 557-583).  That fact is needed only to carry
uniformity from the sampled pivot cell to the row value; it is named as
`DeployedGammaBIsComponentBLanePower`, and with `γ ≠ 0` (the verifier draws
`γ` via `challenge_nonzero_qm31` after the terminal claim is absorbed,
`v5_cu_probe.rs:884-886`) it discharges
`GammaBIsPostCommitmentLaneCoefficient` (`gammaB_interface_of_lane_power`).
The companion kernel fact needs no premise: the terminal covector annihilates
the pivot direction at *every* amplitude
(`terminalDotFunctional_pivot_scaled_eq_zero`), so the `γ^17` scaling cannot
disturb the proved row-993 kernel membership.

**Question 2 (released-view freshness).**  Not provable from the layout, and
the deployed layout gives concrete evidence *against* the literal statement.
No Lean definition of the residual released view exists.  In Rust, the
released relation-claims table (wire prefix bytes `[4583, 5799)`,
`V5_CU_REAL_PREFIX_CLAIMS_OFFSET`, assert `v5_cu_probe.rs:176`; equality with
the parsed table checked at `v5_cu_probe.rs:862-866`; built at
`v5_real_host_proof.rs:595`) contains the Component-B lane evaluated at the
three multilinear points, and a multilinear `eq` covector at a generic point
has nonzero weight at every row, including row 993.  A residual view
containing those three claims therefore *reads* the pivot direction; only the
fourth claim group is checked against the compact terminal covector, which is
pivot-blind (proved here).  What the current definitions do support is proved
here: freshness holds exactly for views that read physical rows other than
993 (`proj_fresh_at_pivot`, `pi_proj_fresh_at_pivot`) and for the terminal
functional itself (`terminal_fresh_at_pivot`).  The named premise for the
deployed residual view is `DeployedResidualViewFreshAtPivotRow`; if it is
false for the full claims table — the current evidence — the honest fallback
is the correlated-invariant hypothesis of
`AspisV5InactiveClaimJointHiding.sharedPivotView_pmf_indep`, not freshness.

**Question 3 (serialization position and authentication).**  Open.  No Lean
module transcribes the v5 wire prefix (`AspisSpendWireView` is the v4
6,785-byte prefix; the v5 prefix is 6,423 bytes,
`programs/aspis-verifier/src/v5_wire_skeleton.rs:55`, assert at line 605).
The deployed positions are: terminal triple at `[5799, 5847)`, carried
inactive claim at `[5847, 5863)` (`V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET`,
`v5_cu_probe.rs:167-168`, pinned by the assert at line 178), reserved tail
zero-checked at lines 811-813.  Authentication: the triple is absorbed under
`label::CLAIM` before `γ` (`v5_cu_probe.rs:880-886`), the claim bytes under
`label::SECOND_PHASE_CLAIM` before `κ` (lines 888-894), and the masked half
of the triple must equal the sumcheck terminal (line 877).  This module
transcribes the offset chain and proves its arithmetic
(`v5_prefix_offset_chain`, mirroring the Rust `const` asserts at
`v5_cu_probe.rs:172-180`), names the codec and position premises
(`DeployedQM31CodecRoundTrip`, binding `QM31::from_le_bytes` /
`write_le_bytes`, `crates/aspis-core/src/field.rs:843/849`;
`DeployedMaskedTerminalAtWireOffset`; `DeployedInactiveClaimAtWireOffset`;
`DeployedJointPairAbsorbedPreChallenge`), proves injectivity of the encoder
from the round-trip premise, and derives the existing interface
`ReleasedViewSerializesExactlyTheJointPair` for the designated pair span
(`releasedPair_serialization_of_offsets`).  The "exactly" caveat stands: the
full wire releases more than the pair, and the excess is Question 2's edge,
not a serialization fact.

Every Rust-facing statement in this module is a named `Prop` hypothesis; none
is discharged by definition.  Everything proved is proved over the real
transcribed layout.
-/

namespace AspisV5InactiveClaimDeployedCorrespondence

open AspisV5SumcheckCommitment AspisV5CompactTerminal AspisV5InactiveClaimJointHiding

variable {K : Type*} [Field K]

/-! ## 1. Unconditional layout theorems

Facts about the deployed transcription that need no new hypothesis.  These are
the complete answer to "what do the current layout definitions already give"
for the row-993 pivot. -/

/-- Row 994: a pad row of the deployed 1,024-row layout, strictly between the
reserved pivot row 993 and the physical end of the block region.  It carries
no covector weight; it serves below as a concrete witness coordinate for the
satisfiability of the hypothesis bundle. -/
def padRow : Row := ⟨994, by omega⟩

/-- The transcribed terminal covector also has weight zero at pad row 994:
`994` is neither the initial row 992 nor any coefficient row
`32 * selector + degree ≤ 987`. -/
theorem terminalWeights_padRow_eq_zero (point : Round → K) (scale : K) :
    terminalWeights point scale padRow = 0 := by
  classical
  have hne : padRow ≠ initialRow := by decide
  simp only [terminalWeights, Pi.add_apply, Finset.sum_apply, basis]
  rw [if_neg hne, zero_add]
  refine Finset.sum_eq_zero fun index _ => if_neg fun hEq => ?_
  have hval : (padRow : ℕ) = 32 * blockSelector index.1 + (index.2 : ℕ) := by
    rw [hEq, coefficientRow_val]
  have hp : (padRow : ℕ) = 994 := rfl
  have hsel := blockSelector_le_thirty index.1
  have hdeg : (index.2 : ℕ) < 28 := index.2.isLt
  omega

/-- **The deployed terminal functional annihilates the pivot direction at
every amplitude.**  `terminalDotFunctional_pivot_eq_zero` covers the unit
vector only; the deployed pivot direction in the combined row space carries
the lane power `γ^17`, so the amplitude-general statement is the one the
correspondence actually needs.  No hypothesis: it follows from the proved
row-993 weight-zero fact. -/
theorem terminalDotFunctional_pivot_scaled_eq_zero (point : Round → K)
    (scale value : K) :
    terminalDotFunctional point scale (basis pivotRow value) = 0 := by
  rw [terminalDotFunctional_apply, dot_basis_right, terminalWeights_pivotRow_eq_zero,
    zero_mul]

/-- The terminal functional is likewise zero on the pad-row direction. -/
theorem terminalDotFunctional_padRow_eq_zero (point : Round → K) (scale : K) :
    terminalDotFunctional point scale (basis padRow 1) = 0 := by
  rw [terminalDotFunctional_apply, dot_basis_right, terminalWeights_padRow_eq_zero,
    zero_mul]

/-- **The authenticated terminal opening is blind to pivot shifts.**  Adding
any multiple of any amplitude of the row-993 direction leaves the deployed
terminal value unchanged.  This is the usable form of the proved kernel fact:
the pivot reservation cannot disturb the terminal check. -/
theorem terminalDotFunctional_pivotShift (point : Round → K) (scale : K)
    (m : Row → K) (p value : K) :
    terminalDotFunctional point scale (m + p • basis pivotRow value)
      = terminalDotFunctional point scale m := by
  rw [map_add, map_smul, terminalDotFunctional_pivot_scaled_eq_zero, smul_zero,
    add_zero]

/-- **The authenticated Component-B message does not occupy the pivot row.**
Row 993 is outside the support of `rowMessage`: it is not the initial row 992
and not any coefficient row (those stop at 987).  This mirrors the deployed
encoder, which writes the structured blocks and row 992 and reserves row 993
for the appended pivot (`V5StructuredBLane::encode`,
`crates/aspis-prover/src/v5_spend_messages.rs:269-301`; the pivot write is
line 294-296). -/
theorem rowMessage_pivotRow_eq_zero (initial : K) (tails : Round → TailDegree → K) :
    rowMessage initial tails pivotRow = 0 := by
  classical
  simp only [rowMessage, Pi.add_apply, Finset.sum_apply, basis]
  rw [if_neg (show pivotRow ≠ initialRow by decide), zero_add]
  refine Finset.sum_eq_zero fun index _ => if_neg fun hEq => ?_
  have hval : (pivotRow : ℕ) = 32 * blockSelector index.1 + (index.2 : ℕ) := by
    rw [hEq, coefficientRow_val]
  have hp : (pivotRow : ℕ) = 993 := rfl
  have hsel := blockSelector_le_thirty index.1
  have hdeg : (index.2 : ℕ) < 28 := index.2.isLt
  omega

/-- **The pivot-carrying message authenticates the same ten-round recurrence
as the bare message.**  Appending any pivot amplitude to `rowMessage` leaves
the deployed terminal evaluation at exactly
`scale * tenRoundTerminal initial tails point`.  The row-993 reservation is
free for the Component-B claim. -/
theorem terminalDotFunctional_pivotShifted_rowMessage (point : Round → K)
    (scale initial : K) (tails : Round → TailDegree → K) (p value : K) :
    terminalDotFunctional point scale
        (rowMessage initial tails + p • basis pivotRow value)
      = scale * tenRoundTerminal initial tails point := by
  rw [terminalDotFunctional_pivotShift, terminalDotFunctional_apply,
    dot_terminalWeights_rowMessage_eq_tenRoundTerminal]

/-- The deployed *optimized* evaluator's initial machine state is also blind
to the pivot direction at every amplitude, through the proved non-`rfl`
optimized-evaluator correspondence. -/
theorem dot_represented1024_optimizedInit_pivot (point : Fin 10 → K)
    (scale value : K) :
    dot (AspisV5CompactTerminalOptimized.represented1024
        (AspisV5CompactTerminalOptimized.optimizedInit point scale))
      (basis pivotRow value) = 0 := by
  rw [dot_basis_right, represented1024_optimizedInit_pivotRow_eq_zero, zero_mul]

/-! ## 2. Named deployed binding premises

Each `Prop` below is one irreducible Rust-binding edge, stated at its smallest
content.  None is proved anywhere in this repository; each docstring names the
exact Rust constant and location that a future binding must transcribe. -/

/-- **Unresolved deployed premise (Question 1): the copy-inactive covector has
weight exactly one at row 993.**  Rust content:
`atomic_state_only_copy_inactive_row_masks_v3()`
(`crates/aspis-statement/src/atomic_state_only_terminal.rs:115-122`) sets the
bit of every row not listed in `COMPILED_ATOMIC_COPY_ACTIVE_ROWS`
(`crates/aspis-statement/src/atomic_state_only_terminal_constants.rs:6`; 210
entries, largest 866, so row 993 is set), and
`WeightAccumulator::add_grouped_64x16_binary_masks_deferred`
(`crates/aspis-core/src/sumcheck.rs:272-298`) gives every set row coefficient
`QM31::ONE`.  Consumed by the verifier at
`programs/aspis-verifier/src/v5_cu_probe.rs:1086` and by the prover's released
claim at `crates/aspis-prover/src/v5_real_host_proof.rs:627-633`; row-993
membership is asserted by the regression at
`programs/aspis-verifier/tests/v5_component_b_structured_correspondence.rs:541-550`.
This is the *only* premise Question 1 needs for the row-space hiding
statements; the lane power is a separate, finer premise below. -/
def DeployedInactiveCovectorIsUnitAtPivotRow (inactive : (Row → K) →ₗ[K] K) : Prop :=
  inactive (basis pivotRow 1) = 1

/-- The Component-B generator-order lane index: sixteen C1 lanes, then the
C2 lanes `Hcopy, B, C`, so the B lane is lane `16 + 1`. -/
def componentBLaneIndex : ℕ := 17

theorem componentBLaneIndex_eq_c1_lanes_add_b_lane :
    componentBLaneIndex = 16 + 1 := rfl

/-- **Unresolved deployed premise (Question 1, cell level): the lane
coefficient is the seventeenth power of the layer-zero challenge.**  One unit
of the pivot *cell* — row 993 of the Component-B lane — enters the combined
row value with coefficient `γ^17`.  Rust content: `V5_C1_LANES = 16`
(`crates/aspis-prover/src/v5_spend_messages.rs:61`, assert line 103),
`V5_COMPONENT_B_LANE = 1` within C2 (line 64), generator order
`semantic[0..16], Hcopy, B, C` (lines 308-309), and the power assignment
`powers[V5_C1_LANES + j]` for C2 lane `j` in `gamma_combine_v5_values`
(lines 557-583).  This premise carries uniformity from a sampled pivot cell
to the row-993 combined value; it is *not* needed for the row-space capstone
below. -/
def DeployedGammaBIsComponentBLanePower (gammaB gamma : K) : Prop :=
  gammaB = gamma ^ componentBLaneIndex

/-- **Unresolved deployed premise (Question 2): the residual released view
does not read the pivot direction.**  Rust surfaces that any binding must
inventory: the released relation-claims table at wire prefix bytes
`[4583, 5799)` (`V5_CU_REAL_PREFIX_CLAIMS_OFFSET`, assert
`programs/aspis-verifier/src/v5_cu_probe.rs:176`; table equality checked at
lines 862-866; built at `crates/aspis-prover/src/v5_real_host_proof.rs:595`)
and the FRI query openings.  Warning recorded, not assumed away: the claims
table contains the Component-B lane evaluated at the three multilinear
points, and a multilinear `eq` covector at a generic point has *nonzero*
weight at row 993, so for a residual view containing those three claims this
premise is expected to be false; only the fourth claim group, checked against
the compact terminal covector, is pivot-blind
(`terminalDotFunctional_pivot_scaled_eq_zero`).  If false, the analysis must
route through the correlated-invariant hypothesis of
`AspisV5InactiveClaimJointHiding.sharedPivotView_pmf_indep` instead of
freshness. -/
def DeployedResidualViewFreshAtPivotRow {V : Type*} [AddCommGroup V] [Module K V]
    (released : (Row → K) →ₗ[K] V) : Prop :=
  released (basis pivotRow 1) = 0

/-! ### The v5 wire-prefix offset chain (Question 3)

Transcription of the deployed offset constants
(`programs/aspis-verifier/src/v5_cu_probe.rs:155-180`).  The definitions are
the Lean-side spelling; `v5_prefix_offset_chain` proves the same arithmetic
the Rust `const` asserts pin.  The identification of these numbers with the
compiled constants is part of the serialization premises below, not a theorem. -/

def qm31Bytes : ℕ := 16
/-- `V5_WIRE_PREFIX_BYTES` (`programs/aspis-verifier/src/v5_wire_skeleton.rs:55`,
asserted `6_423` at line 605). -/
def v5WirePrefixBytes : ℕ := 6423
def v5HeaderBytes : ℕ := 23
def v5C1RootOffset : ℕ := v5HeaderBytes
def v5C2RootOffset : ℕ := v5C1RootOffset + 32
def v5InitialBClaimOffset : ℕ := v5C2RootOffset + 32
def v5SumcheckOffset : ℕ := v5InitialBClaimOffset + qm31Bytes
/-- Ten rounds of twenty-eight stored coefficients, sixteen bytes each. -/
def v5SumcheckBytes : ℕ := 10 * 28 * qm31Bytes
def v5ClaimsOffset : ℕ := v5SumcheckOffset + v5SumcheckBytes
/-- Four claim groups over nineteen lanes. -/
def v5ClaimsBytes : ℕ := 4 * 19 * qm31Bytes
def v5TerminalTripleOffset : ℕ := v5ClaimsOffset + v5ClaimsBytes
def v5MaskedTerminalOffset : ℕ := v5TerminalTripleOffset + 2 * qm31Bytes
def v5InactiveClaimOffset : ℕ := v5TerminalTripleOffset + 3 * qm31Bytes
def v5ReservedOffset : ℕ := v5InactiveClaimOffset + qm31Bytes

/-- The transcribed chain reproduces the pinned Rust offsets
(`v5_cu_probe.rs:172-180`): claims at 4,583, terminal triple at 5,799, masked
terminal at 5,831, carried inactive claim at 5,847, reserved tail at 5,863,
inside the 6,423-byte prefix. -/
theorem v5_prefix_offset_chain :
    v5SumcheckOffset = 103 ∧ v5ClaimsOffset = 4583 ∧
      v5TerminalTripleOffset = 5799 ∧ v5MaskedTerminalOffset = 5831 ∧
      v5InactiveClaimOffset = 5847 ∧ v5ReservedOffset = 5863 ∧
      v5ReservedOffset ≤ v5WirePrefixBytes := by
  decide

/-- **Unresolved deployed premise (Question 3): the QM31 byte codec round
trips.**  Rust content: `QM31::write_le_bytes`
(`crates/aspis-core/src/field.rs:849`) followed by `QM31::from_le_bytes`
(line 843, which returns `None` on non-canonical limbs) recovers the value.
Injectivity of the encoder is *derived* from this premise below, not assumed
separately. -/
def DeployedQM31CodecRoundTrip {Bytes : Type*} (encode : K → Bytes)
    (decode : Bytes → Option K) : Prop :=
  ∀ value : K, decode (encode value) = some value

/-- **Unresolved deployed premise (Question 3): the masked terminal value sits
at prefix bytes `[5831, 5847)`.**  Rust content: the third component of the
terminal triple at `V5_CU_REAL_PREFIX_TERMINAL_OFFSET + 2 * QM31_BYTES`
(`v5_cu_probe.rs:875-876`), checked equal to the sumcheck terminal at line
877.  `slice start stop` denotes the deployed wire prefix bytes `[start, stop)`. -/
def DeployedMaskedTerminalAtWireOffset {Bytes : Type*} (slice : ℕ → ℕ → Bytes)
    (encode : K → Bytes) (t : K) : Prop :=
  slice v5MaskedTerminalOffset v5InactiveClaimOffset = encode t

/-- **Unresolved deployed premise (Question 3): the carried inactive claim
sits at prefix bytes `[5847, 5863)`.**  Rust content:
`V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET` (`v5_cu_probe.rs:167-168`, assert
line 178), decoded at line 887, written by the prover at
`v5_real_host_proof.rs:634-635`; the reserved tail beyond 5,863 is
zero-checked at `v5_cu_probe.rs:811-813`, so no second copy shares the
prefix. -/
def DeployedInactiveClaimAtWireOffset {Bytes : Type*} (slice : ℕ → ℕ → Bytes)
    (encode : K → Bytes) (claim : K) : Prop :=
  slice v5InactiveClaimOffset v5ReservedOffset = encode claim

/-- **Unresolved deployed premise (Question 3): both spans are
transcript-authenticated before the second-phase challenges.**  Rust content:
the terminal triple `[5799, 5847)` is absorbed under `label::CLAIM` before
`γ` is drawn (`v5_cu_probe.rs:880-886`), and the claim span `[5847, 5863)` is
absorbed under `label::SECOND_PHASE_CLAIM` before `κ` is drawn (lines
888-894).  The predicate parameter stands for "absorbed into the Fiat-Shamir
transcript before the dependent challenges"; its own soundness is the
transcript model's obligation, not this file's. -/
def DeployedJointPairAbsorbedPreChallenge {Bytes : Type*} (slice : ℕ → ℕ → Bytes)
    (absorbedBeforeChallenge : Bytes → Prop) : Prop :=
  absorbedBeforeChallenge (slice v5TerminalTripleOffset v5InactiveClaimOffset) ∧
    absorbedBeforeChallenge (slice v5InactiveClaimOffset v5ReservedOffset)

/-! ## 3. Conditional discharges

Theorems consuming only the named premises above plus proved layout facts.
These convert the coarse interfaces of `V5InactiveClaimJointHiding` into the
minimal premises, or eliminate them outright. -/

/-- A one-coordinate row vector of any amplitude is the scalar multiple of the
unit one. -/
theorem basis_eq_smul_basis_one (row : Row) (value : K) :
    basis row value = value • basis row 1 := by
  funext query
  by_cases h : query = row <;> simp [basis, h]

/-- **Discharge of `PivotCoefficientIsGammaB` at the unit pivot.**  The
binary-mask premise *is* the interface at `gammaB = 1`. -/
theorem pivotCoefficient_one_of_binary_mask (inactive : (Row → K) →ₗ[K] K)
    (hmask : DeployedInactiveCovectorIsUnitAtPivotRow inactive) :
    PivotCoefficientIsGammaB inactive (basis pivotRow 1) 1 := by
  rw [PivotCoefficientIsGammaB]
  rw [DeployedInactiveCovectorIsUnitAtPivotRow] at hmask
  exact hmask

/-- **Discharge of `PivotCoefficientIsGammaB` at every scaled pivot.**  Under
the binary-mask premise, the carried claim reads the `c`-amplitude pivot
direction with coefficient exactly `c` — in particular the deployed
cell-image direction `basis pivotRow (γ^17)` with coefficient `γ^17`. -/
theorem pivotCoefficient_scaled_of_binary_mask (inactive : (Row → K) →ₗ[K] K)
    (hmask : DeployedInactiveCovectorIsUnitAtPivotRow inactive) (gammaB : K) :
    PivotCoefficientIsGammaB inactive (basis pivotRow gammaB) gammaB := by
  rw [PivotCoefficientIsGammaB, basis_eq_smul_basis_one, map_smul, smul_eq_mul]
  rw [DeployedInactiveCovectorIsUnitAtPivotRow] at hmask
  rw [hmask, mul_one]

/-- Under the binary-mask premise the pivot feeds the inactive claim: the
`hpivot_inactive` hypothesis of the joint-hiding engine, with no
lane-coefficient fact consumed. -/
theorem pivot_inactive_ne_zero_of_binary_mask (inactive : (Row → K) →ₗ[K] K)
    (hmask : DeployedInactiveCovectorIsUnitAtPivotRow inactive) :
    inactive (basis pivotRow (1 : K)) ≠ 0 := by
  rw [DeployedInactiveCovectorIsUnitAtPivotRow] at hmask
  rw [hmask]
  exact one_ne_zero

/-- The lane power is nonzero exactly when `γ` is: the nonzeroness half of the
γB interface reduces to the `challenge_nonzero_qm31` draw. -/
theorem gammaB_ne_zero_of_lane_power {gammaB gamma : K}
    (hlane : DeployedGammaBIsComponentBLanePower gammaB gamma)
    (hgamma : gamma ≠ 0) : gammaB ≠ 0 := by
  rw [DeployedGammaBIsComponentBLanePower] at hlane
  rw [hlane]
  exact pow_ne_zero _ hgamma

/-- **Discharge of `GammaBIsPostCommitmentLaneCoefficient`, reduced to the
γ-level facts.**  With the lane coefficient spelled as the seventeenth power
of the transcript-derived `γ`, the interface follows from: the derivation of
`γ` from the pivot-carrying commitment (`hderive` — transcript-schedule
correspondence, `v5_cu_probe.rs:836-886`), the lane-power identification
(`hlane`), and `γ ≠ 0` (`challenge_nonzero_qm31`, lines 884-886). -/
theorem gammaB_interface_of_lane_power {Commitment : Type*}
    (deriveGamma : Commitment → K) (pivotCommitment : Commitment)
    (gamma gammaB : K) (hderive : deriveGamma pivotCommitment = gamma)
    (hlane : DeployedGammaBIsComponentBLanePower gammaB gamma)
    (hgamma : gamma ≠ 0) :
    GammaBIsPostCommitmentLaneCoefficient
      (fun commitment => deriveGamma commitment ^ componentBLaneIndex)
      pivotCommitment gammaB := by
  rw [DeployedGammaBIsComponentBLanePower] at hlane
  refine ⟨?_, ?_⟩
  · show deriveGamma pivotCommitment ^ componentBLaneIndex = gammaB
    rw [hderive, hlane]
  · rw [hlane]
    exact pow_ne_zero _ hgamma

/-- **Deployed capstone from the binary-mask premise alone.**  The full triple
joint hiding at the transcribed terminal covector, consuming: the proved
row-993 kernel fact, the single premise
`DeployedInactiveCovectorIsUnitAtPivotRow` (which supplies both
`PivotCoefficientIsGammaB` and, via `1 ≠ 0`, the entire `gammaB ≠ 0`
obligation), the named freshness premise, and restricted surjectivity.  No
lane-coefficient fact is consumed: at the row level the deployed pivot
coefficient is one. -/
theorem deployed_joint_hiding_of_binary_mask {V : Type*} [AddCommGroup V]
    [Module K V] [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    (point : Round → K) (scale : K) (inactive : (Row → K) →ₗ[K] K)
    (released : (Row → K) →ₗ[K] V)
    (hmask : DeployedInactiveCovectorIsUnitAtPivotRow inactive)
    (hfresh : DeployedResidualViewFreshAtPivotRow released)
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
            inactive (m₂ + (u : Row → K)), released (m₂ + (u : Row → K)))) := by
  rw [DeployedResidualViewFreshAtPivotRow] at hfresh
  exact deployed_joint_hiding_from_gammaB point scale inactive released 1
    (pivotCoefficient_one_of_binary_mask inactive hmask) one_ne_zero hfresh hrel
    t m₁ m₂ h₁ h₂

/-! ### Freshness: the provable positive fragment -/

/-- The deployed terminal functional is itself fresh at the pivot: a residual
view built from the terminal covector cannot read row 993. -/
theorem terminal_fresh_at_pivot (point : Round → K) (scale : K) :
    DeployedResidualViewFreshAtPivotRow (terminalDotFunctional point scale) := by
  rw [DeployedResidualViewFreshAtPivotRow]
  exact terminalDotFunctional_pivot_scaled_eq_zero point scale 1

/-- Any single physical row read other than row 993 is fresh at the pivot. -/
theorem proj_fresh_at_pivot (row : Row) (hrow : row ≠ pivotRow) :
    DeployedResidualViewFreshAtPivotRow
      (LinearMap.proj row : (Row → K) →ₗ[K] K) := by
  rw [DeployedResidualViewFreshAtPivotRow]
  simp [basis, hrow]

/-- **The exact boundary of provable freshness.**  A residual view that is any
family of physical row reads avoiding row 993 is fresh at the pivot.  The
deployed claims table is *not* of this shape — its `eq` covectors read every
row — which is why `DeployedResidualViewFreshAtPivotRow` for the deployed
residual view remains an open premise rather than a theorem. -/
theorem pi_proj_fresh_at_pivot {ι : Type*} (rows : ι → Row)
    (hrows : ∀ index, rows index ≠ pivotRow) :
    DeployedResidualViewFreshAtPivotRow
      (LinearMap.pi (fun index => LinearMap.proj (rows index)) :
        (Row → K) →ₗ[K] (ι → K)) := by
  rw [DeployedResidualViewFreshAtPivotRow]
  funext index
  simp [LinearMap.pi_apply, basis, hrows index]

/-! ### Serialization: injectivity from the codec premise, and the pair
interface for the designated span -/

omit [Field K] in
/-- A round-tripping encoder is injective.  This removes the standalone
injectivity assumption from the serialization interface: it is a consequence
of the codec premise. -/
theorem encode_injective_of_codec_roundTrip {Bytes : Type*} {encode : K → Bytes}
    {decode : Bytes → Option K}
    (hcodec : DeployedQM31CodecRoundTrip encode decode) :
    Function.Injective encode := by
  intro left right hEq
  have hleft := hcodec left
  rw [hEq, hcodec right] at hleft
  exact (Option.some_inj.mp hleft).symm

omit [Field K] in
/-- **Partial discharge of `ReleasedViewSerializesExactlyTheJointPair` for the
designated pair span.**  Given the codec round trip and the two position
premises, the existing interface holds for the componentwise pair encoder and
the byte pair `(prefix[5831, 5847), prefix[5847, 5863))`: the encoder is
injective (proved from the round trip) and the released span is exactly the
encoded pair.  Scope caveat, stated rather than hidden: this binds the pair
*span*; the full wire prefix releases further functionals of the same mask,
and whether those read the pivot is Question 2's freshness premise, not a
serialization fact. -/
theorem releasedPair_serialization_of_offsets {Bytes : Type*}
    (slice : ℕ → ℕ → Bytes) (encode : K → Bytes) (decode : Bytes → Option K)
    (hcodec : DeployedQM31CodecRoundTrip encode decode) (t claim : K)
    (hpos_t : DeployedMaskedTerminalAtWireOffset slice encode t)
    (hpos_claim : DeployedInactiveClaimAtWireOffset slice encode claim) :
    ReleasedViewSerializesExactlyTheJointPair
      (fun pair : K × K => (encode pair.1, encode pair.2))
      (slice v5MaskedTerminalOffset v5InactiveClaimOffset,
        slice v5InactiveClaimOffset v5ReservedOffset) t claim := by
  rw [DeployedMaskedTerminalAtWireOffset] at hpos_t
  rw [DeployedInactiveClaimAtWireOffset] at hpos_claim
  refine ⟨?_, ?_⟩
  · intro left right hEq
    have hinj := encode_injective_of_codec_roundTrip hcodec
    exact Prod.ext (hinj (congrArg Prod.fst hEq)) (hinj (congrArg Prod.snd hEq))
  · rw [hpos_t, hpos_claim]

/-! ## 4. Non-vacuity

Satisfiability of every premise, and of the whole capstone hypothesis bundle
at the real transcribed terminal covector — not at a toy model. -/

/-- The binary-mask premise is satisfiable: the row-993 coordinate projection
satisfies it. -/
theorem binary_mask_interface_nonvacuous :
    DeployedInactiveCovectorIsUnitAtPivotRow
      (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K) := by
  rw [DeployedInactiveCovectorIsUnitAtPivotRow]
  simp [basis]

/-- The lane-power premise is satisfiable. -/
theorem lane_power_interface_nonvacuous (gamma : K) :
    DeployedGammaBIsComponentBLanePower (gamma ^ componentBLaneIndex) gamma := rfl

/-- The pad-row projection is surjective on the kernel of the real terminal
functional: pad row 994 has terminal weight zero, so its unit vector is a
kernel witness with nonzero read. -/
theorem proj_padRow_restricted_surjective (point : Round → K) (scale : K) :
    Function.Surjective ((LinearMap.proj padRow : (Row → K) →ₗ[K] K) ∘ₗ
      (LinearMap.ker (terminalDotFunctional point scale)).subtype) :=
  (inactive_on_ker_surjective_iff_kernel_witness
      (terminalDotFunctional point scale) (LinearMap.proj padRow)).mp
    ⟨basis padRow 1,
      LinearMap.mem_ker.mpr (terminalDotFunctional_padRow_eq_zero point scale),
      by simp [basis]⟩

/-- **The whole capstone hypothesis bundle is satisfiable at the real terminal
covector**: the row-993 projection satisfies the binary-mask premise, the
row-994 projection is fresh at the pivot and restrictedly surjective on the
real terminal kernel — simultaneously, for every `point` and `scale`. -/
theorem deployed_hypothesis_bundle_instantiable (point : Round → K) (scale : K) :
    DeployedInactiveCovectorIsUnitAtPivotRow
        (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
      ∧ DeployedResidualViewFreshAtPivotRow
        (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
      ∧ Function.Surjective ((LinearMap.proj padRow : (Row → K) →ₗ[K] K) ∘ₗ
          (LinearMap.ker (terminalDotFunctional point scale)).subtype) :=
  ⟨binary_mask_interface_nonvacuous,
    proj_fresh_at_pivot padRow (by decide),
    proj_padRow_restricted_surjective point scale⟩

/-- **Non-vacuity of the capstone conclusion at the real covector.**  For the
instantiation of the bundle above, the triple joint law is witness-independent
across two genuinely different witnesses of the terminal value `0`: the zero
message and the unit pivot vector, which differ exactly in their inactive
coordinate. -/
theorem deployed_capstone_nonvacuous [Fintype K] [DecidableEq K]
    (point : Round → K) (scale : K) :
    (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale ((0 : Row → K) + (u : Row → K)),
            (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
              ((0 : Row → K) + (u : Row → K)),
            (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
              ((0 : Row → K) + (u : Row → K))))
      = (PMF.uniformOfFintype (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (basis pivotRow 1 + (u : Row → K)),
            (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
              (basis pivotRow 1 + (u : Row → K)),
            (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
              (basis pivotRow 1 + (u : Row → K)))) :=
  deployed_joint_hiding_of_binary_mask point scale (LinearMap.proj pivotRow)
    (LinearMap.proj padRow) binary_mask_interface_nonvacuous
    (proj_fresh_at_pivot padRow (by decide))
    (proj_padRow_restricted_surjective point scale) 0 0 (basis pivotRow 1)
    (map_zero _) (terminalDotFunctional_pivot_scaled_eq_zero point scale 1)

omit [Field K] in
/-- The serialization premises are jointly satisfiable. -/
theorem serialization_interface_nonvacuous (t claim : K) :
    ∃ slice : ℕ → ℕ → Option K,
      DeployedQM31CodecRoundTrip (some : K → Option K) id ∧
        DeployedMaskedTerminalAtWireOffset slice some t ∧
        DeployedInactiveClaimAtWireOffset slice some claim := by
  refine ⟨fun start _ =>
    if start = v5MaskedTerminalOffset then some t else some claim,
    fun _ => rfl, ?_, ?_⟩
  · rw [DeployedMaskedTerminalAtWireOffset]
    exact if_pos rfl
  · rw [DeployedInactiveClaimAtWireOffset]
    exact if_neg (by decide)

/-! ## Status ledger

Interfaces of `V5InactiveClaimJointHiding` after this module:

* `PivotCoefficientIsGammaB` — **discharged conditionally**: proved from the
  single premise `DeployedInactiveCovectorIsUnitAtPivotRow` at the unit pivot
  (`pivotCoefficient_one_of_binary_mask`) and at every scaled pivot
  (`pivotCoefficient_scaled_of_binary_mask`).  The premise is the binary
  row-mask bind; it is smaller than the interface it replaces because it
  fixes the coefficient to the literal `1` of the deployed accumulator.
* `gammaB ≠ 0` (as consumed by `deployed_joint_hiding_from_gammaB`) —
  **eliminated** at the row level: `deployed_joint_hiding_of_binary_mask`
  instantiates it with `one_ne_zero`.
* `GammaBIsPostCommitmentLaneCoefficient` — **discharged conditionally** by
  `gammaB_interface_of_lane_power` from the lane-power premise, the γ
  derivation, and `γ ≠ 0`.
* Residual freshness — **open**, named `DeployedResidualViewFreshAtPivotRow`,
  with the provable fragment fenced exactly
  (`terminal_fresh_at_pivot`, `proj_fresh_at_pivot`, `pi_proj_fresh_at_pivot`)
  and the deployed counter-evidence recorded in the premise docstring.
* `ReleasedViewSerializesExactlyTheJointPair` — **discharged conditionally
  for the pair span** by `releasedPair_serialization_of_offsets` from the
  codec round trip and the two offset premises; injectivity is proved, not
  assumed.  Full-wire exactness is out of scope by construction and routed to
  the freshness premise.
* `PivotBoundByPreChallengeCommitment` and the transcript model behind
  `DeployedJointPairAbsorbedPreChallenge` — untouched here; commitment
  binding remains with `V5SumcheckTranscriptBinding`.
-/

end AspisV5InactiveClaimDeployedCorrespondence

#print axioms AspisV5InactiveClaimDeployedCorrespondence.padRow
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminalWeights_padRow_eq_zero
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminalDotFunctional_pivot_scaled_eq_zero
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminalDotFunctional_padRow_eq_zero
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminalDotFunctional_pivotShift
#print axioms AspisV5InactiveClaimDeployedCorrespondence.rowMessage_pivotRow_eq_zero
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminalDotFunctional_pivotShifted_rowMessage
#print axioms AspisV5InactiveClaimDeployedCorrespondence.dot_represented1024_optimizedInit_pivot
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedInactiveCovectorIsUnitAtPivotRow
#print axioms AspisV5InactiveClaimDeployedCorrespondence.componentBLaneIndex
#print axioms AspisV5InactiveClaimDeployedCorrespondence.componentBLaneIndex_eq_c1_lanes_add_b_lane
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedGammaBIsComponentBLanePower
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedResidualViewFreshAtPivotRow
#print axioms AspisV5InactiveClaimDeployedCorrespondence.v5_prefix_offset_chain
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedQM31CodecRoundTrip
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedMaskedTerminalAtWireOffset
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedInactiveClaimAtWireOffset
#print axioms AspisV5InactiveClaimDeployedCorrespondence.DeployedJointPairAbsorbedPreChallenge
#print axioms AspisV5InactiveClaimDeployedCorrespondence.basis_eq_smul_basis_one
#print axioms AspisV5InactiveClaimDeployedCorrespondence.pivotCoefficient_one_of_binary_mask
#print axioms AspisV5InactiveClaimDeployedCorrespondence.pivotCoefficient_scaled_of_binary_mask
#print axioms AspisV5InactiveClaimDeployedCorrespondence.pivot_inactive_ne_zero_of_binary_mask
#print axioms AspisV5InactiveClaimDeployedCorrespondence.gammaB_ne_zero_of_lane_power
#print axioms AspisV5InactiveClaimDeployedCorrespondence.gammaB_interface_of_lane_power
#print axioms AspisV5InactiveClaimDeployedCorrespondence.deployed_joint_hiding_of_binary_mask
#print axioms AspisV5InactiveClaimDeployedCorrespondence.terminal_fresh_at_pivot
#print axioms AspisV5InactiveClaimDeployedCorrespondence.proj_fresh_at_pivot
#print axioms AspisV5InactiveClaimDeployedCorrespondence.pi_proj_fresh_at_pivot
#print axioms AspisV5InactiveClaimDeployedCorrespondence.encode_injective_of_codec_roundTrip
#print axioms AspisV5InactiveClaimDeployedCorrespondence.releasedPair_serialization_of_offsets
#print axioms AspisV5InactiveClaimDeployedCorrespondence.binary_mask_interface_nonvacuous
#print axioms AspisV5InactiveClaimDeployedCorrespondence.lane_power_interface_nonvacuous
#print axioms AspisV5InactiveClaimDeployedCorrespondence.proj_padRow_restricted_surjective
#print axioms AspisV5InactiveClaimDeployedCorrespondence.deployed_hypothesis_bundle_instantiable
#print axioms AspisV5InactiveClaimDeployedCorrespondence.deployed_capstone_nonvacuous
#print axioms AspisV5InactiveClaimDeployedCorrespondence.serialization_interface_nonvacuous
