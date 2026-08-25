import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriJohnsonListBound

/-!
# V6 high-rate one-fold parameter audit

This file checks the finite arithmetic and the one-fold algebra proposed for
the B10 V6 research profile. It deliberately does not turn the companion
screening script into a security theorem.

The checked facts are:

* the initial code has dimension `1024` and domain size `2^20`;
* one arity-four circle fold ends at `256` coefficients on `2^18` line
  positions;
* the Johnson agreement is exactly `7/192`;
* equation (74) selects multiplicity three at both the initial and output
  rates;
* agreement floors `38230` and `9558`, together with overlap caps `1024` and
  `255`, imply direct list caps `100` and `99` respectively;
* the generic circle encoder/fold square really does specialize to
  `1024 -> 256` coefficients and `2^20 -> 2^18` symbols; and
* the selected V6 grammar uses the three point rows already consumed by the
  maintained selected-hiding terminal, rather than V5's obsolete fourth
  structured-mask row;
* the released-compatible `16 + 3` PCS width would give `30391` bytes; and
* the selected V6 `26 + 3` width gives `33336` bytes at the same frontier cap,
  below the 40-KiB hard limit but not below the 30-KiB optimization target.

The published circle/RS decoding and correlated-agreement theorems, the
one-round Fiat--Shamir/BCS reduction, and the exact production transcript are
separate interfaces. In particular, this file does not claim the screened
`101.51`-bit figure as a proved security bound.
-/

namespace AspisV6OneFoldParameterAudit

open AspisV5FriConcreteEncoderCommutation
open AspisV5FriJohnsonListBound
open AspisV5ComponentCConcreteFoldLinearity

/-! ## Exact profile dimensions -/

def initialCoefficientCount : Nat := 1024
def finalCoefficientCount : Nat := 256
def initialDomainSize : Nat := 2 ^ 20
def finalDomainSize : Nat := 2 ^ 18
def queryCount : Nat := 16
def selectorCount : Nat := 3
def frontierCap : Nat := 209

theorem exact_dimensions :
    initialCoefficientCount = 4 * finalCoefficientCount ∧
      initialDomainSize = 4 * finalDomainSize ∧
      initialDomainSize = 1048576 ∧
      finalDomainSize = 262144 := by
  norm_num [initialCoefficientCount, finalCoefficientCount,
    initialDomainSize, finalDomainSize]

/-! ## Equation (74) at B10 -/

noncomputable def initialRate : Real := 1 / 1024
noncomputable def outputRate : Real := 255 / finalDomainSize
noncomputable def agreement : Real := (1 + 1 / (2 * 3 : Real)) *
  Real.sqrt initialRate

noncomputable def multiplicityRatio (rate : Real) : Real :=
  Real.sqrt rate / (2 * (agreement - Real.sqrt rate))

noncomputable def multiplicity (rate : Real) : Nat :=
  max ⌈multiplicityRatio rate⌉₊ 3

private theorem outputRate_pos : 0 < outputRate := by
  norm_num [outputRate, finalDomainSize]

private theorem sqrt_initialRate_eq : Real.sqrt initialRate = 1 / 32 := by
  rw [show initialRate = (1 / 32 : Real) ^ 2 by
    norm_num [initialRate]]
  rw [Real.sqrt_sq_eq_abs]
  norm_num

theorem exact_agreement : agreement = 7 / 192 := by
  rw [agreement, sqrt_initialRate_eq]
  norm_num

theorem exact_initial_multiplicity_ratio :
    multiplicityRatio initialRate = 3 := by
  rw [multiplicityRatio, exact_agreement, sqrt_initialRate_eq]
  norm_num

theorem exact_initial_multiplicity : multiplicity initialRate = 3 := by
  simp [multiplicity, exact_initial_multiplicity_ratio]

private theorem sqrt_outputRate_sq :
    Real.sqrt outputRate ^ 2 = outputRate :=
  Real.sq_sqrt outputRate_pos.le

private theorem sqrt_outputRate_nonneg : 0 ≤ Real.sqrt outputRate :=
  Real.sqrt_nonneg _

private theorem sqrt_outputRate_lt_one_div_32 :
    Real.sqrt outputRate < 1 / 32 := by
  have hs := sqrt_outputRate_sq
  have hn := sqrt_outputRate_nonneg
  norm_num [outputRate, finalDomainSize] at hs ⊢
  nlinarith

theorem output_multiplicity_ratio_le_three :
    multiplicityRatio outputRate ≤ 3 := by
  have hslt : Real.sqrt outputRate < agreement := by
    rw [exact_agreement]
    have hs := sqrt_outputRate_lt_one_div_32
    norm_num at hs ⊢
    linarith
  have hden : 0 < 2 * (agreement - Real.sqrt outputRate) := by
    linarith
  rw [show multiplicityRatio outputRate =
      Real.sqrt outputRate /
        (2 * (agreement - Real.sqrt outputRate)) by rfl]
  rw [div_le_iff₀ hden]
  rw [exact_agreement]
  have hs := sqrt_outputRate_lt_one_div_32
  norm_num at hs ⊢
  linarith

theorem exact_output_multiplicity : multiplicity outputRate = 3 := by
  have hceil : ⌈multiplicityRatio outputRate⌉₊ ≤ 3 :=
    (Nat.ceil_le).2 output_multiplicity_ratio_le_three
  unfold multiplicity
  omega

/-! ## Exact agreement floors and direct list caps -/

theorem exact_initial_agreement_floor :
    (38229 : Real) < agreement * initialDomainSize ∧
      agreement * initialDomainSize < 38230 := by
  rw [exact_agreement]
  norm_num [initialDomainSize]

theorem exact_output_agreement_floor :
    (9557 : Real) < agreement * finalDomainSize ∧
      agreement * finalDomainSize < 9558 := by
  rw [exact_agreement]
  norm_num [finalDomainSize]

/-- A direct second-moment Johnson argument gives at most 100 initial
coefficient candidates once distinct codewords overlap on at most 1024
coordinates. The published decoding theorem is what must supply that
overlap premise for the intended circle encoder. -/
theorem initial_list_card_lt_101
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (candidateAgreement : Candidate → Finset (Fin 1048576))
    (hlarge : ∀ c, 38230 ≤ (candidateAgreement c).card)
    (hoverlap : ∀ c d, c ≠ d →
      ((candidateAgreement c) ∩ (candidateAgreement d)).card ≤ 1024) :
    Fintype.card Candidate < 101 := by
  apply list_card_lt_of_johnson_parameters candidateAgreement
    1048576 38230 1024 101
  · simp
  · exact hlarge
  · exact hoverlap
  · norm_num
  · norm_num
  · norm_num

/-- After the one fold, the same argument gives at most 99 degree-255
coefficient candidates once distinct output codewords overlap on at most 255
coordinates. -/
theorem output_list_card_lt_100
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (candidateAgreement : Candidate → Finset (Fin 262144))
    (hlarge : ∀ c, 9558 ≤ (candidateAgreement c).card)
    (hoverlap : ∀ c d, c ≠ d →
      ((candidateAgreement c) ∩ (candidateAgreement d)).card ≤ 255) :
    Fintype.card Candidate < 100 := by
  apply list_card_lt_of_johnson_parameters candidateAgreement
    262144 9558 255 100
  · simp
  · exact hlarge
  · exact hoverlap
  · norm_num
  · norm_num
  · norm_num

/-! ## Exact one-fold encoder identity -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

abbrev InitialCoefficients (K : Type*) := Fin 1024 → K
abbrev FinalCoefficients (K : Type*) := Fin 256 → K
abbrev InitialWord (K : Type*) := Fin 1048576 → K
abbrev FinalWord (K : Type*) := Fin 262144 → K

/-- The generic algebraic commuting square specialized to the proposed V6
dimensions. It proves that the sole circle fold ends in the disclosed
256-coefficient object; no later committed FRI layer is required for this
identity. -/
theorem one_circle_fold_ends_in_explicit_final256
    (finalEncoder : FinalCoefficients K →ₗ[K] FinalWord K)
    (alpha : K) (x y : Fin 262144 → K)
    (inverse2x inverse2y : Fin 262144 → F)
    (hx : ∀ i, 2 * x i * algebraMap F K (inverse2x i) = 1)
    (hy : ∀ i, 2 * y i * algebraMap F K (inverse2y i) = 1) :
    circleFoldLayer 262144 alpha inverse2x inverse2y ∘ₗ
        circleLiftEncoder finalEncoder x y =
      finalEncoder ∘ₗ coefficientFoldLayer 256 alpha := by
  exact circleFoldLayer_circleLiftEncoder
    finalEncoder alpha x y inverse2x inverse2y hx hy

/-! ## Exact wire arithmetic from the proposed grammar

The repository has two relevant column widths.  V5's production PCS uses 16
M31 C1 columns and 3 QM31 C2 columns.  V6 integrates all ten selected
mask-only C1 columns and therefore freezes the production profile at 26 + 3.
Keeping both profiles explicit prevents the smaller 16 + 3 comparison result
from being accidentally advertised as the V6 production body.  These counts
also use V6's exact three point-claim rows; the obsolete V5 fourth row is not
part of the V6 grammar. -/

structure WireProfile where
  c1Columns : Nat
  c2Columns : Nat
  queries : Nat
  frontier : Nat
  deriving DecidableEq

def releasedCompatibleWireProfile : WireProfile where
  c1Columns := 16
  c2Columns := 3
  queries := 16
  frontier := 209

def selectedHidingWireProfile : WireProfile where
  c1Columns := 26
  c2Columns := 3
  queries := 16
  frontier := 209

def packedBytes (bits : Nat) : Nat := (bits + 7) / 8

def fixedQm31Count (profile : WireProfile) : Nat :=
  1 + 10 * 27 + 3 * (profile.c1Columns + profile.c2Columns) +
    1 + 2 + 4 * 6 + 256

def fixedWireBytesFor (profile : WireProfile) : Nat :=
  packedBytes (4 * fixedQm31Count profile * 31) + 2 * 32 + 3 * 8

def bytesPerQueryFor (profile : WireProfile) : Nat :=
  packedBytes (4 * profile.c1Columns * 31) +
    packedBytes (4 * profile.c2Columns * 4 * 31) + 32

def maxProofBodyBytes : Nat := 30 * 1024
def hardProofBodyBytes : Nat := 40 * 1024

def proofBodyBytesFor (profile : WireProfile) : Nat :=
  fixedWireBytesFor profile + bytesPerQueryFor profile * profile.queries +
    2 * profile.frontier * 32

theorem released_compatible_fixed_qm31_count :
    fixedQm31Count releasedCompatibleWireProfile = 611 := by
  norm_num [fixedQm31Count, releasedCompatibleWireProfile]

theorem released_compatible_body_size :
    proofBodyBytesFor releasedCompatibleWireProfile = 30391 := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, releasedCompatibleWireProfile]

theorem released_compatible_body_margin :
    proofBodyBytesFor releasedCompatibleWireProfile + 329 =
      maxProofBodyBytes := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, releasedCompatibleWireProfile,
    maxProofBodyBytes]

theorem released_compatible_upload_count :
    (proofBodyBytesFor releasedCompatibleWireProfile + 959) / 960 = 32 := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, releasedCompatibleWireProfile]

theorem selected_hiding_fixed_qm31_count :
    fixedQm31Count selectedHidingWireProfile = 641 := by
  norm_num [fixedQm31Count, selectedHidingWireProfile]

theorem selected_hiding_body_size :
    proofBodyBytesFor selectedHidingWireProfile = 33336 := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, selectedHidingWireProfile]

theorem selected_hiding_does_not_fit_30_kib :
    maxProofBodyBytes < proofBodyBytesFor selectedHidingWireProfile := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, selectedHidingWireProfile,
    maxProofBodyBytes]

theorem selected_hiding_fits_40_kib :
    proofBodyBytesFor selectedHidingWireProfile + 7624 =
      hardProofBodyBytes := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, selectedHidingWireProfile,
    hardProofBodyBytes]

theorem selected_hiding_upload_count :
    (proofBodyBytesFor selectedHidingWireProfile + 959) / 960 = 35 := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, selectedHidingWireProfile]

def selectedHidingCompactWireProfile (frontier : Nat) : WireProfile where
  c1Columns := 26
  c2Columns := 3
  queries := 16
  frontier := frontier

theorem selected_hiding_largest_frontier_below_30_kib :
    proofBodyBytesFor (selectedHidingCompactWireProfile 168) ≤
        maxProofBodyBytes ∧
      maxProofBodyBytes <
        proofBodyBytesFor (selectedHidingCompactWireProfile 169) := by
  norm_num [proofBodyBytesFor, fixedWireBytesFor, bytesPerQueryFor,
    packedBytes, fixedQm31Count, selectedHidingCompactWireProfile,
    maxProofBodyBytes]

/-! ## Conservative BCS round inventory -/

/-- Public prover material after the initial C1 ensemble, deliberately split
more finely than the likely BCS grouping. Keeping the two OOD values and work
nonces separate makes the count an upper bound rather than relying on a
favourable grouping of adjacent bytes. -/
inductive CandidateBoundary where
  | c2Root
  | initialClaim
  | semanticSumcheck (round : Fin 10)
  | claimTable
  | batchWork
  | firstOodValue (index : Fin 2)
  | firstRelationMessage
  | foldWork
  | explicitFinal256
  | relationOnlyMessage (round : Fin 3)
  | finalWork
  deriving DecidableEq

def conservativeM0ExcludedTrace : List CandidateBoundary :=
  [.c2Root,
    .initialClaim,
    .semanticSumcheck 0,
    .semanticSumcheck 1,
    .semanticSumcheck 2,
    .semanticSumcheck 3,
    .semanticSumcheck 4,
    .semanticSumcheck 5,
    .semanticSumcheck 6,
    .semanticSumcheck 7,
    .semanticSumcheck 8,
    .semanticSumcheck 9,
    .claimTable,
    .batchWork,
    .firstOodValue 0,
    .firstOodValue 1,
    .firstRelationMessage,
    .foldWork,
    .explicitFinal256,
    .relationOnlyMessage 0,
    .relationOnlyMessage 1,
    .relationOnlyMessage 2,
    .finalWork]

theorem conservative_trace_length :
    conservativeM0ExcludedTrace.length = 23 := by
  decide

theorem conservative_trace_length_le_30 :
    conservativeM0ExcludedTrace.length ≤ 30 := by
  rw [conservative_trace_length]
  omega

/-- If every genuine public-coin IOP round is injectively assigned to one of
the conservative post-`m0` response boundaries, then the V6 profile has at
most 30 BCS rounds. The required semantic assignment is intentionally an
input: counting serialized objects alone does not prove BCS applicability. -/
theorem genuine_round_count_le_30_of_boundary_embedding
    {Round : Type*} [Fintype Round]
    (roundBoundary : Round ↪ Fin conservativeM0ExcludedTrace.length) :
    Fintype.card Round ≤ 30 := by
  calc
    Fintype.card Round ≤
        Fintype.card (Fin conservativeM0ExcludedTrace.length) :=
      Fintype.card_le_of_injective roundBoundary roundBoundary.injective
    _ = conservativeM0ExcludedTrace.length := Fintype.card_fin _
    _ ≤ 30 := conservative_trace_length_le_30

/-- The compact-query retry hashes are not silently counted as BCS IOP
rounds. They must instead be included in the Fiat--Shamir/random-oracle query
budget of the eventual implementation theorem. -/
def compactSamplerCandidateDrawCap : Nat := selectorCount * 8

theorem exact_compact_sampler_candidate_draw_cap :
    compactSamplerCandidateDrawCap = 24 := by
  norm_num [compactSamplerCandidateDrawCap, selectorCount]

/-! ## Compact-topology arithmetic certificate -/

/-- Counts emitted by the companion exact integer DP for 16-element subsets
of the `2^18` fibre universe. The DP-to-Merkle-frontier correspondence remains
an implementation/proof obligation; the theorem below checks the large-integer
ratio once these counts are supplied. -/
def screenedCompactSubsetCount : Nat :=
  9084139170249583238735014329323684800278941387709235066992254215845298176

def allSixteenSubsetsCount : Nat :=
  23758572837246225120935263320500846372979925468707821836403823401582444544

noncomputable def screenedCompactProbability : Real :=
  screenedCompactSubsetCount / allSixteenSubsetsCount

theorem screened_compact_probability_ge_three_eighths :
    (3 : Real) / 8 ≤ screenedCompactProbability := by
  norm_num [screenedCompactProbability, screenedCompactSubsetCount,
    allSixteenSubsetsCount]

/-! ## Deliberate external theorem boundary -/

/-- Exact protocol-level conclusion still required from the published
one-round circle/RS reduction. Keeping it as data prevents the finite
parameter audit above from being mistaken for the missing soundness theorem.

An implementation theorem must instantiate this interface with the actual
received words, transcript challenges, compact-query sampler, and failure
events. -/
structure PublishedOneFoldReduction (K : Type*) [Field K] where
  initialCandidate : InitialCoefficients K
  finalCandidate : FinalCoefficients K
  foldChallenge : K
  foldEquality :
    finalCandidate = coefficientFoldLayer 256 foldChallenge initialCandidate

/-! ## Audit -/

#print axioms exact_dimensions
#print axioms exact_initial_multiplicity
#print axioms exact_output_multiplicity
#print axioms initial_list_card_lt_101
#print axioms output_list_card_lt_100
#print axioms one_circle_fold_ends_in_explicit_final256
#print axioms released_compatible_body_margin
#print axioms selected_hiding_does_not_fit_30_kib
#print axioms selected_hiding_fits_40_kib
#print axioms selected_hiding_upload_count
#print axioms selected_hiding_largest_frontier_below_30_kib
#print axioms genuine_round_count_le_30_of_boundary_embedding
#print axioms screened_compact_probability_ge_three_eighths

end AspisV6OneFoldParameterAudit
