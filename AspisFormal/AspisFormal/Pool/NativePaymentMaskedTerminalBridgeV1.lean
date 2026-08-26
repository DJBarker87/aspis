import AspisFormal.Pool.NativePaymentRandomizedExtractionV1
import AspisFormal.V5AcceptedSumcheckSourceBridge

/-!
# Native Pool V1 masked-terminal bridge

This module connects the accepted ten-round masked sumcheck boundary to the
exact aggregate consumed by `NativePaymentRandomizedExtractionV1`.

The Boolean restriction of the production native Tag-73 terminal is modeled
literally as

`eq(r, row) * thetaBatch(row) + mu * H1(row)
  + mu^2 * (1 - copyActive(row)) * H1(row)`.

Its masked form is `mask(row) + eta * real(row)`, matching
`state_only_selected_mask_value + eta * original` in Rust.  The kernel proves
the Boolean sum identity, cancellation of the precommitted mask for nonzero
`eta`, and construction of `NativeAcceptedRandomizedTerminal`.

No accepted-oracle conclusion is assumed.  The strongest deterministic
theorem returns four alternatives: the desired native aggregate, a mask-sum
authentication failure, a fixed terminal-opening authentication failure, or
a ten-round degree-27 repair event.  Ruling out/bounding the last three is the
remaining source/PCS/Fiat--Shamir boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.NativePaymentMaskedTerminalBridgeV1

open Module
open AspisPool.NativePaymentRandomizedExtractionV1
open AspisSumcheckMasking
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5SumcheckTranscriptBinding

/-! ## Exact production dimensions and order -/

def nativeTerminalRows : Nat := 1024
def nativeTerminalC1Columns : Nat := 16
def nativeTerminalMaskOnlyC1Columns : Nat := 10
def nativeTerminalHelperColumns : Nat := 2
def nativeTerminalSelectedColumns : Nat := 28
def nativeTerminalPoints : Nat := 3
def nativeTerminalSelectedClaims : Nat := 84
def nativeTerminalSumcheckRounds : Nat := 10
def nativeTerminalRoundDegree : Nat := 27
def nativeTerminalRoundCoefficients : Nat := 28
def nativeTerminalQm31Bytes : Nat := 16
def nativeTerminalRoundMessageBytes : Nat := 448
def nativeTerminalFixedHeapAllocations : Nat := 1
def nativeTerminalSelectorHeapBytes : Nat := 1280
def nativePrivateTransferCopyLinks : Nat := 78
def nativeWithdrawalCopyLinks : Nat := 75
def nativeCopyPatterns : Nat := 13

/-- FNV fingerprints of the two checked-in `[u16; 64]` active-row mask
tables in `payment_semantic_terminal_constants.rs`.  The fingerprints are
audit pins; identifying a Rust table with the `copyActive` function below
remains an explicit source-refinement obligation. -/
def nativePrivateTransferActiveRowsFingerprint : Nat :=
  0xe858c4c0d4e22b94

def nativeWithdrawalActiveRowsFingerprint : Nat :=
  0xe9de6f8fae7f1793

theorem native_masked_terminal_layout_pinned :
    nativeTerminalRows = nativeBooleanRows ∧
    nativeTerminalC1Columns = 16 ∧
    nativeTerminalMaskOnlyC1Columns = 10 ∧
    nativeTerminalHelperColumns = 2 ∧
    nativeTerminalSelectedColumns = nativeTerminalC1Columns +
      nativeTerminalMaskOnlyC1Columns + nativeTerminalHelperColumns ∧
    nativeTerminalPoints = 3 ∧
    nativeTerminalSelectedClaims = nativeTerminalPoints *
      nativeTerminalSelectedColumns ∧
    nativeTerminalSumcheckRounds = nativeZerocheckCoordinates ∧
    nativeTerminalRoundDegree = 27 ∧
    nativeTerminalRoundCoefficients = nativeTerminalRoundDegree + 1 ∧
    nativeTerminalQm31Bytes = 16 ∧
    nativeTerminalRoundMessageBytes = nativeTerminalRoundCoefficients *
      nativeTerminalQm31Bytes ∧
    nativeTerminalFixedHeapAllocations = 1 ∧
    nativeTerminalSelectorHeapBytes = 1280 ∧
    nativePoseidonPackedLanes = 4 ∧ nativeSemanticPackedLanes = 24 ∧
    nativeCopyLanes = 1 ∧ nativeThetaWidth = 29 ∧
    nativeThetaDegree = 28 ∧ nativeMuDegree = 2 ∧
    nativePrivateTransferCopyLinks = 78 ∧
    nativeWithdrawalCopyLinks = 75 ∧ nativeCopyPatterns = 13 := by
  decide

/-! ## Exact Boolean restriction of the strengthened terminal -/

noncomputable def nativeTotalHelperSum
    {K : Type*} [Field K] (helper : Fin 1024 → K) : K :=
  tableSum helper

/-- The exact Boolean sum of `(1 - copy_active) * H1`.  At production Boolean
rows `copyActive` is the multilinear opening of the compiled active-row mask,
so it is zero or one.  The sum identity itself does not need to assume that
fact. -/
noncomputable def nativeInactiveHelperSum
    {K : Type*} [Field K]
    (copyActive helper : Fin 1024 → K) : K :=
  tableSum fun row => (1 - copyActive row) * helper row

/-- Boolean restriction of
`evaluate_pool_v1_*_selected_unmasked_terminal_compiled_tag73_v1`.

The 29-lane order inside `nativeThetaConstraintTable` is Poseidon powers
0--3, semantic powers 4--27, then Copy LogUp power 28. -/
noncomputable def nativeStrengthenedUnmaskedTerminalTable
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (copyActive helper : Fin 1024 → K) : Fin 1024 → K := fun row =>
  nativeMleRowWeight zerocheckPoint row *
      nativeThetaConstraintTable basis rows theta row +
    mu * helper row +
    mu ^ 2 * (1 - copyActive row) * helper row

/-- Summing the literal native Boolean terminal yields exactly the aggregate
consumed by `NativePaymentRandomizedExtractionV1`. -/
theorem tableSum_nativeStrengthenedUnmaskedTerminalTable
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (copyActive helper : Fin 1024 → K) :
    tableSum (nativeStrengthenedUnmaskedTerminalTable basis rows theta
      zerocheckPoint mu copyActive helper) =
      nativeConstraintMLE basis rows theta zerocheckPoint +
        mu * nativeTotalHelperSum helper +
        mu ^ 2 * nativeInactiveHelperSum copyActive helper := by
  classical
  simp only [tableSum, nativeStrengthenedUnmaskedTerminalTable,
    nativeConstraintMLE, nativeTotalHelperSum, nativeInactiveHelperSum,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]

/-- An extracted nonzero-eta masked boundary for the exact native table forces
the exact randomized-terminal aggregate equation. -/
theorem native_accepted_randomized_terminal_of_masked_boundary
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu eta : K)
    (copyActive helper mask : Fin 1024 → K)
    (boundary : ExtractedMaskedSumcheckBoundary eta
      (nativeStrengthenedUnmaskedTerminalTable basis rows theta
        zerocheckPoint mu copyActive helper) mask) :
    NativeAcceptedRandomizedTerminal basis rows theta zerocheckPoint mu
      (nativeTotalHelperSum helper)
      (nativeInactiveHelperSum copyActive helper) := by
  have sumZero : tableSum
      (nativeStrengthenedUnmaskedTerminalTable basis rows theta
        zerocheckPoint mu copyActive helper) = 0 :=
    original_sum_eq_zero_of_mixed_sum eta
      (nativeStrengthenedUnmaskedTerminalTable basis rows theta
        zerocheckPoint mu copyActive helper) mask boundary.etaNonzero
      boundary.boundary
  rw [tableSum_nativeStrengthenedUnmaskedTerminalTable] at sumZero
  exact sumZero

/-! ## Accepted ten-round wire and named authentication boundaries -/

variable {K : Type*} [Field K]
variable {Public Root : Type*}
variable {scheme : FiatShamirSchedule Public Root K}

/-- Raw authentication equalities needed above the accepted mathematical
wire.  These are the exact PCS/source obligations: the initial claim opens to
the fixed mask sum and the returned terminal claim opens to the reference
trace of the fixed masked native table.  No aggregate equation is a field of
this record. -/
structure NativeMaskedTerminalAuthentication
    (wire : AcceptedProductionTenRoundWire scheme)
    (real mask : Fin 1024 → K) where
  honest : FixedOracleTenRoundTrace
    (maskedOracle wire.transcript.eta real mask) wire.transcript.point
  maskInitialAuthenticated : wire.initialClaim = tableSum mask
  terminalOpeningAuthenticated : wire.terminalClaim =
    claimAtStep (tableSum (maskedOracle wire.transcript.eta real mask))
      honest.messages wire.transcript.point (Fin.last 10)

/-- Accepted native wire plus exact claim/opening authentication implies the
aggregate outside the separately named ten-round repair event.  A Fiat--Shamir
or ROM argument is needed only to bound that event; it is not hidden in the
authentication record. -/
theorem native_accepted_randomized_terminal_of_authenticated_wire
    {F : Type*} [Field F] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (copyActive helper mask : Fin 1024 → K)
    (wire : AcceptedProductionTenRoundWire scheme)
    (authentication : NativeMaskedTerminalAuthentication wire
      (nativeStrengthenedUnmaskedTerminalTable basis rows theta
        zerocheckPoint mu copyActive helper) mask)
    (outsideRepair : ¬ TenRoundRepair wire authentication.honest) :
    NativeAcceptedRandomizedTerminal basis rows theta zerocheckPoint mu
      (nativeTotalHelperSum helper)
      (nativeInactiveHelperSum copyActive helper) := by
  apply native_accepted_randomized_terminal_of_masked_boundary basis rows
    theta zerocheckPoint mu wire.transcript.eta copyActive helper mask
  exact accepted_wire_implies_extracted_masked_boundary wire
    wire.transcript.eta
    (nativeStrengthenedUnmaskedTerminalTable basis rows theta
      zerocheckPoint mu copyActive helper) mask {
      etaMatches := rfl
      honest := authentication.honest
      maskInitialAuthenticated := authentication.maskInitialAuthenticated
      terminalAuthenticated := authentication.terminalOpeningAuthenticated
      outsideRepair := outsideRepair
    }

/-- With only a fixed-oracle reference trace, every missing premise remains a
named alternative.  This is the deterministic production boundary: either
the exact native aggregate holds, or the mask claim is unauthenticated, or the
fixed terminal opening is unauthenticated, or a degree-27 repair occurred in
one of the ten rounds. -/
theorem native_aggregate_or_three_named_failures
    {F : Type*} [Field F] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (rows : Fin 1024 → NativeConstraintRowResiduals F K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K)
    (copyActive helper mask : Fin 1024 → K)
    (wire : AcceptedProductionTenRoundWire scheme)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle wire.transcript.eta
        (nativeStrengthenedUnmaskedTerminalTable basis rows theta
          zerocheckPoint mu copyActive helper) mask)
      wire.transcript.point) :
    NativeAcceptedRandomizedTerminal basis rows theta zerocheckPoint mu
        (nativeTotalHelperSum helper)
        (nativeInactiveHelperSum copyActive helper) ∨
      MaskInitialClaimAuthenticationFailure wire mask ∨
      FixedTerminalOpeningAuthenticationFailure wire honest ∨
      TenRoundRepair wire honest := by
  rcases accepted_wire_boundary_or_three_named_failures wire
      wire.transcript.eta
      (nativeStrengthenedUnmaskedTerminalTable basis rows theta
        zerocheckPoint mu copyActive helper) mask rfl honest with
    boundary | maskFailure | terminalFailure | repair
  · exact Or.inl (native_accepted_randomized_terminal_of_masked_boundary
      basis rows theta zerocheckPoint mu wire.transcript.eta copyActive helper
      mask boundary)
  · exact Or.inr (Or.inl maskFailure)
  · exact Or.inr (Or.inr (Or.inl terminalFailure))
  · exact Or.inr (Or.inr (Or.inr repair))

#print axioms native_masked_terminal_layout_pinned
#print axioms tableSum_nativeStrengthenedUnmaskedTerminalTable
#print axioms native_accepted_randomized_terminal_of_masked_boundary
#print axioms native_accepted_randomized_terminal_of_authenticated_wire
#print axioms native_aggregate_or_three_named_failures

end AspisPool.NativePaymentMaskedTerminalBridgeV1
