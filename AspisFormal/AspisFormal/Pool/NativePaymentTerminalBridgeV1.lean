import AspisFormal.Pool.PaymentRelationV1

/-!
# Native Pool V1 Tag-73 payment terminal bridge

This module pins the production native-payment geometry and proves the
deterministic last step from extracted semantic/copy/Poseidon row facts to
`PaymentRelationV1`.  It intentionally does not identify a randomized Tag-73
terminal equality with all of those row facts: that preceding extraction step
still needs its theta, zerocheck, mu and LogUp collision hypotheses.

The value proof is not an application-level range assumption.  Each source is
copied to the exact value auxiliary row, where it is reconstructed from thirty
Boolean cells.  `Nat.ofBits_lt_two_pow` then yields the production `2^30`
bound.  Conservation is likewise derived through the exact rows 870 and 871.
-/

set_option autoImplicit false

namespace AspisPool.NativePaymentTerminalBridgeV1

open AspisPool.PaymentRelationV1
open AspisPool.DepositV1

/-! ## Production Rust constants -/

def traceRows : Nat := 1024
def c1Columns : Nat := 16
def permutationBlocks : Nat := 49
def blockRows : Nat := 16
def twoRoundRowsPerBlock : Nat := 11
def permutationRows : Nat := 784
def pathLevels : Nat := 20
def valueCount : Nat := 3
def valueBits : Nat := 30
def directionRowStart : Nat := 784
def valueAuxRowStart : Nat := 864
def auxiliaryRowEnd : Nat := 879

def initialLanes : Nat := 16
def absorptionZeroLanes : Nat := 16
def merkleLanes : Nat := 17
def directRangeLanes : Nat := 33
def valueLanes : Nat := 2
def publicDigestLanes : Nat := 8
def publicScalarLanes : Nat := 2
def sourceSemanticLanes : Nat := 94
def packedSemanticLanes : Nat := 24
def copyLanes : Nat := 1
def randomizedSemanticLanes : Nat := 25
def poseidonLanes : Nat := 4
def thetaLanes : Nat := 29
def thetaCollisionDegree : Nat := 28
def semanticOracleDegree : Nat := 21
def semanticZerocheckDegree : Nat := 22
def maskedTerminalDegree : Nat := 27
def muAggregateDegree : Nat := 2
def muCollisionRootBound : Nat := 2

def selectedTerminalColumns : Nat := 28
def selectedTerminalPoints : Nat := 3
def selectedTerminalClaims : Nat := 84
def copyPatternCount : Nat := 13
def privateTransferCopyLinks : Nat := 78
def withdrawalCopyLinks : Nat := 75
def auxiliaryUsedColumnMasks : Nat := 96

def tag73RequestBytes : Nat := 600
def tag73FixedGrammarBytes : Nat := 9936
def tag73RootBytes : Nat := 52
def tag73WorkBytes : Nat := 24
def tag73QueryCount : Nat := 16
def tag73QueryBytes : Nat := 621
def tag73MinimumFrontierNodes : Nat := 14
def tag73FrontierCount : Nat := 2
def tag73ProductionFrontierNodes : Nat := 203
def tag73FrontierNodeBytes : Nat := 26
def tag73ProofBodyWithoutFrontiers : Nat := 19948
def tag73ProductionProofBodyBytes : Nat := 30504

def nativeProfileBindingPreimage : String :=
  "aspis:pool-v1:verifier-profile:tag73-native-payment-v1:asvq-v1"

def nativeProfileBinding : List Nat :=
  [0x70, 0xa7, 0x85, 0xea, 0x72, 0x34, 0x69, 0xa1,
   0x34, 0x97, 0x40, 0x71, 0x62, 0xff, 0x01, 0xb5,
   0x5b, 0x33, 0x26, 0x87, 0xfd, 0x9d, 0x0a, 0x8c,
   0x89, 0xb8, 0x12, 0x59, 0xb2, 0xd1, 0x96, 0x3d]

def nativeReleaseBindingPreimage : String :=
  "aspis:v7:pool-v1-payment:26c1-3c2:b10:q16:digest208:cap203:full-c2:work35-31-34:release-v1"

def nativeReleaseBinding : List Nat :=
  [0x9a, 0x29, 0x16, 0xf7, 0x65, 0x7b, 0x7b, 0x85,
   0xa3, 0x51, 0x2d, 0x85, 0xd5, 0xa0, 0x58, 0x9c,
   0x19, 0xe7, 0x55, 0xca, 0x5e, 0x60, 0xd9, 0x10,
   0x71, 0xb8, 0x0c, 0x2a, 0xf6, 0x2d, 0x0d, 0xff]

theorem production_geometry_pinned :
    traceRows = 1024 ∧ c1Columns = 16 ∧ permutationBlocks = 49 ∧
    blockRows = 16 ∧ twoRoundRowsPerBlock = 11 ∧
    permutationRows = 784 ∧ pathLevels = 20 ∧ valueCount = 3 ∧
    valueBits = 30 ∧ directionRowStart = 784 ∧ valueAuxRowStart = 864 ∧
    auxiliaryRowEnd = 879 := by
  decide

theorem production_terminal_lanes_pinned :
    initialLanes = 16 ∧ absorptionZeroLanes = 16 ∧ merkleLanes = 17 ∧
    directRangeLanes = 33 ∧ valueLanes = 2 ∧ publicDigestLanes = 8 ∧
    publicScalarLanes = 2 ∧
    sourceSemanticLanes = initialLanes + absorptionZeroLanes + merkleLanes +
      directRangeLanes + valueLanes + publicDigestLanes + publicScalarLanes ∧
    sourceSemanticLanes = 94 ∧ packedSemanticLanes = 24 ∧
    copyLanes = 1 ∧ randomizedSemanticLanes = 25 ∧
    poseidonLanes = 4 ∧ thetaLanes = 29 ∧ thetaCollisionDegree = 28 ∧
    semanticOracleDegree = 21 ∧ semanticZerocheckDegree = 22 ∧
    maskedTerminalDegree = 27 ∧ muAggregateDegree = 2 ∧
    muCollisionRootBound = 2 ∧ selectedTerminalColumns = 28 ∧
    selectedTerminalPoints = 3 ∧ selectedTerminalClaims = 84 := by
  decide

theorem production_registry_cardinalities_pinned :
    copyPatternCount = 13 ∧ privateTransferCopyLinks = 78 ∧
    withdrawalCopyLinks = 75 ∧ auxiliaryUsedColumnMasks = 96 := by
  decide

theorem production_tag73_wire_pinned :
    tag73RequestBytes = 600 ∧ tag73FixedGrammarBytes = 9936 ∧
    tag73RootBytes = 52 ∧ tag73WorkBytes = 24 ∧
    tag73QueryCount = 16 ∧ tag73QueryBytes = 621 ∧
    tag73MinimumFrontierNodes = 14 ∧ tag73FrontierCount = 2 ∧
    tag73ProductionFrontierNodes = 203 ∧
    tag73FrontierNodeBytes = 26 ∧ tag73ProofBodyWithoutFrontiers = 19948 ∧
    tag73ProductionProofBodyBytes =
      tag73ProofBodyWithoutFrontiers +
        2 * tag73ProductionFrontierNodes * tag73FrontierNodeBytes := by
  decide

theorem native_profile_binding_length : nativeProfileBinding.length = 32 := by
  decide

theorem native_release_binding_length : nativeReleaseBinding.length = 32 := by
  decide

/-! ## Exact value and conservation cells -/

structure CellAddress where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def inputValueCell : CellAddress := ⟨44, 0⟩
def inputAssetCell : CellAddress := ⟨44, 1⟩
def recipientValueCell : CellAddress := ⟨444, 0⟩
def recipientAssetCell : CellAddress := ⟨444, 1⟩
def changeValueCell : CellAddress := ⟨492, 0⟩
def changeAssetCell : CellAddress := ⟨492, 1⟩

def valueSourceCells : Fin 3 → CellAddress
  | ⟨0, _⟩ => inputValueCell
  | ⟨1, _⟩ => recipientValueCell
  | ⟨2, _⟩ => changeValueCell

def valueAuxBaseRows : Fin 3 → Nat
  | ⟨0, _⟩ => 864
  | ⟨1, _⟩ => 866
  | ⟨2, _⟩ => 868

def valueAuxSourceCell (which : Fin 3) : CellAddress :=
  ⟨valueAuxBaseRows which, 10⟩

def valueBitCell (which : Fin 3) (bit : Fin 30) : CellAddress :=
  let base := valueAuxBaseRows which
  let row := if bit.val < 10 then base else if bit.val < 20 then base + 1 else base ^^^ 12
  ⟨row, bit.val % 10⟩

def conservationInputCell : CellAddress := ⟨870, 0⟩
def conservationRecipientOrAmountCell : CellAddress := ⟨870, 1⟩
def conservationPartialCell : CellAddress := ⟨870, 2⟩
def conservationCarriedPartialCell : CellAddress := ⟨871, 0⟩
def conservationChangeCell : CellAddress := ⟨871, 1⟩

def ownerDigestRow : Nat := 11
def inputDigestRow : Nat := 59
def anchorDigestRow : Nat := 379
def nullifierDigestRow : Nat := 411
def recipientDigestRow : Nat := 459
def changeDigestRow : Nat := 507

theorem production_source_cells_pinned :
    inputValueCell = ⟨44, 0⟩ ∧ inputAssetCell = ⟨44, 1⟩ ∧
    recipientValueCell = ⟨444, 0⟩ ∧ recipientAssetCell = ⟨444, 1⟩ ∧
    changeValueCell = ⟨492, 0⟩ ∧ changeAssetCell = ⟨492, 1⟩ := by
  decide

theorem production_auxiliary_rows_pinned :
    valueAuxBaseRows 0 = 864 ∧ valueAuxBaseRows 1 = 866 ∧
    valueAuxBaseRows 2 = 868 ∧
    valueBitCell 0 ⟨20, by omega⟩ = ⟨876, 0⟩ ∧
    valueBitCell 1 ⟨20, by omega⟩ = ⟨878, 0⟩ ∧
    valueBitCell 2 ⟨20, by omega⟩ = ⟨872, 0⟩ ∧
    conservationInputCell = ⟨870, 0⟩ ∧
    conservationRecipientOrAmountCell = ⟨870, 1⟩ ∧
    conservationPartialCell = ⟨870, 2⟩ ∧
    conservationCarriedPartialCell = ⟨871, 0⟩ ∧
    conservationChangeCell = ⟨871, 1⟩ := by
  decide

theorem production_public_digest_rows_pinned :
    ownerDigestRow = 11 ∧ inputDigestRow = 59 ∧ anchorDigestRow = 379 ∧
    nullifierDigestRow = 411 ∧
    recipientDigestRow = 459 ∧ changeDigestRow = 507 := by
  decide

/-! ## Extracted deterministic row facts -/

/-- A typed projection of the native trace after field values have been
decoded to their application types.  The `natCell` map retains the production
row addresses; the other fields name outputs of the exact Poseidon blocks. -/
structure TraceProjection
    (Key Salt Asset Path Owner Root Digest : Type) where
  natCell : CellAddress → Nat
  decodedBits : Fin 3 → Fin 30 → Bool
  inputNullifierKey : Key
  inputSalt : Salt
  inputAsset : Asset
  inputPath : Path
  derivedOwner : Owner
  inputLeaf : Digest
  computedAnchor : Root
  computedNullifier : Digest
  recipientOwner : Owner
  recipientSalt : Salt
  recipientAsset : Asset
  computedRecipient : Digest
  changeOwner : Owner
  changeSalt : Salt
  changeAsset : Asset
  computedChange : Digest

def sourceValue
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (which : Fin 3) : Nat :=
  trace.natCell (valueSourceCells which)

def auxiliaryValue
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (which : Fin 3) : Nat :=
  trace.natCell (valueAuxSourceCell which)

def reconstructedValue
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (which : Fin 3) : Nat :=
  Nat.ofBits (trace.decodedBits which)

/-- Exact Boolean-cell decoding and column-ten reconstruction facts produced
by the three direct-range views at `z`, `succ(z)` and `xor12(z)`. -/
def ValueRowsAccepted
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  (∀ which bit,
    trace.natCell (valueBitCell which bit) =
      (trace.decodedBits which bit).toNat) ∧
  (∀ which, auxiliaryValue trace which = reconstructedValue trace which)

/-- Exact copy links shared by both variants, plus the two row-local
conservation residuals at rows 870 and 871. -/
def CommonValueCopyAndConservation
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  sourceValue trace 0 = auxiliaryValue trace 0 ∧
  sourceValue trace 2 = auxiliaryValue trace 2 ∧
  auxiliaryValue trace 0 = trace.natCell conservationInputCell ∧
  auxiliaryValue trace 1 = trace.natCell conservationRecipientOrAmountCell ∧
  auxiliaryValue trace 2 = trace.natCell conservationChangeCell ∧
  trace.natCell conservationInputCell =
    trace.natCell conservationRecipientOrAmountCell +
      trace.natCell conservationPartialCell ∧
  trace.natCell conservationPartialCell =
    trace.natCell conservationCarriedPartialCell ∧
  trace.natCell conservationCarriedPartialCell =
    trace.natCell conservationChangeCell

def PrivateTransferValueCopy
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  sourceValue trace 1 = auxiliaryValue trace 1

def WithdrawalAmountBinding
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  auxiliaryValue trace 1 = statement.amount ∧ 0 < statement.amount

/-- Granular common Poseidon/copy/public-row facts.  These correspond to the
owner-key, input-note, path, nullifier and public digest/scalar row families;
they are deliberately not packaged as a `Valid*` conclusion. -/
def CommonHashRowsAccepted
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (common : CommonPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  trace.derivedOwner = primitives.ownerKey trace.inputNullifierKey ∧
  trace.inputLeaf = primitives.noteCommitment trace.derivedOwner
    (sourceValue trace 0) trace.inputAsset trace.inputSalt ∧
  trace.computedAnchor = primitives.merkleRoot trace.inputLeaf trace.inputPath ∧
  trace.computedAnchor = common.anchorRoot ∧
  trace.computedNullifier =
    primitives.nullifier trace.inputNullifierKey trace.inputSalt ∧
  trace.computedNullifier = common.nullifier ∧
  trace.inputAsset = common.asset

def PrivateTransferOutputHashRowsAccepted
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  trace.computedRecipient = primitives.noteCommitment trace.recipientOwner
    (sourceValue trace 1) trace.recipientAsset trace.recipientSalt ∧
  trace.computedRecipient = statement.firstOutputCommitment ∧
  trace.recipientAsset = statement.common.asset ∧
  trace.computedChange = primitives.noteCommitment trace.changeOwner
    (sourceValue trace 2) trace.changeAsset trace.changeSalt ∧
  trace.computedChange = statement.secondOutputCommitment ∧
  trace.changeAsset = statement.common.asset

def WithdrawalOutputHashRowsAccepted
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) : Prop :=
  trace.computedChange = primitives.noteCommitment trace.changeOwner
    (sourceValue trace 2) trace.changeAsset trace.changeSalt ∧
  trace.computedChange = statement.changeCommitment ∧
  trace.changeAsset = statement.common.asset

def privateTransferWitnessOfTrace
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) :
    PrivateTransferWitness Key Salt Asset Path Owner :=
  { input := {
      nullifierKey := trace.inputNullifierKey
      inputSalt := trace.inputSalt
      inputAsset := trace.inputAsset
      inputValue := sourceValue trace 0
      path := trace.inputPath }
    firstOutput := {
      owner := trace.recipientOwner
      value := sourceValue trace 1
      asset := trace.recipientAsset
      salt := trace.recipientSalt }
    secondOutput := {
      owner := trace.changeOwner
      value := sourceValue trace 2
      asset := trace.changeAsset
      salt := trace.changeSalt } }

def withdrawalWitnessOfTrace
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest) :
    WithdrawalWitness Key Salt Asset Path Owner :=
  { input := {
      nullifierKey := trace.inputNullifierKey
      inputSalt := trace.inputSalt
      inputAsset := trace.inputAsset
      inputValue := sourceValue trace 0
      path := trace.inputPath }
    change := {
      owner := trace.changeOwner
      value := sourceValue trace 2
      asset := trace.changeAsset
      salt := trace.changeSalt } }

theorem auxiliary_value_lt_valueLimit
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (rows : ValueRowsAccepted trace) (which : Fin 3) :
    auxiliaryValue trace which < valueLimit := by
  rw [rows.2 which]
  exact Nat.ofBits_lt_two_pow (trace.decodedBits which)

theorem private_transfer_value_rows_imply_bounds_and_conservation
    {Key Salt Asset Path Owner Root Digest : Type}
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (rows : ValueRowsAccepted trace)
    (common : CommonValueCopyAndConservation trace)
    (transfer : PrivateTransferValueCopy trace) :
    sourceValue trace 0 < valueLimit ∧
    sourceValue trace 1 < valueLimit ∧
    sourceValue trace 2 < valueLimit ∧
    sourceValue trace 0 = sourceValue trace 1 + sourceValue trace 2 := by
  rcases common with ⟨inputSource, changeSource, inputCopy, recipientCopy,
    changeCopy, firstConservation, partialCopy, secondConservation⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inputSource]
    exact auxiliary_value_lt_valueLimit trace rows 0
  · rw [transfer]
    exact auxiliary_value_lt_valueLimit trace rows 1
  · rw [changeSource]
    exact auxiliary_value_lt_valueLimit trace rows 2
  · calc
      sourceValue trace 0 = auxiliaryValue trace 0 := inputSource
      _ = trace.natCell conservationInputCell := inputCopy
      _ = trace.natCell conservationRecipientOrAmountCell +
          trace.natCell conservationPartialCell := firstConservation
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationPartialCell := by rw [recipientCopy]
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationCarriedPartialCell := by rw [partialCopy]
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationChangeCell := by rw [secondConservation]
      _ = auxiliaryValue trace 1 + auxiliaryValue trace 2 := by rw [changeCopy]
      _ = sourceValue trace 1 + sourceValue trace 2 := by rw [transfer, changeSource]

theorem withdrawal_value_rows_imply_bounds_and_conservation
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (rows : ValueRowsAccepted trace)
    (common : CommonValueCopyAndConservation trace)
    (withdrawal : WithdrawalAmountBinding statement trace) :
    sourceValue trace 0 < valueLimit ∧
    sourceValue trace 2 < valueLimit ∧
    0 < statement.amount ∧ statement.amount < valueLimit ∧
    sourceValue trace 0 = sourceValue trace 2 + statement.amount := by
  rcases common with ⟨inputSource, changeSource, inputCopy, amountCopy,
    changeCopy, firstConservation, partialCopy, secondConservation⟩
  rcases withdrawal with ⟨amountBinding, amountPositive⟩
  refine ⟨?_, ?_, amountPositive, ?_, ?_⟩
  · rw [inputSource]
    exact auxiliary_value_lt_valueLimit trace rows 0
  · rw [changeSource]
    exact auxiliary_value_lt_valueLimit trace rows 2
  · rw [← amountBinding]
    exact auxiliary_value_lt_valueLimit trace rows 1
  · calc
      sourceValue trace 0 = auxiliaryValue trace 0 := inputSource
      _ = trace.natCell conservationInputCell := inputCopy
      _ = trace.natCell conservationRecipientOrAmountCell +
          trace.natCell conservationPartialCell := firstConservation
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationPartialCell := by rw [amountCopy]
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationCarriedPartialCell := by rw [partialCopy]
      _ = auxiliaryValue trace 1 +
          trace.natCell conservationChangeCell := by rw [secondConservation]
      _ = auxiliaryValue trace 1 + auxiliaryValue trace 2 := by rw [changeCopy]
      _ = statement.amount + sourceValue trace 2 := by rw [amountBinding, changeSource]
      _ = sourceValue trace 2 + statement.amount := Nat.add_comm _ _

theorem native_private_transfer_semantic_rows_imply_valid
    {Pool Domain Root Digest Asset Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : PrivateTransferPublic Pool Domain Root Digest Asset)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (valueRows : ValueRowsAccepted trace)
    (valueCopies : CommonValueCopyAndConservation trace)
    (transferCopy : PrivateTransferValueCopy trace)
    (commonHashes : CommonHashRowsAccepted primitives statement.common trace)
    (outputHashes : PrivateTransferOutputHashRowsAccepted primitives statement trace) :
    ValidPrivateTransfer primitives statement (privateTransferWitnessOfTrace trace) := by
  rcases private_transfer_value_rows_imply_bounds_and_conservation
    trace valueRows valueCopies transferCopy with
    ⟨inputBound, recipientBound, changeBound, conservation⟩
  rcases commonHashes with ⟨ownerHash, inputHash, anchorHash, anchorPublic,
    nullifierHash, nullifierPublic, inputAssetPublic⟩
  rcases outputHashes with ⟨recipientHash, recipientPublic, recipientAssetPublic,
    changeHash, changePublic, changeAssetPublic⟩
  refine ⟨inputBound, recipientBound, changeBound, inputAssetPublic,
    recipientAssetPublic, changeAssetPublic, ?_, ?_, ?_, ?_, conservation⟩
  · have anchorEquation :
        primitives.merkleRoot
          (primitives.noteCommitment
            (primitives.ownerKey trace.inputNullifierKey)
            (sourceValue trace 0) trace.inputAsset trace.inputSalt)
          trace.inputPath = statement.common.anchorRoot := by
        rw [← ownerHash, ← inputHash, ← anchorHash]
        exact anchorPublic
    simpa [privateTransferWitnessOfTrace] using anchorEquation
  · exact nullifierHash.symm.trans nullifierPublic
  · exact recipientHash.symm.trans recipientPublic
  · exact changeHash.symm.trans changePublic

theorem native_withdrawal_semantic_rows_imply_valid
    {Pool Domain Root Digest Asset Destination Key Salt Path Owner : Type}
    [DecidableEq Root] [DecidableEq Digest] [DecidableEq Asset]
    (primitives : Primitives Key Salt Asset Path Owner Root Digest)
    (statement : WithdrawalPublic Pool Domain Root Digest Asset Destination)
    (trace : TraceProjection Key Salt Asset Path Owner Root Digest)
    (valueRows : ValueRowsAccepted trace)
    (valueCopies : CommonValueCopyAndConservation trace)
    (amountBinding : WithdrawalAmountBinding statement trace)
    (commonHashes : CommonHashRowsAccepted primitives statement.common trace)
    (outputHashes : WithdrawalOutputHashRowsAccepted primitives statement trace) :
    ValidWithdrawal primitives statement (withdrawalWitnessOfTrace trace) := by
  rcases withdrawal_value_rows_imply_bounds_and_conservation
    statement trace valueRows valueCopies amountBinding with
    ⟨inputBound, changeBound, amountPositive, amountBound, conservation⟩
  rcases commonHashes with ⟨ownerHash, inputHash, anchorHash, anchorPublic,
    nullifierHash, nullifierPublic, inputAssetPublic⟩
  rcases outputHashes with ⟨changeHash, changePublic, changeAssetPublic⟩
  refine ⟨inputBound, changeBound, amountPositive, amountBound,
    inputAssetPublic, changeAssetPublic, ?_, ?_, ?_, conservation⟩
  · have anchorEquation :
        primitives.merkleRoot
          (primitives.noteCommitment
            (primitives.ownerKey trace.inputNullifierKey)
            (sourceValue trace 0) trace.inputAsset trace.inputSalt)
          trace.inputPath = statement.common.anchorRoot := by
        rw [← ownerHash, ← inputHash, ← anchorHash]
        exact anchorPublic
    simpa [withdrawalWitnessOfTrace] using anchorEquation
  · exact nullifierHash.symm.trans nullifierPublic
  · exact changeHash.symm.trans changePublic

#print axioms auxiliary_value_lt_valueLimit
#print axioms private_transfer_value_rows_imply_bounds_and_conservation
#print axioms withdrawal_value_rows_imply_bounds_and_conservation
#print axioms native_private_transfer_semantic_rows_imply_valid
#print axioms native_withdrawal_semantic_rows_imply_valid

end AspisPool.NativePaymentTerminalBridgeV1
