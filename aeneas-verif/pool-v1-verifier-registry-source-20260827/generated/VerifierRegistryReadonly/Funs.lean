/-
Focused normalization of the exact Aeneas translation of
`aspis_pool::registry::require_readonly_registry_account` from
`VerifierRegistryProduction.llbc`.  The function body below is unchanged from
the translator output.  Pure external Rust representations are made
transparent so that no source-equality axiom is introduced.
-/
import Aeneas.Std
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace VerifierRegistryReadonlyGenerated

noncomputable section

local instance {T : Type} : DecidableEq T := Classical.decEq T

abbrev solana_pubkey.Pubkey := Array Std.U8 32#usize
abbrev core.cell.RefCell (T : Type) := T
abbrev alloc.rc.Rc (T : Type) := T

structure solana_account_info.AccountInfo where
  key : solana_pubkey.Pubkey
  lamports : alloc.rc.Rc (core.cell.RefCell Std.U64)
  data : alloc.rc.Rc (core.cell.RefCell (Slice Std.U8))
  owner : solana_pubkey.Pubkey
  rent_epoch : Std.U64
  is_signer : Bool
  is_writable : Bool
  executable : Bool

inductive solana_program_error.ProgramError where
  | Custom : Std.U32 → solana_program_error.ProgramError

@[discriminant u32 [1095966721,1095966722,1095966723,1095966724,
  1095966725,1095966726,1095966727,1095966728,1095966729,1095966730,
  1095966731,1095966732,1095966733,1095966734,1095966735,1095966736,
  1095966737,1095966738,1095966739,1095966740,1095966741,1095966742,
  1095966743,1095966744,1095966745,1095966746,1095966747,1095966748,
  1095966749,1095966750,1095966751,1095966752,1095966753,1095966754,
  1095966755,1095966756,1095966757,1095966758,1095966759,1095966760,
  1095966761,1095966762,1095966763,1095966764,1095966765,1095966766,
  1095966767,1095966768,1095966769,1095966770,1095966771,1095966772,
  1095966773,1095966774]]
inductive error.PoolV1ProgramError where
  | InvalidAccountType
  | InvalidRootPageAddress
  | StateHistoryMismatch
  | TreeFull
  | InsufficientTreeCapacity
  | UnexpectedRootPage
  | NonCanonicalLeaf
  | ArithmeticOverflow
  | InvalidPoolStateAddress
  | InvalidVerifierRegistryAddress
  | InvalidVerifierEntryAddress
  | InvalidVerifierRegistry
  | InvalidVerifierEntry
  | VerifierRegistryPaused
  | VerifierEntryInactive
  | VerifierEntryNotActiveYet
  | VerifierEntryRetired
  | VerifierSelectionMismatch
  | InvalidTokenProgram
  | InvalidMint
  | InvalidTokenAccount
  | InvalidVaultAuthority
  | InvalidVaultTokenAddress
  | InvalidDepositAmount
  | InsufficientDepositFunds
  | UnsupportedTokenConfiguration
  | InvalidEncryptedNotePayload
  | TokenBalanceDeltaMismatch
  | InvalidSourceAuthority
  | InvalidHistoricalAnchorEnvelope
  | HistoricalAnchorIdentityMismatch
  | HistoricalAnchorSelectionMismatch
  | HistoricalAnchorInFuture
  | InvalidHistoricalAnchorPage
  | HistoricalAnchorRootMismatch
  | InvalidNullifierMarkerAddress
  | InvalidNullifierMarkerAccount
  | NullifierAlreadyConsumed
  | InvalidVerifierProgramAccount
  | InvalidVerifierProofAccount
  | VerifierProofBindingMismatch
  | InvalidVerifierDispatchEnvelope
  | VerifierDispatchIdentityMismatch
  | InvalidVerifierReturnProgram
  | InvalidVerifierReturnData
  | VerifierResultBindingMismatch
  | MissingVerifierReturnData
  | InvalidWithdrawalAmount
  | InsufficientVaultFunds
  | InvalidDestinationTokenAccount
  | InvalidSystemProgram
  | InvalidPayer
  | InvalidFreshAccount
  | CpiInvocationForbidden

def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
    (left right : solana_pubkey.Pubkey) : Result Bool :=
  ok (if left = right then true else false)

@[reducible]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey :
    core.cmp.PartialEq solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
  ne := core.cmp.PartialEq.ne.trait_default
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
}

def solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from
    (sourceError : error.PoolV1ProgramError) :
    Result solana_program_error.ProgramError :=
  ok (.Custom (read_discriminant sourceError))

@[reducible]
def solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError :
    core.convert.From solana_program_error.ProgramError error.PoolV1ProgramError := {
  «from» :=
    solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from
}

/- The following definition is the literal Aeneas function body generated
from `programs/aspis-pool/src/registry.rs:99-112`. -/
def registry.require_readonly_registry_account
    (account : solana_account_info.AccountInfo)
    (registry_program : solana_pubkey.Pubkey)
    (invalid : error.PoolV1ProgramError) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.owner
      registry_program
  if b then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        invalid
    ok (core.result.Result.Err pe)
  else if account.executable then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        invalid
    ok (core.result.Result.Err pe)
  else if account.is_writable then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        invalid
    ok (core.result.Result.Err pe)
  else if account.is_signer then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        invalid
    ok (core.result.Result.Err pe)
  else
    ok (core.result.Result.Ok ())

end

end VerifierRegistryReadonlyGenerated
