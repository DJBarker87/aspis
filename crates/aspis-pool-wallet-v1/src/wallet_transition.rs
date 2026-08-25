//! Local-only note/nullifier preparation and finalized output delivery.
//!
//! Spending/nullifier keys enter only borrowed derivation functions. They are
//! decoded into zeroized temporaries, are never retained by a plan, and are
//! never accepted by an encryption or serialization API. Proof generation is
//! deliberately external to this host wallet slice.

use aspis_core::field::{M31, P};
use aspis_pool::{PrivateTransferStatementV1, TransitionReceiptV1, WithdrawalStatementV1};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        pool_v1_nullifier, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind, POOL_V1_LEAF_CAPACITY,
    },
};
use hpke::rand_core::CryptoRng;
use subtle::ConstantTimeEq;

use crate::{
    encrypt_note_v1, pool_transport::TransitionOutputRoleV1, recompute_note_commitment_v1,
    NoteContextV1, NoteOpeningV1, PoolV1WalletError, ViewingPublicKeyV1,
    POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalletTransitionErrorV1 {
    InvalidContext,
    InvalidNullifierKey,
    SpendingKeyMismatch,
    AssetMismatch,
    ValueConservation,
    InvalidReceipt,
    WrongOutputRole,
    Wallet(PoolV1WalletError),
}

impl From<PoolV1WalletError> for WalletTransitionErrorV1 {
    fn from(error: PoolV1WalletError) -> Self {
        Self::Wallet(error)
    }
}

/// Public retained-anchor and verifier-release inputs. No secret key or proof
/// byte is carried here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendContextV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub asset_id: u32,
    pub anchor_sequence: u64,
    pub anchor_root: [u8; 32],
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
}

impl SpendContextV1 {
    pub fn validate(&self) -> Result<(), WalletTransitionErrorV1> {
        if self.pool == [0; 32]
            || self.deployment_domain == [0; 32]
            || self.asset_id >= P
            || self.anchor_sequence > POOL_V1_LEAF_CAPACITY
            || decode_digest_canonical(&self.anchor_root).is_err()
            || self.verifier_profile == [0; 32]
            || self.verifier_release == [0; 32]
        {
            Err(WalletTransitionErrorV1::InvalidContext)
        } else {
            Ok(())
        }
    }
}

pub struct PreparedPrivateTransferV1 {
    pub envelope: HistoricalAnchorEnvelopeV1,
    pub statement: PrivateTransferStatementV1,
    pub recipient_note: NoteOpeningV1,
    pub change_note: NoteOpeningV1,
}

impl core::fmt::Debug for PreparedPrivateTransferV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("PreparedPrivateTransferV1([PUBLIC STATEMENT], [REDACTED NOTES])")
    }
}

pub struct PreparedWithdrawalV1 {
    pub envelope: HistoricalAnchorEnvelopeV1,
    pub statement: WithdrawalStatementV1,
    pub change_note: NoteOpeningV1,
}

impl core::fmt::Debug for PreparedWithdrawalV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str("PreparedWithdrawalV1([PUBLIC STATEMENT], [REDACTED NOTE])")
    }
}

/// Derive the frozen public nullifier after explicitly matching the input
/// opening to a locally held spending/nullifier key.
pub fn derive_note_nullifier_v1(
    input_note: &NoteOpeningV1,
    nullifier_key_bytes: &[u8; 32],
) -> Result<[u8; 32], WalletTransitionErrorV1> {
    let mut nullifier_key = decode_digest_canonical(nullifier_key_bytes)
        .map_err(|_| WalletTransitionErrorV1::InvalidNullifierKey)?;
    let mut expected_owner = derive_owner_key(&nullifier_key);
    let expected_owner_bytes = encode_digest_canonical(&expected_owner);
    if !bool::from(expected_owner_bytes.ct_eq(input_note.owner_key())) {
        nullifier_key.fill(M31(0));
        expected_owner.fill(M31(0));
        return Err(WalletTransitionErrorV1::SpendingKeyMismatch);
    }
    let mut salt = decode_digest_canonical(input_note.salt())
        .map_err(|_| WalletTransitionErrorV1::InvalidContext)?;
    let nullifier = pool_v1_nullifier(&nullifier_key, &salt);
    nullifier_key.fill(M31(0));
    expected_owner.fill(M31(0));
    salt.fill(M31(0));
    Ok(encode_digest_canonical(&nullifier))
}

/// Match one locally held opening to the public nullifier in an already
/// authenticated finalized transition receipt. The caller must obtain the
/// receipt from `finalized_indexer`; this helper does not authenticate RPC.
pub fn finalized_receipt_spends_note_v1(
    input_note: &NoteOpeningV1,
    nullifier_key_bytes: &[u8; 32],
    receipt: &TransitionReceiptV1,
) -> Result<bool, WalletTransitionErrorV1> {
    let expected = derive_note_nullifier_v1(input_note, nullifier_key_bytes)?;
    let observed = encode_digest_canonical(&receipt.nullifier);
    Ok(bool::from(expected.ct_eq(&observed)))
}

fn envelope_v1(
    context: SpendContextV1,
    kind: PoolV1TransitionKind,
    nullifier: aspis_statement::Digest,
) -> HistoricalAnchorEnvelopeV1 {
    HistoricalAnchorEnvelopeV1 {
        transition_kind: kind,
        pool: context.pool,
        deployment_domain: context.deployment_domain,
        anchor_sequence: context.anchor_sequence,
        anchor_root: decode_digest_canonical(&context.anchor_root).unwrap(),
        nullifier,
        verifier_profile: context.verifier_profile,
        verifier_release: context.verifier_release,
    }
}

pub fn prepare_private_transfer_v1(
    context: SpendContextV1,
    input_note: &NoteOpeningV1,
    nullifier_key: &[u8; 32],
    recipient_note: NoteOpeningV1,
    change_note: NoteOpeningV1,
) -> Result<PreparedPrivateTransferV1, WalletTransitionErrorV1> {
    context.validate()?;
    if input_note.asset_id() != context.asset_id
        || recipient_note.asset_id() != context.asset_id
        || change_note.asset_id() != context.asset_id
    {
        return Err(WalletTransitionErrorV1::AssetMismatch);
    }
    let output_value = recipient_note
        .value()
        .checked_add(change_note.value())
        .ok_or(WalletTransitionErrorV1::ValueConservation)?;
    if output_value != input_note.value() {
        return Err(WalletTransitionErrorV1::ValueConservation);
    }
    let nullifier = decode_digest_canonical(&derive_note_nullifier_v1(input_note, nullifier_key)?)
        .map_err(|_| WalletTransitionErrorV1::InvalidNullifierKey)?;
    let recipient_commitment =
        decode_digest_canonical(&recompute_note_commitment_v1(&recipient_note)?)
            .map_err(|_| WalletTransitionErrorV1::InvalidContext)?;
    let change_commitment = decode_digest_canonical(&recompute_note_commitment_v1(&change_note)?)
        .map_err(|_| WalletTransitionErrorV1::InvalidContext)?;
    let envelope = envelope_v1(context, PoolV1TransitionKind::PrivateTransfer, nullifier);
    Ok(PreparedPrivateTransferV1 {
        statement: PrivateTransferStatementV1 {
            pool: context.pool,
            deployment_domain: context.deployment_domain,
            anchor_sequence: context.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier,
            asset_id: M31(context.asset_id),
            recipient_commitment,
            change_commitment,
        },
        envelope,
        recipient_note,
        change_note,
    })
}

pub fn prepare_withdrawal_v1(
    context: SpendContextV1,
    input_note: &NoteOpeningV1,
    nullifier_key: &[u8; 32],
    amount: u32,
    destination_token_account: [u8; 32],
    change_note: NoteOpeningV1,
) -> Result<PreparedWithdrawalV1, WalletTransitionErrorV1> {
    context.validate()?;
    if amount == 0 || amount >= aspis_statement::VALUE_LIMIT || destination_token_account == [0; 32]
    {
        return Err(WalletTransitionErrorV1::ValueConservation);
    }
    if input_note.asset_id() != context.asset_id || change_note.asset_id() != context.asset_id {
        return Err(WalletTransitionErrorV1::AssetMismatch);
    }
    if amount.checked_add(change_note.value()) != Some(input_note.value()) {
        return Err(WalletTransitionErrorV1::ValueConservation);
    }
    let nullifier = decode_digest_canonical(&derive_note_nullifier_v1(input_note, nullifier_key)?)
        .map_err(|_| WalletTransitionErrorV1::InvalidNullifierKey)?;
    let change_commitment = decode_digest_canonical(&recompute_note_commitment_v1(&change_note)?)
        .map_err(|_| WalletTransitionErrorV1::InvalidContext)?;
    let envelope = envelope_v1(context, PoolV1TransitionKind::Withdrawal, nullifier);
    Ok(PreparedWithdrawalV1 {
        statement: WithdrawalStatementV1 {
            pool: context.pool,
            deployment_domain: context.deployment_domain,
            anchor_sequence: context.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier,
            asset_id: M31(context.asset_id),
            amount,
            destination_token_account,
            change_commitment,
        },
        envelope,
        change_note,
    })
}

/// Build the exact HPKE context for a finalized transition output. This is the
/// explicit reconciliation point for recipient/change notes prepared before
/// submission: leaf indices are trusted only after authenticated ASTR/root
/// ingestion.
pub fn finalized_transition_note_context_v1(
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    receipt: &TransitionReceiptV1,
    role: TransitionOutputRoleV1,
) -> Result<NoteContextV1, WalletTransitionErrorV1> {
    if receipt.pool != pool {
        return Err(WalletTransitionErrorV1::InvalidReceipt);
    }
    let (leaf_index, commitment) = match (receipt.transition_kind, role) {
        (PoolV1TransitionKind::PrivateTransfer, TransitionOutputRoleV1::Recipient) => (
            receipt.first_leaf_index,
            encode_digest_canonical(&receipt.first_output),
        ),
        (PoolV1TransitionKind::PrivateTransfer, TransitionOutputRoleV1::Change) => (
            receipt.second_leaf_index,
            receipt.second_output_or_destination,
        ),
        (PoolV1TransitionKind::Withdrawal, TransitionOutputRoleV1::Change) => (
            receipt.first_leaf_index,
            encode_digest_canonical(&receipt.first_output),
        ),
        _ => return Err(WalletTransitionErrorV1::WrongOutputRole),
    };
    if (receipt.transition_kind == PoolV1TransitionKind::PrivateTransfer
        && (receipt.second_leaf_index != receipt.first_leaf_index.saturating_add(1)
            || receipt.root_sequence != receipt.second_leaf_index.saturating_add(1)))
        || (receipt.transition_kind == PoolV1TransitionKind::Withdrawal
            && (receipt.second_leaf_index != 0
                || receipt.root_sequence != receipt.first_leaf_index.saturating_add(1)))
    {
        return Err(WalletTransitionErrorV1::InvalidReceipt);
    }
    NoteContextV1::new(pool, deployment_domain, leaf_index, commitment)
        .map_err(WalletTransitionErrorV1::Wallet)
}

pub fn encrypt_finalized_transition_note_v1(
    csprng: &mut impl CryptoRng,
    recipient: &ViewingPublicKeyV1,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    receipt: &TransitionReceiptV1,
    role: TransitionOutputRoleV1,
    note: &NoteOpeningV1,
) -> Result<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES], WalletTransitionErrorV1> {
    let context = finalized_transition_note_context_v1(pool, deployment_domain, receipt, role)?;
    encrypt_note_v1(csprng, recipient, &context, note).map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transaction_builder::{
        build_private_transfer_instruction_v1, VerifierRouteAccountsV1,
    };
    use solana_program::pubkey::Pubkey;

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn note(owner: aspis_statement::Digest, value: u32, salt: u32) -> NoteOpeningV1 {
        NoteOpeningV1::new(
            encode_digest_canonical(&owner),
            value,
            9,
            encode_digest_canonical(&digest(salt)),
        )
        .unwrap()
    }

    #[test]
    fn local_nullifier_and_change_plan_conserve_value_without_serializing_secret_key() {
        let nullifier_key = digest(100);
        let nullifier_key_bytes = encode_digest_canonical(&nullifier_key);
        let input = note(derive_owner_key(&nullifier_key), 77, 200);
        let recipient = note(digest(300), 30, 400);
        let change = note(digest(500), 47, 600);
        let context = SpendContextV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            asset_id: 9,
            anchor_sequence: 7,
            anchor_root: encode_digest_canonical(&digest(700)),
            verifier_profile: [3; 32],
            verifier_release: [4; 32],
        };
        let prepared =
            prepare_private_transfer_v1(context, &input, &nullifier_key_bytes, recipient, change)
                .unwrap();
        let finalized_receipt = TransitionReceiptV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: prepared.statement.pool,
            nullifier: prepared.statement.nullifier,
            first_output: prepared.statement.recipient_commitment,
            second_output_or_destination: encode_digest_canonical(
                &prepared.statement.change_commitment,
            ),
            withdrawal_amount: 0,
            first_leaf_index: 7,
            second_leaf_index: 8,
            root_sequence: 9,
            root: digest(800),
        };
        assert!(
            finalized_receipt_spends_note_v1(&input, &nullifier_key_bytes, &finalized_receipt,)
                .unwrap()
        );
        let instruction = build_private_transfer_instruction_v1(
            Pubkey::new_from_array([9; 32]),
            7,
            &prepared.envelope,
            &prepared.statement,
            VerifierRouteAccountsV1 {
                payer: Pubkey::new_from_array([10; 32]),
                registry_program: Pubkey::new_from_array([11; 32]),
                verifier_program: Pubkey::new_from_array([12; 32]),
                sealed_proof_account: Pubkey::new_from_array([13; 32]),
            },
        )
        .unwrap();
        assert!(!instruction
            .data
            .windows(nullifier_key_bytes.len())
            .any(|window| window == nullifier_key_bytes));
        assert!(!format!("{prepared:?}").contains(&format!("{:?}", nullifier_key_bytes)));
        assert_eq!(
            prepared.recipient_note.value() + prepared.change_note.value(),
            77
        );
    }

    #[test]
    fn wrong_local_key_and_bad_change_are_rejected() {
        let nullifier_key = digest(100);
        let input = note(derive_owner_key(&nullifier_key), 77, 200);
        let context = SpendContextV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            asset_id: 9,
            anchor_sequence: 7,
            anchor_root: encode_digest_canonical(&digest(700)),
            verifier_profile: [3; 32],
            verifier_release: [4; 32],
        };
        assert_eq!(
            derive_note_nullifier_v1(&input, &encode_digest_canonical(&digest(101))),
            Err(WalletTransitionErrorV1::SpendingKeyMismatch)
        );
        assert_eq!(
            prepare_withdrawal_v1(
                context,
                &input,
                &encode_digest_canonical(&nullifier_key),
                30,
                [9; 32],
                note(digest(500), 48, 600),
            )
            .err(),
            Some(WalletTransitionErrorV1::ValueConservation)
        );
    }
}
