//! Executable Pool V1 private-transfer and withdrawal relations.
//!
//! This module is a no-proof semantic foundation.  It deliberately does not
//! claim that either relation has been compiled into the frozen Tag-73 trace,
//! terminal oracle, transcript, or verifier.  The public encodings are the
//! exact 216-byte `ASCP` and `ASWP` payloads consumed by `aspis-pool`.
//!
//! Pool V1 is fee-free.  Its canonical custody fee is zero and is not a
//! caller-selectable statement field.  `ASCP` keeps bytes 148..152 zero while
//! `ASWP` uses those bytes for the withdrawal amount.  A nonzero in-note fee
//! therefore requires a future statement/profile version.

use aspis_core::field::{M31, P};

use crate::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical, poseidon2::Digest,
    VALUE_LIMIT,
};

use super::{
    format::{pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent},
    historical_anchor::{
        validate_historical_anchor_envelope_v1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
    },
    POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_LEAF_CAPACITY, POOL_V1_TREE_DEPTH,
};

pub const POOL_V1_PAYMENT_STATEMENT_BYTES: usize = 216;
pub const POOL_V1_PAYMENT_STATEMENT_VERSION: u8 = 1;
pub const POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC: [u8; 4] = *b"ASCP";
pub const POOL_V1_WITHDRAWAL_STATEMENT_MAGIC: [u8; 4] = *b"ASWP";
/// Pool V1 has no caller-selectable in-note fee.
pub const POOL_V1_CANONICAL_FEE: u32 = 0;

const POOL_OFFSET: usize = 8;
const DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const ANCHOR_SEQUENCE_OFFSET: usize = 72;
const ANCHOR_ROOT_OFFSET: usize = 80;
const NULLIFIER_OFFSET: usize = 112;
const ASSET_ID_OFFSET: usize = 144;
const AMOUNT_OR_RESERVED_OFFSET: usize = 148;
const FIRST_OUTPUT_OR_DESTINATION_OFFSET: usize = 152;
const SECOND_OUTPUT_OFFSET: usize = 184;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PrivateTransferPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub recipient_commitment: Digest,
    pub change_commitment: Digest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1WithdrawalPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub amount: u32,
    pub destination_token_account: [u8; 32],
    pub change_commitment: Digest,
}

/// One exact depth-20 membership path in the Pool V1 Poseidon tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1MembershipWitnessV1 {
    pub siblings: [Digest; POOL_V1_TREE_DEPTH],
    pub index: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1InputNoteWitnessV1 {
    pub nullifier_key: Digest,
    pub salt: Digest,
    pub value: u32,
    pub membership: PoolV1MembershipWitnessV1,
}

/// A future-spendable Pool V1 note preimage.  `owner_key` uses the frozen
/// owner-key address surface; the commitment itself uses the ordinary note
/// domain, never the retired output-only domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1OutputNoteWitnessV1 {
    pub owner_key: Digest,
    pub salt: Digest,
    pub value: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PrivateTransferWitnessV1 {
    pub input: PoolV1InputNoteWitnessV1,
    pub recipient: PoolV1OutputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1WithdrawalWitnessV1 {
    pub input: PoolV1InputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentRuntimeBindingV1 {
    /// These values must come from the authenticated Pool identity and retained
    /// root page, not from the untrusted statement being checked.
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub asset_id: M31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentRelationContextV1<'a> {
    pub runtime_binding: PoolV1PaymentRuntimeBindingV1,
    /// The program enforces freshness with a canonical marker PDA.  Keeping
    /// the set explicit here makes replay rejection executable in the oracle.
    pub spent_nullifiers: &'a [Digest],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentStatementFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    ZeroRequiredBinding,
    InvalidAnchorSequence,
    NonCanonicalDigest,
    NonCanonicalAssetId,
    InvalidWithdrawalAmount,
    InvalidDestination,
    InvalidEnvelope,
    EnvelopeMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentRelationError {
    InvalidStatement(PoolV1PaymentStatementFormatError),
    NonCanonicalWitnessDigest,
    PathIndexOutOfRange,
    InputValueOutOfRange,
    RecipientValueOutOfRange,
    ChangeValueOutOfRange,
    ConservationOverflow,
    ConservationMismatch,
    AnchorMismatch,
    NullifierMismatch,
    RecipientCommitmentMismatch,
    ChangeCommitmentMismatch,
    NullifierAlreadySpent,
    PoolBindingMismatch,
    DeploymentDomainMismatch,
    AnchorSequenceBindingMismatch,
    AnchorRootBindingMismatch,
    AssetBindingMismatch,
}

#[derive(Clone, Copy)]
struct CommonPublicV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    asset_id: M31,
}

#[inline]
fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

fn validate_common(common: CommonPublicV1) -> Result<(), PoolV1PaymentStatementFormatError> {
    if common.pool == [0u8; 32] || common.deployment_domain == [0u8; 32] {
        return Err(PoolV1PaymentStatementFormatError::ZeroRequiredBinding);
    }
    if common.anchor_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1PaymentStatementFormatError::InvalidAnchorSequence);
    }
    if !digest_is_canonical(&common.anchor_root) || !digest_is_canonical(&common.nullifier) {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest);
    }
    if common.asset_id.0 >= P {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId);
    }
    Ok(())
}

fn transfer_common(public: &PoolV1PrivateTransferPublicV1) -> CommonPublicV1 {
    CommonPublicV1 {
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor_sequence: public.anchor_sequence,
        anchor_root: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
    }
}

fn withdrawal_common(public: &PoolV1WithdrawalPublicV1) -> CommonPublicV1 {
    CommonPublicV1 {
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor_sequence: public.anchor_sequence,
        anchor_root: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
    }
}

pub fn validate_pool_v1_private_transfer_public_v1(
    public: &PoolV1PrivateTransferPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_common(transfer_common(public))?;
    if !digest_is_canonical(&public.recipient_commitment)
        || !digest_is_canonical(&public.change_commitment)
    {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest);
    }
    Ok(())
}

pub fn validate_pool_v1_withdrawal_public_v1(
    public: &PoolV1WithdrawalPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_common(withdrawal_common(public))?;
    if public.amount == 0 || public.amount >= VALUE_LIMIT {
        return Err(PoolV1PaymentStatementFormatError::InvalidWithdrawalAmount);
    }
    if public.destination_token_account == [0u8; 32] {
        return Err(PoolV1PaymentStatementFormatError::InvalidDestination);
    }
    if !digest_is_canonical(&public.change_commitment) {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest);
    }
    Ok(())
}

fn encode_common(
    output: &mut [u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
    magic: [u8; 4],
    kind: PoolV1TransitionKind,
    common: CommonPublicV1,
) {
    output[..4].copy_from_slice(&magic);
    output[4] = POOL_V1_PAYMENT_STATEMENT_VERSION;
    output[5] = kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&common.pool);
    output[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]
        .copy_from_slice(&common.deployment_domain);
    output[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET]
        .copy_from_slice(&common.anchor_sequence.to_le_bytes());
    output[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.anchor_root));
    output[NULLIFIER_OFFSET..ASSET_ID_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.nullifier));
    output[ASSET_ID_OFFSET..AMOUNT_OR_RESERVED_OFFSET]
        .copy_from_slice(&common.asset_id.to_le_bytes());
}

pub fn encode_pool_v1_private_transfer_public_v1(
    public: &PoolV1PrivateTransferPublicV1,
) -> Result<[u8; POOL_V1_PAYMENT_STATEMENT_BYTES], PoolV1PaymentStatementFormatError> {
    validate_pool_v1_private_transfer_public_v1(public)?;
    let mut output = [0u8; POOL_V1_PAYMENT_STATEMENT_BYTES];
    encode_common(
        &mut output,
        POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
        PoolV1TransitionKind::PrivateTransfer,
        transfer_common(public),
    );
    // Bytes 148..152 remain the canonical zero fee/reserved word.
    debug_assert_eq!(
        output[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET],
        POOL_V1_CANONICAL_FEE.to_le_bytes()
    );
    output[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&public.recipient_commitment));
    output[SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&encode_digest_canonical(&public.change_commitment));
    Ok(output)
}

pub fn encode_pool_v1_withdrawal_public_v1(
    public: &PoolV1WithdrawalPublicV1,
) -> Result<[u8; POOL_V1_PAYMENT_STATEMENT_BYTES], PoolV1PaymentStatementFormatError> {
    validate_pool_v1_withdrawal_public_v1(public)?;
    let mut output = [0u8; POOL_V1_PAYMENT_STATEMENT_BYTES];
    encode_common(
        &mut output,
        POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
        PoolV1TransitionKind::Withdrawal,
        withdrawal_common(public),
    );
    output[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET]
        .copy_from_slice(&public.amount.to_le_bytes());
    output[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&public.destination_token_account);
    output[SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&encode_digest_canonical(&public.change_commitment));
    Ok(output)
}

fn require_header(
    bytes: &[u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
    magic: [u8; 4],
    kind: PoolV1TransitionKind,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    if bytes[..4] != magic {
        return Err(PoolV1PaymentStatementFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAYMENT_STATEMENT_VERSION {
        return Err(PoolV1PaymentStatementFormatError::WrongVersion);
    }
    if bytes[5] != kind as u8 {
        return Err(PoolV1PaymentStatementFormatError::WrongTransitionKind);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PaymentStatementFormatError::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolV1PaymentStatementFormatError::NonZeroReserved);
    }
    Ok(())
}

fn decode_common(
    bytes: &[u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
) -> Result<CommonPublicV1, PoolV1PaymentStatementFormatError> {
    let asset = u32::from_le_bytes(
        bytes[ASSET_ID_OFFSET..AMOUNT_OR_RESERVED_OFFSET]
            .try_into()
            .unwrap(),
    );
    if asset >= P {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId);
    }
    let common = CommonPublicV1 {
        pool: bytes[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET]
            .try_into()
            .unwrap(),
        deployment_domain: bytes[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
        anchor_sequence: u64::from_le_bytes(
            bytes[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        anchor_root: decode_digest_canonical(
            bytes[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET]
                .try_into()
                .unwrap(),
        )
        .map_err(|_| PoolV1PaymentStatementFormatError::NonCanonicalDigest)?,
        nullifier: decode_digest_canonical(
            bytes[NULLIFIER_OFFSET..ASSET_ID_OFFSET].try_into().unwrap(),
        )
        .map_err(|_| PoolV1PaymentStatementFormatError::NonCanonicalDigest)?,
        asset_id: M31(asset),
    };
    validate_common(common)?;
    Ok(common)
}

pub fn decode_pool_v1_private_transfer_public_v1(
    bytes: &[u8],
) -> Result<PoolV1PrivateTransferPublicV1, PoolV1PaymentStatementFormatError> {
    let bytes: &[u8; POOL_V1_PAYMENT_STATEMENT_BYTES] = bytes
        .try_into()
        .map_err(|_| PoolV1PaymentStatementFormatError::WrongLength)?;
    require_header(
        bytes,
        POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
        PoolV1TransitionKind::PrivateTransfer,
    )?;
    if bytes[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET]
        != POOL_V1_CANONICAL_FEE.to_le_bytes()
    {
        return Err(PoolV1PaymentStatementFormatError::NonZeroReserved);
    }
    let common = decode_common(bytes)?;
    let public = PoolV1PrivateTransferPublicV1 {
        pool: common.pool,
        deployment_domain: common.deployment_domain,
        anchor_sequence: common.anchor_sequence,
        anchor_root: common.anchor_root,
        nullifier: common.nullifier,
        asset_id: common.asset_id,
        recipient_commitment: decode_digest_canonical(
            bytes[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
                .try_into()
                .unwrap(),
        )
        .map_err(|_| PoolV1PaymentStatementFormatError::NonCanonicalDigest)?,
        change_commitment: decode_digest_canonical(
            bytes[SECOND_OUTPUT_OFFSET..].try_into().unwrap(),
        )
        .map_err(|_| PoolV1PaymentStatementFormatError::NonCanonicalDigest)?,
    };
    validate_pool_v1_private_transfer_public_v1(&public)?;
    Ok(public)
}

pub fn decode_pool_v1_withdrawal_public_v1(
    bytes: &[u8],
) -> Result<PoolV1WithdrawalPublicV1, PoolV1PaymentStatementFormatError> {
    let bytes: &[u8; POOL_V1_PAYMENT_STATEMENT_BYTES] = bytes
        .try_into()
        .map_err(|_| PoolV1PaymentStatementFormatError::WrongLength)?;
    require_header(
        bytes,
        POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
        PoolV1TransitionKind::Withdrawal,
    )?;
    let common = decode_common(bytes)?;
    let public = PoolV1WithdrawalPublicV1 {
        pool: common.pool,
        deployment_domain: common.deployment_domain,
        anchor_sequence: common.anchor_sequence,
        anchor_root: common.anchor_root,
        nullifier: common.nullifier,
        asset_id: common.asset_id,
        amount: u32::from_le_bytes(
            bytes[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET]
                .try_into()
                .unwrap(),
        ),
        destination_token_account: bytes[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
            .try_into()
            .unwrap(),
        change_commitment: decode_digest_canonical(
            bytes[SECOND_OUTPUT_OFFSET..].try_into().unwrap(),
        )
        .map_err(|_| PoolV1PaymentStatementFormatError::NonCanonicalDigest)?,
    };
    validate_pool_v1_withdrawal_public_v1(&public)?;
    Ok(public)
}

fn validate_envelope_common(
    envelope: &HistoricalAnchorEnvelopeV1,
    kind: PoolV1TransitionKind,
    common: CommonPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_historical_anchor_envelope_v1(envelope)
        .map_err(|_| PoolV1PaymentStatementFormatError::InvalidEnvelope)?;
    if envelope.transition_kind != kind
        || envelope.pool != common.pool
        || envelope.deployment_domain != common.deployment_domain
        || envelope.anchor_sequence != common.anchor_sequence
        || envelope.anchor_root != common.anchor_root
        || envelope.nullifier != common.nullifier
    {
        return Err(PoolV1PaymentStatementFormatError::EnvelopeMismatch);
    }
    Ok(())
}

pub fn validate_pool_v1_private_transfer_envelope_binding_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    public: &PoolV1PrivateTransferPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_pool_v1_private_transfer_public_v1(public)?;
    validate_envelope_common(
        envelope,
        PoolV1TransitionKind::PrivateTransfer,
        transfer_common(public),
    )
}

pub fn validate_pool_v1_withdrawal_envelope_binding_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    public: &PoolV1WithdrawalPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_pool_v1_withdrawal_public_v1(public)?;
    validate_envelope_common(
        envelope,
        PoolV1TransitionKind::Withdrawal,
        withdrawal_common(public),
    )
}

fn witness_digest_is_canonical(input: &PoolV1InputNoteWitnessV1) -> bool {
    digest_is_canonical(&input.nullifier_key)
        && digest_is_canonical(&input.salt)
        && input.membership.siblings.iter().all(digest_is_canonical)
}

fn output_witness_is_canonical(output: &PoolV1OutputNoteWitnessV1) -> bool {
    digest_is_canonical(&output.owner_key) && digest_is_canonical(&output.salt)
}

pub fn pool_v1_membership_root_v1(
    leaf: Digest,
    membership: &PoolV1MembershipWitnessV1,
) -> Result<Digest, PoolV1PaymentRelationError> {
    if u64::from(membership.index) >= POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1PaymentRelationError::PathIndexOutOfRange);
    }
    let mut current = leaf;
    for (level, sibling) in membership.siblings.iter().enumerate() {
        current = if (membership.index >> level) & 1 == 0 {
            pool_v1_tree_parent(&current, sibling)
        } else {
            pool_v1_tree_parent(sibling, &current)
        };
    }
    Ok(current)
}

fn validate_input_and_path(
    input: &PoolV1InputNoteWitnessV1,
) -> Result<(), PoolV1PaymentRelationError> {
    if !witness_digest_is_canonical(input) {
        return Err(PoolV1PaymentRelationError::NonCanonicalWitnessDigest);
    }
    if u64::from(input.membership.index) >= POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1PaymentRelationError::PathIndexOutOfRange);
    }
    if input.value >= VALUE_LIMIT {
        return Err(PoolV1PaymentRelationError::InputValueOutOfRange);
    }
    Ok(())
}

fn validate_common_relation(
    common: CommonPublicV1,
    input: &PoolV1InputNoteWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<(), PoolV1PaymentRelationError> {
    if common.pool != context.runtime_binding.pool {
        return Err(PoolV1PaymentRelationError::PoolBindingMismatch);
    }
    if common.deployment_domain != context.runtime_binding.deployment_domain {
        return Err(PoolV1PaymentRelationError::DeploymentDomainMismatch);
    }
    if common.anchor_sequence != context.runtime_binding.anchor_sequence {
        return Err(PoolV1PaymentRelationError::AnchorSequenceBindingMismatch);
    }
    if common.anchor_root != context.runtime_binding.anchor_root {
        return Err(PoolV1PaymentRelationError::AnchorRootBindingMismatch);
    }
    if common.asset_id != context.runtime_binding.asset_id {
        return Err(PoolV1PaymentRelationError::AssetBindingMismatch);
    }
    let owner_key = derive_owner_key(&input.nullifier_key);
    let leaf = pool_v1_note_commitment(&owner_key, input.value, common.asset_id, &input.salt);
    if pool_v1_membership_root_v1(leaf, &input.membership)? != common.anchor_root {
        return Err(PoolV1PaymentRelationError::AnchorMismatch);
    }
    if pool_v1_nullifier(&input.nullifier_key, &input.salt) != common.nullifier {
        return Err(PoolV1PaymentRelationError::NullifierMismatch);
    }
    if context
        .spent_nullifiers
        .iter()
        .any(|spent| spent == &common.nullifier)
    {
        return Err(PoolV1PaymentRelationError::NullifierAlreadySpent);
    }
    Ok(())
}

pub fn evaluate_pool_v1_private_transfer_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<(), PoolV1PaymentRelationError> {
    validate_pool_v1_private_transfer_public_v1(public)
        .map_err(PoolV1PaymentRelationError::InvalidStatement)?;
    if !output_witness_is_canonical(&witness.recipient)
        || !output_witness_is_canonical(&witness.change)
    {
        return Err(PoolV1PaymentRelationError::NonCanonicalWitnessDigest);
    }
    let outputs = witness
        .recipient
        .value
        .checked_add(witness.change.value)
        .ok_or(PoolV1PaymentRelationError::ConservationOverflow)?;
    validate_input_and_path(&witness.input)?;
    if witness.recipient.value >= VALUE_LIMIT {
        return Err(PoolV1PaymentRelationError::RecipientValueOutOfRange);
    }
    if witness.change.value >= VALUE_LIMIT {
        return Err(PoolV1PaymentRelationError::ChangeValueOutOfRange);
    }
    if outputs != witness.input.value {
        return Err(PoolV1PaymentRelationError::ConservationMismatch);
    }
    validate_common_relation(transfer_common(public), &witness.input, context)?;
    if pool_v1_note_commitment(
        &witness.recipient.owner_key,
        witness.recipient.value,
        public.asset_id,
        &witness.recipient.salt,
    ) != public.recipient_commitment
    {
        return Err(PoolV1PaymentRelationError::RecipientCommitmentMismatch);
    }
    if pool_v1_note_commitment(
        &witness.change.owner_key,
        witness.change.value,
        public.asset_id,
        &witness.change.salt,
    ) != public.change_commitment
    {
        return Err(PoolV1PaymentRelationError::ChangeCommitmentMismatch);
    }
    Ok(())
}

pub fn evaluate_pool_v1_withdrawal_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<(), PoolV1PaymentRelationError> {
    validate_pool_v1_withdrawal_public_v1(public)
        .map_err(PoolV1PaymentRelationError::InvalidStatement)?;
    if !output_witness_is_canonical(&witness.change) {
        return Err(PoolV1PaymentRelationError::NonCanonicalWitnessDigest);
    }
    let accounted = witness
        .change
        .value
        .checked_add(public.amount)
        .ok_or(PoolV1PaymentRelationError::ConservationOverflow)?;
    validate_input_and_path(&witness.input)?;
    if witness.change.value >= VALUE_LIMIT {
        return Err(PoolV1PaymentRelationError::ChangeValueOutOfRange);
    }
    if accounted != witness.input.value {
        return Err(PoolV1PaymentRelationError::ConservationMismatch);
    }
    validate_common_relation(withdrawal_common(public), &witness.input, context)?;
    if pool_v1_note_commitment(
        &witness.change.owner_key,
        witness.change.value,
        public.asset_id,
        &witness.change.salt,
    ) != public.change_commitment
    {
        return Err(PoolV1PaymentRelationError::ChangeCommitmentMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;
    use sha2::{Digest as _, Sha256};

    use super::*;
    use crate::{
        atomic_state_only_trace::atomic_merkle_root_v3,
        pool_v1::verifier_statement_payload_digest_v1, MerklePath,
    };

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn membership() -> PoolV1MembershipWitnessV1 {
        PoolV1MembershipWitnessV1 {
            siblings: core::array::from_fn(|level| digest(1_000 + level as u32 * 100)),
            index: 0x5_4321,
        }
    }

    fn input(value: u32) -> PoolV1InputNoteWitnessV1 {
        PoolV1InputNoteWitnessV1 {
            nullifier_key: digest(10),
            salt: digest(100),
            value,
            membership: membership(),
        }
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn transfer_context<'a>(
        public: &PoolV1PrivateTransferPublicV1,
        spent_nullifiers: &'a [Digest],
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers,
        }
    }

    fn withdrawal_context<'a>(
        public: &PoolV1WithdrawalPublicV1,
        spent_nullifiers: &'a [Digest],
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers,
        }
    }

    fn transfer_fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PrivateTransferWitnessV1,
        HistoricalAnchorEnvelopeV1,
    ) {
        let witness = PoolV1PrivateTransferWitnessV1 {
            input: input(1_000),
            recipient: output(300, 600),
            change: output(500, 400),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let input_leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let anchor_root =
            pool_v1_membership_root_v1(input_leaf, &witness.input.membership).unwrap();
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &witness.recipient.owner_key,
                witness.recipient.value,
                asset_id,
                &witness.recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor_sequence: public.anchor_sequence,
            anchor_root: public.anchor_root,
            nullifier: public.nullifier,
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        };
        (public, witness, envelope)
    }

    fn withdrawal_fixture() -> (
        PoolV1WithdrawalPublicV1,
        PoolV1WithdrawalWitnessV1,
        HistoricalAnchorEnvelopeV1,
    ) {
        let witness = PoolV1WithdrawalWitnessV1 {
            input: input(1_000),
            change: output(700, 750),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let input_leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let anchor_root =
            pool_v1_membership_root_v1(input_leaf, &witness.input.membership).unwrap();
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9u8; 32],
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor_sequence: public.anchor_sequence,
            anchor_root: public.anchor_root,
            nullifier: public.nullifier,
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        };
        (public, witness, envelope)
    }

    #[test]
    fn honest_transfer_and_withdrawal_accept_with_exact_v3_membership() {
        let (transfer, transfer_witness, transfer_envelope) = transfer_fixture();
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &transfer,
                &transfer_witness,
                transfer_context(&transfer, &[])
            ),
            Ok(())
        );
        assert_eq!(
            validate_pool_v1_private_transfer_envelope_binding_v1(&transfer_envelope, &transfer),
            Ok(())
        );

        let (withdrawal, withdrawal_witness, withdrawal_envelope) = withdrawal_fixture();
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(
                &withdrawal,
                &withdrawal_witness,
                withdrawal_context(&withdrawal, &[])
            ),
            Ok(())
        );
        assert_eq!(
            validate_pool_v1_withdrawal_envelope_binding_v1(&withdrawal_envelope, &withdrawal),
            Ok(())
        );

        let input = &transfer_witness.input;
        let owner = derive_owner_key(&input.nullifier_key);
        let leaf = pool_v1_note_commitment(&owner, input.value, transfer.asset_id, &input.salt);
        let legacy_shape = MerklePath {
            siblings: Vec::from(input.membership.siblings),
            index: input.membership.index,
        };
        assert_eq!(
            pool_v1_membership_root_v1(leaf, &input.membership).unwrap(),
            atomic_merkle_root_v3(leaf, &legacy_shape).unwrap()
        );
    }

    #[test]
    fn exact_statement_encodings_roundtrip_and_pin_zero_fee() {
        let (transfer, _, _) = transfer_fixture();
        let transfer_bytes = encode_pool_v1_private_transfer_public_v1(&transfer).unwrap();
        assert_eq!(transfer_bytes.len(), 216);
        assert_eq!(&transfer_bytes[..8], &[b'A', b'S', b'C', b'P', 1, 1, 1, 0]);
        assert_eq!(&transfer_bytes[148..152], &[0u8; 4]);
        assert_eq!(
            decode_pool_v1_private_transfer_public_v1(&transfer_bytes),
            Ok(transfer)
        );

        let (withdrawal, _, _) = withdrawal_fixture();
        let withdrawal_bytes = encode_pool_v1_withdrawal_public_v1(&withdrawal).unwrap();
        assert_eq!(withdrawal_bytes.len(), 216);
        assert_eq!(
            &withdrawal_bytes[..8],
            &[b'A', b'S', b'W', b'P', 1, 2, 1, 0]
        );
        assert_eq!(
            &withdrawal_bytes[148..152],
            &withdrawal.amount.to_le_bytes()
        );
        assert_eq!(
            decode_pool_v1_withdrawal_public_v1(&withdrawal_bytes),
            Ok(withdrawal)
        );

        let mut fee_mutation = transfer_bytes;
        fee_mutation[148] = 1;
        assert_eq!(
            decode_pool_v1_private_transfer_public_v1(&fee_mutation),
            Err(PoolV1PaymentStatementFormatError::NonZeroReserved)
        );
        let mut trailing_fee = withdrawal_bytes.to_vec();
        trailing_fee.extend_from_slice(&1u32.to_le_bytes());
        assert_eq!(
            decode_pool_v1_withdrawal_public_v1(&trailing_fee),
            Err(PoolV1PaymentStatementFormatError::WrongLength)
        );
    }

    #[test]
    fn output_anchor_and_replay_mutations_fail_closed() {
        let (public, witness, _) = transfer_fixture();
        let mut changed = public;
        changed.recipient_commitment[0] = changed.recipient_commitment[0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &changed,
                &witness,
                transfer_context(&public, &[])
            ),
            Err(PoolV1PaymentRelationError::RecipientCommitmentMismatch)
        );

        let mut changed = public;
        changed.change_commitment[0] = changed.change_commitment[0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &changed,
                &witness,
                transfer_context(&public, &[])
            ),
            Err(PoolV1PaymentRelationError::ChangeCommitmentMismatch)
        );

        let mut changed = public;
        changed.anchor_root[0] = changed.anchor_root[0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &changed,
                &witness,
                transfer_context(&public, &[])
            ),
            Err(PoolV1PaymentRelationError::AnchorRootBindingMismatch)
        );

        let mut changed_witness = witness;
        changed_witness.input.membership.siblings[0][0] =
            changed_witness.input.membership.siblings[0][0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &public,
                &changed_witness,
                transfer_context(&public, &[])
            ),
            Err(PoolV1PaymentRelationError::AnchorMismatch)
        );

        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &public,
                &witness,
                transfer_context(&public, &[public.nullifier])
            ),
            Err(PoolV1PaymentRelationError::NullifierAlreadySpent)
        );

        let (withdrawal, withdrawal_witness, _) = withdrawal_fixture();
        let mut changed = withdrawal;
        changed.change_commitment[0] = changed.change_commitment[0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(
                &changed,
                &withdrawal_witness,
                withdrawal_context(&withdrawal, &[])
            ),
            Err(PoolV1PaymentRelationError::ChangeCommitmentMismatch)
        );

        let mut changed = withdrawal;
        changed.amount += 1;
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(
                &changed,
                &withdrawal_witness,
                withdrawal_context(&withdrawal, &[])
            ),
            Err(PoolV1PaymentRelationError::ConservationMismatch)
        );
    }

    #[test]
    fn destination_pool_and_domain_mutations_are_transcript_visible() {
        let (public, witness, _) = withdrawal_fixture();
        let encoded = encode_pool_v1_withdrawal_public_v1(&public).unwrap();
        let digest = verifier_statement_payload_digest_v1(
            POOL_V1_PAYMENT_STATEMENT_VERSION,
            &[3u8; 32],
            &[4u8; 32],
            &encoded,
            sha256,
        )
        .unwrap();

        let changed = PoolV1WithdrawalPublicV1 {
            destination_token_account: [10u8; 32],
            ..public
        };
        // Destination is a public choice checked against the actual token
        // account by the Pool program, not a hidden witness preimage.  The
        // same witness defines a valid relation for a new destination, but a
        // proof for the original destination cannot be replayed because the
        // exact payload and dispatch digest change.
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(&changed, &witness, withdrawal_context(&public, &[])),
            Ok(())
        );
        let changed_bytes = encode_pool_v1_withdrawal_public_v1(&changed).unwrap();
        assert_ne!(changed_bytes, encoded);
        assert_ne!(
            verifier_statement_payload_digest_v1(
                POOL_V1_PAYMENT_STATEMENT_VERSION,
                &[3u8; 32],
                &[4u8; 32],
                &changed_bytes,
                sha256,
            )
            .unwrap(),
            digest
        );

        for (changed, expected) in [
            (
                PoolV1WithdrawalPublicV1 {
                    pool: [11u8; 32],
                    ..public
                },
                PoolV1PaymentRelationError::PoolBindingMismatch,
            ),
            (
                PoolV1WithdrawalPublicV1 {
                    deployment_domain: [12u8; 32],
                    ..public
                },
                PoolV1PaymentRelationError::DeploymentDomainMismatch,
            ),
            (
                PoolV1WithdrawalPublicV1 {
                    anchor_sequence: public.anchor_sequence + 1,
                    ..public
                },
                PoolV1PaymentRelationError::AnchorSequenceBindingMismatch,
            ),
            (
                PoolV1WithdrawalPublicV1 {
                    asset_id: M31(public.asset_id.0 + 1),
                    ..public
                },
                PoolV1PaymentRelationError::AssetBindingMismatch,
            ),
        ] {
            assert_eq!(
                evaluate_pool_v1_withdrawal_v1(
                    &changed,
                    &witness,
                    withdrawal_context(&public, &[])
                ),
                Err(expected)
            );
            let changed_bytes = encode_pool_v1_withdrawal_public_v1(&changed).unwrap();
            assert_ne!(changed_bytes, encoded);
            assert_ne!(
                verifier_statement_payload_digest_v1(
                    POOL_V1_PAYMENT_STATEMENT_VERSION,
                    &[3u8; 32],
                    &[4u8; 32],
                    &changed_bytes,
                    sha256,
                )
                .unwrap(),
                digest
            );
        }
    }

    #[test]
    fn conservation_range_destination_and_overflow_attacks_reject() {
        let (transfer, witness, _) = transfer_fixture();
        let mut changed = witness;
        changed.change.value -= 1;
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &transfer,
                &changed,
                transfer_context(&transfer, &[])
            ),
            Err(PoolV1PaymentRelationError::ConservationMismatch)
        );

        let mut changed = witness;
        changed.recipient.value = u32::MAX;
        changed.change.value = 1;
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &transfer,
                &changed,
                transfer_context(&transfer, &[])
            ),
            Err(PoolV1PaymentRelationError::ConservationOverflow)
        );

        let mut changed = witness;
        changed.input.value = VALUE_LIMIT;
        changed.recipient.value = VALUE_LIMIT - 1;
        changed.change.value = 1;
        assert_eq!(
            evaluate_pool_v1_private_transfer_v1(
                &transfer,
                &changed,
                transfer_context(&transfer, &[])
            ),
            Err(PoolV1PaymentRelationError::InputValueOutOfRange)
        );

        let (withdrawal, withdrawal_witness, _) = withdrawal_fixture();
        let mut changed = withdrawal_witness;
        changed.change.value = u32::MAX;
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(
                &withdrawal,
                &changed,
                withdrawal_context(&withdrawal, &[])
            ),
            Err(PoolV1PaymentRelationError::ConservationOverflow)
        );

        let mut bad_destination = withdrawal;
        bad_destination.destination_token_account = [0u8; 32];
        assert_eq!(
            evaluate_pool_v1_withdrawal_v1(
                &bad_destination,
                &withdrawal_witness,
                withdrawal_context(&withdrawal, &[])
            ),
            Err(PoolV1PaymentRelationError::InvalidStatement(
                PoolV1PaymentStatementFormatError::InvalidDestination
            ))
        );
    }
}
