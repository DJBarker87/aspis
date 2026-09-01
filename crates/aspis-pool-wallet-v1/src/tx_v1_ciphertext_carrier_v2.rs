//! Canonical wallet ciphertext carrier for one TxV1 Pool terminal.
//!
//! ASQ8 remains the exact final top-level instruction and ASR8 remains the
//! Pool return value.  The immediately preceding instruction invokes the
//! immutable SPL Noop program with this fixed-size envelope and one readonly
//! wallet/proof-authority signer.  Consequently the authority's ordinary
//! Solana transaction signature covers the carrier, ASQ8, account list,
//! resource configuration, fee payer and recent blockhash together.
//!
//! Ciphertexts are delivery metadata, not part of the proved spend relation.
//! Omitting or corrupting them can deny note recovery to a recipient, but can
//! neither change the two proved output commitments nor make an invalid spend
//! cryptographically valid.

use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_terminal_request_v1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1TransitionKind,
    },
};
use sha2::{Digest as _, Sha256};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};

use crate::{validate_encrypted_note_payload_v1, POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES};

pub const POOL_V1_TX_V1_CIPHERTEXT_CARRIER_MAGIC_V2: [u8; 4] = *b"ASC8";
pub const POOL_V1_TX_V1_CIPHERTEXT_CARRIER_VERSION_V2: u8 = 1;
pub const POOL_V1_TX_V1_CIPHERTEXT_CARRIER_DIGEST_ENCODING_V2: u8 = 1;
pub const POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2: usize = 496;

/// Immutable SPL Noop program. It accepts arbitrary instruction data and is
/// used only as a transaction-visible carrier; it owns no Aspis state.
pub const POOL_V1_TX_V1_CIPHERTEXT_CARRIER_PROGRAM_V2: Pubkey =
    solana_program::pubkey!("noopb9bkMVfRPU8AsbpTUg8AQkHtKwMYZiFUjNRtMmV");

const POOL_OFFSET: usize = 16;
const ATTEMPT_OFFSET: usize = 48;
const PROOF_ACCOUNT_OFFSET: usize = 80;
const TERMINAL_REQUEST_SHA256_OFFSET: usize = 112;
const RECIPIENT_COMMITMENT_OFFSET: usize = 144;
const CHANGE_COMMITMENT_OFFSET: usize = 176;
const RECIPIENT_CIPHERTEXT_OFFSET: usize = 208;
const CHANGE_CIPHERTEXT_OFFSET: usize =
    RECIPIENT_CIPHERTEXT_OFFSET + POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES;

const PRIVATE_TRANSFER_PRESENT_MASK: u8 = 0b11;
const WITHDRAWAL_PRESENT_MASK: u8 = 0b10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TxV1CiphertextCarrierErrorV2 {
    ZeroIdentity,
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransition,
    WrongPresenceMask,
    NonZeroReserved,
    NonCanonicalDigest,
    InvalidCiphertext,
    InvalidOrdinal,
    TerminalMismatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TxV1CiphertextCarrierV2 {
    transition_kind: PoolV1TransitionKind,
    carrier_instruction_ordinal: u16,
    terminal_instruction_ordinal: u16,
    pool: [u8; 32],
    attempt_id: [u8; 32],
    proof_account: [u8; 32],
    terminal_request_sha256: [u8; 32],
    recipient_commitment: [u8; 32],
    change_commitment: [u8; 32],
    recipient_ciphertext: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    change_ciphertext: [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES],
}

impl TxV1CiphertextCarrierV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn from_terminal_v2(
        request: &PoolV1PairForestTerminalRequestV1,
        proof_account: [u8; 32],
        carrier_instruction_ordinal: u16,
        terminal_instruction_ordinal: u16,
        recipient_ciphertext: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
        change_ciphertext: [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES],
    ) -> Result<Self, TxV1CiphertextCarrierErrorV2> {
        if proof_account == [0u8; 32] {
            return Err(TxV1CiphertextCarrierErrorV2::ZeroIdentity);
        }
        if carrier_instruction_ordinal
            .checked_add(1)
            .is_none_or(|next| next != terminal_instruction_ordinal)
        {
            return Err(TxV1CiphertextCarrierErrorV2::InvalidOrdinal);
        }
        validate_encrypted_note_payload_v1(&change_ciphertext)
            .map_err(|_| TxV1CiphertextCarrierErrorV2::InvalidCiphertext)?;
        if let Some(recipient) = &recipient_ciphertext {
            validate_encrypted_note_payload_v1(recipient)
                .map_err(|_| TxV1CiphertextCarrierErrorV2::InvalidCiphertext)?;
        }
        let request_bytes = encode_pool_v1_pair_forest_terminal_request_v1(request)
            .map_err(|_| TxV1CiphertextCarrierErrorV2::TerminalMismatch)?;
        let (transition_kind, pool, recipient_commitment, change_commitment) = match request.public
        {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
                if recipient_ciphertext.is_none() {
                    return Err(TxV1CiphertextCarrierErrorV2::WrongPresenceMask);
                }
                (
                    PoolV1TransitionKind::PrivateTransfer,
                    public.pool,
                    encode_digest_canonical(&public.recipient_commitment),
                    encode_digest_canonical(&public.change_commitment),
                )
            }
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
                if recipient_ciphertext.is_some() {
                    return Err(TxV1CiphertextCarrierErrorV2::WrongPresenceMask);
                }
                (
                    PoolV1TransitionKind::Withdrawal,
                    public.pool,
                    [0u8; 32],
                    encode_digest_canonical(&public.change_commitment),
                )
            }
        };
        if pool == [0u8; 32] {
            return Err(TxV1CiphertextCarrierErrorV2::ZeroIdentity);
        }
        Ok(Self {
            transition_kind,
            carrier_instruction_ordinal,
            terminal_instruction_ordinal,
            pool,
            // In Tag-73 the proof account address is the attempt identifier.
            // Keep both typed fields in the envelope and require equality so a
            // future lifecycle cannot silently reinterpret one of them.
            attempt_id: proof_account,
            proof_account,
            terminal_request_sha256: Sha256::digest(request_bytes).into(),
            recipient_commitment,
            change_commitment,
            recipient_ciphertext,
            change_ciphertext,
        })
    }

    pub fn transition_kind_v2(&self) -> PoolV1TransitionKind {
        self.transition_kind
    }

    pub fn carrier_instruction_ordinal_v2(&self) -> u16 {
        self.carrier_instruction_ordinal
    }

    pub fn terminal_instruction_ordinal_v2(&self) -> u16 {
        self.terminal_instruction_ordinal
    }

    pub fn pool_v2(&self) -> &[u8; 32] {
        &self.pool
    }

    pub fn attempt_id_v2(&self) -> &[u8; 32] {
        &self.attempt_id
    }

    pub fn proof_account_v2(&self) -> &[u8; 32] {
        &self.proof_account
    }

    pub fn recipient_commitment_v2(&self) -> &[u8; 32] {
        &self.recipient_commitment
    }

    pub fn change_commitment_v2(&self) -> &[u8; 32] {
        &self.change_commitment
    }

    pub fn recipient_ciphertext_v2(&self) -> Option<&[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]> {
        self.recipient_ciphertext.as_ref()
    }

    pub fn change_ciphertext_v2(&self) -> &[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES] {
        &self.change_ciphertext
    }

    pub fn validate_terminal_v2(
        &self,
        request_bytes: &[u8],
        observed_proof_account: [u8; 32],
        carrier_instruction_ordinal: u16,
        terminal_instruction_ordinal: u16,
    ) -> Result<(), TxV1CiphertextCarrierErrorV2> {
        let request =
            aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_request_v1(request_bytes)
                .map_err(|_| TxV1CiphertextCarrierErrorV2::TerminalMismatch)?;
        let (transition_kind, pool, recipient, change) = match request.public {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => (
                PoolV1TransitionKind::PrivateTransfer,
                public.pool,
                encode_digest_canonical(&public.recipient_commitment),
                encode_digest_canonical(&public.change_commitment),
            ),
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => (
                PoolV1TransitionKind::Withdrawal,
                public.pool,
                [0u8; 32],
                encode_digest_canonical(&public.change_commitment),
            ),
        };
        let request_sha256: [u8; 32] = Sha256::digest(request_bytes).into();
        if self.transition_kind != transition_kind
            || self.pool != pool
            || self.attempt_id != observed_proof_account
            || self.proof_account != observed_proof_account
            || self.terminal_request_sha256 != request_sha256
            || self.recipient_commitment != recipient
            || self.change_commitment != change
            || self.carrier_instruction_ordinal != carrier_instruction_ordinal
            || self.terminal_instruction_ordinal != terminal_instruction_ordinal
            || carrier_instruction_ordinal
                .checked_add(1)
                .is_none_or(|next| next != terminal_instruction_ordinal)
        {
            return Err(TxV1CiphertextCarrierErrorV2::TerminalMismatch);
        }
        Ok(())
    }
}

fn transition_byte_v2(kind: PoolV1TransitionKind) -> u8 {
    match kind {
        PoolV1TransitionKind::PrivateTransfer => 1,
        PoolV1TransitionKind::Withdrawal => 2,
    }
}

pub fn encode_tx_v1_ciphertext_carrier_v2(
    carrier: &TxV1CiphertextCarrierV2,
) -> Result<[u8; POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2], TxV1CiphertextCarrierErrorV2> {
    if carrier.pool == [0u8; 32]
        || carrier.attempt_id == [0u8; 32]
        || carrier.proof_account == [0u8; 32]
        || carrier.attempt_id != carrier.proof_account
        || carrier.terminal_request_sha256 == [0u8; 32]
    {
        return Err(TxV1CiphertextCarrierErrorV2::ZeroIdentity);
    }
    if carrier
        .carrier_instruction_ordinal
        .checked_add(1)
        .is_none_or(|next| next != carrier.terminal_instruction_ordinal)
    {
        return Err(TxV1CiphertextCarrierErrorV2::InvalidOrdinal);
    }
    if carrier.transition_kind == PoolV1TransitionKind::Withdrawal {
        if carrier.recipient_commitment != [0u8; 32] {
            return Err(TxV1CiphertextCarrierErrorV2::NonCanonicalDigest);
        }
    } else {
        decode_digest_canonical(&carrier.recipient_commitment)
            .map_err(|_| TxV1CiphertextCarrierErrorV2::NonCanonicalDigest)?;
    }
    decode_digest_canonical(&carrier.change_commitment)
        .map_err(|_| TxV1CiphertextCarrierErrorV2::NonCanonicalDigest)?;
    validate_encrypted_note_payload_v1(&carrier.change_ciphertext)
        .map_err(|_| TxV1CiphertextCarrierErrorV2::InvalidCiphertext)?;
    if let Some(recipient) = &carrier.recipient_ciphertext {
        validate_encrypted_note_payload_v1(recipient)
            .map_err(|_| TxV1CiphertextCarrierErrorV2::InvalidCiphertext)?;
    }
    let mask = match carrier.transition_kind {
        PoolV1TransitionKind::PrivateTransfer if carrier.recipient_ciphertext.is_some() => {
            PRIVATE_TRANSFER_PRESENT_MASK
        }
        PoolV1TransitionKind::Withdrawal
            if carrier.recipient_ciphertext.is_none()
                && carrier.recipient_commitment == [0u8; 32] =>
        {
            WITHDRAWAL_PRESENT_MASK
        }
        _ => return Err(TxV1CiphertextCarrierErrorV2::WrongPresenceMask),
    };
    let mut output = [0u8; POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2];
    output[..4].copy_from_slice(&POOL_V1_TX_V1_CIPHERTEXT_CARRIER_MAGIC_V2);
    output[4] = POOL_V1_TX_V1_CIPHERTEXT_CARRIER_VERSION_V2;
    output[5] = transition_byte_v2(carrier.transition_kind);
    output[6] = mask;
    output[7] = POOL_V1_TX_V1_CIPHERTEXT_CARRIER_DIGEST_ENCODING_V2;
    output[8..10].copy_from_slice(&carrier.carrier_instruction_ordinal.to_le_bytes());
    output[10..12].copy_from_slice(&carrier.terminal_instruction_ordinal.to_le_bytes());
    output[POOL_OFFSET..ATTEMPT_OFFSET].copy_from_slice(&carrier.pool);
    output[ATTEMPT_OFFSET..PROOF_ACCOUNT_OFFSET].copy_from_slice(&carrier.attempt_id);
    output[PROOF_ACCOUNT_OFFSET..TERMINAL_REQUEST_SHA256_OFFSET]
        .copy_from_slice(&carrier.proof_account);
    output[TERMINAL_REQUEST_SHA256_OFFSET..RECIPIENT_COMMITMENT_OFFSET]
        .copy_from_slice(&carrier.terminal_request_sha256);
    output[RECIPIENT_COMMITMENT_OFFSET..CHANGE_COMMITMENT_OFFSET]
        .copy_from_slice(&carrier.recipient_commitment);
    output[CHANGE_COMMITMENT_OFFSET..RECIPIENT_CIPHERTEXT_OFFSET]
        .copy_from_slice(&carrier.change_commitment);
    if let Some(recipient) = &carrier.recipient_ciphertext {
        output[RECIPIENT_CIPHERTEXT_OFFSET..CHANGE_CIPHERTEXT_OFFSET].copy_from_slice(recipient);
    }
    output[CHANGE_CIPHERTEXT_OFFSET..].copy_from_slice(&carrier.change_ciphertext);
    Ok(output)
}

pub fn decode_tx_v1_ciphertext_carrier_v2(
    bytes: &[u8],
) -> Result<TxV1CiphertextCarrierV2, TxV1CiphertextCarrierErrorV2> {
    if bytes.len() != POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2 {
        return Err(TxV1CiphertextCarrierErrorV2::WrongLength);
    }
    if bytes[..4] != POOL_V1_TX_V1_CIPHERTEXT_CARRIER_MAGIC_V2 {
        return Err(TxV1CiphertextCarrierErrorV2::WrongMagic);
    }
    if bytes[4] != POOL_V1_TX_V1_CIPHERTEXT_CARRIER_VERSION_V2
        || bytes[7] != POOL_V1_TX_V1_CIPHERTEXT_CARRIER_DIGEST_ENCODING_V2
    {
        return Err(TxV1CiphertextCarrierErrorV2::WrongVersion);
    }
    if bytes[12..16] != [0u8; 4] {
        return Err(TxV1CiphertextCarrierErrorV2::NonZeroReserved);
    }
    let transition_kind = match bytes[5] {
        1 => PoolV1TransitionKind::PrivateTransfer,
        2 => PoolV1TransitionKind::Withdrawal,
        _ => return Err(TxV1CiphertextCarrierErrorV2::WrongTransition),
    };
    let expected_mask = if transition_kind == PoolV1TransitionKind::PrivateTransfer {
        PRIVATE_TRANSFER_PRESENT_MASK
    } else {
        WITHDRAWAL_PRESENT_MASK
    };
    if bytes[6] != expected_mask {
        return Err(TxV1CiphertextCarrierErrorV2::WrongPresenceMask);
    }
    let recipient_bytes: [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES] = bytes
        [RECIPIENT_CIPHERTEXT_OFFSET..CHANGE_CIPHERTEXT_OFFSET]
        .try_into()
        .map_err(|_| TxV1CiphertextCarrierErrorV2::WrongLength)?;
    let recipient_ciphertext = if transition_kind == PoolV1TransitionKind::PrivateTransfer {
        Some(recipient_bytes)
    } else {
        if recipient_bytes != [0u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES] {
            return Err(TxV1CiphertextCarrierErrorV2::NonZeroReserved);
        }
        None
    };
    let carrier = TxV1CiphertextCarrierV2 {
        transition_kind,
        carrier_instruction_ordinal: u16::from_le_bytes(bytes[8..10].try_into().unwrap()),
        terminal_instruction_ordinal: u16::from_le_bytes(bytes[10..12].try_into().unwrap()),
        pool: bytes[POOL_OFFSET..ATTEMPT_OFFSET].try_into().unwrap(),
        attempt_id: bytes[ATTEMPT_OFFSET..PROOF_ACCOUNT_OFFSET]
            .try_into()
            .unwrap(),
        proof_account: bytes[PROOF_ACCOUNT_OFFSET..TERMINAL_REQUEST_SHA256_OFFSET]
            .try_into()
            .unwrap(),
        terminal_request_sha256: bytes[TERMINAL_REQUEST_SHA256_OFFSET..RECIPIENT_COMMITMENT_OFFSET]
            .try_into()
            .unwrap(),
        recipient_commitment: bytes[RECIPIENT_COMMITMENT_OFFSET..CHANGE_COMMITMENT_OFFSET]
            .try_into()
            .unwrap(),
        change_commitment: bytes[CHANGE_COMMITMENT_OFFSET..RECIPIENT_CIPHERTEXT_OFFSET]
            .try_into()
            .unwrap(),
        recipient_ciphertext,
        change_ciphertext: bytes[CHANGE_CIPHERTEXT_OFFSET..].try_into().unwrap(),
    };
    let canonical = encode_tx_v1_ciphertext_carrier_v2(&carrier)?;
    if canonical != bytes {
        return Err(TxV1CiphertextCarrierErrorV2::TerminalMismatch);
    }
    Ok(carrier)
}

pub fn build_tx_v1_ciphertext_carrier_instruction_v2(
    carrier: &TxV1CiphertextCarrierV2,
    wallet_proof_authority: Pubkey,
) -> Result<Instruction, TxV1CiphertextCarrierErrorV2> {
    if wallet_proof_authority == Pubkey::default() {
        return Err(TxV1CiphertextCarrierErrorV2::ZeroIdentity);
    }
    Ok(Instruction {
        program_id: POOL_V1_TX_V1_CIPHERTEXT_CARRIER_PROGRAM_V2,
        accounts: vec![AccountMeta::new_readonly(wallet_proof_authority, true)],
        data: encode_tx_v1_ciphertext_carrier_v2(carrier)?.to_vec(),
    })
}

const _: () = assert!(CHANGE_CIPHERTEXT_OFFSET == 352);
const _: () = assert!(
    CHANGE_CIPHERTEXT_OFFSET + POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES
        == POOL_V1_TX_V1_CIPHERTEXT_CARRIER_BYTES_V2
);

#[cfg(test)]
pub(crate) fn structurally_valid_test_note_envelope_v2(
    seed: u8,
) -> [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES] {
    let mut payload = [seed; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES];
    payload[..4].copy_from_slice(&crate::POOL_V1_NOTE_ENVELOPE_MAGIC);
    payload[4] = crate::POOL_V1_NOTE_ENVELOPE_VERSION;
    payload[5] = crate::POOL_V1_NOTE_ENVELOPE_FLAGS;
    payload[6..8].copy_from_slice(&crate::POOL_V1_NOTE_HPKE_KEM_ID.to_be_bytes());
    payload[8..10].copy_from_slice(&crate::POOL_V1_NOTE_HPKE_KDF_ID.to_be_bytes());
    payload[10..12].copy_from_slice(&crate::POOL_V1_NOTE_HPKE_AEAD_ID.to_be_bytes());
    payload[12..14].copy_from_slice(&(crate::POOL_V1_NOTE_CIPHERTEXT_BYTES as u16).to_be_bytes());
    payload[14..16].fill(0);
    debug_assert!(validate_encrypted_note_payload_v1(&payload).is_ok());
    payload
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    };

    use super::*;

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + index as u32 + 1))
    }

    fn request(withdrawal: bool) -> PoolV1PairForestTerminalRequestV1 {
        let public = if withdrawal {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: [0x11; 32],
                deployment_domain: [0x12; 32],
                anchor_sequence: 4,
                anchor_root: digest(10),
                nullifier: digest(20),
                asset_id: M31(30),
                amount: 40,
                destination_token_account: [0x13; 32],
                change_commitment: digest(50),
            })
        } else {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1 {
                pool: [0x11; 32],
                deployment_domain: [0x12; 32],
                anchor_sequence: 4,
                anchor_root: digest(10),
                nullifier: digest(20),
                asset_id: M31(30),
                recipient_commitment: digest(40),
                change_commitment: digest(50),
            })
        };
        PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [0x21; 32],
            verifier_release: [0x22; 32],
            pool_program: [0x23; 32],
            public,
        }
    }

    fn carrier(withdrawal: bool) -> TxV1CiphertextCarrierV2 {
        TxV1CiphertextCarrierV2::from_terminal_v2(
            &request(withdrawal),
            [0x31; 32],
            0,
            1,
            (!withdrawal).then(|| structurally_valid_test_note_envelope_v2(0x41)),
            structurally_valid_test_note_envelope_v2(0x42),
        )
        .unwrap()
    }

    #[test]
    fn carrier_is_fixed_canonical_and_binds_the_exact_terminal() {
        for withdrawal in [false, true] {
            let request = request(withdrawal);
            let carrier = carrier(withdrawal);
            let encoded = encode_tx_v1_ciphertext_carrier_v2(&carrier).unwrap();
            assert_eq!(encoded.len(), 496);
            assert_eq!(
                decode_tx_v1_ciphertext_carrier_v2(&encoded),
                Ok(carrier.clone())
            );
            assert_eq!(
                carrier.validate_terminal_v2(
                    &encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap(),
                    [0x31; 32],
                    0,
                    1,
                ),
                Ok(())
            );

            let mut wrong_request = request;
            wrong_request.verifier_release[0] ^= 1;
            assert_eq!(
                carrier.validate_terminal_v2(
                    &encode_pool_v1_pair_forest_terminal_request_v1(&wrong_request).unwrap(),
                    [0x31; 32],
                    0,
                    1,
                ),
                Err(TxV1CiphertextCarrierErrorV2::TerminalMismatch)
            );
            assert_eq!(
                carrier.validate_terminal_v2(
                    &encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap(),
                    [0x32; 32],
                    0,
                    1,
                ),
                Err(TxV1CiphertextCarrierErrorV2::TerminalMismatch)
            );
        }
    }

    #[test]
    fn carrier_rejects_truncation_trailing_reserved_mask_and_ciphertext_mutations() {
        let encoded = encode_tx_v1_ciphertext_carrier_v2(&carrier(false)).unwrap();
        assert_eq!(
            decode_tx_v1_ciphertext_carrier_v2(&encoded[..encoded.len() - 1]),
            Err(TxV1CiphertextCarrierErrorV2::WrongLength)
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_tx_v1_ciphertext_carrier_v2(&trailing),
            Err(TxV1CiphertextCarrierErrorV2::WrongLength)
        );
        for (offset, expected) in [
            (12, TxV1CiphertextCarrierErrorV2::NonZeroReserved),
            (6, TxV1CiphertextCarrierErrorV2::WrongPresenceMask),
            (
                RECIPIENT_CIPHERTEXT_OFFSET,
                TxV1CiphertextCarrierErrorV2::InvalidCiphertext,
            ),
        ] {
            let mut mutated = encoded;
            mutated[offset] ^= 1;
            assert_eq!(decode_tx_v1_ciphertext_carrier_v2(&mutated), Err(expected));
        }

        let withdrawal = encode_tx_v1_ciphertext_carrier_v2(&carrier(true)).unwrap();
        let mut nonzero_absent_slot = withdrawal;
        nonzero_absent_slot[RECIPIENT_CIPHERTEXT_OFFSET] = 1;
        assert_eq!(
            decode_tx_v1_ciphertext_carrier_v2(&nonzero_absent_slot),
            Err(TxV1CiphertextCarrierErrorV2::NonZeroReserved)
        );
    }
}
