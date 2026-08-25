use aspis_core::field::M31;
use aspis_pool::{
    decode_private_transfer_instruction_v1, decode_withdrawal_instruction_v1,
    encode_private_transfer_instruction_v1, encode_withdrawal_instruction_v1,
    PrivateTransferStatementV1, WithdrawalStatementV1, POOL_V1_SPEND_INSTRUCTION_BYTES,
};
use aspis_statement::{
    pool_v1::{
        decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
        encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
        HistoricalAnchorEnvelopeV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        PoolV1WithdrawalPublicV1, POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES,
        POOL_V1_PAYMENT_STATEMENT_BYTES,
    },
    poseidon2::Digest,
};

const OUTER_HEADER_BYTES: usize = 8;
const STATEMENT_OFFSET: usize = OUTER_HEADER_BYTES + POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES;

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn envelope(kind: PoolV1TransitionKind) -> HistoricalAnchorEnvelopeV1 {
    HistoricalAnchorEnvelopeV1 {
        transition_kind: kind,
        pool: [1u8; 32],
        deployment_domain: [2u8; 32],
        anchor_sequence: 257,
        anchor_root: digest(10),
        nullifier: digest(100),
        verifier_profile: [3u8; 32],
        verifier_release: [4u8; 32],
    }
}

#[test]
fn private_transfer_relation_encoding_is_byte_exact_to_pool_payload() {
    let envelope = envelope(PoolV1TransitionKind::PrivateTransfer);
    let pool_statement = PrivateTransferStatementV1 {
        pool: envelope.pool,
        deployment_domain: envelope.deployment_domain,
        anchor_sequence: envelope.anchor_sequence,
        anchor_root: envelope.anchor_root,
        nullifier: envelope.nullifier,
        asset_id: M31(77),
        recipient_commitment: digest(200),
        change_commitment: digest(300),
    };
    let relation_statement = PoolV1PrivateTransferPublicV1 {
        pool: pool_statement.pool,
        deployment_domain: pool_statement.deployment_domain,
        anchor_sequence: pool_statement.anchor_sequence,
        anchor_root: pool_statement.anchor_root,
        nullifier: pool_statement.nullifier,
        asset_id: pool_statement.asset_id,
        recipient_commitment: pool_statement.recipient_commitment,
        change_commitment: pool_statement.change_commitment,
    };

    let instruction = encode_private_transfer_instruction_v1(&envelope, &pool_statement).unwrap();
    let relation_payload = encode_pool_v1_private_transfer_public_v1(&relation_statement).unwrap();
    assert_eq!(instruction.len(), POOL_V1_SPEND_INSTRUCTION_BYTES);
    assert_eq!(relation_payload.len(), POOL_V1_PAYMENT_STATEMENT_BYTES);
    assert_eq!(&instruction[STATEMENT_OFFSET..], &relation_payload);

    let pool_decoded = decode_private_transfer_instruction_v1(&instruction).unwrap();
    let relation_decoded =
        decode_pool_v1_private_transfer_public_v1(pool_decoded.statement_payload).unwrap();
    assert_eq!(relation_decoded, relation_statement);
    assert_eq!(
        pool_decoded.statement.recipient_commitment,
        relation_decoded.recipient_commitment
    );
    assert_eq!(
        pool_decoded.statement.change_commitment,
        relation_decoded.change_commitment
    );
}

#[test]
fn withdrawal_relation_encoding_is_byte_exact_to_pool_payload() {
    let envelope = envelope(PoolV1TransitionKind::Withdrawal);
    let pool_statement = WithdrawalStatementV1 {
        pool: envelope.pool,
        deployment_domain: envelope.deployment_domain,
        anchor_sequence: envelope.anchor_sequence,
        anchor_root: envelope.anchor_root,
        nullifier: envelope.nullifier,
        asset_id: M31(77),
        amount: 250,
        destination_token_account: [9u8; 32],
        change_commitment: digest(300),
    };
    let relation_statement = PoolV1WithdrawalPublicV1 {
        pool: pool_statement.pool,
        deployment_domain: pool_statement.deployment_domain,
        anchor_sequence: pool_statement.anchor_sequence,
        anchor_root: pool_statement.anchor_root,
        nullifier: pool_statement.nullifier,
        asset_id: pool_statement.asset_id,
        amount: pool_statement.amount,
        destination_token_account: pool_statement.destination_token_account,
        change_commitment: pool_statement.change_commitment,
    };

    let instruction = encode_withdrawal_instruction_v1(&envelope, &pool_statement).unwrap();
    let relation_payload = encode_pool_v1_withdrawal_public_v1(&relation_statement).unwrap();
    assert_eq!(instruction.len(), POOL_V1_SPEND_INSTRUCTION_BYTES);
    assert_eq!(relation_payload.len(), POOL_V1_PAYMENT_STATEMENT_BYTES);
    assert_eq!(&instruction[STATEMENT_OFFSET..], &relation_payload);

    let pool_decoded = decode_withdrawal_instruction_v1(&instruction).unwrap();
    let relation_decoded =
        decode_pool_v1_withdrawal_public_v1(pool_decoded.statement_payload).unwrap();
    assert_eq!(relation_decoded, relation_statement);
    assert_eq!(pool_decoded.statement.amount, relation_decoded.amount);
    assert_eq!(
        pool_decoded.statement.destination_token_account,
        relation_decoded.destination_token_account
    );
    assert_eq!(
        pool_decoded.statement.change_commitment,
        relation_decoded.change_commitment
    );
}
