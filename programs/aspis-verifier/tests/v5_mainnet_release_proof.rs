#![cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]

use aspis_core::field::M31;
use aspis_statement::{
    atomic_payment_statement_digest_v4, decode_digest_canonical, AtomicPaymentStatementV4,
    SpendPublic,
};
use aspis_verifier::v5_cu_probe::verify_uploaded_v5_mode9_cu_fixture;
use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;
use solana_program::{account_info::AccountInfo, clock::Epoch, hash::hashv, pubkey::Pubkey};
use std::str::FromStr;

const MAINNET_PROOF: &[u8] =
    include_bytes!("../../../release/aspis-v5-tag67-mainnet-v1/proof/v5-mainnet-proof.bin");
const MAINNET_STATEMENT_JSON: &[u8] = include_bytes!(
    "../../../release/aspis-v5-tag67-mainnet-v1/statement/v5-mainnet-statement.json"
);

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut output = [0u8; 32];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    output
}

fn decode_digest(value: &str) -> [M31; 8] {
    decode_digest_canonical(&decode_hex_32(value)).unwrap()
}

fn mainnet_statement() -> AtomicPaymentStatementV4 {
    AtomicPaymentStatementV4 {
        pool: decode_hex_32("0d5b6b8aef565a35887ad0c60acbaa27a7c8db501a1adfc1ad2171c44664de48"),
        sequence: 0,
        spend: SpendPublic {
            anchor: decode_digest(
                "2f1c920dc6b3ad1fa6d29a0da5eb3232892c4c0edcd86c4a3825215a9fb7da63",
            ),
            nullifier: decode_digest(
                "251bbb2be96bef3b6eccab04da5ab27bc3b3c04bfb9ef5598a417d3406759317",
            ),
            output_commitment: decode_digest(
                "7a08e0333baf4b7bc34e14690adcb507ef6e32021e5767628d388337eab0c30e",
            ),
            asset_id: M31(17),
            fee: 1,
        },
        output_anchor: decode_digest(
            "e0de9172992f6e4803419a5fca909d3d3507ee7d81cc956ef4977a1ceeab967f",
        ),
        deployment_domain: decode_hex_32(
            "87682be1a518ecc95f7aac6e7f400a1419c0383a0d554877a6ab0a3ce6e31936",
        ),
    }
}

fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

fn sealed_account_bytes(proof: &[u8]) -> Vec<u8> {
    let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    data[..4].copy_from_slice(b"ASPU");
    data[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    data[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    data
}

fn verify(statement: &AtomicPaymentStatementV4) -> solana_program::entrypoint::ProgramResult {
    let statement_digest = atomic_payment_statement_digest_v4(statement, host_hashv).unwrap();
    let key = Pubkey::new_unique();
    let owner = aspis_verifier::id();
    let mut lamports = 1u64;
    let mut data = sealed_account_bytes(MAINNET_PROOF);
    let account = AccountInfo::new(
        &key,
        false,
        false,
        &mut lamports,
        &mut data,
        &owner,
        false,
        Epoch::default(),
    );
    verify_uploaded_v5_mode9_cu_fixture(&account, statement, &statement_digest)
}

#[test]
fn tag67_exact_released_mainnet_proof_passes_the_deployed_callback() {
    assert_eq!(MAINNET_PROOF.len(), 75_358);
    assert_eq!(
        hashv(&[MAINNET_STATEMENT_JSON]).to_bytes(),
        decode_hex_32("0cdc34bc7f835640cff76d1085df9ba966df9f39eb228f3002f927cf30958113")
    );
    assert_eq!(verify(&mainnet_statement()), Ok(()));
}

#[test]
fn tag67_mainnet_nullifier_derives_the_recorded_address_at_bump_255() {
    let nullifier =
        decode_hex_32("251bbb2be96bef3b6eccab04da5ab27bc3b3c04bfb9ef5598a417d3406759317");
    let (address, bump) =
        aspis_verifier::atomic_payment::atomic_nullifier_address(&aspis_verifier::id(), &nullifier);
    assert_eq!(
        address,
        Pubkey::from_str("7Umhkv2Z3E2DksnpivCz2tovtbRoL1uXtnYBAtQBgu8Q").unwrap()
    );
    assert_eq!(bump, u8::MAX);
}

#[test]
fn tag67_exact_released_proof_is_bound_to_every_public_field() {
    let original = mainnet_statement();
    let mut variants = Vec::new();

    let mut changed = original.clone();
    changed.pool[0] ^= 1;
    variants.push(changed);
    let mut changed = original.clone();
    changed.sequence = 1;
    variants.push(changed);
    let mut changed = original.clone();
    changed.spend.anchor[0] = changed.spend.anchor[0].add(M31::ONE);
    variants.push(changed);
    let mut changed = original.clone();
    changed.spend.nullifier[0] = changed.spend.nullifier[0].add(M31::ONE);
    variants.push(changed);
    let mut changed = original.clone();
    changed.spend.output_commitment[0] = changed.spend.output_commitment[0].add(M31::ONE);
    variants.push(changed);
    let mut changed = original.clone();
    changed.output_anchor[0] = changed.output_anchor[0].add(M31::ONE);
    variants.push(changed);
    let mut changed = original.clone();
    changed.spend.asset_id = changed.spend.asset_id.add(M31::ONE);
    variants.push(changed);
    let mut changed = original.clone();
    changed.spend.fee += 1;
    variants.push(changed);
    let mut changed = original;
    changed.deployment_domain[0] ^= 1;
    variants.push(changed);

    for changed in &variants {
        assert!(verify(changed).is_err());
    }
}
