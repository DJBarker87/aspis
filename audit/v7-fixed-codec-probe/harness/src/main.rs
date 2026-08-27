use std::{env, fmt::Debug, fs};

use anyhow::{anyhow, bail, ensure, Result};
use aspis_core::{
    field::{CM31, M31, P, QM31},
    v6_onefold::V6_FIXED_PACKED_FIELD_BYTES,
    v7_fixed_codec_experiment::{
        experimental_fixed_section_checksum, selected_packed_fixed_section_checksum,
        transcode_fixed_section_from_tag73, V7FixedCodecVariant, V7_FIXED_CODEC_TOTAL_QM31,
    },
};
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;

const PROGRAM: [u8; 32] = [0x7c; 32];
const FIXTURE_ACCOUNT: [u8; 32] = [0x7d; 32];
const COMPUTE_LIMIT: u32 = 200_000;

fn fields() -> Vec<QM31> {
    (0..V7_FIXED_CODEC_TOTAL_QM31)
        .map(|ordinal| {
            let base = (ordinal as u32).wrapping_mul(1_000_003) % P;
            QM31 {
                c0: CM31::new(M31(base), M31((base + 1) % P)),
                c1: CM31::new(M31((base + 2) % P), M31((base + 3) % P)),
            }
        })
        .collect()
}

fn pack_tag73(fields: &[QM31]) -> Vec<u8> {
    let mut output = vec![0u8; V6_FIXED_PACKED_FIELD_BYTES];
    for (field, value) in fields.iter().enumerate() {
        for (limb, word) in [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
            .into_iter()
            .enumerate()
        {
            let bit_start = (4 * field + limb) * 31;
            for bit in 0..31 {
                output[(bit_start + bit) / 8] |=
                    (((word >> bit) & 1) as u8) << ((bit_start + bit) % 8);
            }
        }
    }
    output
}

fn checksum_bytes(value: QM31) -> [u8; 16] {
    let mut output = [0u8; 16];
    value.write_le_bytes(&mut output);
    output
}

fn wire<T, E: Debug>(result: Result<T, E>) -> Result<T> {
    result.map_err(|error| anyhow!("wire error: {error:?}"))
}

fn main() -> Result<()> {
    let path = env::args()
        .nth(1)
        .ok_or_else(|| anyhow!("usage: harness <probe.so>"))?;
    if env::args().nth(2).is_some() {
        bail!("unexpected extra argument");
    }
    let program = Address::from(PROGRAM);
    let fixture_account = Address::from(FIXTURE_ACCOUNT);
    let payer = Keypair::new_from_array([0x42; 32]);
    let mut svm = LiteSVM::new();
    svm.airdrop(&payer.pubkey(), 1_000_000_000)
        .map_err(|failed| anyhow!("airdrop failed: {:?}", failed.err))?;
    svm.add_program(program, &fs::read(path)?)?;

    let packed = pack_tag73(&fields());
    let canonical_pre = wire(transcode_fixed_section_from_tag73(
        &packed,
        V7FixedCodecVariant::CanonicalPreFinal,
    ))?;
    let canonical_final = wire(transcode_fixed_section_from_tag73(
        &packed,
        V7FixedCodecVariant::CanonicalFinal256,
    ))?;
    let canonical_both = wire(transcode_fixed_section_from_tag73(
        &packed,
        V7FixedCodecVariant::CanonicalBoth,
    ))?;
    let fixtures = [
        (
            0u8,
            "selected-packed",
            packed.clone(),
            wire(selected_packed_fixed_section_checksum(&packed))?,
        ),
        (
            1u8,
            "canonical-pre-final",
            canonical_pre.clone(),
            wire(experimental_fixed_section_checksum(
                &canonical_pre,
                V7FixedCodecVariant::CanonicalPreFinal,
            ))?,
        ),
        (
            2u8,
            "canonical-final256",
            canonical_final.clone(),
            wire(experimental_fixed_section_checksum(
                &canonical_final,
                V7FixedCodecVariant::CanonicalFinal256,
            ))?,
        ),
        (
            3u8,
            "canonical-both",
            canonical_both.clone(),
            wire(experimental_fixed_section_checksum(
                &canonical_both,
                V7FixedCodecVariant::CanonicalBoth,
            ))?,
        ),
    ];

    let expected = checksum_bytes(fixtures[0].3);
    for (mode, label, bytes, host_checksum) in fixtures {
        ensure!(checksum_bytes(host_checksum) == expected);
        svm.set_account(
            fixture_account,
            Account {
                lamports: svm.minimum_balance_for_rent_exemption(bytes.len()),
                data: bytes.clone(),
                owner: program,
                executable: false,
                rent_epoch: 0,
            },
        )
        .map_err(|error| anyhow!("install fixture: {error}"))?;
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_LIMIT),
                Instruction {
                    program_id: program,
                    accounts: vec![AccountMeta::new_readonly(fixture_account, false)],
                    data: vec![mode],
                },
            ],
            Some(&payer.pubkey()),
            &[&payer],
            svm.latest_blockhash(),
        );
        let simulated = svm.simulate_transaction(tx).map_err(|failed| {
            anyhow!(
                "{label} failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
        ensure!(simulated.meta.return_data.program_id == program);
        ensure!(simulated.meta.return_data.data == expected);
        println!(
            "mode={mode} label={label} bytes={} component_tx_cu={}",
            bytes.len(),
            simulated.meta.compute_units_consumed
        );
    }
    Ok(())
}
