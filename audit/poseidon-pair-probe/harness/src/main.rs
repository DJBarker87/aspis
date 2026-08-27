use std::{env, fs};

use anyhow::{anyhow, Result};
use litesvm::LiteSVM;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::Instruction;
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;

fn main() -> Result<()> {
    let path = env::args().nth(1).expect("usage: harness <probe.so>");
    let program_id = Address::from([0x73; 32]);
    let mut svm = LiteSVM::new();
    let payer = Keypair::new_from_array([0x42; 32]);
    svm.airdrop(&payer.pubkey(), 1_000_000_000)
        .map_err(|failed| anyhow!("airdrop failed: {:?}", failed.err))?;
    svm.add_program(program_id, &fs::read(path)?)?;
    for count in [0u16, 1, 20, 21, 40] {
        let instructions = [
            ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
            Instruction {
                program_id,
                accounts: vec![],
                data: count.to_le_bytes().to_vec(),
            },
        ];
        let tx = Transaction::new_signed_with_payer(
            &instructions,
            Some(&payer.pubkey()),
            &[&payer],
            svm.latest_blockhash(),
        );
        let result = svm.simulate_transaction(tx).map_err(|failed| {
            anyhow!(
                "count={count} failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
        println!("count={count} cu={}", result.meta.compute_units_consumed);
    }
    Ok(())
}
