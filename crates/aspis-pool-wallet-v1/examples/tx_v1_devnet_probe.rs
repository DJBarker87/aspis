//! Read-only public-devnet capability probe for Solana transaction v1.
//!
//! This executable contains no signer and exposes no send/simulate path.

use aspis_pool_wallet_v1::lane_forest_transaction_v1::probe_public_devnet_tx_v1_capability_v2;

fn main() {
    match probe_public_devnet_tx_v1_capability_v2() {
        Ok(capability) => {
            println!("{capability:#?}");
            println!(
                "execution_activated={}",
                capability.execution_activated_v2()
            );
        }
        Err(error) => {
            eprintln!("public devnet TxV1 probe failed: {error:?}");
            std::process::exit(1);
        }
    }
}
