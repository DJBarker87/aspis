//! Read-only public-devnet capability probe for Solana transaction v1.
//!
//! This executable contains no signer and exposes no send/simulate path.

use aspis_pool_wallet_v1::lane_forest_transaction_v1::probe_public_devnet_tx_v1_capability_v2;

fn main() {
    match probe_public_devnet_tx_v1_capability_v2() {
        Ok(capability) => {
            let execution_activated = capability.execution_activated_v2();
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "schema": "aspis.v7.public-devnet-txv1-capability.v1",
                    "capability": capability,
                    "executionActivated": execution_activated,
                }))
                .expect("fixed capability JSON")
            );
        }
        Err(error) => {
            eprintln!("public devnet TxV1 probe failed: {error:?}");
            std::process::exit(1);
        }
    }
}
