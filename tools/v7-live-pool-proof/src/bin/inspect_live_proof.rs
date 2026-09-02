use std::{env, fs, str::FromStr};

use anyhow::{bail, ensure, Context, Result};
use aspis_core::v7_fixed_canonical_audit::V7_CANONICAL_BODY_WITHOUT_FRONTIERS;
use aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES;
use aspis_prover::HOST_HASH;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_statement_v1,
    v7_pool_pair_forest_tag73_statement_digest_v1, PoolV1PairForestTerminalStatementV1,
    V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use solana_program::pubkey::Pubkey;

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let statement_path = args.next().context("missing ASF8 path")?;
    let proof_path = args.next().context("missing proof-body path")?;
    let verifier = Pubkey::from_str(&args.next().context("missing verifier program id")?)
        .context("invalid verifier program id")?;
    let attempt = Pubkey::from_str(&args.next().context("missing proof-account attempt id")?)
        .context("invalid proof-account attempt id")?;
    ensure!(args.next().is_none(), "unexpected trailing argument");

    let statement_bytes: [u8; 1880] = fs::read(statement_path)
        .context("read ASF8")?
        .try_into()
        .map_err(|bytes: Vec<u8>| anyhow::anyhow!("ASF8 has {} bytes, expected 1880", bytes.len()))?;
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(&statement_bytes)
        .map_err(|error| anyhow::anyhow!("decode ASF8: {error:?}"))?;
    let proof = fs::read(proof_path).context("read proof body")?;
    let frontier_bytes = proof
        .len()
        .checked_sub(V7_CANONICAL_BODY_WITHOUT_FRONTIERS)
        .context("proof shorter than canonical fixed body")?;
    let bytes_per_paired_node = 2 * V7_COMPACT_DIGEST_BYTES;
    ensure!(
        frontier_bytes % bytes_per_paired_node == 0,
        "proof length does not encode two exact frontiers"
    );
    let frontier_nodes = frontier_bytes / bytes_per_paired_node;
    let statement_digest =
        v7_pool_pair_forest_tag73_statement_digest_v1(&statement_bytes, HOST_HASH);
    let transition = &statement.common().lane_transition;
    let verified = match &statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { ref public, .. } => {
            aspis_verifier::v7_verifier::verify_v7_pool_pair_forest_private_transfer_canonical_with_statement_digest(
                HOST_HASH,
                &proof,
                frontier_nodes,
                &verifier,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                &attempt,
                public,
                transition,
                statement_digest,
                true,
            )
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { ref public, .. } => {
            aspis_verifier::v7_verifier::verify_v7_pool_pair_forest_withdrawal_canonical_with_statement_digest(
                HOST_HASH,
                &proof,
                frontier_nodes,
                &verifier,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                &attempt,
                public,
                transition,
                statement_digest,
                true,
            )
        }
    };
    let verified = match verified {
        Ok(value) => value,
        Err(error) => bail!("proof verification failed: {error:?}"),
    };
    println!(
        "{{\"proofBytes\":{},\"frontierNodes\":{},\"compactCounter\":{}}}",
        proof.len(),
        verified.transcript.frontier_nodes,
        verified.transcript.compact_counter
    );
    Ok(())
}
