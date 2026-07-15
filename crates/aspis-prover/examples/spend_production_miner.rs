//! Local production-path miner for the frozen Spend proof.
//!
//! This example uses fresh OS entropy, a durable burned-nonce ledger, the
//! exact cap-17 q3 GoodSpend worker, canonical minimum PoW, and the fixed public
//! release controller. It never exposes a partial attempt or retry detail.

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{compiler_fence, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, SystemTime};

use aspis_core::field::M31;
use aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore;
use aspis_prover::state_only_spend::build_hiding_atomic_state_only_spend_first_good_v3;
use aspis_prover::state_only_spend_release::{
    SpendFixedReleaseController, SpendPublicRelease, SpendReleaseChannel, SpendSystemReleaseClock,
};
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
    output_commitment, AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn fixture(
    pool: [u8; 32],
    sequence: u64,
    deployment_domain: [u8; 32],
    fixture_seed: u32,
) -> (AtomicPaymentStatementV4, SpendWitness) {
    let seeded_digest = |base: u32| {
        digest(
            base.checked_add(fixture_seed)
                .expect("ASPIS_SPEND_FIXTURE_SEED overflow"),
        )
    };
    let nullifier_key = seeded_digest(101);
    let input_salt = seeded_digest(301);
    let output_salt = seeded_digest(501);
    let output_owner_key = seeded_digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|level| seeded_digest(1_000 + 31 * level))
            .collect(),
        index: 0x5_a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool,
        sequence,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
        deployment_domain,
    };
    (statement, witness)
}

/// Decode one base58 Solana public key into its 32 raw bytes.
fn decode_base58_32(role: &str, value: &str) -> [u8; 32] {
    const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let mut bytes: Vec<u8> = Vec::with_capacity(32);
    for symbol in value.bytes() {
        let mut carry = ALPHABET
            .iter()
            .position(|&candidate| candidate == symbol)
            .unwrap_or_else(|| panic!("{role} is not base58"));
        for byte in bytes.iter_mut() {
            carry += usize::from(*byte) * 58;
            *byte = (carry & 0xff) as u8;
            carry >>= 8;
        }
        while carry != 0 {
            bytes.push((carry & 0xff) as u8);
            carry >>= 8;
        }
    }
    for symbol in value.bytes() {
        if symbol == b'1' {
            bytes.push(0);
        } else {
            break;
        }
    }
    assert_eq!(bytes.len(), 32, "{role} must decode to exactly 32 bytes");
    bytes.reverse();
    bytes.try_into().unwrap()
}

#[derive(Default)]
struct OneReleaseChannel {
    release: Option<SpendPublicRelease>,
}

impl SpendReleaseChannel for OneReleaseChannel {
    fn publish(&mut self, release: SpendPublicRelease) {
        assert!(self.release.replace(release).is_none());
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn scrub_witness(witness: &mut SpendWitness) {
    for value in witness
        .nullifier_key
        .iter_mut()
        .chain(&mut witness.input_salt)
        .chain(&mut witness.output_salt)
        .chain(&mut witness.output_owner_key)
    {
        // SAFETY: every pointer is a live, uniquely borrowed M31 cell. The
        // volatile write prevents the cleanup from being optimized away.
        unsafe { core::ptr::write_volatile(value, M31::ZERO) };
    }
    unsafe {
        core::ptr::write_volatile(&mut witness.input_asset_id, M31::ZERO);
        core::ptr::write_volatile(&mut witness.value, 0);
        core::ptr::write_volatile(&mut witness.value_out, 0);
        core::ptr::write_volatile(&mut witness.merkle_path.index, 0);
    }
    for sibling in &mut witness.merkle_path.siblings {
        for value in sibling {
            unsafe { core::ptr::write_volatile(value, M31::ZERO) };
        }
    }
    compiler_fence(Ordering::SeqCst);
}

fn main() {
    let mut args = std::env::args().skip(1);
    let cluster_tag = args
        .next()
        .expect("usage: spend_production_miner <cluster-tag> <program-id> <pool-pubkey> [output] [ledger] [boundary-seconds]");
    assert!(
        !cluster_tag.is_empty() && cluster_tag.len() <= 64,
        "cluster tag must be a short nonempty name such as mainnet-beta or devnet"
    );
    let program_id = decode_base58_32("program id", &args.next().expect("program id argument"));
    let pool = decode_base58_32("pool pubkey", &args.next().expect("pool pubkey argument"));
    let output = PathBuf::from(
        args.next()
            .unwrap_or_else(|| "artifact-output/spend-production-mined.bin".to_owned()),
    );
    let ledger = PathBuf::from(
        args.next()
            .unwrap_or_else(|| "artifact-output/spend-production-nonce-ledger".to_owned()),
    );
    let boundary_seconds = args
        .next()
        .map(|value| value.parse::<u64>().expect("boundary seconds"))
        .unwrap_or(3_600);
    assert!(args.next().is_none(), "too many arguments");

    // The production statement is always sequence 0 of a freshly initialized
    // pool, bound to the deployment domain the pool stores at init.
    let sequence = 0u64;
    let fixture_seed = std::env::var("ASPIS_SPEND_FIXTURE_SEED")
        .map(|value| value.parse::<u32>().expect("ASPIS_SPEND_FIXTURE_SEED"))
        .unwrap_or(0);
    let deployment_domain =
        aspis_statement::atomic_deployment_domain(HOST_HASH, &program_id, cluster_tag.as_bytes());
    let boundary = SystemTime::now()
        .checked_add(Duration::from_secs(boundary_seconds))
        .expect("release boundary overflow");
    let mut controller = SpendFixedReleaseController::new(boundary);
    let (statement, mut witness) = fixture(pool, sequence, deployment_domain, fixture_seed);
    let statement_sidecar = serde_json::json!({
        "artifact": "aspis_spend_production_statement",
        "pool_hex": hex(&statement.pool),
        "sequence": statement.sequence,
        "current_anchor_hex": hex(&encode_digest_canonical(&statement.spend.anchor)),
        "nullifier_hex": hex(&encode_digest_canonical(&statement.spend.nullifier)),
        "output_commitment_hex": hex(&encode_digest_canonical(&statement.spend.output_commitment)),
        "output_anchor_hex": hex(&encode_digest_canonical(&statement.output_anchor)),
        "asset_id": statement.spend.asset_id.0,
        "fee": statement.spend.fee,
        "deployment_domain_hex": hex(&statement.deployment_domain),
        "selection_rule": "least GoodSpend selector from three post-final branches",
        "witness_independent_public_metadata": true,
    });
    if let Some(parent) = ledger.parent() {
        fs::create_dir_all(parent).expect("create nonce-ledger directory");
    }
    let mut nonce_store =
        DurableStateOnlyMaskNonceStore::open(&ledger).expect("open durable nonce ledger");
    let (sender, receiver) = mpsc::sync_channel(1);
    let worker = thread::spawn(move || {
        let completion = build_hiding_atomic_state_only_spend_first_good_v3(
            &statement,
            &witness,
            &mut nonce_store,
        );
        scrub_witness(&mut witness);
        let _ = sender.send(completion);
    });

    // The boundary event remains live while the private worker mines. If the
    // worker has not delivered a complete result by the preselected instant,
    // the controller publishes Abort on time and the process exits without
    // waiting for a late result.
    let mut clock = SpendSystemReleaseClock;
    let completed = loop {
        let Ok(remaining) = boundary.duration_since(SystemTime::now()) else {
            break false;
        };
        if remaining.is_zero() {
            break false;
        }
        match receiver.recv_timeout(remaining.min(Duration::from_millis(250))) {
            Ok(completion) => {
                controller.record_first_good_completion(&clock, completion);
                break true;
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break false,
        }
    };
    let mut channel = OneReleaseChannel::default();
    controller.release(&mut clock, &mut channel);
    if completed {
        worker.join().expect("private Spend worker panicked");
    } else {
        drop(worker);
    }

    match channel.release.expect("one release event") {
        SpendPublicRelease::Proof(proof) => {
            if let Some(parent) = output.parent() {
                fs::create_dir_all(parent).expect("create proof directory");
            }
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&output)
                .expect("create fresh released proof");
            file.write_all(&proof).expect("write released proof");
            file.sync_all().expect("sync released proof");
            let statement_path = output.with_extension("statement.json");
            let statement_bytes = serde_json::to_vec_pretty(&statement_sidecar)
                .expect("serialize public statement sidecar");
            let mut statement_file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&statement_path)
                .expect("create fresh public statement sidecar");
            statement_file
                .write_all(&statement_bytes)
                .expect("write public statement sidecar");
            statement_file
                .sync_all()
                .expect("sync public statement sidecar");
            println!("proof={}", output.display());
            println!("statement={}", statement_path.display());
            println!("bytes={}", proof.len());
            println!("sha256={}", hex(&HOST_HASH(&[&proof])));
            println!("cluster_tag={cluster_tag}");
            println!("deployment_domain={}", hex(&deployment_domain));
            println!("fixture_seed={fixture_seed}");
        }
        SpendPublicRelease::Abort => {
            println!("abort");
            std::process::exit(2);
        }
    }
}
