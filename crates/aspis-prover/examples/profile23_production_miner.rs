//! Local production-path miner for the frozen Profile23 proof.
//!
//! This example uses fresh OS entropy, a durable burned-nonce ledger, the
//! exact cap-17 q3 Good23 worker, canonical minimum PoW, and the fixed public
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
use aspis_prover::state_only_profile23::build_hiding_atomic_state_only_profile23_first_good_v3;
use aspis_prover::state_only_profile23_release::{
    Profile23FixedReleaseController, Profile23PublicRelease, Profile23ReleaseChannel,
    Profile23SystemReleaseClock,
};
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
    output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn fixture(
    pool: [u8; 32],
    sequence: u64,
    fixture_seed: u32,
) -> (AtomicPaymentStatementV3, SpendWitness) {
    let seeded_digest = |base: u32| {
        digest(
            base.checked_add(fixture_seed)
                .expect("ASPIS_PROFILE23_FIXTURE_SEED overflow"),
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
    let statement = AtomicPaymentStatementV3 {
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
    };
    (statement, witness)
}

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(
        value.len(),
        64,
        "ASPIS_PROFILE23_POOL_HEX must be 64 hex characters"
    );
    let mut result = [0u8; 32];
    for (index, byte) in result.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .expect("ASPIS_PROFILE23_POOL_HEX contains non-hex characters");
    }
    result
}

#[derive(Default)]
struct OneReleaseChannel {
    release: Option<Profile23PublicRelease>,
}

impl Profile23ReleaseChannel for OneReleaseChannel {
    fn publish(&mut self, release: Profile23PublicRelease) {
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
    let output = PathBuf::from(
        args.next()
            .unwrap_or_else(|| "artifact-output/profile23-production-mined.bin".to_owned()),
    );
    let ledger = PathBuf::from(
        args.next()
            .unwrap_or_else(|| "artifact-output/profile23-production-nonce-ledger".to_owned()),
    );
    let boundary_seconds = args
        .next()
        .map(|value| value.parse::<u64>().expect("boundary seconds"))
        .unwrap_or(3_600);
    assert!(args.next().is_none(), "too many arguments");

    let pool = std::env::var("ASPIS_PROFILE23_POOL_HEX")
        .map(|value| decode_hex_32(&value))
        .unwrap_or([0x5a; 32]);
    let sequence = std::env::var("ASPIS_PROFILE23_SEQUENCE")
        .map(|value| value.parse::<u64>().expect("ASPIS_PROFILE23_SEQUENCE"))
        .unwrap_or(73);
    let fixture_seed = std::env::var("ASPIS_PROFILE23_FIXTURE_SEED")
        .map(|value| value.parse::<u32>().expect("ASPIS_PROFILE23_FIXTURE_SEED"))
        .unwrap_or(0);
    let boundary = SystemTime::now()
        .checked_add(Duration::from_secs(boundary_seconds))
        .expect("release boundary overflow");
    let mut controller = Profile23FixedReleaseController::new(boundary);
    let (statement, mut witness) = fixture(pool, sequence, fixture_seed);
    let statement_sidecar = serde_json::json!({
        "artifact": "profile23_production_statement",
        "pool_hex": hex(&statement.pool),
        "sequence": statement.sequence,
        "current_anchor_hex": hex(&encode_digest_canonical(&statement.spend.anchor)),
        "nullifier_hex": hex(&encode_digest_canonical(&statement.spend.nullifier)),
        "output_commitment_hex": hex(&encode_digest_canonical(&statement.spend.output_commitment)),
        "output_anchor_hex": hex(&encode_digest_canonical(&statement.output_anchor)),
        "asset_id": statement.spend.asset_id.0,
        "fee": statement.spend.fee,
        "selection_rule": "least Good23 selector from three post-final branches",
        "witness_independent_public_metadata": true,
    });
    if let Some(parent) = ledger.parent() {
        fs::create_dir_all(parent).expect("create nonce-ledger directory");
    }
    let mut nonce_store =
        DurableStateOnlyMaskNonceStore::open(&ledger).expect("open durable nonce ledger");
    let (sender, receiver) = mpsc::sync_channel(1);
    let worker = thread::spawn(move || {
        let completion = build_hiding_atomic_state_only_profile23_first_good_v3(
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
    let mut clock = Profile23SystemReleaseClock;
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
        worker.join().expect("private Profile23 worker panicked");
    } else {
        drop(worker);
    }

    match channel.release.expect("one release event") {
        Profile23PublicRelease::Proof(proof) => {
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
            println!("fixture_seed={fixture_seed}");
        }
        Profile23PublicRelease::Abort => {
            println!("abort");
            std::process::exit(2);
        }
    }
}
