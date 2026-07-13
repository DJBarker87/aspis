//! Local-only mined Profile-22 artifact builder.
//!
//! This example deliberately has no transaction, RPC, signer, keypair, or
//! upload dependency.  It uses the production first-good/Good22 worker, the
//! durable nonce ledger, and the fixed-release controller.  The proof file is
//! created only by the release channel, after the configured public epoch and
//! after the ordinary production verifier accepts it.

use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use aspis_core::field::M31;
use aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore;
use aspis_prover::state_only_profile22::build_hiding_atomic_state_only_profile22_first_good_v3;
use aspis_prover::state_only_profile22_release::{
    Profile22FixedReleaseController, Profile22PublicRelease, Profile22ReleaseChannel,
    Profile22SystemReleaseClock,
};
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_profile22::verify_atomic_state_only_profile22_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
};

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArtifactSummary {
    length: usize,
    sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LocalReleaseOutcome {
    Abort,
    Failed,
}

struct LocalArtifactChannel<'a> {
    output: PathBuf,
    statement: &'a AtomicPaymentStatementV3,
    summary: Option<ArtifactSummary>,
    outcome: Option<LocalReleaseOutcome>,
}

impl<'a> LocalArtifactChannel<'a> {
    fn new(output: PathBuf, statement: &'a AtomicPaymentStatementV3) -> Self {
        Self {
            output,
            statement,
            summary: None,
            outcome: None,
        }
    }

    fn write_verified(&self, bytes: &[u8]) -> Result<ArtifactSummary, ()> {
        // This is the ordinary production verifier.  The diagnostic unmined
        // entry point is intentionally not imported by this executable.
        verify_atomic_state_only_profile22_v3(bytes, self.statement, HOST_HASH, None)
            .map_err(|_| ())?;

        let parent = self
            .output
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        fs::create_dir_all(parent).map_err(|_| ())?;
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        let mut file = options.open(&self.output).map_err(|_| ())?;
        if file.write_all(bytes).and_then(|_| file.sync_all()).is_err() {
            let _ = fs::remove_file(&self.output);
            return Err(());
        }
        if sync_directory(parent).is_err() {
            let _ = fs::remove_file(&self.output);
            return Err(());
        }
        Ok(ArtifactSummary {
            length: bytes.len(),
            sha256: HOST_HASH(&[bytes]),
        })
    }
}

impl Profile22ReleaseChannel for LocalArtifactChannel<'_> {
    fn publish(&mut self, release: Profile22PublicRelease) {
        debug_assert!(self.summary.is_none() && self.outcome.is_none());
        match release {
            Profile22PublicRelease::Proof(mut bytes) => {
                match self.write_verified(&bytes) {
                    Ok(summary) => self.summary = Some(summary),
                    Err(()) => self.outcome = Some(LocalReleaseOutcome::Failed),
                }
                bytes.fill(0);
            }
            Profile22PublicRelease::Abort => {
                self.outcome = Some(LocalReleaseOutcome::Abort);
            }
        }
    }
}

#[cfg(unix)]
fn sync_directory(directory: &Path) -> std::io::Result<()> {
    File::open(directory)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_directory: &Path) -> std::io::Result<()> {
    Ok(())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

/// Frozen local artifact statement/witness.  The proof randomness is not
/// frozen: the production worker samples every attempt from the OS.
fn artifact_fixture() -> (AtomicPaymentStatementV3, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
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
        pool: [0x5a; 32],
        sequence: 73,
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

struct Arguments {
    output: PathBuf,
    nonce_ledger: PathBuf,
    release_epoch: SystemTime,
}

fn parse_arguments(mut values: impl Iterator<Item = String>) -> Option<Arguments> {
    let output = PathBuf::from(values.next()?);
    let nonce_ledger = PathBuf::from(values.next()?);
    let release_unix_seconds = values.next()?.parse::<u64>().ok()?;
    if values.next().is_some()
        || output.as_os_str().is_empty()
        || nonce_ledger.as_os_str().is_empty()
    {
        return None;
    }
    let release_epoch = UNIX_EPOCH.checked_add(Duration::from_secs(release_unix_seconds))?;
    Some(Arguments {
        output,
        nonce_ledger,
        release_epoch,
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn run(arguments: Arguments) -> Option<ArtifactSummary> {
    // Refuse a boundary that has already passed before doing any expensive
    // proof work.  The fixed-release controller still makes the authoritative
    // completion-before-boundary decision after the private worker returns.
    if arguments.release_epoch <= SystemTime::now() || arguments.output.exists() {
        return None;
    }
    let (statement, witness) = artifact_fixture();
    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(&arguments.nonce_ledger).ok()?;
    let mut controller = Profile22FixedReleaseController::new(arguments.release_epoch);
    let mut clock = Profile22SystemReleaseClock;

    // This is the only expensive call.  It owns fresh OS attempt entropy,
    // mining, the fixed sixteen-attempt cap, and the strong Good22 decision.
    let completion = build_hiding_atomic_state_only_profile22_first_good_v3(
        &statement,
        &witness,
        &mut nonce_store,
    );
    controller.record_first_good_completion(&clock, completion);

    let mut channel = LocalArtifactChannel::new(arguments.output, &statement);
    let _released = controller.release(&mut clock, &mut channel);
    channel.summary
}

fn main() -> ExitCode {
    let Some(arguments) = parse_arguments(env::args().skip(1)) else {
        return ExitCode::from(2);
    };
    let Some(summary) = run(arguments) else {
        return ExitCode::FAILURE;
    };
    println!("length={}", summary.length);
    println!("sha256={}", hex(&summary.sha256));
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temporary_path(label: &str) -> PathBuf {
        let mut random = [0u8; 16];
        getrandom::fill(&mut random).unwrap();
        let suffix = hex(&random);
        env::temp_dir().join(format!("aspis-{label}-{}-{suffix}", std::process::id()))
    }

    #[test]
    fn arguments_require_one_output_one_ledger_and_one_absolute_epoch() {
        assert!(parse_arguments(
            ["proof.bin", "nonce-ledger", "2000000000"]
                .into_iter()
                .map(str::to_owned)
        )
        .is_some());
        assert!(
            parse_arguments(["proof.bin", "nonce-ledger"].into_iter().map(str::to_owned)).is_none()
        );
        assert!(parse_arguments(
            ["proof.bin", "nonce-ledger", "not-an-epoch"]
                .into_iter()
                .map(str::to_owned)
        )
        .is_none());
    }

    #[test]
    fn abort_release_creates_no_artifact() {
        let output = temporary_path("profile22-local-abort");
        let (statement, _) = artifact_fixture();
        let mut channel = LocalArtifactChannel::new(output.clone(), &statement);
        channel.publish(Profile22PublicRelease::Abort);
        assert_eq!(channel.outcome, Some(LocalReleaseOutcome::Abort));
        assert!(channel.summary.is_none());
        assert!(!output.exists());
    }

    #[test]
    fn invalid_or_unmined_bytes_are_not_written() {
        let output = temporary_path("profile22-local-invalid");
        let (statement, _) = artifact_fixture();
        let mut channel = LocalArtifactChannel::new(output.clone(), &statement);
        channel.publish(Profile22PublicRelease::Proof(vec![0u8; 64]));
        assert_eq!(channel.outcome, Some(LocalReleaseOutcome::Failed));
        assert!(channel.summary.is_none());
        assert!(!output.exists());
    }
}
