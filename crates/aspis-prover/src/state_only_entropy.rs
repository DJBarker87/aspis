//! Production host-side entropy and crash-safe mask-attempt reservation.
//!
//! Proof construction must reserve the public attempt nonce durably before
//! deriving either the affine field masks or the private Merkle salts.  The
//! reservation is append-only: a failed build or process crash burns it.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use aspis_core::state_only_hiding::StateOnlyHidingContext;
use aspis_core::state_only_masked_switch_basis::PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT;
use aspis_core::HashFn;
use aspis_statement::{
    atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3,
    STATE_ONLY_POSEIDON_TRACE_ROWS,
};
use sha2::{Digest, Sha256};
use zeroize::{Zeroize, Zeroizing};

use crate::state_only_hiding::{
    build_atomic_state_only_mask_material_v3_from_entropy_ref, StateOnlyMaskBuildError,
    StateOnlyMaskMaterial, StateOnlyMaskNonceStore,
};

const ATTEMPT_RESERVATION_DOMAIN: &[u8] = b"aspis:state-only:attempt-reservation:v1";
const PROFILE21_ATTEMPT_BINDING_DOMAIN: &[u8] = b"aspis:state-only:profile21:attempt-binding:v1";
const PROFILE22_PRIVATE_ATTEMPT_BINDING_DOMAIN: &[u8] =
    b"aspis:state-only:profile22-private:attempt-binding:v1";
const PROFILE22_PRIVATE_WIRE_DESCRIPTOR: &[u8] =
    b"profile=22;depths=17,17,15,13,11;widths=416,128,64,64,64;trees=c1,c2,w1,w2,w3";
// The domain-separator byte strings below keep the release's original
// working-name spelling: they are hashed into deterministic-fixture entropy
// derivation, and the committed unmined fixture (and its pinned regression
// values) must stay reproducible byte-for-byte.
const SPEND_PRIVATE_ATTEMPT_BINDING_DOMAIN: &[u8] =
    b"aspis:state-only:profile23-zero-factor:attempt-binding:v1";
const SPEND_PRIVATE_WIRE_DESCRIPTOR: &[u8] =
    b"profile=23;generators=H26,G27,D28;factorD=0;selector=3;depths=17,17,15,13,11;widths=416,192,64,64,64;trees=c1,c2,w1,w2,w3";
const SPEND_D_SEED_DOMAIN: &[u8] = b"aspis:state-only:profile23:zero-factor-d-seed:v1";
const PROFILE21_SOURCE_SEED_DOMAIN: &[u8] = b"aspis:state-only:profile21:source-seed:v1";
const PROFILE21_SOURCE_EXPAND_DOMAIN: &[u8] = b"aspis:state-only:profile21:source-expand:v1";
const LEAF_SALT_DOMAIN: &[u8] = b"aspis:state-only:private-leaf-salt:v1";
const RESERVATION_MAGIC: &[u8; 16] = b"ASPIS-MASK-V1\0\0\0";
const ENTROPY_RETRY_LIMIT: usize = 16;

#[derive(Debug)]
pub enum StateOnlyAttemptEntropyError {
    Os(getrandom::Error),
    RepeatedZeroBlock,
}

impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self {
        Self::Os(value)
    }
}

/// Three independent 256-bit attempt values sampled from the operating
/// system. The public nonce is serialized; both private seeds are zeroized on
/// drop. The field seed and leaf-salt seed are never derived from one another.
pub struct StateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    field_mask_entropy: Zeroizing<[u8; 32]>,
    leaf_salt_seed: Zeroizing<[u8; 32]>,
}

/// A successful durable reservation and affine-mask build is the only way to
/// obtain this type. Private leaf salts therefore cannot be derived before
/// the public attempt nonce is burned.
pub struct ReservedStateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    precommit_binding: [u8; 32],
    leaf_salt_seed: Zeroizing<[u8; 32]>,
    source_mask_seed: Zeroizing<[u8; 32]>,
}

struct SensitiveQm31Vec(Vec<aspis_core::field::QM31>);

impl Drop for SensitiveQm31Vec {
    fn drop(&mut self) {
        for value in &mut self.0 {
            // SAFETY: the buffer is uniquely owned by this drop guard.
            unsafe { core::ptr::write_volatile(value, aspis_core::field::QM31::ZERO) };
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

impl StateOnlyAttemptSecrets {
    /// Construct fixed attempt secrets for a byte-exact profile-21 fixture.
    ///
    /// This API does not exist in a default or production build. Enabling the
    /// feature that exposes it is unsafe for proof generation because reusing
    /// these values reuses both affine-mask entropy and private-leaf salts.
    #[cfg(any(test, feature = "insecure-profile21-fixture"))]
    pub fn deterministic_profile21_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    /// Construct fixed attempt secrets for the byte-exact profile-22 fixture.
    /// This is deliberately absent from production builds.
    #[cfg(any(test, feature = "insecure-profile22-fixture"))]
    pub fn deterministic_profile22_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    /// Construct fixed attempt secrets for a byte-exact, nondefault
    /// spend fixture. This API is never present in a production build.
    #[cfg(any(test, feature = "insecure-spend-fixture"))]
    pub fn deterministic_spend_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    pub fn generate() -> Result<Self, StateOnlyAttemptEntropyError> {
        for _ in 0..ENTROPY_RETRY_LIMIT {
            let mut bytes = Zeroizing::new([0u8; 96]);
            getrandom::fill(bytes.as_mut())?;

            let mut mask_nonce = [0u8; 32];
            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            mask_nonce.copy_from_slice(&bytes[..32]);
            field_mask_entropy.copy_from_slice(&bytes[32..64]);
            leaf_salt_seed.copy_from_slice(&bytes[64..]);

            if mask_nonce != [0; 32] && *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32]
            {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }

    pub fn mask_nonce(&self) -> [u8; 32] {
        self.mask_nonce
    }

    /// Durably burn the public nonce, then build the atomic affine masks.
    /// Success returns the only type capable of deriving private leaf salts.
    /// Any later build failure drops and zeroizes both private seeds while the
    /// durable reservation remains present.
    pub fn reserve_and_build_atomic_mask_material_v3(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        // The ordinary builder retains its exact reserve-before-derivation
        // invariant. This single-use adapter acknowledges the reservation
        // already made durably above without touching storage a second time.
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_atomic_state_only_mask_material_v3_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            PROFILE21_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }
}

struct PreReservedNonce {
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    consumed: bool,
}

impl StateOnlyMaskNonceStore for PreReservedNonce {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        if self.consumed
            || statement_digest != self.statement_digest
            || mask_nonce != self.mask_nonce
        {
            return false;
        }
        self.consumed = true;
        true
    }
}

impl ReservedStateOnlyAttemptSecrets {
    pub fn mask_nonce(&self) -> [u8; 32] {
        self.mask_nonce
    }

    /// Derive one profile-21 private salt from the canonical attempt binding.
    /// Callers cannot omit the statement, mask/layout, source-basis or burned
    /// nonce fields from this binding.
    pub fn derive_profile21_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = profile21_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Derive one profile-22 private salt without importing profile 21's
    /// retired masked-switch basis into the attempt binding.
    pub fn derive_profile22_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding =
            profile22_private_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Spend salt binding includes the widened C2 descriptor and the
    /// q3 selector envelope, so no private opening can be replayed as p22.
    pub fn derive_spend_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = spend_private_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Expand one independently domain-separated full-domain QM31 D lane.
    /// Values on copy-inactive rows have zero sum, matching the raw-block
    /// balancing convention used by G/H1 while leaving every active row and
    /// all four tower coordinates private. D is not passed to the H oracle.
    pub fn derive_spend_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce
            || context.layout_factor_fingerprint
                != aspis_core::state_only_hiding::PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = spend_private_attempt_binding(hash, &self.precommit_binding, context);
        let mut expander = Profile21SourceExpander::new(
            hash,
            hash(&[
                SPEND_D_SEED_DOMAIN,
                &attempt_binding,
                self.source_mask_seed.as_ref(),
            ]),
        );
        let mut d = SensitiveQm31Vec(Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            d.0.push(expander.qm31()?);
        }
        let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
        for &row in atomic_state_only_copy_active_rows_v3() {
            active[usize::from(row)] = true;
        }
        let dependent = active
            .iter()
            .position(|is_active| !*is_active)
            .ok_or(StateOnlyMaskBuildError::Layout)?;
        let sum =
            d.0.iter()
                .copied()
                .enumerate()
                .filter(|(row, _)| !active[*row] && *row != dependent)
                .fold(aspis_core::field::QM31::ZERO, |sum, value| sum.add(value.1));
        d.0[dependent] = aspis_core::field::QM31::ZERO.sub(sum);
        Ok(core::mem::take(&mut d.0))
    }

    /// Deterministically expand the reserved attempt's field-mask domain into
    /// the two independent 35-QM31 logical source words `(X,F)`. This method
    /// exists only on the post-reservation typestate, so neither source word
    /// can be generated under an unburned public attempt nonce.
    pub fn derive_profile21_source_masks(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<
        ([aspis_core::field::QM31; 35], [aspis_core::field::QM31; 35]),
        StateOnlyMaskBuildError,
    > {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = profile21_attempt_binding(hash, &self.precommit_binding, context);
        let mut expander = Profile21SourceExpander::new(
            hash,
            hash(&[
                PROFILE21_SOURCE_SEED_DOMAIN,
                &attempt_binding,
                self.source_mask_seed.as_ref(),
            ]),
        );
        let mut x = [aspis_core::field::QM31::ZERO; 35];
        let mut f = [aspis_core::field::QM31::ZERO; 35];
        for value in x.iter_mut().chain(f.iter_mut()) {
            *value = expander.qm31()?;
        }
        Ok((x, f))
    }
}

struct Profile21SourceExpander {
    hash: HashFn,
    seed: Zeroizing<[u8; 32]>,
    counter: u64,
    block: [u8; 32],
    word: usize,
}

impl Profile21SourceExpander {
    fn new(hash: HashFn, seed: [u8; 32]) -> Self {
        Self {
            hash,
            seed: Zeroizing::new(seed),
            counter: 0,
            block: [0; 32],
            word: 8,
        }
    }

    fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            self.block = (self.hash)(&[
                PROFILE21_SOURCE_EXPAND_DOMAIN,
                self.seed.as_ref(),
                &self.counter.to_le_bytes(),
            ]);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }

    fn m31(&mut self) -> Result<aspis_core::field::M31, StateOnlyMaskBuildError> {
        for _ in 0..16 {
            let candidate = self.next_word() & 0x7fff_ffff;
            if candidate < aspis_core::field::P {
                return Ok(aspis_core::field::M31(candidate));
            }
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }

    fn qm31(&mut self) -> Result<aspis_core::field::QM31, StateOnlyMaskBuildError> {
        Ok(aspis_core::field::QM31 {
            c0: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
            c1: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
        })
    }
}

impl Drop for Profile21SourceExpander {
    fn drop(&mut self) {
        self.block.zeroize();
        self.counter.zeroize();
        self.word.zeroize();
    }
}

/// Canonical public binding shared by every field-mask and private-leaf
/// derivation in one profile-21 attempt.
pub fn profile21_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        PROFILE21_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        &PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT.to_le_bytes(),
    ])
}

/// Canonical profile-22 salt binding.  It deliberately has no source-code or
/// switch-basis input because profile 22 is the ordinary width-28 protocol.
pub fn profile22_private_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        PROFILE22_PRIVATE_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        PROFILE22_PRIVATE_WIRE_DESCRIPTOR,
    ])
}

pub fn spend_private_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        SPEND_PRIVATE_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        SPEND_PRIVATE_WIRE_DESCRIPTOR,
    ])
}

/// Append-only filesystem-backed nonce ledger. `create_new` is the
/// concurrency linearization point; file and directory `fsync` make a
/// successful reservation durable before mask derivation. Any I/O error is
/// fail-closed through the boolean trait and is retained for diagnostics.
pub struct DurableStateOnlyMaskNonceStore {
    directory: PathBuf,
    last_error: Option<io::ErrorKind>,
}

impl DurableStateOnlyMaskNonceStore {
    pub fn open(directory: impl AsRef<Path>) -> io::Result<Self> {
        fs::create_dir_all(directory.as_ref())?;
        let metadata = fs::metadata(directory.as_ref())?;
        if !metadata.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotADirectory,
                "mask nonce ledger path is not a directory",
            ));
        }
        Ok(Self {
            directory: directory.as_ref().to_path_buf(),
            last_error: None,
        })
    }

    pub fn last_error(&self) -> Option<io::ErrorKind> {
        self.last_error
    }

    fn reservation_path(&self, mask_nonce: &[u8; 32]) -> PathBuf {
        // The nonce is burned globally within this wallet ledger, even if a
        // caller tries to reuse it under a different statement digest.
        let mut hasher = Sha256::new();
        hasher.update(ATTEMPT_RESERVATION_DOMAIN);
        hasher.update(mask_nonce);
        let digest: [u8; 32] = hasher.finalize().into();
        let mut name = String::with_capacity(69);
        for byte in digest {
            use std::fmt::Write as _;
            write!(&mut name, "{byte:02x}").expect("writing to String cannot fail");
        }
        name.push_str(".burn");
        self.directory.join(name)
    }

    pub fn reserve_fallible(
        &mut self,
        statement_digest: [u8; 32],
        mask_nonce: [u8; 32],
    ) -> io::Result<bool> {
        self.last_error = None;
        let path = self.reservation_path(&mask_nonce);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        let mut file = match options.open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error),
        };

        // A partially written file is still a burned nonce. Never remove it
        // on failure.
        file.write_all(RESERVATION_MAGIC)?;
        file.write_all(&statement_digest)?;
        file.write_all(&mask_nonce)?;
        file.sync_all()?;
        sync_directory(&self.directory)?;
        Ok(true)
    }
}

impl StateOnlyMaskNonceStore for DurableStateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        match self.reserve_fallible(statement_digest, mask_nonce) {
            Ok(reserved) => reserved,
            Err(error) => {
                self.last_error = Some(error.kind());
                false
            }
        }
    }
}

#[cfg(unix)]
fn sync_directory(directory: &Path) -> io::Result<()> {
    File::open(directory)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_directory: &Path) -> io::Result<()> {
    // `create_new` remains atomic. Platforms without directory-fsync support
    // must place this ledger on a storage layer whose metadata is durable.
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;

    fn temporary_ledger(label: &str) -> PathBuf {
        let mut random = [0u8; 16];
        getrandom::fill(&mut random).unwrap();
        let suffix = random
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        std::env::temp_dir().join(format!("aspis-{label}-{}-{suffix}", std::process::id()))
    }

    #[test]
    fn os_attempt_separates_field_and_leaf_domains() {
        let attempt = StateOnlyAttemptSecrets::generate().unwrap();
        let nonce = attempt.mask_nonce();
        assert_ne!(nonce, [0; 32]);
        let context = StateOnlyHidingContext::atomic_v3([0x11; 32], nonce);
        let mut store = crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let (attempt, _material) = attempt
            .reserve_and_build_atomic_mask_material_v3(
                crate::HOST_HASH,
                [0x21; 32],
                context,
                &mut store,
            )
            .unwrap();
        let a = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 1, 7)
            .unwrap();
        let b = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 2, 7)
            .unwrap();
        let c = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 1, 8)
            .unwrap();
        let profile22 = attempt
            .derive_profile22_leaf_salt(crate::HOST_HASH, context, 1, 7)
            .unwrap();
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(a, profile22);
        let (x, f) = attempt
            .derive_profile21_source_masks(crate::HOST_HASH, context)
            .unwrap();
        let (x_again, f_again) = attempt
            .derive_profile21_source_masks(crate::HOST_HASH, context)
            .unwrap();
        assert_eq!(x, x_again);
        assert_eq!(f, f_again);
        assert_ne!(x, f);
        assert!(x
            .iter()
            .all(|value| *value != aspis_core::field::QM31::ZERO));

        let wrong_context = StateOnlyHidingContext::atomic_v3([0x11; 32], [0x99; 32]);
        assert_eq!(
            attempt
                .derive_profile21_leaf_salt(crate::HOST_HASH, wrong_context, 1, 7)
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout
        );
    }

    #[test]
    fn durable_ledger_burns_nonce_across_reopen_and_statements() {
        let directory = temporary_ledger("nonce-reopen");
        let nonce = [0xa5; 32];
        let mut first = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
        assert!(first.reserve([1; 32], nonce));
        assert_eq!(first.last_error(), None);
        drop(first);

        let mut reopened = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
        assert!(!reopened.reserve([1; 32], nonce));
        assert!(!reopened.reserve([2; 32], nonce));
        assert_eq!(reopened.last_error(), None);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn concurrent_reservation_has_exactly_one_winner() {
        let directory = temporary_ledger("nonce-race");
        fs::create_dir_all(&directory).unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let mut handles = Vec::new();
        for statement in [[3u8; 32], [4u8; 32]] {
            let directory = directory.clone();
            let barrier = Arc::clone(&barrier);
            handles.push(thread::spawn(move || {
                let mut store = DurableStateOnlyMaskNonceStore::open(directory).unwrap();
                barrier.wait();
                store.reserve(statement, [0x7b; 32])
            }));
        }
        barrier.wait();
        let winners = handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .filter(|won| *won)
            .count();
        assert_eq!(winners, 1);
        fs::remove_dir_all(directory).unwrap();
    }
}
