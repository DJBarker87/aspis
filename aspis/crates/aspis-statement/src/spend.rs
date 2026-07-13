//! Executable no-proof SpendV0-min evaluator.

use alloc::vec::Vec;

use aspis_core::field::{M31, P};

use crate::poseidon2::{hash_fields, Digest};

pub const VALUE_LIMIT: u32 = 1 << 30;
pub const RANGE_LIMB_BITS: u32 = 10;
pub const RANGE_LIMB_LIMIT: u16 = 1 << RANGE_LIMB_BITS;
pub const RANGE_LIMBS_PER_VALUE: usize = 3;

pub(crate) const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
pub(crate) const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
pub(crate) const DOMAIN_NOTE: M31 = M31(0x4153_0003);
/// Retired pre-v2 output domain. A commitment made with this domain is not a
/// leaf accepted by input-note membership and must never enter the pool.
#[cfg(test)]
const DOMAIN_OUTPUT_LEGACY: M31 = M31(0x4153_0004);
pub(crate) const DOMAIN_MERKLE_NODE: M31 = M31(0x4153_0005);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub siblings: Vec<Digest>,
    pub index: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendPublic {
    pub anchor: Digest,
    pub nullifier: Digest,
    pub output_commitment: Digest,
    pub asset_id: M31,
    pub fee: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendWitness {
    pub nullifier_key: Digest,
    pub input_salt: Digest,
    pub output_salt: Digest,
    pub output_owner_key: Digest,
    pub input_asset_id: M31,
    pub value: u32,
    pub value_out: u32,
    pub merkle_path: MerklePath,
}

/// Witness columns for the candidate 10-bit range-check lookup.
///
/// Six limbs replace the 64 Boolean bit constraints previously budgeted for
/// the two private values. The fee remains public and is range-checked by the
/// verifier program directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeLookupWitness {
    pub input_value_limbs: [u16; RANGE_LIMBS_PER_VALUE],
    pub output_value_limbs: [u16; RANGE_LIMBS_PER_VALUE],
}

impl RangeLookupWitness {
    pub fn from_spend(witness: &SpendWitness) -> Self {
        Self {
            input_value_limbs: decompose_10bit_limbs(witness.value),
            output_value_limbs: decompose_10bit_limbs(witness.value_out),
        }
    }
}

#[derive(Clone, Copy)]
pub struct EvaluationContext<'a> {
    pub merkle_depth: usize,
    /// The pool/program enforces this set on chain. Supplying it here makes
    /// double-spend behavior executable in the evaluator corpus.
    pub spent_nullifiers: &'a [Digest],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpendError {
    MerkleDepthMismatch,
    MerkleIndexOutOfRange,
    AssetMismatch,
    InputValueOutOfRange,
    OutputValueOutOfRange,
    FeeOutOfRange,
    BalanceMismatch,
    AnchorMismatch,
    NullifierMismatch,
    OutputCommitmentMismatch,
    NullifierAlreadySpent,
    RangeLookupLimbOutOfRange,
    RangeLookupReconstructionMismatch,
}

pub fn decompose_10bit_limbs(value: u32) -> [u16; RANGE_LIMBS_PER_VALUE] {
    let mask = u32::from(RANGE_LIMB_LIMIT) - 1;
    core::array::from_fn(|index| ((value >> (index as u32 * RANGE_LIMB_BITS)) & mask) as u16)
}

pub fn verify_10bit_range_lookup(
    value: u32,
    limbs: &[u16; RANGE_LIMBS_PER_VALUE],
) -> Result<(), SpendError> {
    if limbs.iter().any(|limb| *limb >= RANGE_LIMB_LIMIT) {
        return Err(SpendError::RangeLookupLimbOutOfRange);
    }

    let reconstructed = limbs.iter().enumerate().fold(0u32, |acc, (index, limb)| {
        acc + (u32::from(*limb) << (index as u32 * RANGE_LIMB_BITS))
    });
    if reconstructed != value {
        return Err(SpendError::RangeLookupReconstructionMismatch);
    }
    Ok(())
}

fn append_digest(output: &mut Vec<M31>, digest: &Digest) {
    output.extend_from_slice(digest);
}

pub fn derive_owner_key(nullifier_key: &Digest) -> Digest {
    derive_owner_key_with(nullifier_key, &mut hash_fields)
}

pub fn derive_nullifier(nullifier_key: &Digest, salt: &Digest) -> Digest {
    derive_nullifier_with(nullifier_key, salt, &mut hash_fields)
}

fn derive_owner_key_with<H>(nullifier_key: &Digest, hash: &mut H) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    hash(DOMAIN_OWNER_KEY, nullifier_key)
}

fn derive_nullifier_with<H>(nullifier_key: &Digest, salt: &Digest, hash: &mut H) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    let mut input = Vec::with_capacity(16);
    append_digest(&mut input, nullifier_key);
    append_digest(&mut input, salt);
    hash(DOMAIN_NULLIFIER, &input)
}

pub fn note_commitment(owner_key: &Digest, value: u32, asset_id: M31, salt: &Digest) -> Digest {
    note_commitment_with(owner_key, value, asset_id, salt, &mut hash_fields)
}

fn note_commitment_with<H>(
    owner_key: &Digest,
    value: u32,
    asset_id: M31,
    salt: &Digest,
    hash: &mut H,
) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    debug_assert!(value < P);
    let mut input = Vec::with_capacity(18);
    append_digest(&mut input, owner_key);
    input.push(M31(value));
    input.push(asset_id);
    append_digest(&mut input, salt);
    hash(DOMAIN_NOTE, &input)
}

pub fn output_commitment(owner_key: &Digest, value: u32, asset_id: M31, salt: &Digest) -> Digest {
    output_commitment_with(owner_key, value, asset_id, salt, &mut hash_fields)
}

/// Legacy, unspendable output-domain commitment retained only for migration
/// diagnostics. Production SpendV0 uses [`output_commitment`].
#[cfg(test)]
fn output_commitment_legacy(
    owner_key: &Digest,
    value: u32,
    asset_id: M31,
    salt: &Digest,
) -> Digest {
    output_commitment_with_domain(
        DOMAIN_OUTPUT_LEGACY,
        owner_key,
        value,
        asset_id,
        salt,
        &mut hash_fields,
    )
}

fn output_commitment_with<H>(
    owner_key: &Digest,
    value: u32,
    asset_id: M31,
    salt: &Digest,
    hash: &mut H,
) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    // V2 outputs are ordinary spendable note leaves. Domain-separating an
    // output from a future input makes the output permanently unspendable.
    output_commitment_with_domain(DOMAIN_NOTE, owner_key, value, asset_id, salt, hash)
}

fn output_commitment_with_domain<H>(
    domain: M31,
    owner_key: &Digest,
    value: u32,
    asset_id: M31,
    salt: &Digest,
    hash: &mut H,
) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    debug_assert!(value < P);
    let mut input = Vec::with_capacity(18);
    append_digest(&mut input, owner_key);
    input.push(M31(value));
    input.push(asset_id);
    append_digest(&mut input, salt);
    hash(domain, &input)
}

fn merkle_parent_with<H>(left: &Digest, right: &Digest, hash: &mut H) -> Digest
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    let mut input = Vec::with_capacity(16);
    append_digest(&mut input, left);
    append_digest(&mut input, right);
    hash(DOMAIN_MERKLE_NODE, &input)
}

pub fn merkle_root(leaf: Digest, path: &MerklePath) -> Result<Digest, SpendError> {
    merkle_root_with(leaf, path, &mut hash_fields)
}

fn merkle_root_with<H>(leaf: Digest, path: &MerklePath, hash: &mut H) -> Result<Digest, SpendError>
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    if path.siblings.len() < 32 && path.index >> path.siblings.len() != 0 {
        return Err(SpendError::MerkleIndexOutOfRange);
    }
    let mut current = leaf;
    for (level, sibling) in path.siblings.iter().enumerate() {
        current = if (path.index >> level) & 1 == 0 {
            merkle_parent_with(&current, sibling, hash)
        } else {
            merkle_parent_with(sibling, &current, hash)
        };
    }
    Ok(current)
}

fn validate_shape_and_asset(
    public: &SpendPublic,
    witness: &SpendWitness,
    context: EvaluationContext<'_>,
) -> Result<(), SpendError> {
    if witness.merkle_path.siblings.len() != context.merkle_depth {
        return Err(SpendError::MerkleDepthMismatch);
    }
    if context.merkle_depth < 32 && witness.merkle_path.index >> context.merkle_depth != 0 {
        return Err(SpendError::MerkleIndexOutOfRange);
    }
    if witness.input_asset_id != public.asset_id {
        return Err(SpendError::AssetMismatch);
    }
    Ok(())
}

fn evaluate_spend_after_value_checks(
    public: &SpendPublic,
    witness: &SpendWitness,
    context: EvaluationContext<'_>,
) -> Result<(), SpendError> {
    evaluate_spend_after_value_checks_with(public, witness, context, &mut hash_fields)
}

fn evaluate_spend_after_value_checks_with<H>(
    public: &SpendPublic,
    witness: &SpendWitness,
    context: EvaluationContext<'_>,
    hash: &mut H,
) -> Result<(), SpendError>
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    if public.fee >= VALUE_LIMIT {
        return Err(SpendError::FeeOutOfRange);
    }
    if witness.value_out.checked_add(public.fee) != Some(witness.value) {
        return Err(SpendError::BalanceMismatch);
    }

    let owner_key = derive_owner_key_with(&witness.nullifier_key, hash);
    let note = note_commitment_with(
        &owner_key,
        witness.value,
        witness.input_asset_id,
        &witness.input_salt,
        hash,
    );
    if merkle_root_with(note, &witness.merkle_path, hash)? != public.anchor {
        return Err(SpendError::AnchorMismatch);
    }

    if derive_nullifier_with(&witness.nullifier_key, &witness.input_salt, hash) != public.nullifier
    {
        return Err(SpendError::NullifierMismatch);
    }
    if output_commitment_with(
        &witness.output_owner_key,
        witness.value_out,
        public.asset_id,
        &witness.output_salt,
        hash,
    ) != public.output_commitment
    {
        return Err(SpendError::OutputCommitmentMismatch);
    }
    if context
        .spent_nullifiers
        .iter()
        .any(|spent| spent == &public.nullifier)
    {
        return Err(SpendError::NullifierAlreadySpent);
    }
    Ok(())
}

/// Evaluate every SpendV0-min economic relation without constructing a
/// proof. This reference path uses direct integer range checks.
pub fn evaluate_spend(
    public: &SpendPublic,
    witness: &SpendWitness,
    context: EvaluationContext<'_>,
) -> Result<(), SpendError> {
    validate_shape_and_asset(public, witness, context)?;
    if witness.value >= VALUE_LIMIT {
        return Err(SpendError::InputValueOutOfRange);
    }
    if witness.value_out >= VALUE_LIMIT {
        return Err(SpendError::OutputValueOutOfRange);
    }
    evaluate_spend_after_value_checks(public, witness, context)
}

/// Evaluate the same SpendV0-min statement with exact 10-bit limb lookup
/// semantics for the two private values.
///
/// This is still a no-proof semantic oracle. A future LogUp relation must
/// prove membership of each limb in the fixed `[0, 1024)` table and enforce
/// the two reconstruction equalities represented here.
pub fn evaluate_spend_with_range_lookup(
    public: &SpendPublic,
    witness: &SpendWitness,
    range_witness: &RangeLookupWitness,
    context: EvaluationContext<'_>,
) -> Result<(), SpendError> {
    validate_shape_and_asset(public, witness, context)?;
    verify_10bit_range_lookup(witness.value, &range_witness.input_value_limbs)?;
    verify_10bit_range_lookup(witness.value_out, &range_witness.output_value_limbs)?;
    evaluate_spend_after_value_checks(public, witness, context)
}

/// Internal evaluator seam used by the trace builder. It executes the same
/// shape, range, economic, and public-binding checks as
/// [`evaluate_spend_with_range_lookup`], while routing every hash invocation
/// through the supplied implementation.
pub(crate) fn evaluate_spend_with_range_lookup_and_hasher<H>(
    public: &SpendPublic,
    witness: &SpendWitness,
    range_witness: &RangeLookupWitness,
    context: EvaluationContext<'_>,
    hash: &mut H,
) -> Result<(), SpendError>
where
    H: FnMut(M31, &[M31]) -> Digest,
{
    validate_shape_and_asset(public, witness, context)?;
    verify_10bit_range_lookup(witness.value, &range_witness.input_value_limbs)?;
    verify_10bit_range_lookup(witness.value_out, &range_witness.output_value_limbs)?;
    evaluate_spend_after_value_checks_with(public, witness, context, hash)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DEPTH: usize = 20;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn fixture(value: u32, value_out: u32, fee: u32) -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let owner_key = derive_owner_key(&nullifier_key);
        let leaf = note_commitment(&owner_key, value, asset_id, &input_salt);
        let path = MerklePath {
            siblings: (0..DEPTH)
                .map(|level| digest(1_000 + level as u32 * 31))
                .collect(),
            index: 0x5a5a5 & ((1 << DEPTH) - 1),
        };
        let anchor = merkle_root(leaf, &path).unwrap();
        let public = SpendPublic {
            anchor,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path: path,
        };
        (public, witness)
    }

    fn evaluate(public: &SpendPublic, witness: &SpendWitness) -> Result<(), SpendError> {
        evaluate_spend(
            public,
            witness,
            EvaluationContext {
                merkle_depth: DEPTH,
                spent_nullifiers: &[],
            },
        )
    }

    fn evaluate_lookup(
        public: &SpendPublic,
        witness: &SpendWitness,
        range_witness: &RangeLookupWitness,
    ) -> Result<(), SpendError> {
        evaluate_spend_with_range_lookup(
            public,
            witness,
            range_witness,
            EvaluationContext {
                merkle_depth: DEPTH,
                spent_nullifiers: &[],
            },
        )
    }

    #[test]
    fn valid_spend_and_value_boundaries_accept() {
        for (value, value_out, fee) in [
            (0, 0, 0),
            (1, 0, 1),
            (VALUE_LIMIT - 1, VALUE_LIMIT - 1, 0),
            (VALUE_LIMIT - 1, VALUE_LIMIT - 2, 1),
        ] {
            let (public, witness) = fixture(value, value_out, fee);
            assert_eq!(evaluate(&public, &witness), Ok(()));
            assert_eq!(
                evaluate_lookup(&public, &witness, &RangeLookupWitness::from_spend(&witness)),
                Ok(())
            );
        }
    }

    #[test]
    fn field_wrap_inflation_rejects() {
        // This forged balance is true in M31: (P-1) + 2 == 1. It must fail
        // the integer range check before field arithmetic can launder it.
        assert_eq!(M31(P - 1).add(M31(2)), M31(1));
        let (public, witness) = fixture(1, P - 1, 2);
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::OutputValueOutOfRange)
        );
        assert!(
            evaluate_lookup(&public, &witness, &RangeLookupWitness::from_spend(&witness)).is_err()
        );
    }

    #[test]
    fn ten_bit_lookup_membership_and_reconstruction_have_teeth() {
        let (public, witness) = fixture(1_000_000, 999_999, 1);
        let canonical = RangeLookupWitness::from_spend(&witness);
        assert_eq!(evaluate_lookup(&public, &witness, &canonical), Ok(()));

        let mut non_member = canonical;
        non_member.input_value_limbs[0] = RANGE_LIMB_LIMIT;
        assert_eq!(
            evaluate_lookup(&public, &witness, &non_member),
            Err(SpendError::RangeLookupLimbOutOfRange)
        );

        let mut wrong_reconstruction = canonical;
        wrong_reconstruction.output_value_limbs[0] ^= 1;
        assert_eq!(
            evaluate_lookup(&public, &witness, &wrong_reconstruction),
            Err(SpendError::RangeLookupReconstructionMismatch)
        );

        // The low 30-bit decomposition of 2^30 is all zero. Exact
        // reconstruction is what stops truncation from becoming a range proof.
        let (public, witness) = fixture(VALUE_LIMIT, 0, 0);
        let truncated = RangeLookupWitness::from_spend(&witness);
        assert_eq!(truncated.input_value_limbs, [0; RANGE_LIMBS_PER_VALUE]);
        assert_eq!(
            evaluate_lookup(&public, &witness, &truncated),
            Err(SpendError::RangeLookupReconstructionMismatch)
        );
    }

    #[test]
    fn range_and_balance_attacks_reject() {
        let (public, witness) = fixture(VALUE_LIMIT, 0, 0);
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::InputValueOutOfRange)
        );

        let (mut public, mut witness) = fixture(VALUE_LIMIT - 1, VALUE_LIMIT - 1, 0);
        witness.value_out = VALUE_LIMIT;
        public.output_commitment = output_commitment(
            &witness.output_owner_key,
            witness.value_out,
            public.asset_id,
            &witness.output_salt,
        );
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::OutputValueOutOfRange)
        );

        let (mut public, witness) = fixture(7, 7, 0);
        public.fee = VALUE_LIMIT;
        assert_eq!(evaluate(&public, &witness), Err(SpendError::FeeOutOfRange));

        let (mut public, mut witness) = fixture(7, 6, 1);
        witness.value_out = 5;
        public.output_commitment = output_commitment(
            &witness.output_owner_key,
            5,
            public.asset_id,
            &witness.output_salt,
        );
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::BalanceMismatch)
        );
    }

    #[test]
    fn public_binding_and_membership_attacks_reject() {
        let (mut public, witness) = fixture(10, 9, 1);
        public.asset_id = public.asset_id.add(M31::ONE);
        assert_eq!(evaluate(&public, &witness), Err(SpendError::AssetMismatch));

        let (mut public, witness) = fixture(10, 9, 1);
        public.anchor[0] = public.anchor[0].add(M31::ONE);
        assert_eq!(evaluate(&public, &witness), Err(SpendError::AnchorMismatch));

        let (public, mut witness) = fixture(10, 9, 1);
        witness.merkle_path.siblings[3][2] = witness.merkle_path.siblings[3][2].add(M31::ONE);
        assert_eq!(evaluate(&public, &witness), Err(SpendError::AnchorMismatch));

        let (public, mut witness) = fixture(10, 9, 1);
        witness.nullifier_key[0] = witness.nullifier_key[0].add(M31::ONE);
        assert_eq!(evaluate(&public, &witness), Err(SpendError::AnchorMismatch));
    }

    #[test]
    fn nullifier_output_and_double_spend_attacks_reject() {
        let (mut public, witness) = fixture(10, 9, 1);
        public.nullifier[0] = public.nullifier[0].add(M31::ONE);
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::NullifierMismatch)
        );

        let (mut public, witness) = fixture(10, 9, 1);
        public.output_commitment[0] = public.output_commitment[0].add(M31::ONE);
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::OutputCommitmentMismatch)
        );

        let (public, witness) = fixture(10, 9, 1);
        assert_eq!(
            evaluate_spend(
                &public,
                &witness,
                EvaluationContext {
                    merkle_depth: DEPTH,
                    spent_nullifiers: &[public.nullifier],
                },
            ),
            Err(SpendError::NullifierAlreadySpent)
        );
    }

    #[test]
    fn v2_output_is_exactly_the_next_spend_note_leaf() {
        let owner = digest(7_001);
        let salt = digest(8_001);
        let value = 123_456;
        let asset = M31(91);
        assert_eq!(
            output_commitment(&owner, value, asset, &salt),
            note_commitment(&owner, value, asset, &salt)
        );
        assert_ne!(
            output_commitment_legacy(&owner, value, asset, &salt),
            note_commitment(&owner, value, asset, &salt)
        );
    }

    #[test]
    fn path_shape_attacks_reject() {
        let (public, mut witness) = fixture(10, 9, 1);
        witness.merkle_path.siblings.pop();
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::MerkleDepthMismatch)
        );

        let (public, mut witness) = fixture(10, 9, 1);
        witness.merkle_path.index = 1 << DEPTH;
        assert_eq!(
            evaluate(&public, &witness),
            Err(SpendError::MerkleIndexOutOfRange)
        );
    }
}
