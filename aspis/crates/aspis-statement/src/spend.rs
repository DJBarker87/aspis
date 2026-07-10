//! Executable no-proof SpendV0-min evaluator.

use alloc::vec::Vec;

use aspis_core::field::{M31, P};

use crate::poseidon2::{hash_fields, Digest};

pub const VALUE_LIMIT: u32 = 1 << 30;

const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
const DOMAIN_NOTE: M31 = M31(0x4153_0003);
const DOMAIN_OUTPUT: M31 = M31(0x4153_0004);
const DOMAIN_MERKLE_NODE: M31 = M31(0x4153_0005);

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
}

fn append_digest(output: &mut Vec<M31>, digest: &Digest) {
    output.extend_from_slice(digest);
}

pub fn derive_owner_key(nullifier_key: &Digest) -> Digest {
    hash_fields(DOMAIN_OWNER_KEY, nullifier_key)
}

pub fn derive_nullifier(nullifier_key: &Digest, salt: &Digest) -> Digest {
    let mut input = Vec::with_capacity(16);
    append_digest(&mut input, nullifier_key);
    append_digest(&mut input, salt);
    hash_fields(DOMAIN_NULLIFIER, &input)
}

pub fn note_commitment(owner_key: &Digest, value: u32, asset_id: M31, salt: &Digest) -> Digest {
    debug_assert!(value < P);
    let mut input = Vec::with_capacity(18);
    append_digest(&mut input, owner_key);
    input.push(M31(value));
    input.push(asset_id);
    append_digest(&mut input, salt);
    hash_fields(DOMAIN_NOTE, &input)
}

pub fn output_commitment(owner_key: &Digest, value: u32, asset_id: M31, salt: &Digest) -> Digest {
    debug_assert!(value < P);
    let mut input = Vec::with_capacity(18);
    append_digest(&mut input, owner_key);
    input.push(M31(value));
    input.push(asset_id);
    append_digest(&mut input, salt);
    hash_fields(DOMAIN_OUTPUT, &input)
}

fn merkle_parent(left: &Digest, right: &Digest) -> Digest {
    let mut input = Vec::with_capacity(16);
    append_digest(&mut input, left);
    append_digest(&mut input, right);
    hash_fields(DOMAIN_MERKLE_NODE, &input)
}

pub fn merkle_root(leaf: Digest, path: &MerklePath) -> Result<Digest, SpendError> {
    if path.siblings.len() < 32 && path.index >> path.siblings.len() != 0 {
        return Err(SpendError::MerkleIndexOutOfRange);
    }
    let mut current = leaf;
    for (level, sibling) in path.siblings.iter().enumerate() {
        current = if (path.index >> level) & 1 == 0 {
            merkle_parent(&current, sibling)
        } else {
            merkle_parent(sibling, &current)
        };
    }
    Ok(current)
}

/// Evaluate every SpendV0-min economic relation without constructing a
/// proof. Success means the witness satisfies the statement and the supplied
/// pool context has not already consumed its nullifier.
pub fn evaluate_spend(
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
    if witness.value >= VALUE_LIMIT {
        return Err(SpendError::InputValueOutOfRange);
    }
    if witness.value_out >= VALUE_LIMIT {
        return Err(SpendError::OutputValueOutOfRange);
    }
    if public.fee >= VALUE_LIMIT {
        return Err(SpendError::FeeOutOfRange);
    }
    if witness.value_out.checked_add(public.fee) != Some(witness.value) {
        return Err(SpendError::BalanceMismatch);
    }

    let owner_key = derive_owner_key(&witness.nullifier_key);
    let note = note_commitment(
        &owner_key,
        witness.value,
        witness.input_asset_id,
        &witness.input_salt,
    );
    if merkle_root(note, &witness.merkle_path)? != public.anchor {
        return Err(SpendError::AnchorMismatch);
    }

    if derive_nullifier(&witness.nullifier_key, &witness.input_salt) != public.nullifier {
        return Err(SpendError::NullifierMismatch);
    }
    if output_commitment(
        &witness.output_owner_key,
        witness.value_out,
        public.asset_id,
        &witness.output_salt,
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
