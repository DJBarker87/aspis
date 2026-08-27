//! Production-inactive verifier seam for the conservative staged pair route.
//!
//! The byte parser and accepted-result transport are complete. The actual
//! seven-lane semantic terminal, Merkle authentication, and one-fold relation
//! are intentionally not stubbed: until they exist, no dispatch instruction
//! can construct `AcceptedV7StagedPairAfterstateV1` or emit return data.

use aspis_core::{v6_onefold::V6WireError, v7_staged_pair::V7StagedPairOneFoldWire};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_live_snapshot_v1, encode_pool_v1_pair_verifier_result_v1,
    PoolV1PairAfterstateV1, PoolV1PairLiveSnapshotErrorV1, PoolV1PairLiveSnapshotV1,
    PoolV1PairVerifierResultErrorV1, POOL_V1_PAIR_VERIFIER_RESULT_BYTES,
};
use solana_program::program;

pub const V7_STAGED_PAIR_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-staged-pair-seven-c2-late-snapshot:asvq-v1";
/// SHA-256 of `V7_STAGED_PAIR_PROFILE_BINDING_PREIMAGE`.
pub const V7_STAGED_PAIR_PROFILE_BINDING: [u8; 32] = [
    0xd6, 0x31, 0x5f, 0x90, 0xf5, 0x4f, 0xd7, 0x39, 0x76, 0x7e, 0x7a, 0x18, 0xf4, 0xa6, 0x62, 0x2b,
    0xab, 0xeb, 0xf5, 0x31, 0xbb, 0x3e, 0x5e, 0xba, 0x32, 0x35, 0x06, 0x63, 0xf6, 0xb6, 0xac, 0x94,
];
pub const V7_STAGED_PAIR_RELEASE_BINDING_PREIMAGE: &[u8] =
    b"aspis:verifier:v7:tag73:staged-pair:seven-c2:late-snapshot:proof34658:result688:v1";
/// SHA-256 of `V7_STAGED_PAIR_RELEASE_BINDING_PREIMAGE`.
pub const V7_STAGED_PAIR_RELEASE_BINDING: [u8; 32] = [
    0xa6, 0xe7, 0x6b, 0x24, 0xd1, 0x9f, 0x3a, 0x73, 0xcc, 0x87, 0x0b, 0x5a, 0x1d, 0xa4, 0x97, 0x03,
    0x77, 0xeb, 0xa2, 0x19, 0xcc, 0xe8, 0xb9, 0x31, 0x4b, 0x05, 0x73, 0xb6, 0xf3, 0xee, 0xe8, 0xbb,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7StagedPairProfileErrorV1 {
    Wire(V6WireError),
    Snapshot(PoolV1PairLiveSnapshotErrorV1),
    Result(PoolV1PairVerifierResultErrorV1),
    AfterstateIndexMismatch,
}

impl From<V6WireError> for V7StagedPairProfileErrorV1 {
    fn from(error: V6WireError) -> Self {
        Self::Wire(error)
    }
}

impl From<PoolV1PairLiveSnapshotErrorV1> for V7StagedPairProfileErrorV1 {
    fn from(error: PoolV1PairLiveSnapshotErrorV1) -> Self {
        Self::Snapshot(error)
    }
}

impl From<PoolV1PairVerifierResultErrorV1> for V7StagedPairProfileErrorV1 {
    fn from(error: PoolV1PairVerifierResultErrorV1) -> Self {
        Self::Result(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedV7StagedPairInputsV1<'a> {
    pub wire: V7StagedPairOneFoldWire<'a>,
    pub live_snapshot: PoolV1PairLiveSnapshotV1,
}

pub fn parse_v7_staged_pair_inputs_v1<'a>(
    proof: &'a [u8],
    frontier_nodes: usize,
    live_snapshot: &[u8],
) -> Result<ParsedV7StagedPairInputsV1<'a>, V7StagedPairProfileErrorV1> {
    Ok(ParsedV7StagedPairInputsV1 {
        wire: V7StagedPairOneFoldWire::parse(proof, frontier_nodes)?,
        live_snapshot: decode_pool_v1_pair_live_snapshot_v1(live_snapshot)?,
    })
}

/// Opaque capability produced only by this crate after the future full staged
/// verifier has accepted the exact proof/snapshot pair. Keeping the field
/// private prevents a caller outside the verifier crate from manufacturing a
/// successful 688-byte result.
pub(crate) struct AcceptedV7StagedPairAfterstateV1 {
    afterstate: PoolV1PairAfterstateV1,
}

/// Final source seam for the future full verifier. It checks the exact
/// one-pair index transition; the caller must have checked every cryptographic
/// equation before invoking it.
pub(crate) fn accept_v7_staged_pair_after_full_verification_v1(
    live_snapshot: &PoolV1PairLiveSnapshotV1,
    afterstate: PoolV1PairAfterstateV1,
) -> Result<AcceptedV7StagedPairAfterstateV1, V7StagedPairProfileErrorV1> {
    if live_snapshot.next_pair_index.checked_add(1) != Some(afterstate.next_pair_index) {
        return Err(V7StagedPairProfileErrorV1::AfterstateIndexMismatch);
    }
    Ok(AcceptedV7StagedPairAfterstateV1 { afterstate })
}

pub(crate) fn encode_accepted_v7_staged_pair_result_v1(
    accepted: AcceptedV7StagedPairAfterstateV1,
) -> Result<[u8; POOL_V1_PAIR_VERIFIER_RESULT_BYTES], V7StagedPairProfileErrorV1> {
    let mut result = [0u8; POOL_V1_PAIR_VERIFIER_RESULT_BYTES];
    encode_pool_v1_pair_verifier_result_v1(&accepted.afterstate, &mut result)?;
    Ok(result)
}

/// The only return-data helper accepts the opaque post-verification token.
/// No current instruction reaches it because the seven-lane verifier is not
/// yet complete or registered.
pub(crate) fn emit_accepted_v7_staged_pair_result_v1(
    accepted: AcceptedV7StagedPairAfterstateV1,
) -> Result<(), V7StagedPairProfileErrorV1> {
    let result = encode_accepted_v7_staged_pair_result_v1(accepted)?;
    program::set_return_data(&result);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::{field::M31, v7_staged_pair::V7_STAGED_PAIR_MAX_BODY_BYTES};
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_live_snapshot_v1, POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
        POOL_V1_PAIR_TREE_DEPTH,
    };
    use std::vec;

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|lane| M31(seed + lane as u32 + 1))
    }

    fn snapshot() -> PoolV1PairLiveSnapshotV1 {
        PoolV1PairLiveSnapshotV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            sequence: 73,
            next_pair_index: 73,
            current_root: digest(100),
            frontier: core::array::from_fn(|level| digest(200 + 10 * level as u32)),
        }
    }

    #[test]
    fn staged_profile_is_fresh_and_parses_exact_maximum_grammar() {
        assert_ne!(
            V7_STAGED_PAIR_PROFILE_BINDING,
            crate::v7_pool_dispatch::V7_POOL_TAG73_PROFILE_BINDING
        );
        assert_ne!(
            V7_STAGED_PAIR_RELEASE_BINDING,
            crate::v7_transaction::V7_RELEASE_BINDING
        );
        let snapshot = snapshot();
        let mut snapshot_bytes = [0u8; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
        encode_pool_v1_pair_live_snapshot_v1(&snapshot, &mut snapshot_bytes).unwrap();
        let proof = vec![0u8; V7_STAGED_PAIR_MAX_BODY_BYTES];
        let parsed = parse_v7_staged_pair_inputs_v1(&proof, 203, &snapshot_bytes).unwrap();
        assert_eq!(parsed.live_snapshot, snapshot);
        assert_eq!(parsed.wire.query(0).unwrap().c2_packed.len(), 434);
    }

    #[test]
    fn result_capability_requires_exact_one_pair_index_step() {
        let snapshot = snapshot();
        let afterstate = PoolV1PairAfterstateV1 {
            next_pair_index: 74,
            root: digest(500),
            frontier: core::array::from_fn(|level| digest(600 + 10 * level as u32)),
        };
        let accepted =
            accept_v7_staged_pair_after_full_verification_v1(&snapshot, afterstate).unwrap();
        let encoded = encode_accepted_v7_staged_pair_result_v1(accepted).unwrap();
        assert_eq!(encoded.len(), 688);

        let wrong = PoolV1PairAfterstateV1 {
            next_pair_index: 75,
            ..afterstate
        };
        assert_eq!(
            accept_v7_staged_pair_after_full_verification_v1(&snapshot, wrong).err(),
            Some(V7StagedPairProfileErrorV1::AfterstateIndexMismatch)
        );
        assert_eq!(POOL_V1_PAIR_TREE_DEPTH, 20);
    }
}
