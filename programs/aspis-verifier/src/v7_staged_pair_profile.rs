//! Production-inactive verifier seam for the merged-C1 pair route.
//!
//! The byte parser and accepted-result transport are complete. The actual
//! pair semantic terminal, Merkle authentication, and one-fold relation
//! are intentionally not stubbed: until they exist, no dispatch instruction
//! can construct `AcceptedV7StagedPairAfterstateV1` or emit return data.

use aspis_core::{
    v6_onefold::V6WireError,
    v7_staged_pair::{V7StagedPairOneFoldWire, V7_STAGED_PAIR_MAX_BODY_BYTES},
};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_live_snapshot_v1, decode_pool_v1_pair_verified_afterstate_v1,
    encode_pool_v1_pair_verified_afterstate_v1, PoolV1PairLatePublicStatementErrorV1,
    PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotErrorV1, PoolV1PairVerifiedAfterstateV1,
    PoolV1PairVerifierTransportErrorV1, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
};
use solana_program::program;

pub const V7_STAGED_PAIR_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-pair-merged-c1-pre-root:logical29:proof30504:asja688:v3";
/// SHA-256 of `V7_STAGED_PAIR_PROFILE_BINDING_PREIMAGE`.
pub const V7_STAGED_PAIR_PROFILE_BINDING: [u8; 32] = [
    0xfd, 0x74, 0x55, 0xc8, 0xd1, 0x05, 0x7e, 0x3e, 0xe0, 0x86, 0x6c, 0x01, 0x4e, 0xf4, 0x23, 0xba,
    0xe9, 0xde, 0x18, 0x9d, 0x55, 0x3a, 0x3d, 0xd4, 0xdd, 0xcb, 0x45, 0xf9, 0x58, 0xe7, 0x6f, 0xa9,
];
pub const V7_STAGED_PAIR_RELEASE_BINDING_PREIMAGE: &[u8] =
    b"aspis:verifier:v7:tag73:pair-merged-c1:pre-root-public-statement:logical29:proof30504:result688:v3";
/// SHA-256 of `V7_STAGED_PAIR_RELEASE_BINDING_PREIMAGE`.
pub const V7_STAGED_PAIR_RELEASE_BINDING: [u8; 32] = [
    0x58, 0x3c, 0x24, 0x1a, 0x62, 0x89, 0xb0, 0x9c, 0x93, 0x60, 0xc4, 0xdc, 0x5e, 0x93, 0xf0, 0x07,
    0xb5, 0x2c, 0x06, 0x4b, 0x4b, 0x8d, 0xe8, 0xac, 0x90, 0x16, 0x35, 0xdd, 0x85, 0x62, 0x0e, 0x12,
];

/// Profile-specific bytes stored before the compact proof in the finalized
/// verifier-owned upload payload. The generic 40-byte ASPU header is unchanged.
pub const V7_STAGED_PAIR_PROOF_METADATA_BYTES: usize = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
pub const V7_STAGED_PAIR_MAX_UPLOAD_PAYLOAD_BYTES: usize =
    V7_STAGED_PAIR_PROOF_METADATA_BYTES + V7_STAGED_PAIR_MAX_BODY_BYTES;
pub const V7_STAGED_PAIR_MAX_PROOF_ACCOUNT_BYTES: usize =
    crate::lifecycle::PROOF_ACCOUNT_HEADER_LEN + V7_STAGED_PAIR_MAX_UPLOAD_PAYLOAD_BYTES;
/// The terminal instruction carries no copy of the old snapshot or ASJA.
pub const V7_STAGED_PAIR_TERMINAL_INSTRUCTION_METADATA_BYTES: usize = 0;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7StagedPairProfileErrorV1 {
    Wire(V6WireError),
    Snapshot(PoolV1PairLiveSnapshotErrorV1),
    LateStatement(PoolV1PairLatePublicStatementErrorV1),
    Result(PoolV1PairVerifierTransportErrorV1),
}

impl From<V6WireError> for V7StagedPairProfileErrorV1 {
    fn from(error: V6WireError) -> Self {
        Self::Wire(error)
    }
}

impl From<PoolV1PairLatePublicStatementErrorV1> for V7StagedPairProfileErrorV1 {
    fn from(error: PoolV1PairLatePublicStatementErrorV1) -> Self {
        Self::LateStatement(error)
    }
}

impl From<PoolV1PairLiveSnapshotErrorV1> for V7StagedPairProfileErrorV1 {
    fn from(error: PoolV1PairLiveSnapshotErrorV1) -> Self {
        Self::Snapshot(error)
    }
}

impl From<PoolV1PairVerifierTransportErrorV1> for V7StagedPairProfileErrorV1 {
    fn from(error: PoolV1PairVerifierTransportErrorV1) -> Self {
        Self::Result(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedV7StagedPairInputsV1<'a> {
    pub wire: V7StagedPairOneFoldWire<'a>,
    pub late_statement: PoolV1PairLatePublicStatementV1,
}

pub fn parse_v7_staged_pair_inputs_v1<'a>(
    finalized_upload_payload: &'a [u8],
    frontier_nodes: usize,
    account_derived_live_snapshot: &[u8],
) -> Result<ParsedV7StagedPairInputsV1<'a>, V7StagedPairProfileErrorV1> {
    if finalized_upload_payload.len() < V7_STAGED_PAIR_PROOF_METADATA_BYTES {
        return Err(V7StagedPairProfileErrorV1::Wire(V6WireError::WrongLength));
    }
    let (candidate_bytes, proof) =
        finalized_upload_payload.split_at(V7_STAGED_PAIR_PROOF_METADATA_BYTES);
    let live_snapshot = decode_pool_v1_pair_live_snapshot_v1(account_derived_live_snapshot)?;
    let candidate_afterstate = decode_pool_v1_pair_verified_afterstate_v1(candidate_bytes)?;
    if live_snapshot.next_pair_index.checked_add(1) != Some(candidate_afterstate.next_pair_index) {
        return Err(V7StagedPairProfileErrorV1::LateStatement(
            PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch,
        ));
    }
    Ok(ParsedV7StagedPairInputsV1 {
        wire: V7StagedPairOneFoldWire::parse(proof, frontier_nodes)?,
        late_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot,
            candidate_afterstate,
        },
    })
}

/// Opaque capability produced only by this crate after the future full staged
/// verifier has accepted the exact proof/snapshot pair. Keeping the field
/// private prevents a caller outside the verifier crate from manufacturing a
/// successful 688-byte result.
pub(crate) struct AcceptedV7StagedPairAfterstateV1 {
    afterstate: PoolV1PairVerifiedAfterstateV1,
}

/// Final source seam for the future full verifier. It checks the exact
/// public candidate bound before the C1 root; the caller must have checked every
/// cryptographic equation before invoking it. One pair index step represents
/// two commitment slots for a private transfer.
pub(crate) fn accept_v7_staged_pair_after_full_verification_v1(
    late_statement: &PoolV1PairLatePublicStatementV1,
) -> AcceptedV7StagedPairAfterstateV1 {
    AcceptedV7StagedPairAfterstateV1 {
        afterstate: late_statement.candidate_afterstate,
    }
}

pub(crate) fn encode_accepted_v7_staged_pair_result_v1(
    accepted: AcceptedV7StagedPairAfterstateV1,
) -> Result<[u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES], V7StagedPairProfileErrorV1> {
    Ok(encode_pool_v1_pair_verified_afterstate_v1(
        &accepted.afterstate,
    )?)
}

/// The only return-data helper accepts the opaque post-verification token.
/// No current instruction reaches it because the merged-C1 pair verifier is not
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
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_live_snapshot_v1, PoolV1PairLiveSnapshotV1,
        POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
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
        assert_eq!(
            solana_program::hash::hash(V7_STAGED_PAIR_PROFILE_BINDING_PREIMAGE).to_bytes(),
            V7_STAGED_PAIR_PROFILE_BINDING
        );
        assert_eq!(
            solana_program::hash::hash(V7_STAGED_PAIR_RELEASE_BINDING_PREIMAGE).to_bytes(),
            V7_STAGED_PAIR_RELEASE_BINDING
        );
        assert_ne!(
            V7_STAGED_PAIR_PROFILE_BINDING,
            crate::v7_pool_dispatch::V7_POOL_TAG73_PROFILE_BINDING
        );
        assert_ne!(
            V7_STAGED_PAIR_RELEASE_BINDING,
            crate::v7_transaction::V7_RELEASE_BINDING
        );
        let snapshot = snapshot();
        let candidate_afterstate = PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 74,
            next_root: digest(500),
            next_frontier: core::array::from_fn(|level| digest(600 + 10 * level as u32)),
        };
        let statement = PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate,
        };
        let mut snapshot_bytes = [0u8; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
        encode_pool_v1_pair_live_snapshot_v1(&snapshot, &mut snapshot_bytes).unwrap();
        let mut upload = vec![0u8; V7_STAGED_PAIR_MAX_UPLOAD_PAYLOAD_BYTES];
        upload[..V7_STAGED_PAIR_PROOF_METADATA_BYTES].copy_from_slice(
            &encode_pool_v1_pair_verified_afterstate_v1(&candidate_afterstate).unwrap(),
        );
        let parsed = parse_v7_staged_pair_inputs_v1(&upload, 203, &snapshot_bytes).unwrap();
        assert_eq!(parsed.late_statement, statement);
        assert_eq!(parsed.wire.query(0).unwrap().c2_packed.len(), 186);

        let accepted = accept_v7_staged_pair_after_full_verification_v1(&parsed.late_statement);
        let encoded = encode_accepted_v7_staged_pair_result_v1(accepted).unwrap();
        assert_eq!(encoded.len(), POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
        assert_eq!(&encoded[..], &upload[..V7_STAGED_PAIR_PROOF_METADATA_BYTES]);
        assert_eq!(V7_STAGED_PAIR_MAX_UPLOAD_PAYLOAD_BYTES, 31_192);
        assert_eq!(V7_STAGED_PAIR_MAX_PROOF_ACCOUNT_BYTES, 31_232);
        assert_eq!(V7_STAGED_PAIR_TERMINAL_INSTRUCTION_METADATA_BYTES, 0);

        let mut wrong_index = upload;
        wrong_index[8..16].copy_from_slice(&75u64.to_le_bytes());
        assert_eq!(
            parse_v7_staged_pair_inputs_v1(&wrong_index, 203, &snapshot_bytes).err(),
            Some(V7StagedPairProfileErrorV1::LateStatement(
                PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch
            ))
        );
    }

    #[test]
    fn result_capability_echoes_only_the_pre_root_candidate() {
        let snapshot = snapshot();
        let afterstate = PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 74,
            next_root: digest(500),
            next_frontier: core::array::from_fn(|level| digest(600 + 10 * level as u32)),
        };
        let statement = PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: afterstate,
        };
        let accepted = accept_v7_staged_pair_after_full_verification_v1(&statement);
        let encoded = encode_accepted_v7_staged_pair_result_v1(accepted).unwrap();
        assert_eq!(encoded.len(), 688);
        assert_eq!(POOL_V1_PAIR_TREE_DEPTH, 20);
    }
}
