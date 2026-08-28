//! Production-inactive honest integration for the eight-lane Pool forest.
//!
//! This module stops at the exact trace and residual boundary. It deliberately
//! does not construct a proof, select a profile, invoke a verifier, or alter
//! any wire/account format.

use aspis_statement::{
    pool_v1::{
        pair_constraint_residuals::PoolV1PairConstraintResidualErrorV1,
        pair_forest_constraint_residuals::{
            evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1,
            evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1,
            PoolV1PairForestConstraintResidualsV1,
            POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT,
            POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT,
        },
        pair_forest_trace::{
            compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
            PoolV1PairForestMergedC1CompilationV1, PoolV1PairForestPrivateTransferWitnessV1,
            PoolV1PairForestWithdrawalWitnessV1,
        },
        pair_trace::PoolV1PairTraceErrorV1,
        PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1, PoolV1PrivateTransferPublicV1,
        PoolV1WithdrawalPublicV1,
    },
    poseidon2::Digest,
};

pub const POOL_V1_PAIR_FOREST_OUTPUT_LANES_V1: u8 = 8;

/// The public output lane is the low three bits of the canonical first
/// nullifier limb. Production Pool code will eventually need one shared
/// account-level implementation; this inactive host helper fixes the intended
/// arithmetic without activating that plumbing.
#[inline]
pub const fn pool_v1_pair_forest_output_lane_from_nullifier_v1(nullifier: &Digest) -> u8 {
    (nullifier[0].0 as u8) & (POOL_V1_PAIR_FOREST_OUTPUT_LANES_V1 - 1)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestHonestErrorV1 {
    OutputLaneMismatch { expected: u8, provided: u8 },
    Trace(PoolV1PairTraceErrorV1),
    Residual(PoolV1PairConstraintResidualErrorV1),
    UnexpectedResidualCount { expected: usize, actual: usize },
    NonZeroResidual,
}

impl From<PoolV1PairTraceErrorV1> for PoolV1PairForestHonestErrorV1 {
    fn from(error: PoolV1PairTraceErrorV1) -> Self {
        Self::Trace(error)
    }
}

impl From<PoolV1PairConstraintResidualErrorV1> for PoolV1PairForestHonestErrorV1 {
    fn from(error: PoolV1PairConstraintResidualErrorV1) -> Self {
        Self::Residual(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestHonestCompilationV1 {
    pub output_lane: u8,
    pub compilation: PoolV1PairForestMergedC1CompilationV1,
    pub residuals: PoolV1PairForestConstraintResidualsV1,
}

fn require_output_lane(
    nullifier: &Digest,
    provided: u8,
) -> Result<(), PoolV1PairForestHonestErrorV1> {
    let expected = pool_v1_pair_forest_output_lane_from_nullifier_v1(nullifier);
    if provided != expected {
        return Err(PoolV1PairForestHonestErrorV1::OutputLaneMismatch { expected, provided });
    }
    Ok(())
}

fn finish(
    output_lane: u8,
    compilation: PoolV1PairForestMergedC1CompilationV1,
    residuals: PoolV1PairForestConstraintResidualsV1,
    expected_residual_count: usize,
) -> Result<PoolV1PairForestHonestCompilationV1, PoolV1PairForestHonestErrorV1> {
    let actual = residuals.residual_count();
    if actual != expected_residual_count {
        return Err(PoolV1PairForestHonestErrorV1::UnexpectedResidualCount {
            expected: expected_residual_count,
            actual,
        });
    }
    if !residuals.all_zero() {
        return Err(PoolV1PairForestHonestErrorV1::NonZeroResidual);
    }
    Ok(PoolV1PairForestHonestCompilationV1 {
        output_lane,
        compilation,
        residuals,
    })
}

/// Compile and check an honest transfer against a private 23-level forest
/// membership extension and the exact current state of the public output
/// lane. The existing pair-slot direction is carried by `witness.input.pair`;
/// its 20 lane levels and three private super-root levels are not inferred
/// from the public output lane.
pub fn compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairForestPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    output_lane: u8,
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestHonestCompilationV1, PoolV1PairForestHonestErrorV1> {
    require_output_lane(&public.nullifier, output_lane)?;
    let compilation = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        public,
        witness,
        context,
        output_lane_snapshot,
    )?;
    let residuals = evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
        public,
        &compilation.public_statement,
        &compilation.semantic_c1,
    )?;
    finish(
        output_lane,
        compilation,
        residuals,
        POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT,
    )
}

/// Withdrawal counterpart of
/// [`compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1`].
pub fn compile_and_check_pool_v1_pair_forest_withdrawal_honest_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairForestWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    output_lane: u8,
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestHonestCompilationV1, PoolV1PairForestHonestErrorV1> {
    require_output_lane(&public.nullifier, output_lane)?;
    let compilation = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
        public,
        witness,
        context,
        output_lane_snapshot,
    )?;
    let residuals = evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1(
        public,
        &compilation.public_statement,
        &compilation.semantic_c1,
    )?;
    finish(
        output_lane,
        compilation,
        residuals,
        POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT,
    )
}

const _: () = assert!(POOL_V1_PAIR_FOREST_OUTPUT_LANES_V1 == 1 << 3);

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        derive_owner_key,
        pool_v1::{
            pair_forest_trace::PoolV1PairForestInputNoteWitnessV1,
            pair_trace::PoolV1PairInputNoteWitnessV1, pool_v1_note_commitment, pool_v1_nullifier,
            pool_v1_tree_parent, IncrementalMerkleTreeV1, PoolV1MembershipWitnessV1,
            PoolV1OutputNoteWitnessV1, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1,
            PoolV1PaymentRuntimeBindingV1, PoolV1TreeError, POOL_V1_PAIR_TREE_DEPTH,
        },
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        let zero = [M31::ZERO; 8];
        let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
        roots[0] = pool_v1_tree_parent(&zero, &zero);
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
        }
        roots
    }

    fn snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn input_witness(value: u32) -> PoolV1PairForestInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, value, asset, &salt);
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value,
                pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
                    .unwrap(),
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            super_root_directions: [true, false, true],
        }
    }

    fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            let sibling = input.super_root_siblings[level];
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&sibling, &current)
            } else {
                pool_v1_tree_parent(&current, &sibling)
            };
        }
        current
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn context<'a>(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        asset_id: M31,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool,
                deployment_domain,
                anchor_sequence: 42,
                anchor_root: anchor,
                asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    #[derive(Clone, Copy)]
    struct TransferFixture {
        public: PoolV1PrivateTransferPublicV1,
        witness: PoolV1PairForestPrivateTransferWitnessV1,
        snapshot: PoolV1PairLiveSnapshotV1,
    }

    fn transfer_fixture() -> TransferFixture {
        let input = input_witness(1_000);
        let recipient = output(300, 600);
        let change = output(500, 400);
        let asset_id = M31(77);
        let anchor = global_anchor(&input);
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &recipient.owner_key,
                recipient.value,
                asset_id,
                &recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                asset_id,
                &change.salt,
            ),
        };
        TransferFixture {
            public,
            witness,
            snapshot: snapshot_at(public.pool, public.deployment_domain, 13),
        }
    }

    fn run_transfer(
        fixture: &TransferFixture,
    ) -> Result<PoolV1PairForestHonestCompilationV1, PoolV1PairForestHonestErrorV1> {
        let lane = pool_v1_pair_forest_output_lane_from_nullifier_v1(&fixture.public.nullifier);
        compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1(
            &fixture.public,
            &fixture.witness,
            context(
                fixture.public.pool,
                fixture.public.deployment_domain,
                fixture.public.anchor_root,
                fixture.public.asset_id,
            ),
            lane,
            fixture.snapshot,
        )
    }

    #[test]
    fn honest_transfer_and_withdrawal_compile_to_exact_zero_residuals() {
        let transfer = transfer_fixture();
        let checked = run_transfer(&transfer).unwrap();
        assert!(checked.residuals.all_zero());
        assert_eq!(
            checked.residuals.residual_count(),
            POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT
        );
        assert_eq!(
            checked.output_lane,
            pool_v1_pair_forest_output_lane_from_nullifier_v1(&transfer.public.nullifier)
        );
        assert_eq!(
            checked.compilation.public_statement.live_snapshot,
            transfer.snapshot
        );
        assert_eq!(
            checked
                .compilation
                .public_statement
                .candidate_afterstate
                .next_pair_index,
            transfer.snapshot.next_pair_index + 1
        );

        let input = input_witness(1_000);
        let change = output(700, 750);
        let asset_id = M31(77);
        let anchor = global_anchor(&input);
        let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change };
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9; 32],
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                asset_id,
                &change.salt,
            ),
        };
        let lane = pool_v1_pair_forest_output_lane_from_nullifier_v1(&public.nullifier);
        let checked = compile_and_check_pool_v1_pair_forest_withdrawal_honest_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            lane,
            snapshot_at(public.pool, public.deployment_domain, 13),
        )
        .unwrap();
        assert!(checked.residuals.all_zero());
        assert_eq!(
            checked.residuals.residual_count(),
            POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT
        );
    }

    #[test]
    fn each_private_super_root_bit_and_sibling_is_bound_to_the_historical_anchor() {
        let honest = transfer_fixture();
        for level in 0..3 {
            let mut changed = honest;
            changed.witness.input.super_root_directions[level] =
                !changed.witness.input.super_root_directions[level];
            assert_eq!(
                run_transfer(&changed),
                Err(PoolV1PairForestHonestErrorV1::Trace(
                    PoolV1PairTraceErrorV1::AnchorMismatch
                )),
                "direction level={level}"
            );

            let mut changed = honest;
            changed.witness.input.super_root_siblings[level][0] =
                changed.witness.input.super_root_siblings[level][0].add(M31::ONE);
            assert_eq!(
                run_transfer(&changed),
                Err(PoolV1PairForestHonestErrorV1::Trace(
                    PoolV1PairTraceErrorV1::AnchorMismatch
                )),
                "sibling level={level}"
            );
        }
    }

    #[test]
    fn public_anchor_output_lane_and_live_beforestate_mutations_fail_closed() {
        let honest = transfer_fixture();

        let mut changed = honest;
        changed.public.anchor_root[0] = changed.public.anchor_root[0].add(M31::ONE);
        assert_eq!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::AnchorMismatch
            ))
        );

        let expected = pool_v1_pair_forest_output_lane_from_nullifier_v1(&honest.public.nullifier);
        let wrong = (expected + 1) % POOL_V1_PAIR_FOREST_OUTPUT_LANES_V1;
        assert_eq!(
            compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1(
                &honest.public,
                &honest.witness,
                context(
                    honest.public.pool,
                    honest.public.deployment_domain,
                    honest.public.anchor_root,
                    honest.public.asset_id,
                ),
                wrong,
                honest.snapshot,
            ),
            Err(PoolV1PairForestHonestErrorV1::OutputLaneMismatch {
                expected,
                provided: wrong,
            })
        );

        let mut changed = honest;
        changed.snapshot.current_root[0] = changed.snapshot.current_root[0].add(M31::ONE);
        assert!(matches!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::Tree(PoolV1TreeError::RootMismatch)
            ))
        ));

        let mut changed = honest;
        // Index 13 has level two live in its binary frontier.
        changed.snapshot.frontier[2][0] = changed.snapshot.frontier[2][0].add(M31::ONE);
        assert!(matches!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::Tree(PoolV1TreeError::RootMismatch)
            ))
        ));

        let mut changed = honest;
        changed.snapshot.next_pair_index += 1;
        assert_eq!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::SnapshotBindingMismatch
            ))
        );
    }

    #[test]
    fn occupancy_and_value_mutations_fail_before_zero_residual_acceptance() {
        let honest = transfer_fixture();

        let mut changed = honest;
        changed.witness.input.pair.pair_leaf.second_occupied = M31::ZERO;
        assert_eq!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::PairLeaf(PoolV1PairLeafErrorV1::SentinelInverseMismatch)
            ))
        );

        let mut changed = honest;
        changed.witness.recipient.value += 1;
        assert_eq!(
            run_transfer(&changed),
            Err(PoolV1PairForestHonestErrorV1::Trace(
                PoolV1PairTraceErrorV1::Conservation
            ))
        );
    }
}
