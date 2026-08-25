//! Read-only Pool V1 historical-anchor authentication.
//!
//! This layer binds an exact versioned statement envelope to the canonical
//! Pool state, the exact indexed root in its canonical history-page PDA and an
//! expected verifier profile/release.  It does not check nullifier freshness,
//! invoke a verifier, append outputs, or expose an instruction.

use aspis_statement::pool_v1::{
    decode_historical_anchor_envelope_v1, root_history_location, HistoricalAnchorEnvelopeV1,
    PoolV1TransitionKind,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::{
    error::PoolV1ProgramError,
    history::{
        read_retained_root, require_program_owned, require_root_page_address,
        validate_root_page_bytes, RootPageHeaderV1,
    },
    state::{pool_v1_state_address, CanonicalPoolStateV1, PoolStateV1},
};

/// Exact transition/profile/release selected by the separately authenticated
/// verifier-registry layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoricalAnchorAuthorizationV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
}

/// Evidence that one envelope names the exact retained Pool root and expected
/// transition/profile/release.  Possessing this value is not proof acceptance
/// and grants no state-write authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedHistoricalAnchorV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: aspis_statement::poseidon2::Digest,
    pub nullifier: aspis_statement::poseidon2::Digest,
    pub transition_kind: PoolV1TransitionKind,
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
}

/// Sealed evidence that the exact anchor page passed one complete canonical
/// validation against an already authenticated Pool state.  The private
/// fields prevent callers from manufacturing a page-validation capability.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PrevalidatedHistoricalAnchorV1 {
    authenticated: AuthenticatedHistoricalAnchorV1,
    history_page: Pubkey,
    header: RootPageHeaderV1,
}

impl PrevalidatedHistoricalAnchorV1 {
    pub(crate) fn authenticated(self) -> AuthenticatedHistoricalAnchorV1 {
        self.authenticated
    }

    pub(crate) fn history_page(self) -> Pubkey {
        self.history_page
    }

    pub(crate) fn header(self) -> RootPageHeaderV1 {
        self.header
    }
}

fn load_canonical_pool_state(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
) -> Result<PoolStateV1, ProgramError> {
    require_program_owned(pool_account, program_id)?;
    if pool_account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let state = {
        let data = pool_account.try_borrow_data()?;
        PoolStateV1::decode(&data, pool_account.key)?
    };
    let asset_mint = Pubkey::new_from_array(state.identity.asset_mint);
    if pool_account.key != &pool_v1_state_address(program_id, &asset_mint).0 {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    Ok(state)
}

fn bind_envelope_to_state_and_selection(
    pool_account: &AccountInfo,
    state: &PoolStateV1,
    envelope: &HistoricalAnchorEnvelopeV1,
    expected: HistoricalAnchorAuthorizationV1,
) -> Result<(), ProgramError> {
    if envelope.pool != pool_account.key.to_bytes()
        || envelope.pool != state.identity.pool
        || envelope.deployment_domain != state.identity.deployment_domain
    {
        return Err(PoolV1ProgramError::HistoricalAnchorIdentityMismatch.into());
    }
    if envelope.transition_kind != expected.transition_kind
        || envelope.verifier_profile != expected.verifier_profile
        || envelope.verifier_release != expected.verifier_release
    {
        return Err(PoolV1ProgramError::HistoricalAnchorSelectionMismatch.into());
    }
    if envelope.anchor_sequence > state.current_root_sequence() {
        return Err(PoolV1ProgramError::HistoricalAnchorInFuture.into());
    }
    Ok(())
}

fn require_history_page_privileges(
    history_page_account: &AccountInfo,
    anchor_page_number: u64,
    current_page_number: u64,
) -> Result<(), ProgramError> {
    if history_page_account.is_signer
        || (anchor_page_number != current_page_number && history_page_account.is_writable)
    {
        return Err(PoolV1ProgramError::InvalidHistoricalAnchorPage.into());
    }
    Ok(())
}

/// Authenticate one exact historical anchor without modifying any account.
///
/// `pool_account` may be writable because the atomic spend handler also appends
/// to it. An older history page must be read-only. The page that
/// contains the current root may be writable because it can also be the
/// transition's current output page; the later append kernel independently
/// enforces the precise page writability required by that transition.
fn authenticate_historical_anchor_against_state_v1(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    history_page_account: &AccountInfo,
    envelope_bytes: &[u8],
    expected: HistoricalAnchorAuthorizationV1,
    state: &PoolStateV1,
) -> Result<PrevalidatedHistoricalAnchorV1, ProgramError> {
    let envelope = decode_historical_anchor_envelope_v1(envelope_bytes)
        .map_err(|_| PoolV1ProgramError::InvalidHistoricalAnchorEnvelope)?;
    bind_envelope_to_state_and_selection(pool_account, state, &envelope, expected)?;

    let location = root_history_location(envelope.anchor_sequence);
    let current_location = root_history_location(state.current_root_sequence());
    require_program_owned(history_page_account, program_id)?;
    require_history_page_privileges(
        history_page_account,
        location.page_number,
        current_location.page_number,
    )?;
    require_root_page_address(
        program_id,
        pool_account.key,
        location.page_number,
        history_page_account,
    )?;
    let (header, retained_root) = {
        let data = history_page_account.try_borrow_data()?;
        let header = validate_root_page_bytes(&data, pool_account.key, location.page_number)
            .map_err(|_| ProgramError::from(PoolV1ProgramError::InvalidHistoricalAnchorPage))?;
        let retained = read_retained_root(&data, header, envelope.anchor_sequence)
            .map_err(|_| PoolV1ProgramError::InvalidHistoricalAnchorPage)?;
        (header, retained)
    };
    if retained_root != envelope.anchor_root {
        return Err(PoolV1ProgramError::HistoricalAnchorRootMismatch.into());
    }

    Ok(PrevalidatedHistoricalAnchorV1 {
        authenticated: AuthenticatedHistoricalAnchorV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            transition_kind: envelope.transition_kind,
            verifier_profile: envelope.verifier_profile,
            verifier_release: envelope.verifier_release,
        },
        history_page: *history_page_account.key,
        header,
    })
}

/// Processor-only adapter that carries forward its already complete canonical
/// Pool decode.  The Pool account is not exposed to an intervening CPI before
/// this call, so repeating the depth-20 reconstruction would prove the same
/// fact twice.
pub(crate) fn authenticate_historical_anchor_after_prevalidated_state_v1(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    history_page_account: &AccountInfo,
    envelope_bytes: &[u8],
    expected: HistoricalAnchorAuthorizationV1,
    state: &CanonicalPoolStateV1,
) -> Result<PrevalidatedHistoricalAnchorV1, ProgramError> {
    state.require_same_writable_account(program_id, pool_account)?;
    authenticate_historical_anchor_against_state_v1(
        program_id,
        pool_account,
        history_page_account,
        envelope_bytes,
        expected,
        state.as_state(),
    )
}

pub fn authenticate_historical_anchor_v1(
    program_id: &Pubkey,
    pool_account: &AccountInfo,
    history_page_account: &AccountInfo,
    envelope_bytes: &[u8],
    expected: HistoricalAnchorAuthorizationV1,
) -> Result<AuthenticatedHistoricalAnchorV1, ProgramError> {
    let state = load_canonical_pool_state(program_id, pool_account)?;
    authenticate_historical_anchor_against_state_v1(
        program_id,
        pool_account,
        history_page_account,
        envelope_bytes,
        expected,
        &state,
    )
    .map(PrevalidatedHistoricalAnchorV1::authenticated)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        empty_roots::POOL_V1_EMPTY_ROOTS,
        state::{PoolInitializationV1, POOL_V1_STATE_ACCOUNT_BYTES},
        LEGACY_SPL_TOKEN_PROGRAM_ID,
    };
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{encode_historical_anchor_envelope_v1, RootHistoryPageV1, VerifierPolicyV1},
        poseidon2::Digest,
    };
    use solana_program::clock::Epoch;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 29 * index as u32))
    }

    fn initialization(mint: &Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: [6u8; 32],
                registry_authority: [7u8; 32],
                policy_binding: [8u8; 32],
            },
        }
    }

    fn expected() -> HistoricalAnchorAuthorizationV1 {
        HistoricalAnchorAuthorizationV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            verifier_profile: [9u8; 32],
            verifier_release: [10u8; 32],
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    #[derive(Clone)]
    struct Fixture {
        program_id: Pubkey,
        pool_key: Pubkey,
        page_key: Pubkey,
        pool_data: [u8; POOL_V1_STATE_ACCOUNT_BYTES],
        page_data: std::vec::Vec<u8>,
        first_root: Digest,
        current_root: Digest,
    }

    fn fixture() -> Fixture {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint).0;
        let base = PoolStateV1::genesis(&pool_key, initialization(&mint)).unwrap();
        let (tree, first) = base
            .tree
            .append_one_with_empty_roots(digest(100), &POOL_V1_EMPTY_ROOTS)
            .unwrap();
        let (tree, second) = tree
            .append_one_with_empty_roots(digest(200), &POOL_V1_EMPTY_ROOTS)
            .unwrap();
        let state = PoolStateV1 { tree, ..base };
        let mut page = RootHistoryPageV1::genesis(
            pool_key.to_bytes(),
            POOL_V1_EMPTY_ROOTS[aspis_statement::pool_v1::POOL_V1_TREE_DEPTH],
        );
        page.push(1, first.root).unwrap();
        page.push(2, second.root).unwrap();
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        Fixture {
            program_id,
            pool_key,
            page_key,
            pool_data: state.encode().unwrap(),
            page_data: page.encode().unwrap().to_vec(),
            first_root: first.root,
            current_root: second.root,
        }
    }

    fn envelope(fixture: &Fixture, sequence: u64, root: Digest) -> HistoricalAnchorEnvelopeV1 {
        HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: fixture.pool_key.to_bytes(),
            deployment_domain: [5u8; 32],
            anchor_sequence: sequence,
            anchor_root: root,
            nullifier: digest(300),
            verifier_profile: [9u8; 32],
            verifier_release: [10u8; 32],
        }
    }

    fn authenticate(
        fixture: &mut Fixture,
        envelope: HistoricalAnchorEnvelopeV1,
        expected: HistoricalAnchorAuthorizationV1,
        page_key: Pubkey,
        page_signer: bool,
        page_writable: bool,
    ) -> Result<AuthenticatedHistoricalAnchorV1, ProgramError> {
        let encoded = encode_historical_anchor_envelope_v1(&envelope).unwrap();
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let pool = account(
            &fixture.pool_key,
            &fixture.program_id,
            &mut pool_lamports,
            &mut fixture.pool_data,
            false,
            true,
        );
        let page = account(
            &page_key,
            &fixture.program_id,
            &mut page_lamports,
            &mut fixture.page_data,
            page_signer,
            page_writable,
        );
        authenticate_historical_anchor_v1(&fixture.program_id, &pool, &page, &encoded, expected)
    }

    #[test]
    fn retained_sequence_one_authenticates_after_sequence_two_is_appended() {
        let mut fixture = fixture();
        let envelope = envelope(&fixture, 1, fixture.first_root);
        let page_key = fixture.page_key;
        let before_pool = fixture.pool_data;
        let before_page = fixture.page_data.clone();
        let authenticated =
            authenticate(&mut fixture, envelope, expected(), page_key, false, false).unwrap();
        assert_eq!(authenticated.anchor_sequence, 1);
        assert_eq!(authenticated.anchor_root, fixture.first_root);
        assert_ne!(authenticated.anchor_root, fixture.current_root);
        assert_eq!(fixture.pool_data, before_pool);
        assert_eq!(fixture.page_data, before_page);
    }

    #[test]
    fn exact_current_root_also_authenticates_without_mutation() {
        let mut fixture = fixture();
        let envelope = envelope(&fixture, 2, fixture.current_root);
        let page_key = fixture.page_key;
        let authenticated =
            authenticate(&mut fixture, envelope, expected(), page_key, false, true).unwrap();
        assert_eq!(authenticated.anchor_sequence, 2);
        assert_eq!(authenticated.anchor_root, fixture.current_root);
    }

    #[test]
    fn prevalidated_state_adapter_is_exact_and_still_rejects_page_corruption() {
        let base = fixture();
        let selected = envelope(&base, 1, base.first_root);
        let encoded = encode_historical_anchor_envelope_v1(&selected).unwrap();

        let mut standalone = base.clone();
        let standalone_page_key = standalone.page_key;
        let standalone_result = authenticate(
            &mut standalone,
            selected,
            expected(),
            standalone_page_key,
            false,
            false,
        )
        .unwrap();

        let mut prevalidated = base.clone();
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let canonical = {
            let pool = account(
                &prevalidated.pool_key,
                &prevalidated.program_id,
                &mut pool_lamports,
                &mut prevalidated.pool_data,
                false,
                true,
            );
            CanonicalPoolStateV1::decode_account(&prevalidated.program_id, &pool).unwrap()
        };
        let sealed = {
            let pool = account(
                &prevalidated.pool_key,
                &prevalidated.program_id,
                &mut pool_lamports,
                &mut prevalidated.pool_data,
                false,
                true,
            );
            let page = account(
                &prevalidated.page_key,
                &prevalidated.program_id,
                &mut page_lamports,
                &mut prevalidated.page_data,
                false,
                false,
            );
            authenticate_historical_anchor_after_prevalidated_state_v1(
                &prevalidated.program_id,
                &pool,
                &page,
                &encoded,
                expected(),
                &canonical,
            )
            .unwrap()
        };
        assert_eq!(sealed.authenticated(), standalone_result);
        assert_eq!(sealed.history_page(), prevalidated.page_key);
        assert_eq!(sealed.header().filled, 3);

        let mut corrupt = base;
        let last = corrupt.page_data.len() - 1;
        corrupt.page_data[last] = 1;
        let mut corrupt_pool_lamports = 1;
        let mut corrupt_page_lamports = 1;
        let canonical = {
            let pool = account(
                &corrupt.pool_key,
                &corrupt.program_id,
                &mut corrupt_pool_lamports,
                &mut corrupt.pool_data,
                false,
                true,
            );
            CanonicalPoolStateV1::decode_account(&corrupt.program_id, &pool).unwrap()
        };
        let result = {
            let pool = account(
                &corrupt.pool_key,
                &corrupt.program_id,
                &mut corrupt_pool_lamports,
                &mut corrupt.pool_data,
                false,
                true,
            );
            let page = account(
                &corrupt.page_key,
                &corrupt.program_id,
                &mut corrupt_page_lamports,
                &mut corrupt.page_data,
                false,
                false,
            );
            authenticate_historical_anchor_after_prevalidated_state_v1(
                &corrupt.program_id,
                &pool,
                &page,
                &encoded,
                expected(),
                &canonical,
            )
        };
        assert_eq!(
            result,
            Err(PoolV1ProgramError::InvalidHistoricalAnchorPage.into())
        );
    }

    #[test]
    fn wrong_root_domain_selection_future_or_page_fails_closed() {
        let base = fixture();
        let cases = [
            (
                HistoricalAnchorEnvelopeV1 {
                    anchor_root: digest(999),
                    ..envelope(&base, 1, base.first_root)
                },
                expected(),
                base.page_key,
                PoolV1ProgramError::HistoricalAnchorRootMismatch.into(),
            ),
            (
                HistoricalAnchorEnvelopeV1 {
                    deployment_domain: [99u8; 32],
                    ..envelope(&base, 1, base.first_root)
                },
                expected(),
                base.page_key,
                PoolV1ProgramError::HistoricalAnchorIdentityMismatch.into(),
            ),
            (
                envelope(&base, 1, base.first_root),
                HistoricalAnchorAuthorizationV1 {
                    verifier_release: [99u8; 32],
                    ..expected()
                },
                base.page_key,
                PoolV1ProgramError::HistoricalAnchorSelectionMismatch.into(),
            ),
            (
                envelope(&base, 3, base.current_root),
                expected(),
                base.page_key,
                PoolV1ProgramError::HistoricalAnchorInFuture.into(),
            ),
            (
                envelope(&base, 1, base.first_root),
                expected(),
                Pubkey::new_unique(),
                PoolV1ProgramError::InvalidRootPageAddress.into(),
            ),
        ];
        for (envelope, expected, page_key, error) in cases {
            let mut fixture = base.clone();
            let before_pool = fixture.pool_data;
            let before_page = fixture.page_data.clone();
            assert_eq!(
                authenticate(&mut fixture, envelope, expected, page_key, false, false),
                Err(error)
            );
            assert_eq!(fixture.pool_data, before_pool);
            assert_eq!(fixture.page_data, before_page);
        }
    }

    #[test]
    fn history_page_signer_is_rejected_without_writes() {
        let mut fixture = fixture();
        let envelope = envelope(&fixture, 1, fixture.first_root);
        let page_key = fixture.page_key;
        let before_pool = fixture.pool_data;
        let before_page = fixture.page_data.clone();
        assert_eq!(
            authenticate(&mut fixture, envelope, expected(), page_key, true, false),
            Err(PoolV1ProgramError::InvalidHistoricalAnchorPage.into())
        );
        assert_eq!(fixture.pool_data, before_pool);
        assert_eq!(fixture.page_data, before_page);
    }

    #[test]
    fn older_page_writable_privilege_is_rejected() {
        let mut fixture = fixture();
        let mut page_lamports = 1;
        let page = account(
            &fixture.page_key,
            &fixture.program_id,
            &mut page_lamports,
            &mut fixture.page_data,
            false,
            true,
        );
        assert_eq!(
            require_history_page_privileges(&page, 0, 1),
            Err(PoolV1ProgramError::InvalidHistoricalAnchorPage.into())
        );
    }
}
