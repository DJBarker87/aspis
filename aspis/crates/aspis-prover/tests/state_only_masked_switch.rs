use aspis_core::state_only_masked_switch::{
    verify_state_only_masked_switch, verify_state_only_masked_switch_diagnostic_unmined,
    MaskedSwitchVerifyError, MASKED_SWITCH_QUERY_COUNT,
};
use sha2::{Digest, Sha256};

const FIXTURE: &[u8] =
    include_bytes!("../../../results/stage2/proofs/state_only_masked_switch_p21_unmined.bin");
const STATEMENT: [u8; 32] = [
    0x01, 0xd5, 0x13, 0x3c, 0x1b, 0xa1, 0xd9, 0xf0, 0x65, 0xa9, 0xcf, 0x98, 0x79, 0xaf, 0x31, 0x50,
    0x8c, 0x32, 0x76, 0x75, 0xd7, 0x3b, 0x06, 0x73, 0x6e, 0x03, 0x0a, 0x50, 0x82, 0x87, 0x24, 0x09,
];

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

#[test]
fn profile21_masked_switch_fixture_and_teeth() {
    let schedule = verify_state_only_masked_switch_diagnostic_unmined(FIXTURE, &STATEMENT, hash)
        .expect("p21 masked-switch fixture");
    assert_eq!(schedule.queries.len(), MASKED_SWITCH_QUERY_COUNT);
    assert_eq!(
        verify_state_only_masked_switch(FIXTURE, &STATEMENT, hash),
        Err(MaskedSwitchVerifyError::SourceWork),
        "the production API must not inherit the tag45 unmined bypass",
    );

    // Byte classes cover every causal transcript field, both authenticated
    // leaf lanes, and both independent Merkle frontiers.
    let teeth = [
        (0usize, "version"),
        (1, "xf root"),
        (33, "tX"),
        (49, "muF"),
        (65, "source work"),
        (73, "U coefficients"),
        (633, "translated root"),
        (665, "beta0"),
        (681, "beta1"),
        (697, "final work"),
        (705, "query count"),
        (707, "packed q X lane"),
        (771, "packed q F lane"),
        (835, "packed q U lane"),
        (3783, "xf frontier"),
        (11_115, "u frontier"),
    ];
    for (offset, label) in teeth {
        let mut corrupted = FIXTURE.to_vec();
        corrupted[offset] ^= 1;
        assert!(
            verify_state_only_masked_switch_diagnostic_unmined(&corrupted, &STATEMENT, hash)
                .is_err(),
            "corruption escaped: {label} at {offset}",
        );
    }

    // Every disclosed U coefficient is transcript-bound. The verifier then
    // checks its literal evaluation at every authenticated q value.
    for coefficient in 0..35 {
        let mut corrupted = FIXTURE.to_vec();
        corrupted[73 + 16 * coefficient] ^= 1;
        assert!(
            verify_state_only_masked_switch_diagnostic_unmined(&corrupted, &STATEMENT, hash)
                .is_err(),
            "disclosed U coefficient {coefficient} escaped",
        );
    }

    let mut swapped_targets = FIXTURE.to_vec();
    let t_x = swapped_targets[33..49].to_vec();
    let mu_f = swapped_targets[49..65].to_vec();
    swapped_targets[33..49].copy_from_slice(&mu_f);
    swapped_targets[49..65].copy_from_slice(&t_x);
    assert!(
        verify_state_only_masked_switch_diagnostic_unmined(&swapped_targets, &STATEMENT, hash,)
            .is_err(),
        "target-order transcript tooth escaped",
    );

    let mut trailing = FIXTURE.to_vec();
    trailing.push(0);
    assert_eq!(
        verify_state_only_masked_switch_diagnostic_unmined(&trailing, &STATEMENT, hash),
        Err(MaskedSwitchVerifyError::TrailingBytes),
    );
}
