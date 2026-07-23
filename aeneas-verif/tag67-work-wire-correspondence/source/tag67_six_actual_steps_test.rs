#[path = "tag67_six_actual_steps.rs"]
mod six;

#[test]
fn success_emits_exact_six_positioned_steps() {
    let trace = six::tag67_proof_six_actual_steps(
        true, true, true, true, true, true,
        10, 11, 12, 13, 14, 15,
    )
    .unwrap();
    assert_eq!(trace.map(|step| step.position), [0, 1, 2, 3, 4, 5]);
    assert_eq!(trace.map(|step| step.bits), [37, 34, 33, 30, 25, 32]);
    assert_eq!(trace.map(|step| step.label), [28, 20, 20, 20, 20, 5]);
    assert_eq!(trace.map(|step| step.fold_round), [255, 0, 1, 2, 3, 255]);
    assert_eq!(trace.map(|step| step.nonce), [10, 11, 12, 13, 14, 15]);
    assert_eq!(trace.map(|step| step.next_action), [0, 1, 2, 3, 4, 5]);
}

#[test]
fn every_failed_position_short_circuits() {
    for failed in 0..6 {
        let mut ok = [true; 6];
        ok[failed] = false;
        assert!(six::tag67_proof_six_actual_steps(
            ok[0], ok[1], ok[2], ok[3], ok[4], ok[5],
            10, 11, 12, 13, 14, 15,
        )
        .is_none());
    }
}

#[test]
fn fold_round_out_of_range_returns_before_event() {
    assert!(six::tag67_proof_check_and_absorb_fold(true, 4, 17).is_none());
}
