use aspis_core::state_only_hiding::state_only_hiding_layout_factor_fingerprint_for_registry;
use aspis_statement::atomic_state_only_registry::{
    atomic_state_only_relation_free_mask_cells_v3,
    atomic_state_only_relation_free_mask_fingerprint_v3,
};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_active_rows_v3, PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
};

fn main() {
    let layout = atomic_state_only_relation_free_mask_fingerprint_v3().unwrap();
    let factors = state_only_hiding_layout_factor_fingerprint_for_registry(
        layout,
        PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
        true,
    );
    println!(
        "cells={}",
        atomic_state_only_relation_free_mask_cells_v3()
            .unwrap()
            .len()
    );
    println!("active={}", atomic_state_only_copy_active_rows_v3().len());
    println!("layout=0x{layout:016x}");
    println!(
        "active_fingerprint=0x{PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3:016x}"
    );
    println!("layout_factor=0x{factors:016x}");
}
