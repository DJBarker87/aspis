# Source-authentic v5 retry-cap correspondence

This bundle authenticates one narrow fact: the cap compiled from the real
feature-gated host source is `17`, exactly the cap used by
`AspisFormal.V5SelectionHidingAbort`. It does **not** prove the generic
`FnMut` retry loop, a production caller, entropy/domain separation, liveness,
or a non-abort probability.

## Result

The strongest theorem is:

```lean
theorem extracted_retry_cap_matches_maintained_model :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_HOST_GOOD_RETRY_CAP.val =
      AspisV5SelectionHidingAbort.spendRetryCap
```

It compiles under Lean 4.32 at default handwritten limits. Both exported
theorems have axiom closure exactly within
`{propext, Classical.choice, Quot.sound}`.

## Provenance

- source: `crates/aspis-prover/src/v5_real_host_proof.rs:73`
- source SHA-256:
  `691dedfdcfbe4e8570d2501a2c16813f5c7840cc4f64d68046403069c75b7dbc`
- matcher:
  `crate::v5_mask::real_host_proof::V5_REAL_HOST_GOOD_RETRY_CAP`
- LLBC SHA-256:
  `c08cdc3b274d4aa7595ee9846eb449dd8df74b2e6e1bb7bca378f351ad1c742b`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust: `nightly-2026-06-01`
- generated backend: Lean 4.31; replayed against the maintained Lean 4.32
  model using the audited Aeneas compatibility backend.

Extraction command:

```sh
cd /Users/dominic/ZK/crates/aspis-prover
CARGO_TARGET_DIR=/Users/dominic/ZK/aeneas-verif/retry-good/cargo-target \
RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
  /private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
    --preset=aeneas \
    --start-from='crate::v5_mask::real_host_proof::V5_REAL_HOST_GOOD_RETRY_CAP' \
    --dest-file='/Users/dominic/ZK/aeneas-verif/retry-good/llbc/retry_cap.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask
```

The LLBC has `has_errors = false`, two ordered declarations, and embeds bytes
identical to the current source. `replay-lean432.sh` rechecks that binding,
reconstructs the mechanical 4.31→4.32 normalization, compiles both modules,
and audits every exported theorem.

## Exact remaining blocker

The complete retry manager remains source-correspondence-open. Authentic
Charon extraction succeeds, but pinned Aeneas fails in
`InterpBorrows.ml:884` on the mutable callback borrowed across the loop. A
temporary tail-recursive diagnostic moved past that fixed point but failed in
`SymbolicToPureValues.ml:127` while translating the generic callback value; it
was reverted exactly. The maintained abstract cap-17 selection/abort law is
kernel-checked, but no report should describe that as an executable Rust-loop
proof.
