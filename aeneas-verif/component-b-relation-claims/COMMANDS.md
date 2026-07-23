# Reproduction commands

## Charon

```sh
cd /Users/dominic/ZK/crates/aspis-prover
RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
CARGO_TARGET_DIR=/Users/dominic/ZK/aeneas-verif/component-b-relation-claims/cargo-target-field \
/private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
  --preset=aeneas \
  --start-from='aspis_prover::v5_mask::split_layer_zero::evaluate_component_b_relation_claims' \
  --include='aspis_core::field' \
  --dest-file='/Users/dominic/ZK/aeneas-verif/component-b-relation-claims/llbc/component_b_relation_claims.llbc' \
  -- --release --locked -p aspis-prover --features v5-mask
```

## Aeneas

```sh
/private/tmp/aspis-aeneas-tools.aTcyie/aeneas/bin/aeneas \
  -backend lean \
  /Users/dominic/ZK/aeneas-verif/component-b-relation-claims/llbc/component_b_relation_claims.llbc \
  -dest /Users/dominic/ZK/aeneas-verif/component-b-relation-claims/generated \
  -loops-to-rec \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar
```

The heartbeat and recursion options above belong only to raw mechanical
generation. They do not occur in accepted handwritten or merged proof files.

## Targeted Rust verification

```sh
cd /Users/dominic/ZK
cargo check --release --locked -p aspis-prover --features v5-mask
cargo test --release --locked -p aspis-prover --features v5-mask \
  component_b_relation_claims_select_exact_c2_lane_one -- --nocapture
```

## Lean 4.32 direct replay

The maintained MLE prerequisites are built by
`aeneas-verif/multilinear-eval/check-lean432.sh`. With their OLean directory
first in `LEAN_PATH`, the three final modules are compiled as follows:

```sh
aeneas_path=$(cd /private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean \
  && lake env printenv LEAN_PATH)
aspis_path=$(cd /Users/dominic/ZK/AspisFormal && lake env printenv LEAN_PATH)
work=/private/tmp/aspis-b-relation-claims-lean-20260722

LEAN_PATH="$work:$aspis_path:$aeneas_path" \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -o "$work/ComponentBRelationClaimsGenerated.olean" \
  aeneas-verif/component-b-relation-claims/proof/ComponentBRelationClaimsGenerated.lean

LEAN_PATH="$work:$aspis_path:$aeneas_path" \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -o "$work/ComponentBRelationClaimsProof.olean" \
  aeneas-verif/component-b-relation-claims/proof/ComponentBRelationClaimsProof.lean

LEAN_PATH="$work:$aspis_path:$aeneas_path" \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -o "$work/ComponentBRelationClaimsTerminalBridge.olean" \
  aeneas-verif/component-b-relation-claims/proof/ComponentBRelationClaimsTerminalBridge.lean
```

`replay-lean432.sh` provides a fresh-directory replay rather than depending on
the dated paths in this transcript.
