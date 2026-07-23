# Commands

## Charon

```sh
cd /Users/dominic/ZK
CARGO_TARGET_DIR=/private/tmp/component-b-unified-target-rerun-20260722 \
  /private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
    --preset=aeneas \
    --start-from='aspis_prover::v5_sumcheck_mask::v5_sumcheck_mask_mixing_evaluate_correspondence' \
    --start-from='aspis_prover::v5_sumcheck_mask::_::sample' \
    --start-from='aspis_prover::v5_sumcheck_mask::sample_zero_boundary_round' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial' \
    --include='aspis_core::state_only_sumcheck::state_only_boundary_sum' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_DEGREE' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_COEFFICIENTS' \
    --dest-file='/Users/dominic/ZK/aeneas-verif/component-b-mask/unified-current-20260722/llbc/component_b_sampler_mixing_evaluate_unified_20260722.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask
```

The serialized LLBC options record these exact three matchers, includes,
preset, destination, and owning package graph.

## Aeneas

```sh
/private/tmp/aspis-aeneas-tools.aTcyie/aeneas/bin/aeneas \
  -backend lean \
  /Users/dominic/ZK/aeneas-verif/component-b-mask/unified-current-20260722/llbc/component_b_sampler_mixing_evaluate_unified_20260722.llbc \
  -dest /Users/dominic/ZK/aeneas-verif/component-b-mask/unified-current-20260722/generated/sampler-helper-raw \
  -namespace ComponentBGenerated \
  -split-files \
  -gen-lib-entry \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar
```

The generation limits above are Aeneas generation settings.  They are removed
from the retained normalized modules; all retained proofs compile at Lean's
default limits.

## Lean 4.32 clean replay

```sh
AENEAS432_BACKEND=/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean \
COMPONENT_B_REPLAY_OUT=/private/tmp/component-b-unified-independent \
  /Users/dominic/ZK/aeneas-verif/component-b-mask/unified-current-20260722/replay-lean432.sh
```

## Rust tests

```sh
CARGO_TARGET_DIR=/private/tmp/aspis-b-terminal-tests \
  cargo +nightly-2026-06-01 test --release --locked \
    -p aspis-prover --features v5-mask \
    v5_sumcheck_mask::tests::correspondence_helper_calls_the_actual_mixing_and_evaluator \
    -- --exact

CARGO_TARGET_DIR=/private/tmp/aspis-b-terminal-tests \
  cargo +nightly-2026-06-01 test --release --locked \
    -p aspis-prover --features v5-mask --lib
```
