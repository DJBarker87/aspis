# Component-B evaluator commands

All commands ran from `/Users/dominic/ZK` unless a `cd` is shown.

## Rust tests

```sh
cargo +nightly-2026-06-01 test --release --locked -p aspis-core \
  state_only_sumcheck::tests::
cargo +nightly-2026-06-01 test --release --locked -p aspis-core --lib
```

## Owning-crate extraction

```sh
cd /Users/dominic/ZK/crates/aspis-prover
CARGO_TARGET_DIR=/Users/dominic/ZK/aeneas-verif/component-b-mask/target-v5-combined-20260720c \
  /private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::evaluate' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --dest-file='/Users/dominic/ZK/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_including_core.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask
```

The successful start matcher is exactly
`aspis_prover::v5_sumcheck_mask::_::evaluate`. The two real core includes and
the generated round-count include are part of the successful command.

```sh
/private/tmp/aspis-aeneas-tools.aTcyie/aeneas/bin/aeneas \
  -backend lean \
  /Users/dominic/ZK/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_including_core.llbc \
  -dest /Users/dominic/ZK/aeneas-verif/component-b-mask/generated/v5-evaluate-including-core \
  -max-heartbeats 200000 -max-recdepth 1000 -abort-on-error \
  -warnings-as-errors -no-progress-bar
```

The Aeneas limits above govern generation only. All retained Lean replay and
proof commands below use Lean's default proof limits.

## Lean 4.32 replay

The replay uses the patched Aeneas b59d5188 runtime supplied by the primary
lane and its authenticated arithmetic bundle. The durable gate is
`./replay-lean432.sh`; it accepts their locations as environment variables.

## 2026-07-22 authoritative current-source extraction

```sh
cd /Users/dominic/ZK/crates/aspis-prover
CARGO_TARGET_DIR=/Users/dominic/ZK/aeneas-verif/component-b-mask/target-v5-current-evaluate-20260722 \
  /private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::evaluate' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial' \
    --include='aspis_core::state_only_sumcheck::state_only_boundary_sum' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_DEGREE' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_COEFFICIENTS' \
    --dest-file='/Users/dominic/ZK/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_current_20260722.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask

/private/tmp/aspis-aeneas-tools.aTcyie/aeneas/bin/aeneas \
  -backend lean \
  /Users/dominic/ZK/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_current_20260722.llbc \
  -dest /private/tmp/component-b-current-evaluate-split-20260722a \
  -namespace ComponentBV5EvaluateCurrent20260722 \
  -split-files \
  -max-heartbeats 200000 -max-recdepth 1000 \
  -abort-on-error -warnings-as-errors -no-progress-bar
```

The LLBC has 101 ordered declarations, 67 file records, `has_errors=false`, and
SHA-256 `5d5d4a47d2013a3ff629c549c281c94a87c595f3c6883a4b54daf239e08fef47`.
It embeds the exact current v5 source SHA `f1fb486f…`.  Aeneas generation limits
above do not affect the retained proof replay; `replay-lean432.sh` compiles all
normalized modules at Lean defaults and authenticates the complete retained
raw-to-normalized diff.

## Deterministic terminal capstone replay

The durable all-proof gate excludes the generic sampler and compiles 49
exported evaluator/terminal theorems with 49 matching `#print axioms` commands:

```sh
cd /Users/dominic/ZK/aeneas-verif/component-b-mask
AENEAS432_BACKEND=/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean \
  ./replay-lean432.sh
```

This uses Lean 4.32 default proof limits.  The current-source mixing kernel has
its independent exact extraction and replay commands in
`mixing-current-20260721/COMMANDS.md`; its successful matchers are
`aspis_prover::v5_sumcheck_mask::_::round_polynomial` and
`aspis_prover::v5_sumcheck_mask::_::mixed_round_polynomial`.

## Optional authentic sampler extraction evidence

The generic sampler is not part of the deterministic replay or theorem claim.
For provenance only, the retained nonempty LLBC was produced from the owning
crate by:

```sh
cd /Users/dominic/ZK/crates/aspis-prover
CARGO_TARGET_DIR=/Users/dominic/ZK/aeneas-verif/component-b-mask/target-v5-sampler-authenticated-constants-20260721 \
  /private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::sample' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_DEGREE' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_COEFFICIENTS' \
    --include='aspis_core::state_only_sumcheck::state_only_boundary_sum' \
    --dest-file='/Users/dominic/ZK/aeneas-verif/component-b-mask/llbc/component_b_v5_sampler_authenticated_constants_20260721.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask
```

It has 88 ordered declaration groups and `has_errors=false`.  The LLBC and raw
generated output are retained in `metadata/SHA256SUMS`, but no sampler proof is
in that manifest or replay.
