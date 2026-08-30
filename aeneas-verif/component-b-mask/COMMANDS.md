# Component-B evaluator commands

All commands ran from `<repo>` unless a `cd` is shown.

## Rust tests

```sh
cargo +nightly-2026-06-01 test --release --locked -p aspis-core \
  state_only_sumcheck::tests::
cargo +nightly-2026-06-01 test --release --locked -p aspis-core --lib
```

## Owning-crate extraction

```sh
cd <repo>/crates/aspis-prover
CARGO_TARGET_DIR=<repo>/aeneas-verif/component-b-mask/target-v5-combined-20260720c \
  "$CHARON_BIN" cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::evaluate' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --dest-file='<repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_including_core.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask
```

The successful start matcher is exactly
`aspis_prover::v5_sumcheck_mask::_::evaluate`. The two real core includes and
the generated round-count include are part of the successful command.

```sh
"$AENEAS_BIN" \
  -backend lean \
  <repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_including_core.llbc \
  -dest <repo>/aeneas-verif/component-b-mask/generated/v5-evaluate-including-core \
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
cd <repo>/crates/aspis-prover
CARGO_TARGET_DIR=<repo>/aeneas-verif/component-b-mask/target-v5-current-evaluate-20260722 \
  "$CHARON_BIN" cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::evaluate' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::evaluate_state_only_polynomial' \
    --include='aspis_core::state_only_sumcheck::state_only_boundary_sum' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_DEGREE' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_COEFFICIENTS' \
    --dest-file='<repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_current_20260722.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask

"$AENEAS_BIN" \
  -backend lean \
  <repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_evaluate_current_20260722.llbc \
  -dest <temporary> \
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

## Sampler/evaluator terminal integration replay

The durable all-proof gate compiles 81 exported sampler/evaluator/terminal
theorems with 81 matching `#print axioms` commands:

```sh
cd <repo>/aeneas-verif/component-b-mask
AENEAS432_BACKEND=$AENEAS_LEAN_BACKEND \
  ./replay-lean432.sh
```

This uses Lean 4.32 default proof limits.  The current-source mixing kernel has
its independent exact extraction and replay commands in
`mixing-current-20260721/COMMANDS.md`; its successful matchers are
`aspis_prover::v5_sumcheck_mask::_::round_polynomial` and
`aspis_prover::v5_sumcheck_mask::_::mixed_round_polynomial`.

## Authoritative authentic sampler extraction

The source-authentic sampler LLBC used by the integration theorem was produced from the
owning crate by:

```sh
cd <repo>/crates/aspis-prover
CARGO_TARGET_DIR=<repo>/aeneas-verif/component-b-mask/target-v5-sampler-current-20260722 \
  "$CHARON_BIN" cargo \
    --preset=aeneas --abort-on-error \
    --start-from='aspis_prover::v5_sumcheck_mask::_::sample' \
    --include='aspis_core::field' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_ROUNDS' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_DEGREE' \
    --include='aspis_core::state_only_sumcheck::STATE_ONLY_SUMCHECK_COEFFICIENTS' \
    --include='aspis_core::state_only_sumcheck::state_only_boundary_sum' \
    --dest-file='<repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_sampler_current_20260722.llbc' \
    -- --release --locked -p aspis-prover --features v5-mask

"$AENEAS_BIN" \
  -backend lean \
  <repo>/aeneas-verif/component-b-mask/llbc/component_b_v5_sampler_current_20260722.llbc \
  -dest <temporary> \
  -split-files \
  -max-heartbeats 200000 -max-recdepth 1000 \
  -abort-on-error -warnings-as-errors -no-progress-bar
```

It has 88 ordered declaration groups and `has_errors=false`. The replay checks
both embedded owning-source files byte-for-byte, authenticates the complete
raw-to-Lean-4.32 normalization diff, and compiles the generated modules at
default proof limits.
