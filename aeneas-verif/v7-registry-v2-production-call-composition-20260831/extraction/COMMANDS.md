# Focused extraction and replay commands

The commands below were run from the task-owned Linux copy of source revision
`7179f7c550fe0461f4251dea5268af73876da91d` inside zero-swap systemd scopes.
Paths identify the pinned tool binaries used for the frozen run.

## Charon

```sh
/usr/bin/time -v \
  /home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon \
  cargo --preset aeneas --mir built --sysroot default \
  --start-from crate::v7_pair_forest_dispatch::reconstruct_asq8_statement_box_v1 \
  --start-from crate::v7_pair_forest_dispatch::emit_result_v1 \
  --include aspis_statement \
  --include aspis_core::field::M31 \
  --opaque crate::verify::sbf_hashv \
  --dest-file V7PairForestProductionCodecs02.llbc \
  -- --package aspis-verifier --lib --no-default-features \
  --features v7-pair-forest-one-tx-candidate
```

## Aeneas

```sh
/usr/bin/time -v \
  /home/dombarker/project-offloads/v7-pure-debug-build-output-r2/aeneas-borrowfree-variantfn-namespace-r1 \
  -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7PairForestProductionCodecsGenerated \
  -dest generated-codecs-02 \
  -subdir V7PairForestProductionCodecs \
  -split-files -emit-json V7PairForestProductionCodecs02.llbc
```

The generated external templates were completed with the same transparent
standard-library models used by the accepted source bundles. Then the checked
namespace staging transform was applied:

```sh
./source-transform/namespace-codec-generated-identifiers.sh generated-codecs-02
```

## Focused Lean order

With the pinned Aeneas Lean backend, generated codec directory, proof
directory, and the already-compiled Registry V2 caller/deployment bridge on
`LEAN_PATH`, compile only:

```sh
lean -o V7PairForestProductionCodecs/Types.olean \
  V7PairForestProductionCodecs/Types.lean
lean -o V7PairForestProductionCodecs/FunsExternal.olean \
  V7PairForestProductionCodecs/FunsExternal.lean
lean -o V7PairForestProductionCodecs/Funs.olean \
  V7PairForestProductionCodecs/Funs.lean
lean -o proof/V7PairForestProductionCodecSourceBridge.olean \
  proof/V7PairForestProductionCodecSourceBridge.lean
lean proof/V7RegistryV2ProductionAcceptedPathComposition.lean
```

The final target prints its axiom set directly. `evidence/NUC-RUNS.md` records
the exact units, invocations, wall times, peaks, swaps, and exits.
